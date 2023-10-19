use crate::{format, internal_err, public_key, signer::EthSigner};
use anyhow::anyhow;
use borderland_runtime_api::{ConvertTransactionRuntimeApi, EthereumRuntimeRPCApi};
use ethereum::TransactionV2 as EthereumTransaction;
use ethereum_types::{H160, H256, H512, H64, U256, U64};
use fc_rpc_core::{types::*, EthApiServer};
use futures::TryFutureExt;
use jsonrpsee::core::{async_trait, RpcResult};
use jsonrpsee::{core::Error as RpcError, types::error::CallError};
use sc_client_api::{
    backend::{Backend, StorageProvider},
    BlockBackend,
};
use sc_network_sync::SyncingService;
use sc_transaction_pool::{ChainApi, Pool};
use sc_transaction_pool_api::TransactionSource;
use sc_transaction_pool_api::{InPoolTransaction, TransactionPool};
use scale_codec::Encode;
use sp_api::{ApiRef, CallApiAt, Core, HeaderT, ProvideRuntimeApi};
use sp_block_builder::BlockBuilder as BlockBuilderApi;
use sp_blockchain::HeaderBackend;
use sp_consensus::SyncOracle;
use sp_io::hashing::blake2_256;
use sp_runtime::traits::{Block as BlockT, NumberFor, UniqueSaturatedInto};
use sp_runtime::{generic::BlockId, traits::Zero};
use std::{collections::BTreeMap, marker::PhantomData, sync::Arc};

pub async fn native_block_id<B: BlockT, C>(
    client: &C,
    number: Option<BlockNumber>,
) -> RpcResult<Option<BlockId<B>>>
where
    B: BlockT,
    <B as BlockT>::Hash: From<H256>,
    C: HeaderBackend<B> + 'static,
{
    Ok(match number.unwrap_or(BlockNumber::Latest) {
        BlockNumber::Hash { hash, .. } => Some(BlockId::Hash(hash.into())),
        BlockNumber::Num(number) => Some(BlockId::Number(number.unique_saturated_into())),
        BlockNumber::Latest => Some(BlockId::Hash(client.info().best_hash)),
        BlockNumber::Earliest => Some(BlockId::Number(Zero::zero())),
        BlockNumber::Pending => None,
        BlockNumber::Safe => Some(BlockId::Hash(client.info().finalized_hash)),
        BlockNumber::Finalized => Some(BlockId::Hash(client.info().finalized_hash)),
    })
}

fn convert_substrate_block<SubstrateBlock: BlockT>(
    block: SubstrateBlock,
    eth_transactions: Vec<(EthereumTransaction, H256)>,
    hash: H256,
    base_fee: Option<U256>,
    full_transactions: bool,
    is_pending: bool,
) -> Rich<Block>
where
    <SubstrateBlock as BlockT>::Hash: Into<H256>,
    <<SubstrateBlock as BlockT>::Header as HeaderT>::Number: Into<U256>,
{
    let (hash, miner, nonce, total_difficulty) = if !is_pending {
        (
            Some(hash),
            Some(Default::default()), // TODO.
            Some(Default::default()), // TODO.
            Some(U256::zero()),
        )
    } else {
        (None, None, None, None)
    };

    Rich {
        inner: Block {
            header: Header {
                hash,
                parent_hash: block.header().parent_hash().clone().into(),
                uncles_hash: Default::default(), // TODO.
                author: Default::default(),      // TODO.
                miner,
                state_root: block.header().state_root().clone().into(),
                transactions_root: block.header().extrinsics_root().clone().into(),
                receipts_root: block.header().extrinsics_root().clone().into(), // TODO.
                number: Some(block.header().number().clone().into()),
                gas_used: Default::default(),       // TODO.
                gas_limit: Default::default(),      // TODO.
                extra_data: Default::default(),     // TODO.
                logs_bloom: Default::default(),     // TODO.
                timestamp: U256::from(1000 / 1000), // TODO.
                difficulty: Default::default(),     // TODO.
                nonce,
                size: Some(U256::from(block.header().encoded_size() as u32)),
            },
            total_difficulty,
            uncles: vec![],
            transactions: {
                if full_transactions {
                    BlockTransactions::Full(
                        eth_transactions
                            .iter()
                            .enumerate()
                            .map(|(index, (transaction, _))| {
                                transaction_build(
                                    transaction.clone(),
                                    Some((
                                        block.header().hash().clone().into(),
                                        block.header().number().clone().into(),
                                    )),
                                    index.into(),
                                )
                            })
                            .collect(),
                    )
                } else {
                    BlockTransactions::Hashes(
                        eth_transactions.iter().map(|(_, hash)| *hash).collect(),
                    )
                }
            },
            size: Some(U256::from(block.encoded_size() as u32)),
            base_fee_per_gas: base_fee,
        },
        extra_info: BTreeMap::new(),
    }
}

fn transaction_build(
    ethereum_transaction: EthereumTransaction,
    block_hash_number: Option<(H256, U256)>,
    index: U256,
) -> Transaction {
    let mut transaction: Transaction = ethereum_transaction.clone().into();

    if let EthereumTransaction::EIP1559(_) = ethereum_transaction {
        if block_hash_number.is_none() {
            // If transaction is not mined yet, gas price is considered just max fee per gas.
            transaction.gas_price = transaction.max_fee_per_gas;
        } else {
            let max_priority_fee_per_gas = transaction.max_priority_fee_per_gas.unwrap_or_default();
            let max_fee_per_gas = transaction.max_fee_per_gas.unwrap_or_default();
            // If transaction is already mined, gas price is the effective gas price.
            transaction.gas_price = Some(max_priority_fee_per_gas.min(max_fee_per_gas));
        }
    }

    let pubkey = match public_key(&ethereum_transaction) {
        Ok(p) => Some(p),
        Err(_e) => None,
    };

    // Block hash.
    transaction.block_hash = block_hash_number.map(|t| t.0);
    // Block number.
    transaction.block_number = block_hash_number.map(|t| t.1);
    // Transaction index.
    transaction.transaction_index = Some(index); // TODO.

    // Public key.
    transaction.public_key = pubkey.as_ref().map(H512::from);

    transaction
}

fn pending_runtime_api<'a, B: BlockT, C, BE, A: ChainApi>(
    client: &'a C,
    graph: &'a Pool<A>,
) -> RpcResult<ApiRef<'a, C::Api>>
where
    B: BlockT,
    C: ProvideRuntimeApi<B>,
    C::Api: BlockBuilderApi<B> + EthereumRuntimeRPCApi<B>,
    C: HeaderBackend<B> + StorageProvider<B, BE> + 'static,
    BE: Backend<B>,
    A: ChainApi<Block = B> + 'static,
{
    // In case of Pending, we need an overlayed state to query over.
    let api = client.runtime_api();
    let best_hash = client.info().best_hash;
    // Get all transactions in the ready queue.
    let xts: Vec<<B as BlockT>::Extrinsic> = graph
        .validated_pool()
        .ready()
        .map(|in_pool_tx| in_pool_tx.data().clone())
        .collect::<Vec<<B as BlockT>::Extrinsic>>();
    // Manually initialize the overlay.
    if let Ok(Some(header)) = client.header(best_hash) {
        let parent_hash = *header.parent_hash();
        api.initialize_block(parent_hash, &header)
            .map_err(|e| internal_err(format!("Runtime api access error: {:?}", e)))?;
        // Apply the ready queue to the best block's state.
        for xt in xts {
            let _ = api.apply_extrinsic(best_hash, xt);
        }
        Ok(api)
    } else {
        Err(internal_err(format!(
            "Cannot get header for block {:?}",
            best_hash
        )))
    }
}

pub struct EthCompatServer<Block: BlockT, Client, Backend, Api: ChainApi, TxPool> {
    client: Arc<Client>,
    sync: Arc<SyncingService<Block>>,
    graph: Arc<Pool<Api>>,
    pool: Arc<TxPool>,

    signers: Vec<Box<dyn EthSigner>>,

    _marker: PhantomData<(Block, Backend)>,
}

impl<Block: BlockT, Client, Backend, Api: ChainApi, TxPool>
    EthCompatServer<Block, Client, Backend, Api, TxPool>
{
    pub fn new(
        client: Arc<Client>,
        sync: Arc<SyncingService<Block>>,
        graph: Arc<Pool<Api>>,
        pool: Arc<TxPool>,
        signers: Vec<Box<dyn EthSigner>>,
    ) -> Self {
        Self {
            client,
            sync,
            graph,
            pool,
            signers,

            _marker: PhantomData,
        }
    }
}

#[async_trait]
impl<Block, Client, BackEnd, Api, TxPool> EthApiServer
    for EthCompatServer<Block, Client, BackEnd, Api, TxPool>
where
    Api: ChainApi<Block = Block> + 'static,
    Block: BlockT,
    <Block as BlockT>::Hash: From<H256>,
    BackEnd: Backend<Block> + 'static,
    Client: CallApiAt<Block> + ProvideRuntimeApi<Block>,
    Client::Api:
        BlockBuilderApi<Block> + ConvertTransactionRuntimeApi<Block> + EthereumRuntimeRPCApi<Block>,
    Client: HeaderBackend<Block> + StorageProvider<Block, BackEnd> + 'static,
    Client: BlockBackend<Block>,
    TxPool: TransactionPool<Block = Block> + 'static,

    <Block as BlockT>::Hash: Into<H256>,
    <<Block as BlockT>::Header as HeaderT>::Number: Into<U256>,
{
    // ########################################################################
    // Client
    // ########################################################################

    fn protocol_version(&self) -> RpcResult<u64> {
        log::error!("EthCompatServer called: protocol_version");

        Ok(1)
    }

    fn syncing(&self) -> RpcResult<SyncStatus> {
        log::error!("EthCompatServer called: syncing");

        if self.sync.is_major_syncing() {
            let block_number = U256::from(UniqueSaturatedInto::<u128>::unique_saturated_into(
                self.client.info().best_number,
            ));

            Ok(SyncStatus::Info(SyncInfo {
                starting_block: U256::zero(),
                current_block: block_number,
                // TODO `highest_block` is not correct, should load `best_seen_block`.
                highest_block: block_number,
                warp_chunks_amount: None,
                warp_chunks_processed: None,
            }))
        } else {
            Ok(SyncStatus::None)
        }
    }

    fn author(&self) -> RpcResult<H160> {
        log::error!("EthCompatServer called: author");

        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    fn accounts(&self) -> RpcResult<Vec<H160>> {
        log::error!("EthCompatServer called: accounts");

        let mut accounts = Vec::new();
        for signer in &*self.signers {
            accounts.append(&mut signer.accounts());
        }
        Ok(accounts)
    }

    fn block_number(&self) -> RpcResult<U256> {
        log::error!("EthCompatServer called: block_number");

        Ok(U256::from(
            UniqueSaturatedInto::<u128>::unique_saturated_into(self.client.info().best_number),
        ))
    }

    fn chain_id(&self) -> RpcResult<Option<U64>> {
        log::error!("EthCompatServer called: chain_id");

        let hash = self.client.info().best_hash;
        Ok(Some(
            self.client
                .runtime_api()
                .chain_id(hash)
                .map_err(|err| {
                    RpcError::Call(CallError::Failed(anyhow!(
                        "Failed to fetch chain id: {:?}",
                        err
                    )))
                })?
                .into(),
        ))
    }

    // ########################################################################
    // Block
    // ########################################################################

    async fn block_by_hash(&self, hash: H256, full: bool) -> RpcResult<Option<RichBlock>> {
        log::error!(
            "EthCompatServer called: block_by_hash({:?}, {:?})",
            hash,
            full
        );

        let block_hash: <Block as BlockT>::Hash = hash.into();

        let substrate_block = self.client.block(block_hash).map_err(|err| {
            RpcError::Call(CallError::Failed(anyhow!(
                "Failed to find block: {:?}",
                err
            )))
        })?;

        let maybe_transactions = self.client.block_body(block_hash).map_err(|err| {
            RpcError::Call(CallError::Failed(anyhow!(
                "Failed to find block: {:?}",
                err
            )))
        })?;

        let base_fee = self.client.runtime_api().gas_price(block_hash).ok();

        match (substrate_block, maybe_transactions) {
            (Some(block), Some(transactions)) => {
                let eth_transactions: Vec<(EthereumTransaction, H256)> = self
                    .client
                    .runtime_api()
                    .extrinsic_filter_with_hash(block_hash, transactions)
                    .map_err(|err| {
                        RpcError::Call(CallError::Failed(anyhow!(
                            "Failed to filter transactions: {:?}",
                            err
                        )))
                    })?;

                let rich_block = convert_substrate_block(
                    block.block,
                    eth_transactions,
                    hash,
                    base_fee,
                    full,
                    false,
                );

                Ok(Some(rich_block))
            }
            _ => Ok(None),
        }
    }

    async fn block_by_number(
        &self,
        number: BlockNumber,
        full: bool,
    ) -> RpcResult<Option<RichBlock>> {
        log::error!(
            "EthCompatServer called: block_by_number({:?}, {:?})",
            number,
            full
        );

        match number {
            BlockNumber::Pending => {
                let best_hash = self.client.info().best_hash;

                // Get current in-pool transactions
                let mut xts: Vec<<Block as BlockT>::Extrinsic> = Vec::new();
                // ready validated pool
                xts.extend(
                    self.graph
                        .validated_pool()
                        .ready()
                        .map(|in_pool_tx| in_pool_tx.data().clone())
                        .collect::<Vec<<Block as BlockT>::Extrinsic>>(),
                );

                // future validated pool
                xts.extend(
                    self.graph
                        .validated_pool()
                        .futures()
                        .iter()
                        .map(|(_hash, extrinsic)| extrinsic.clone())
                        .collect::<Vec<<Block as BlockT>::Extrinsic>>(),
                );

                let substrate_block = self.client.block(best_hash).map_err(|err| {
                    RpcError::Call(CallError::Failed(anyhow!(
                        "Failed to find block: {:?}",
                        err
                    )))
                })?;

                let base_fee = self.client.runtime_api().gas_price(best_hash).ok();

                match substrate_block {
                    Some(block) => {
                        let eth_transactions: Vec<(EthereumTransaction, H256)> = self
                            .client
                            .runtime_api()
                            .extrinsic_filter_with_hash(best_hash, xts)
                            .map_err(|err| {
                                RpcError::Call(CallError::Failed(anyhow!(
                                    "Failed to filter transactions: {:?}",
                                    err
                                )))
                            })?;

                        let rich_block = convert_substrate_block(
                            block.block,
                            eth_transactions,
                            best_hash.into(),
                            base_fee,
                            full,
                            false,
                        );

                        Ok(Some(rich_block))
                    }
                    _ => Ok(None),
                }
            }

            BlockNumber::Num(num) => {
                let id = BlockId::number(NumberFor::<Block>::try_from(num).map_err(|_| {
                    RpcError::Call(CallError::Failed(anyhow!("Invalid block number")))
                })?);

                let hash = self.client.expect_block_hash_from_id(&id).map_err(|_| {
                    RpcError::Call(CallError::Failed(anyhow!(
                        "Expect block number from id: {}",
                        id
                    )))
                })?;

                let substrate_block = self.client.block(hash).map_err(|err| {
                    RpcError::Call(CallError::Failed(anyhow!(
                        "Failed to find block: {:?}",
                        err
                    )))
                })?;

                let maybe_transactions = self.client.block_body(hash).map_err(|err| {
                    RpcError::Call(CallError::Failed(anyhow!(
                        "Failed to find block: {:?}",
                        err
                    )))
                })?;

                let base_fee = self.client.runtime_api().gas_price(hash).ok();

                match (substrate_block, maybe_transactions) {
                    (Some(block), Some(transactions)) => {
                        let eth_transactions: Vec<(EthereumTransaction, H256)> = self
                            .client
                            .runtime_api()
                            .extrinsic_filter_with_hash(hash, transactions)
                            .map_err(|err| {
                                RpcError::Call(CallError::Failed(anyhow!(
                                    "Failed to filter transactions: {:?}",
                                    err
                                )))
                            })?;

                        log::error!(
                            "EthCompatServer block_by_number eth_transactions: {:#?}",
                            eth_transactions
                        );

                        let rich_block = convert_substrate_block(
                            block.block,
                            eth_transactions,
                            hash.into(),
                            base_fee,
                            full,
                            false,
                        );

                        Ok(Some(rich_block))
                    }
                    _ => Ok(None),
                }
            }

            _ => Ok(None),
        }
    }

    async fn block_transaction_count_by_hash(&self, hash: H256) -> RpcResult<Option<U256>> {
        log::error!(
            "EthCompatServer called: block_transaction_count_by_hash({:?})",
            hash
        );

        Ok(self
            .client
            .block_body(hash.into())
            .map_err(|err| {
                RpcError::Call(CallError::Failed(anyhow!(
                    "Failed to find block: {:?}",
                    err
                )))
            })?
            .map(|txs| U256::from(txs.len())))
    }

    async fn block_transaction_count_by_number(
        &self,
        number: BlockNumber,
    ) -> RpcResult<Option<U256>> {
        log::error!(
            "EthCompatServer called: block_transaction_count_by_number({:?})",
            number
        );

        match number {
            BlockNumber::Pending => {
                // Get current in-pool transactions
                let mut xts: Vec<<Block as BlockT>::Extrinsic> = Vec::new();
                // ready validated pool
                xts.extend(
                    self.graph
                        .validated_pool()
                        .ready()
                        .map(|in_pool_tx| in_pool_tx.data().clone())
                        .collect::<Vec<<Block as BlockT>::Extrinsic>>(),
                );

                // future validated pool
                xts.extend(
                    self.graph
                        .validated_pool()
                        .futures()
                        .iter()
                        .map(|(_hash, extrinsic)| extrinsic.clone())
                        .collect::<Vec<<Block as BlockT>::Extrinsic>>(),
                );

                Ok(Some(U256::from(xts.len())))
            }

            BlockNumber::Num(num) => {
                let id = BlockId::number(NumberFor::<Block>::try_from(num).map_err(|_| {
                    RpcError::Call(CallError::Failed(anyhow!("Invalid block number")))
                })?);

                let hash = self.client.expect_block_hash_from_id(&id).map_err(|_| {
                    RpcError::Call(CallError::Failed(anyhow!(
                        "Expect block number from id: {}",
                        id
                    )))
                })?;

                let maybe_transactions = self.client.block_body(hash).map_err(|err| {
                    RpcError::Call(CallError::Failed(anyhow!(
                        "Failed to find block: {:?}",
                        err
                    )))
                })?;

                Ok(maybe_transactions.map(|txs| U256::from(txs.len())))
            }

            _ => Ok(None),
        }
    }

    fn block_uncles_count_by_hash(&self, hash: H256) -> RpcResult<U256> {
        log::error!(
            "EthCompatServer called: block_uncles_count_by_hash({:?})",
            hash
        );
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    fn block_uncles_count_by_number(&self, number: BlockNumber) -> RpcResult<U256> {
        log::error!(
            "EthCompatServer called: block_uncles_count_by_number({:?})",
            number
        );
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    fn uncle_by_block_hash_and_index(
        &self,
        hash: H256,
        index: Index,
    ) -> RpcResult<Option<RichBlock>> {
        log::error!(
            "EthCompatServer called: uncle_by_block_hash_and_index({:?}, {:?})",
            hash,
            index
        );
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    fn uncle_by_block_number_and_index(
        &self,
        number: BlockNumber,
        index: Index,
    ) -> RpcResult<Option<RichBlock>> {
        log::error!(
            "EthCompatServer called: uncle_by_block_number_and_index({:?}, {:?})",
            number,
            index
        );
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    // ########################################################################
    // Transaction
    // ########################################################################

    async fn transaction_by_hash(&self, hash: H256) -> RpcResult<Option<Transaction>> {
        log::error!("EthCompatServer called: transaction_by_hash({:?})", hash);
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    async fn transaction_by_block_hash_and_index(
        &self,
        hash: H256,
        index: Index,
    ) -> RpcResult<Option<Transaction>> {
        log::error!(
            "EthCompatServer called: transaction_by_block_hash_and_index({:?}, {:?})",
            hash,
            index
        );
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    async fn transaction_by_block_number_and_index(
        &self,
        number: BlockNumber,
        index: Index,
    ) -> RpcResult<Option<Transaction>> {
        log::error!(
            "EthCompatServer called: transaction_by_block_number_and_index({:?}, {:?})",
            number,
            index
        );
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    async fn transaction_receipt(&self, hash: H256) -> RpcResult<Option<Receipt>> {
        log::error!("EthCompatServer called: transaction_receipt({:?})", hash);

        Ok(None)
    }

    // ########################################################################
    // State
    // ########################################################################

    async fn balance(&self, address: H160, number: Option<BlockNumber>) -> RpcResult<U256> {
        log::error!(
            "EthCompatServer called: balance({:?}, {:?})",
            address,
            number
        );

        let number = number.unwrap_or(BlockNumber::Latest);

        if number == BlockNumber::Pending {
            let api = pending_runtime_api(self.client.as_ref(), self.graph.as_ref())?;
            Ok(api
                .account_basic(self.client.info().best_hash, address)
                .map_err(|err| {
                    RpcError::Call(CallError::Failed(anyhow!(
                        "Failed to fetch chain id: {:?}",
                        err
                    )))
                })?
                .balance)
        } else {
            // TODO: Implement balance query at specific block.

            let api = pending_runtime_api(self.client.as_ref(), self.graph.as_ref())?;
            Ok(api
                .account_basic(self.client.info().best_hash, address)
                .map_err(|err| {
                    RpcError::Call(CallError::Failed(anyhow!(
                        "Failed to fetch chain id: {:?}",
                        err
                    )))
                })?
                .balance)
        }
    }

    async fn storage_at(
        &self,
        address: H160,
        index: U256,
        number: Option<BlockNumber>,
    ) -> RpcResult<H256> {
        log::error!(
            "EthCompatServer called: storage_at({:?}, {:?}, {:?})",
            address,
            index,
            number
        );
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    async fn transaction_count(
        &self,
        address: H160,
        number: Option<BlockNumber>,
    ) -> RpcResult<U256> {
        log::error!(
            "EthCompatServer called: transaction_count({:?}, {:?})",
            address,
            number
        );

        match number {
            Some(BlockNumber::Pending) => {
                let substrate_hash = self.client.info().best_hash;

                let nonce = self
                    .client
                    .runtime_api()
                    .account_basic(substrate_hash, address)
                    .map_err(|err| {
                        RpcError::Call(CallError::Failed(anyhow!(
                            "fetch runtime account basic failed: {:?}",
                            err
                        )))
                    })?
                    .nonce;

                let mut current_nonce = nonce;
                let mut current_tag = ("EthTx", (address, nonce)).encode();
                for tx in self.pool.ready() {
                    // since transactions in `ready()` need to be ordered by nonce
                    // it's fine to continue with current iterator.
                    if tx.provides().get(0) == Some(&current_tag) {
                        current_nonce = current_nonce.saturating_add(1.into());
                        current_tag = ("EthTx", (address, current_nonce)).encode();
                    }
                }

                Ok(current_nonce)
            }

            Some(BlockNumber::Num(num)) => {
                let id = BlockId::number(NumberFor::<Block>::try_from(num).map_err(|_| {
                    RpcError::Call(CallError::Failed(anyhow!("Invalid block number")))
                })?);

                let substrate_hash = self.client.expect_block_hash_from_id(&id).map_err(|_| {
                    RpcError::Call(CallError::Failed(anyhow!(
                        "Expect block number from id: {}",
                        id
                    )))
                })?;

                Ok(self
                    .client
                    .runtime_api()
                    .account_basic(substrate_hash, address)
                    .map_err(|err| {
                        RpcError::Call(CallError::Failed(anyhow!(
                            "fetch runtime account basic failed: {:?}",
                            err
                        )))
                    })?
                    .nonce)
            }

            _ => Err(jsonrpsee::core::Error::HttpNotImplemented),
        }
    }

    async fn code_at(&self, address: H160, number: Option<BlockNumber>) -> RpcResult<Bytes> {
        log::error!(
            "EthCompatServer called: code_at({:?}, {:?})",
            address,
            number
        );

        Ok(Bytes(vec![]))
    }

    // ########################################################################
    // Execute
    // ########################################################################

    async fn call(
        &self,
        request: CallRequest,
        number: Option<BlockNumber>,
        state_overrides: Option<BTreeMap<H160, CallStateOverride>>,
    ) -> RpcResult<Bytes> {
        log::error!(
            "EthCompatServer called: call({:?}, {:?}, {:?})",
            request,
            number,
            state_overrides
        );
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    async fn estimate_gas(
        &self,
        request: CallRequest,
        number: Option<BlockNumber>,
    ) -> RpcResult<U256> {
        log::error!(
            "EthCompatServer called: estimate_gas({:?}, {:?})",
            request,
            number
        );
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    // ########################################################################
    // Fee
    // ########################################################################

    fn gas_price(&self) -> RpcResult<U256> {
        log::error!("EthCompatServer called: gas_price");

        let block_hash = self.client.info().best_hash;

        self.client
            .runtime_api()
            .gas_price(block_hash)
            .map_err(|err| {
                RpcError::Call(CallError::Failed(anyhow!(
                    "Failed to fetch chain id: {:?}",
                    err
                )))
            })
    }

    async fn fee_history(
        &self,
        block_count: U256,
        newest_block: BlockNumber,
        reward_percentiles: Option<Vec<f64>>,
    ) -> RpcResult<FeeHistory> {
        log::error!(
            "EthCompatServer called: fee_history({:?}, {:?}, {:?})",
            block_count,
            newest_block,
            reward_percentiles
        );
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    fn max_priority_fee_per_gas(&self) -> RpcResult<U256> {
        log::error!("EthCompatServer called: max_priority_fee_per_gas");
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    // ########################################################################
    // Mining
    // ########################################################################

    fn is_mining(&self) -> RpcResult<bool> {
        log::error!("EthCompatServer called: is_mining");
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    fn hashrate(&self) -> RpcResult<U256> {
        log::error!("EthCompatServer called: hashrate");
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    fn work(&self) -> RpcResult<Work> {
        log::error!("EthCompatServer called: work");
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    fn submit_hashrate(&self, hashrate: U256, id: H256) -> RpcResult<bool> {
        log::error!(
            "EthCompatServer called: submit_hashrate({:?}, {:?})",
            hashrate,
            id
        );
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    fn submit_work(&self, nonce: H64, pow_hash: H256, mix_digest: H256) -> RpcResult<bool> {
        log::error!(
            "EthCompatServer called: submit_work({:?}, {:?}, {:?})",
            nonce,
            pow_hash,
            mix_digest
        );
        Err(jsonrpsee::core::Error::HttpNotImplemented)
    }

    // ########################################################################
    // Submit
    // ########################################################################

    async fn send_transaction(&self, request: TransactionRequest) -> RpcResult<H256> {
        log::error!("EthCompatServer called: send_transaction({:?})", request);

        let from = match request.from {
            Some(from) => from,
            None => {
                let accounts = match self.accounts() {
                    Ok(accounts) => accounts,
                    Err(e) => return Err(e),
                };

                match accounts.get(0) {
                    Some(account) => *account,
                    None => {
                        return Err(RpcError::Call(CallError::Failed(anyhow!(
                            "No signers available"
                        ))))
                    }
                }
            }
        };

        let nonce = match request.nonce {
            Some(nonce) => nonce,
            None => match self.transaction_count(from, None).await {
                Ok(nonce) => nonce,
                Err(e) => return Err(e),
            },
        };

        let chain_id = match self.chain_id() {
            Ok(Some(chain_id)) => chain_id.as_u64(),
            Ok(None) => {
                return Err(RpcError::Call(CallError::Failed(anyhow!(
                    "Chain id not available"
                ))))
            }
            Err(e) => return Err(e),
        };

        let message: Option<TransactionMessage> = request.into();
        let message = match message {
            Some(TransactionMessage::Legacy(mut m)) => {
                m.nonce = nonce;
                m.chain_id = Some(chain_id);
                TransactionMessage::Legacy(m)
            }
            Some(TransactionMessage::EIP2930(mut m)) => {
                m.nonce = nonce;
                m.chain_id = chain_id;
                TransactionMessage::EIP2930(m)
            }
            Some(TransactionMessage::EIP1559(mut m)) => {
                m.nonce = nonce;
                m.chain_id = chain_id;
                TransactionMessage::EIP1559(m)
            }
            _ => {
                return Err(RpcError::Call(CallError::Failed(anyhow!(
                    "Invalid transaction parameters"
                ))))
            }
        };

        let mut transaction = None;

        for signer in &self.signers {
            if signer.accounts().contains(&from) {
                match signer.sign(message, &from) {
                    Ok(t) => transaction = Some(t),
                    Err(e) => return Err(e),
                }
                break;
            }
        }

        let transaction = match transaction {
            Some(transaction) => transaction,
            None => {
                return Err(RpcError::Call(CallError::Failed(anyhow!(
                    "No signer available"
                ))))
            }
        };
        let transaction_hash = transaction.hash();

        let block_hash = self.client.info().best_hash;

        let extrinsic = match self
            .client
            .runtime_api()
            .convert_transaction(block_hash, transaction)
        {
            Ok(extrinsic) => extrinsic,
            Err(_) => {
                return Err(RpcError::Call(CallError::Failed(anyhow!(
                    "Cannot access runtime api"
                ))))
            }
        };

        self.pool
            .submit_one(
                &BlockId::Hash(block_hash),
                TransactionSource::Local,
                extrinsic,
            )
            .map_ok(move |_| transaction_hash)
            .map_err(|err| internal_err(format::Geth::pool_error(err)))
            .await
    }

    async fn send_raw_transaction(&self, bytes: Bytes) -> RpcResult<H256> {
        log::error!("EthCompatServer called: send_raw_transaction({:?})", bytes);

        let slice = &bytes.0[..];
        if slice.is_empty() {
            return Err(RpcError::Call(CallError::Failed(anyhow!(
                "Transaction data is empty"
            ))));
        }
        let transaction: ethereum::TransactionV2 = match ethereum::EnvelopedDecodable::decode(slice)
        {
            Ok(transaction) => transaction,
            Err(_) => {
                return Err(RpcError::Call(CallError::Failed(anyhow!(
                    "Failed to decode transaction"
                ))))
            }
        };

        let transaction_hash = transaction.hash();

        let block_hash = self.client.info().best_hash;

        let extrinsic = match self
            .client
            .runtime_api()
            .convert_transaction(block_hash, transaction)
        {
            Ok(extrinsic) => extrinsic,
            Err(_) => {
                return Err(RpcError::Call(CallError::Failed(anyhow!(
                    "Cannot access runtime api"
                ))))
            }
        };

        let extrinsic_hash = H256::from(extrinsic.using_encoded(blake2_256));

        log::error!(
            "EthCompatServer send_raw_transaction transaction_hash: {:?}",
            transaction_hash
        );
        log::error!(
            "EthCompatServer send_raw_transaction extrinsic_hash: {:?}",
            extrinsic_hash
        );

        self.pool
            .submit_one(
                &BlockId::Hash(block_hash),
                TransactionSource::Local,
                extrinsic,
            )
            //.map_ok(move |_| transaction_hash)
            .map_ok(move |_| extrinsic_hash)
            .map_err(|err| internal_err(format::Geth::pool_error(err)))
            .await
    }
}
