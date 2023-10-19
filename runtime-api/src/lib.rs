#![cfg_attr(not(feature = "std"), no_std)]
#![allow(clippy::too_many_arguments)]
#![deny(unused_crate_dependencies)]

use ethereum::Log;
use ethereum_types::Bloom;
use scale_codec::{Decode, Encode};
use scale_info::TypeInfo;
// Substrate
use sp_core::{H160, H256, U256};
use sp_runtime::{traits::Block as BlockT, Permill, RuntimeDebug};
use sp_std::vec::Vec;

#[derive(Clone, Eq, PartialEq, Default, RuntimeDebug, Encode, Decode, TypeInfo)]
pub struct TransactionStatus {
    pub transaction_hash: H256,
    pub transaction_index: u32,
    pub from: H160,
    pub to: Option<H160>,
    pub contract_address: Option<H160>,
    pub logs: Vec<Log>,
    pub logs_bloom: Bloom,
}

#[derive(Eq, PartialEq, Clone, Encode, Decode, sp_runtime::RuntimeDebug)]
pub struct TxPoolResponse {
    pub ready: Vec<ethereum::TransactionV2>,
    pub future: Vec<ethereum::TransactionV2>,
}

sp_api::decl_runtime_apis! {
    /// API necessary for Ethereum-compatibility layer.
    #[api_version(1)]
    pub trait EthereumRuntimeRPCApi {
        /// Returns runtime defined pallet_evm::ChainId.
        fn chain_id() -> u64;
        /// Returns pallet_evm::Accounts by address.
        fn account_basic(address: H160) -> fp_evm::Account;
        /// Returns FixedGasPrice::min_gas_price
        fn gas_price() -> U256;
        /// For a given account address, returns pallet_evm::AccountCodes.
        fn account_code_at(address: H160) -> Vec<u8>;
        /// Returns the converted FindAuthor::find_author authority id.
        fn author() -> H160;
        /// For a given account address and index, returns pallet_evm::AccountStorages.
        fn storage_at(address: H160, index: U256) -> H256;
        /// Returns a frame_ethereum::call response. If `estimate` is true,
        fn call(
            from: H160,
            to: H160,
            data: Vec<u8>,
            value: U256,
            gas_limit: U256,
            max_fee_per_gas: Option<U256>,
            max_priority_fee_per_gas: Option<U256>,
            nonce: Option<U256>,
            estimate: bool,
            access_list: Option<Vec<(H160, Vec<H256>)>>,
        ) -> Result<fp_evm::ExecutionInfoV2::<Vec<u8>>, sp_runtime::DispatchError>;
        /// Returns a frame_ethereum::create response.
        fn create(
            from: H160,
            data: Vec<u8>,
            value: U256,
            gas_limit: U256,
            max_fee_per_gas: Option<U256>,
            max_priority_fee_per_gas: Option<U256>,
            nonce: Option<U256>,
            estimate: bool,
            access_list: Option<Vec<(H160, Vec<H256>)>>,
        ) -> Result<fp_evm::ExecutionInfoV2::<H160>, sp_runtime::DispatchError>;
        /// Return the current block.
        fn current_block() -> Option<ethereum::BlockV2>;
        /// Return the current receipt.
        fn current_receipts() -> Option<Vec<ethereum::ReceiptV3>>;
        /// Return the current transaction status.
        fn current_transaction_statuses() -> Option<Vec<TransactionStatus>>;
        /// Return all the current data for a block in a single runtime call.
        fn current_all() -> (
            Option<ethereum::BlockV2>,
            Option<Vec<ethereum::ReceiptV3>>,
            Option<Vec<TransactionStatus>>
        );
        /// Receives a `Vec<OpaqueExtrinsic>` and filters all the ethereum transactions.
        fn extrinsic_filter(
            xts: Vec<<Block as BlockT>::Extrinsic>,
        ) -> Vec<ethereum::TransactionV2>;
        /// Receives a `Vec<OpaqueExtrinsic>` and filters all the ethereum transactions.
        /// Returns Ethereum transactions and their Substrate extrinsic hash.
        fn extrinsic_filter_with_hash(
            xts: Vec<<Block as BlockT>::Extrinsic>,
        ) -> Vec<(ethereum::TransactionV2, H256)>;
        /// Return the elasticity multiplier.
        fn elasticity() -> Option<Permill>;
        /// Used to determine if gas limit multiplier for non-transactional calls (eth_call/estimateGas)
        /// is supported.
        fn gas_limit_multiplier_support();
        /// Return the pending block.
        fn pending_block(
            xts: Vec<<Block as BlockT>::Extrinsic>,
        ) -> (Option<ethereum::BlockV2>, Option<Vec<TransactionStatus>>);
    }

    #[api_version(1)]
    pub trait ConvertTransactionRuntimeApi {
        fn convert_transaction(transaction: ethereum::TransactionV2) -> <Block as BlockT>::Extrinsic;
    }
}

pub trait ConvertTransaction<E> {
    fn convert_transaction(&self, transaction: ethereum::TransactionV2) -> E;
}

// `NoTransactionConverter` is a non-instantiable type (an enum with no variants),
// so we are guaranteed at compile time that `NoTransactionConverter` can never be instantiated.
pub enum NoTransactionConverter {}
impl<E> ConvertTransaction<E> for NoTransactionConverter {
    // `convert_transaction` is a method taking `&self` as a parameter, so it can only be called via an instance of type Self,
    // so we are guaranteed at compile time that this method can never be called.
    fn convert_transaction(&self, _transaction: ethereum::TransactionV2) -> E {
        unreachable!()
    }
}
