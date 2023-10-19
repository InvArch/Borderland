#![allow(
    clippy::too_many_arguments,
    clippy::large_enum_variant,
    clippy::manual_range_contains,
    clippy::explicit_counter_loop,
    clippy::len_zero,
    clippy::new_without_default
)]
#![deny(unused_crate_dependencies)]

mod eth;
mod eth_pubsub;
mod format;
mod net;
mod signer;
mod txpool;
mod web3;

pub use self::{
    eth::EthCompatServer,
    eth_pubsub::{EthPubSub, EthereumSubIdProvider},
    net::Net,
    signer::{EthDevSigner, EthSigner},
    txpool::TxPool,
    web3::Web3,
};

pub use ethereum::TransactionV2 as EthereumTransaction;
pub use fc_rpc_core::{
    EthApiServer, EthFilterApiServer, EthPubSubApiServer, NetApiServer, TxPoolApiServer,
    Web3ApiServer,
};
pub use fc_storage::{
    OverrideHandle, RuntimeApiStorageOverride, SchemaV1Override, SchemaV2Override,
    SchemaV3Override, StorageOverride,
};

pub fn err<T: ToString>(code: i32, message: T, data: Option<&[u8]>) -> jsonrpsee::core::Error {
    jsonrpsee::core::Error::Call(jsonrpsee::types::error::CallError::Custom(
        jsonrpsee::types::error::ErrorObject::owned(
            code,
            message.to_string(),
            data.map(|bytes| {
                jsonrpsee::core::to_json_raw_value(&format!("0x{}", hex::encode(bytes)))
                    .expect("fail to serialize data")
            }),
        ),
    ))
}

pub fn internal_err<T: ToString>(message: T) -> jsonrpsee::core::Error {
    err(jsonrpsee::types::error::INTERNAL_ERROR_CODE, message, None)
}

pub fn internal_err_with_data<T: ToString>(message: T, data: &[u8]) -> jsonrpsee::core::Error {
    err(
        jsonrpsee::types::error::INTERNAL_ERROR_CODE,
        message,
        Some(data),
    )
}

pub fn public_key(transaction: &EthereumTransaction) -> Result<[u8; 64], sp_io::EcdsaVerifyError> {
    let mut sig = [0u8; 65];
    let mut msg = [0u8; 32];
    match transaction {
        EthereumTransaction::Legacy(t) => {
            sig[0..32].copy_from_slice(&t.signature.r()[..]);
            sig[32..64].copy_from_slice(&t.signature.s()[..]);
            sig[64] = t.signature.standard_v();
            msg.copy_from_slice(&ethereum::LegacyTransactionMessage::from(t.clone()).hash()[..]);
        }
        EthereumTransaction::EIP2930(t) => {
            sig[0..32].copy_from_slice(&t.r[..]);
            sig[32..64].copy_from_slice(&t.s[..]);
            sig[64] = t.odd_y_parity as u8;
            msg.copy_from_slice(&ethereum::EIP2930TransactionMessage::from(t.clone()).hash()[..]);
        }
        EthereumTransaction::EIP1559(t) => {
            sig[0..32].copy_from_slice(&t.r[..]);
            sig[32..64].copy_from_slice(&t.s[..]);
            sig[64] = t.odd_y_parity as u8;
            msg.copy_from_slice(&ethereum::EIP1559TransactionMessage::from(t.clone()).hash()[..]);
        }
    }
    sp_io::crypto::secp256k1_ecdsa_recover(&sig, &msg)
}
