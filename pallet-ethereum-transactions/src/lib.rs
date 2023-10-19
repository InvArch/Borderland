#![cfg_attr(not(feature = "std"), no_std)]

use sp_core::{H160, H256};

pub use self::pallet::*;

pub trait AddressMapping<A> {
    fn into_account_id(address: H160) -> A;
}

#[frame_support::pallet]
pub mod pallet {
    use super::*;
    use codec::{Decode, Encode};
    use ethereum::TransactionV2 as Transaction;
    use frame_support::{
        dispatch::{DispatchInfo, Dispatchable, PostDispatchInfo},
        pallet_prelude::*,
    };
    use frame_system::{pallet_prelude::*, RawOrigin};
    use sp_runtime::{traits::SignedExtension, transaction_validity::TransactionValidityError};
    use sp_std::vec::Vec;

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config {
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
        type RuntimeCall: Parameter
            + Dispatchable<
                Info = DispatchInfo,
                RuntimeOrigin = <Self as frame_system::Config>::RuntimeOrigin,
                PostInfo = PostDispatchInfo,
            > + From<frame_system::Call<Self>>
            + Decode
            + Encode;

        /// H160 -> AccountId
        type AddressMapping: AddressMapping<Self::AccountId>;
    }

    #[pallet::error]
    pub enum Error<T> {
        Unknown,
        InvalidSignature,
    }

    #[pallet::event]
    #[pallet::generate_deposit(fn deposit_event)]
    pub enum Event<T: Config> {
        SomethingHappened,
    }

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        #[pallet::call_index(0)]
        #[pallet::weight(1)]
        pub fn verify_ethereum_transaction(
            origin: OriginFor<T>,
            transaction: Transaction,
        ) -> DispatchResultWithPostInfo {
            ensure_none(origin)?;

            let signer = Self::verify_signature_get_signer(&transaction)
                .ok_or(Error::<T>::InvalidSignature)?;

            let substrate_transaction =
                Self::convert_to_substrate(&transaction).map_err(|_| Error::<T>::Unknown)?;

            substrate_transaction
                .dispatch(RawOrigin::Signed(T::AddressMapping::into_account_id(signer)).into())
                .into()
        }
    }

    #[pallet::validate_unsigned]
    impl<T: Config> ValidateUnsigned for Pallet<T>
    where
        <T as frame_system::Config>::RuntimeCall: Dispatchable<Info = DispatchInfo>,
        <T as frame_system::Config>::RuntimeCall: From<Call<T>>,
        T::Index: TryFrom<sp_core::U256>,
    {
        type Call = Call<T>;

        fn validate_unsigned(_source: TransactionSource, call: &Self::Call) -> TransactionValidity {
            if let Call::verify_ethereum_transaction { transaction } = call {
                let nonce = match transaction {
                    Transaction::Legacy(t) => t.nonce,
                    Transaction::EIP1559(t) => t.nonce,
                    Transaction::EIP2930(t) => t.nonce,
                };

                // Check signature.
                let Some(signer) = Self::verify_signature_get_signer(&transaction) else {
                    return InvalidTransaction::BadProof.into()
                };

                let substrate_address = T::AddressMapping::into_account_id(signer);

                // TODO: Validate Signed Extensions.
                let check_nonce =
                    frame_system::CheckNonce::<T>::from(T::Index::try_from(nonce).map_err(
                        |_| TransactionValidityError::Invalid(InvalidTransaction::Future),
                    )?);
                let nonce_validity = check_nonce.validate(
                    &substrate_address,
                    &call.clone().into(),
                    &Default::default(),
                    Default::default(),
                )?;

                // TODO: Pre-dispatch Signed Extensions.
                check_nonce.pre_dispatch(
                    &substrate_address,
                    &call.clone().into(),
                    &Default::default(),
                    Default::default(),
                )?;

                ValidTransaction::with_tag_prefix("EthTx")
                    .and_provides((signer, nonce))
                    .propagate(true)
                    .combine_with(nonce_validity)
                    .build()
            } else {
                InvalidTransaction::Call.into()
            }
        }
    }

    impl<T: Config> Pallet<T> {
        fn verify_signature_get_signer(transaction: &Transaction) -> Option<H160> {
            let mut sig = [0u8; 65];
            let mut msg = [0u8; 32];
            match transaction {
                Transaction::Legacy(t) => {
                    sig[0..32].copy_from_slice(&t.signature.r()[..]);
                    sig[32..64].copy_from_slice(&t.signature.s()[..]);
                    sig[64] = t.signature.standard_v();
                    msg.copy_from_slice(
                        &ethereum::LegacyTransactionMessage::from(t.clone()).hash()[..],
                    );
                }
                Transaction::EIP2930(t) => {
                    sig[0..32].copy_from_slice(&t.r[..]);
                    sig[32..64].copy_from_slice(&t.s[..]);
                    sig[64] = t.odd_y_parity as u8;
                    msg.copy_from_slice(
                        &ethereum::EIP2930TransactionMessage::from(t.clone()).hash()[..],
                    );
                }
                Transaction::EIP1559(t) => {
                    sig[0..32].copy_from_slice(&t.r[..]);
                    sig[32..64].copy_from_slice(&t.s[..]);
                    sig[64] = t.odd_y_parity as u8;
                    msg.copy_from_slice(
                        &ethereum::EIP1559TransactionMessage::from(t.clone()).hash()[..],
                    );
                }
            }
            let pubkey = sp_io::crypto::secp256k1_ecdsa_recover(&sig, &msg).ok()?;
            Some(H160::from(H256::from(sp_io::hashing::keccak_256(&pubkey))))
        }

        fn convert_to_substrate(
            transaction: &Transaction,
        ) -> Result<<T as Config>::RuntimeCall, ()> {
            let (
                input,
                _value,
                _gas_limit,
                _max_fee_per_gas,
                _max_priority_fee_per_gas,
                _nonce,
                action,
                _access_list,
            ) = {
                match transaction {
                    Transaction::Legacy(t) => (
                        t.input.clone(),
                        t.value,
                        t.gas_limit,
                        Some(t.gas_price),
                        Some(t.gas_price),
                        Some(t.nonce),
                        t.action,
                        Vec::new(),
                    ),
                    Transaction::EIP2930(t) => {
                        let access_list: Vec<(H160, Vec<H256>)> = t
                            .access_list
                            .iter()
                            .map(|item| (item.address, item.storage_keys.clone()))
                            .collect();
                        (
                            t.input.clone(),
                            t.value,
                            t.gas_limit,
                            Some(t.gas_price),
                            Some(t.gas_price),
                            Some(t.nonce),
                            t.action,
                            access_list,
                        )
                    }
                    Transaction::EIP1559(t) => {
                        let access_list: Vec<(H160, Vec<H256>)> = t
                            .access_list
                            .iter()
                            .map(|item| (item.address, item.storage_keys.clone()))
                            .collect();
                        (
                            t.input.clone(),
                            t.value,
                            t.gas_limit,
                            Some(t.max_fee_per_gas),
                            Some(t.max_priority_fee_per_gas),
                            Some(t.nonce),
                            t.action,
                            access_list,
                        )
                    }
                }
            };

            if let ethereum::TransactionAction::Call(_target) = action {
                if let Ok(runtime_call) = <T as Config>::RuntimeCall::decode(&mut input.as_slice())
                {
                    Ok(runtime_call)
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        }
    }
}
