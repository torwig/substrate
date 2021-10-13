// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! A module that implements instrumented code cache.
//!
//! - In order to run contract code we need to instrument it with gas metering.
//! To do that we need to provide the schedule which will supply exact gas costs values.
//! We cache this code in the storage saving the schedule version.
//! - Before running contract code we check if the cached code has the schedule version that
//! is equal to the current saved schedule.
//! If it is equal then run the code, if it isn't reinstrument with the current schedule.
//! - When we update the schedule we want it to have strictly greater version than the current saved
//!   one:
//! this guarantees that every instrumented contract code in cache cannot have the version equal to
//! the current one. Thus, before executing a contract it should be reinstrument with new schedule.

#[cfg(feature = "runtime-benchmarks")]
pub use self::private::reinstrument;
use crate::{
	gas::{GasMeter, Token},
	storage::meter::{Diff, NestedMeter as StorageMeter},
	wasm::{prepare, PrefabWasmModule},
	weights::WeightInfo,
	CodeHash, CodeStorage, Config, Error, Event, Pallet as Contracts, PristineCode, Schedule,
	Weight,
};
use frame_support::{
	dispatch::{DispatchError, DispatchResult},
	pallet_prelude::Encode,
};
use sp_core::crypto::UncheckedFrom;

/// Put the instrumented module in storage.
///
/// Increments the refcount of the in-storage `prefab_module` if it already exists in storage
/// under the specified `code_hash`.
pub fn store<T: Config>(
	mut prefab_module: PrefabWasmModule<T>,
	storage_meter: Option<&mut StorageMeter<T>>,
	instantiated: bool,
) -> DispatchResult
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	let code_hash = sp_std::mem::take(&mut prefab_module.code_hash);

	// Cases which does not modify the storage aren't an error. We can safely ignore them.
	let _ = <CodeStorage<T>>::try_mutate(&code_hash, |existing| match existing {
		Some(module) => {
			let mut dirty = false;

			// We instrument any uploaded contract anyways. We might as well store it to save
			// a potential re-instrumentation later.
			if prefab_module.instruction_weights_version > module.instruction_weights_version {
				module.code = prefab_module.code;
				module.instruction_weights_version = prefab_module.instruction_weights_version;
				dirty = true;
			}

			// When the code was merely uploaded but not instantiated we can skip this.
			if instantiated {
				module.refcount = module.refcount.checked_add(1).expect(
					"
					refcount is 64bit. Generating this overflow would require to store
					_at least_ 18 exabyte of data assuming that a contract consumes only
					one byte of data. Any node would run out of storage space before hitting
					this overflow.
					qed
				",
				);
				dirty = true;
			}

			// We can save one write to storage when determing that we didn't change anything.
			if dirty {
				Ok(())
			} else {
				Err(())
			}
		},
		None => {
			// TODO: charge caller for new code and transfer to code hash account (not contract)
			let orig_code = prefab_module.original_code.take().expect(
				"
					If an executable isn't in storage it was uploaded.
					If it was uploaded the original code must exist. qed
				",
			);
			<PristineCode<T>>::insert(&code_hash, orig_code);
			prefab_module.refcount = if instantiated { 1 } else { 0 };
			*existing = Some(prefab_module);
			Contracts::<T>::deposit_event(Event::CodeStored { code_hash });
			Ok(())
		},
	});

	Ok(())
}

/// Decrement the refcount of a code in-storage by one.
///
/// # Note
///
/// A contract whose refcount dropped to zero isn't automatically removed. A `remove_code`
/// treansaction must be submitted by the original uploader to do so.
pub fn decrement_refcount<T: Config>(
	code_hash: CodeHash<T>,
	gas_meter: &mut GasMeter<T>,
) -> Result<(), DispatchError>
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	if let Ok(len) = estimate_code_size::<T>(&code_hash) {
		gas_meter.charge(CodeToken::UpdateRefcount(len))?;
	}
	<CodeStorage<T>>::mutate(code_hash, |existing| {
		if let Some(module) = existing {
			module.refcount = module.refcount.saturating_sub(1);
		}
	});
	Ok(())
}

/// Load code with the given code hash.
///
/// If the module was instrumented with a lower version of schedule than
/// the current one given as an argument, then this function will perform
/// re-instrumentation and update the cache in the storage.
pub fn load<T: Config>(
	code_hash: CodeHash<T>,
	schedule: &Schedule<T>,
	gas_meter: &mut GasMeter<T>,
) -> Result<PrefabWasmModule<T>, DispatchError>
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	gas_meter.charge(CodeToken::Load(estimate_code_size::<T>(&code_hash)?))?;

	let mut prefab_module =
		<CodeStorage<T>>::get(code_hash).ok_or_else(|| Error::<T>::CodeNotFound)?;
	prefab_module.code_hash = code_hash;

	if prefab_module.instruction_weights_version < schedule.instruction_weights.version {
		// The instruction weights have changed.
		// We need to re-instrument the code with the new instruction weights.
		gas_meter.charge(CodeToken::Instrument(prefab_module.original_code_len))?;
		private::reinstrument(&mut prefab_module, schedule)?;
	}

	Ok(prefab_module)
}

mod private {
	use super::*;

	/// Instruments the passed prefab wasm module with the supplied schedule.
	pub fn reinstrument<T: Config>(
		prefab_module: &mut PrefabWasmModule<T>,
		schedule: &Schedule<T>,
	) -> Result<(), DispatchError>
	where
		T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
	{
		let original_code = <PristineCode<T>>::get(&prefab_module.code_hash)
			.ok_or_else(|| Error::<T>::CodeNotFound)?;
		prefab_module.code = prepare::reinstrument_contract::<T>(original_code, schedule)?;
		prefab_module.instruction_weights_version = schedule.instruction_weights.version;
		<CodeStorage<T>>::insert(&prefab_module.code_hash, &*prefab_module);
		Ok(())
	}
}

/// Get the size of the instrumented code stored at `code_hash` without loading it.
///
/// The returned value is slightly too large because it also contains the fields apart from
/// `code` which are located inside [`PrefabWasmModule`]. However, those are negligible when
/// compared to the code size. Additionally, charging too much weight is completely safe.
fn estimate_code_size<T: Config>(code_hash: &CodeHash<T>) -> Result<u32, DispatchError>
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	let key = <CodeStorage<T>>::hashed_key_for(code_hash);
	let len = stored_len(&key).ok_or_else(|| Error::<T>::CodeNotFound)?;
	Ok(len)
}

/// Returns the encoded length of the storage item at the specified `key`.
fn stored_len(key: &[u8]) -> Option<u32> {
	let mut data = [0u8; 0];
	sp_io::storage::read(key, &mut data, 0)
}

/// Costs for operations that are related to code handling.
#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
enum CodeToken {
	/// Weight for instrumenting a contract contract of the supplied size in bytes.
	Instrument(u32),
	/// Weight for loading a contract per kilobyte.
	Load(u32),
	/// Weight for changing the refcount of a contract per kilobyte.
	UpdateRefcount(u32),
}

impl<T> Token<T> for CodeToken
where
	T: Config,
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	fn weight(&self) -> Weight {
		use self::CodeToken::*;
		// In case of `Load` and `UpdateRefcount` we already covered the general costs of
		// accessing the storage but still need to account for the actual size of the
		// contract code. This is why we substract `T::*::(0)`. We need to do this at this
		// point because when charging the general weight we do not know the size of
		// the contract.
		match *self {
			Instrument(len) => T::WeightInfo::instrument(len / 1024),
			Load(len) =>
				T::WeightInfo::code_load(len / 1024).saturating_sub(T::WeightInfo::code_load(0)),
			UpdateRefcount(len) => T::WeightInfo::code_refcount(len / 1024)
				.saturating_sub(T::WeightInfo::code_refcount(0)),
		}
	}
}
