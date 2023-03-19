// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Collection of allocator implementations.
//!
//! This crate provides the following allocator implementations:
//! - A freeing-bump allocator: [`FreeingBumpHeapAllocator`](freeing_bump::FreeingBumpHeapAllocator)

#![cfg_attr(not(feature = "std"), no_std)]

#![warn(missing_docs)]

#[cfg(feature = "std")]
mod error;
#[cfg(feature = "std")]
mod freeing_bump;

#[cfg(feature = "std")]
pub use error::Error;
#[cfg(feature = "std")]
pub use freeing_bump::{AllocationStats, FreeingBumpHeapAllocator};

/// The maximum number of bytes that can be allocated at one time.
// The maximum possible allocation size was chosen rather arbitrary, 32 MiB should be enough for
// everybody.
// 2^25 bytes, 32 MiB
pub const MAX_POSSIBLE_ALLOCATION: u32 = 33_554_432;
