// SPDX-License-Identifier: EUPL-1.2
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax WASM Runtime
//!
//! Low-level runtime support for Ephapax compiled to WebAssembly.
//! This provides the memory management primitives used by generated code.

#![cfg_attr(not(feature = "std"), no_std)]
#![allow(clippy::missing_safety_doc)]

// Panic handler for no_std environments (WASM target)
#[cfg(all(not(feature = "std"), not(test), target_arch = "wasm32"))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    // In WASM, we can't do much - just loop forever
    loop {}
}

/// String handle: offset into linear memory
pub type StringHandle = u32;

/// Memory layout constants
pub mod layout {
    /// Offset of bump pointer
    pub const BUMP_PTR: usize = 0;
    /// Offset of region stack pointer
    pub const REGION_SP: usize = 4;
    /// Start of region stack
    pub const REGION_STACK: usize = 8;
    /// Maximum region stack depth
    pub const MAX_REGION_DEPTH: usize = 64;
    /// Start of heap
    pub const HEAP_START: usize = REGION_STACK + MAX_REGION_DEPTH * 4;
}

/// Initialise runtime memory
///
/// # Safety
///
/// Must be called before any other runtime functions.
/// Assumes linear memory is properly allocated.
#[no_mangle]
pub unsafe extern "C" fn __ephapax_init() {
    // Set initial bump pointer
    core::ptr::write(layout::BUMP_PTR as *mut u32, layout::HEAP_START as u32);
    // Set initial region stack pointer (empty)
    core::ptr::write(layout::REGION_SP as *mut u32, layout::REGION_STACK as u32);
}

/// Bump allocate `size` bytes, return pointer
///
/// # Safety
///
/// Assumes runtime has been initialised and sufficient memory is available.
#[no_mangle]
pub unsafe extern "C" fn __ephapax_bump_alloc(size: u32) -> u32 {
    let bump_ptr = core::ptr::read(layout::BUMP_PTR as *const u32);
    let new_ptr = bump_ptr + size;
    core::ptr::write(layout::BUMP_PTR as *mut u32, new_ptr);
    bump_ptr
}

/// Create a new string from data pointer and length
/// Returns a handle (pointer to string header)
///
/// # Safety
///
/// `data_ptr` must point to valid memory of at least `len` bytes.
#[no_mangle]
pub unsafe extern "C" fn __ephapax_string_new(data_ptr: u32, len: u32) -> StringHandle {
    // Allocate header (8 bytes: ptr + len)
    let handle = __ephapax_bump_alloc(8);

    // Store pointer
    core::ptr::write(handle as *mut u32, data_ptr);
    // Store length
    core::ptr::write((handle + 4) as *mut u32, len);

    handle
}

/// Get the length of a string
///
/// # Safety
///
/// `handle` must be a valid string handle.
#[no_mangle]
pub unsafe extern "C" fn __ephapax_string_len(handle: StringHandle) -> u32 {
    core::ptr::read((handle + 4) as *const u32)
}

/// Get the data pointer of a string
///
/// # Safety
///
/// `handle` must be a valid string handle.
#[no_mangle]
pub unsafe extern "C" fn __ephapax_string_ptr(handle: StringHandle) -> u32 {
    core::ptr::read(handle as *const u32)
}

/// Concatenate two strings, consuming both handles
/// Returns a new handle
///
/// # Safety
///
/// Both handles must be valid string handles.
#[no_mangle]
pub unsafe extern "C" fn __ephapax_string_concat(h1: StringHandle, h2: StringHandle) -> StringHandle {
    let ptr1 = core::ptr::read(h1 as *const u32);
    let len1 = core::ptr::read((h1 + 4) as *const u32);
    let ptr2 = core::ptr::read(h2 as *const u32);
    let len2 = core::ptr::read((h2 + 4) as *const u32);

    let new_len = len1 + len2;
    let new_data = __ephapax_bump_alloc(new_len);

    // Copy first string
    core::ptr::copy_nonoverlapping(ptr1 as *const u8, new_data as *mut u8, len1 as usize);

    // Copy second string
    core::ptr::copy_nonoverlapping(ptr2 as *const u8, (new_data + len1) as *mut u8, len2 as usize);

    // Create new handle
    __ephapax_string_new(new_data, new_len)
}

/// Drop a string handle (no-op with regions, memory freed on region exit)
#[no_mangle]
pub extern "C" fn __ephapax_string_drop(_handle: StringHandle) {
    // No-op: memory is managed by regions
}

/// Enter a new region: save current bump pointer
///
/// Returns 1 on success, 0 if region stack is full.
///
/// # Safety
///
/// Must not exceed maximum region depth.
#[no_mangle]
pub unsafe extern "C" fn __ephapax_region_enter() -> u32 {
    let region_sp = core::ptr::read(layout::REGION_SP as *const u32);

    // Bounds check: ensure we don't exceed maximum region depth
    let max_sp = (layout::REGION_STACK + layout::MAX_REGION_DEPTH * 4) as u32;
    if region_sp >= max_sp {
        // Region stack full - cannot nest deeper
        return 0;
    }

    let bump_ptr = core::ptr::read(layout::BUMP_PTR as *const u32);

    // Push bump_ptr onto region stack
    core::ptr::write(region_sp as *mut u32, bump_ptr);

    // Increment region stack pointer
    core::ptr::write(layout::REGION_SP as *mut u32, region_sp + 4);

    1 // Success
}

/// Exit region: restore bump pointer, freeing all region allocations
///
/// Returns 1 on success, 0 if no region is active (underflow).
///
/// # Safety
///
/// Must have a matching `__ephapax_region_enter` call.
#[no_mangle]
pub unsafe extern "C" fn __ephapax_region_exit() -> u32 {
    let region_sp = core::ptr::read(layout::REGION_SP as *const u32);

    // Bounds check: ensure we have a region to exit
    if region_sp <= layout::REGION_STACK as u32 {
        // No region to exit - stack underflow
        return 0;
    }

    // Decrement and read saved bump_ptr
    let new_sp = region_sp - 4;
    let saved_bump = core::ptr::read(new_sp as *const u32);

    // Restore bump pointer (effectively frees all region allocations)
    core::ptr::write(layout::BUMP_PTR as *mut u32, saved_bump);
    core::ptr::write(layout::REGION_SP as *mut u32, new_sp);

    1 // Success
}

/// Check if we're in any region
///
/// # Safety
///
/// Assumes runtime has been initialised.
#[no_mangle]
pub unsafe extern "C" fn __ephapax_in_region() -> u32 {
    let region_sp = core::ptr::read(layout::REGION_SP as *const u32);
    if region_sp > layout::REGION_STACK as u32 {
        1
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    // Tests would run in native mode, not WASM
    // Integration tests should use wasm-bindgen-test
}
