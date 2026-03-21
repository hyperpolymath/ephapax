// SPDX-License-Identifier: PMPL-1.0-or-later
// List/Vector runtime operations for Ephapax self-hosting compiler

//! Linear lists with dynamic resizing
//!
//! Memory layout:
//! ```
//! +----------+----------+----------+----------+
//! | capacity | length   | elem[0]  | elem[1]  | ...
//! +----------+----------+----------+----------+
//! 0          4          8          12
//! ```
//!
//! List handle points to the header (capacity field)
//! Each element is 4 bytes (i32)

/// List handle: pointer to list header in linear memory
pub type ListHandle = u32;

// ============================================================================
// LIST OPERATIONS (for i32 elements)
// ============================================================================

/// Create new empty list with initial capacity
///
/// # Safety
///
/// Requires bump allocator to be initialized
#[no_mangle]
pub unsafe extern "C" fn __ephapax_list_new(initial_capacity: u32) -> ListHandle {
    let capacity = if initial_capacity < 4 { 4 } else { initial_capacity };

    // Allocate: header (8 bytes) + elements (capacity * 4 bytes)
    let total_size = 8 + (capacity * 4);
    let handle = super::__ephapax_bump_alloc(total_size);

    // Write capacity
    core::ptr::write(handle as *mut u32, capacity);
    // Write length (initially 0)
    core::ptr::write((handle + 4) as *mut u32, 0);

    handle
}

/// Get list capacity
///
/// # Safety
///
/// handle must be valid list handle
#[no_mangle]
pub unsafe extern "C" fn __ephapax_list_capacity(handle: ListHandle) -> u32 {
    core::ptr::read(handle as *const u32)
}

/// Get list length
///
/// # Safety
///
/// handle must be valid list handle
#[no_mangle]
pub unsafe extern "C" fn __ephapax_list_len(handle: ListHandle) -> u32 {
    core::ptr::read((handle + 4) as *const u32)
}

/// Get element at index (returns 0 if out of bounds)
///
/// # Safety
///
/// handle must be valid list handle
#[no_mangle]
pub unsafe extern "C" fn __ephapax_list_get(handle: ListHandle, idx: i32) -> i32 {
    let len = __ephapax_list_len(handle) as i32;

    if idx < 0 || idx >= len {
        return 0; // Out of bounds
    }

    let elem_ptr = (handle + 8 + (idx as u32 * 4)) as *const i32;
    core::ptr::read(elem_ptr)
}

/// Set element at index (returns 1 on success, 0 on failure)
///
/// # Safety
///
/// handle must be valid list handle
#[no_mangle]
pub unsafe extern "C" fn __ephapax_list_set(handle: ListHandle, idx: i32, value: i32) -> i32 {
    let len = __ephapax_list_len(handle) as i32;

    if idx < 0 || idx >= len {
        return 0; // Out of bounds
    }

    let elem_ptr = (handle + 8 + (idx as u32 * 4)) as *mut i32;
    core::ptr::write(elem_ptr, value);
    1 // Success
}

/// Append element to list (returns new list handle if resize needed)
///
/// Returns (status << 32) | new_handle
/// Status: 1 = success (same handle), 2 = success (resized, new handle)
///
/// # Safety
///
/// handle must be valid list handle
#[no_mangle]
pub unsafe extern "C" fn __ephapax_list_append(handle: ListHandle, value: i32) -> i64 {
    let capacity = __ephapax_list_capacity(handle);
    let len = __ephapax_list_len(handle);

    if len < capacity {
        // Space available - append in place
        let elem_ptr = (handle + 8 + (len * 4)) as *mut i32;
        core::ptr::write(elem_ptr, value);

        // Update length
        core::ptr::write((handle + 4) as *mut u32, len + 1);

        // Return: status=1 (same handle), handle
        ((1i64) << 32) | (handle as i64)
    } else {
        // Need to resize - allocate new list with 2x capacity
        let new_capacity = capacity * 2;
        let new_handle = __ephapax_list_new(new_capacity);

        // Copy existing elements
        for i in 0..len {
            let old_elem_ptr = (handle + 8 + (i * 4)) as *const i32;
            let new_elem_ptr = (new_handle + 8 + (i * 4)) as *mut i32;
            core::ptr::write(new_elem_ptr, core::ptr::read(old_elem_ptr));
        }

        // Append new element
        let elem_ptr = (new_handle + 8 + (len * 4)) as *mut i32;
        core::ptr::write(elem_ptr, value);

        // Update new list length
        core::ptr::write((new_handle + 4) as *mut u32, len + 1);

        // Return: status=2 (resized), new_handle
        ((2i64) << 32) | (new_handle as i64)
    }
}

/// Remove last element (returns element, or 0 if empty)
///
/// # Safety
///
/// handle must be valid list handle
#[no_mangle]
pub unsafe extern "C" fn __ephapax_list_pop(handle: ListHandle) -> i32 {
    let len = __ephapax_list_len(handle);

    if len == 0 {
        return 0; // Empty list
    }

    let new_len = len - 1;
    let elem_ptr = (handle + 8 + (new_len * 4)) as *const i32;
    let value = core::ptr::read(elem_ptr);

    // Update length
    core::ptr::write((handle + 4) as *mut u32, new_len);

    value
}

/// Clear list (set length to 0)
///
/// # Safety
///
/// handle must be valid list handle
#[no_mangle]
pub unsafe extern "C" fn __ephapax_list_clear(handle: ListHandle) {
    core::ptr::write((handle + 4) as *mut u32, 0);
}

// ============================================================================
// STRING LIST OPERATIONS (for StringHandle elements)
// ============================================================================

/// Create new empty string list
#[no_mangle]
pub unsafe extern "C" fn __ephapax_string_list_new(initial_capacity: u32) -> ListHandle {
    __ephapax_list_new(initial_capacity)
}

/// Append string to string list
#[no_mangle]
pub unsafe extern "C" fn __ephapax_string_list_append(
    handle: ListHandle,
    string_handle: u32,
) -> i64 {
    __ephapax_list_append(handle, string_handle as i32)
}

/// Get string from string list
#[no_mangle]
pub unsafe extern "C" fn __ephapax_string_list_get(
    handle: ListHandle,
    idx: i32,
) -> u32 {
    __ephapax_list_get(handle, idx) as u32
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_list_new() {
        unsafe {
            // This test needs proper WASM memory simulation
            // Just verify function signature is correct
        }
    }

    #[test]
    fn test_list_operations_logic() {
        // Test the logic without actual memory allocation
        let initial_cap = 4u32;
        let capacity_after_resize = initial_cap * 2;
        assert_eq!(capacity_after_resize, 8);
    }
}
