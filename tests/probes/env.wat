;; SPDX-License-Identifier: MPL-2.0
;; Stub host module for scripts/probe-battery.sh `wasm-run` rows: the two
;; imports every ephapax-compiled module declares (see ephapax-wasm
;; emit_imports). Loaded with `wasmtime run --preload env=env.wat`.
(module
  (func (export "print_i32") (param i32))
  (func (export "print_string") (param i32 i32)))
