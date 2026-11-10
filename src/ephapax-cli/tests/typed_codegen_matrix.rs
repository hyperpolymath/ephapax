// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// typed_codegen_matrix.rs: v2 plan rung E5 gate.
//
// A generated type x operation conformance matrix. Every case is a
// zero-parameter function in one module. The module is compiled once and
// each case runs twice: as wasm (wasmtime, a fresh instance per case) and
// in the interpreter. The two must agree on the printed value, or both
// must fail (a wasm trap against an interpreter error).
//
// Covered: every binary operator, unary operator and comparison on every
// operand type the checker accepts, and each value type in each container
// position (pair field, tuple field, list element, sum payload, `copy`,
// `if` / `let` / `match` result, extern parameter and result), and each
// value type as a closure parameter, a closure result and a captured
// value (v2 plan rung E9).

use ephapax_interp::Interpreter;
use wasmtime::{Engine, Linker, Module, Store, Val};

/// One case: the result type and the expression.
struct Case {
    ty: &'static str,
    expr: String,
}

/// One case from its result type and its expression.
fn case(ty: &'static str, expr: impl Into<String>) -> Case {
    Case {
        ty,
        expr: expr.into(),
    }
}

/// Sample operands of each numeric type, boundary values included.
fn samples(ty: &str) -> Vec<String> {
    let v: &[&str] = match ty {
        "I32" => &["0", "1", "-1", "7", "-3", "2147483647", "-2147483648"],
        // A small I64 has no literal form (`1` is an I32), so it is
        // written as a difference of two I64 literals.
        "I64" => &[
            "(5000000000 - 5000000000)",
            "(5000000000 - 4999999999)",
            "(4999999999 - 5000000000)",
            "5000000000",
            "-5000000000",
            "9223372036854775807",
            "-9223372036854775808",
        ],
        "F32" => &[
            "0.0f32",
            "(-(0.0f32))",
            "1.5f32",
            "(-(2.25f32))",
            "0.1f32",
            "3.0f32",
            "340282346638528860000000000000000000000.0f32",
            "(1.0f32 / 0.0f32)",
            "(0.0f32 / 0.0f32)",
        ],
        "F64" => &[
            "0.0",
            "(-(0.0))",
            "1.5",
            "(-(2.25))",
            "0.1",
            "3.0",
            // 1e308: the grammar has no exponent form.
            "1e308",
            "(1.0 / 0.0)",
            "(0.0 / 0.0)",
        ],
        "Bool" => &["true", "false"],
        other => panic!("no samples for {other}"),
    };
    v.iter()
        .map(|s| {
            if *s == "1e308" {
                format!("1{}.0", "0".repeat(308))
            } else {
                s.to_string()
            }
        })
        .collect()
}

/// The numeric types.
const NUMERIC: [&str; 4] = ["I32", "I64", "F32", "F64"];
/// The types that a wasm value can have.
const VALUE_TYPES: [&str; 5] = ["I32", "I64", "F32", "F64", "Bool"];

/// Each case of the matrix: the operators, the conversions and the
/// value forms, at each type.
fn cases_matrix() -> Vec<Case> {
    let mut out = Vec::new();

    // Arithmetic and comparisons: every operator on every pair of samples.
    for ty in NUMERIC {
        let vals = samples(ty);
        for a in &vals {
            for b in &vals {
                for op in ["+", "-", "*", "/", "%"] {
                    out.push(case(ty, format!("{a} {op} {b}")));
                }
                for op in ["<", "<=", ">", ">=", "==", "!="] {
                    out.push(case("Bool", format!("{a} {op} {b}")));
                }
            }
            out.push(case(ty, format!("-({a})")));
        }
    }
    for a in samples("Bool") {
        for b in samples("Bool") {
            for op in ["&&", "||", "==", "!="] {
                out.push(case("Bool", format!("{a} {op} {b}")));
            }
        }
        out.push(case("Bool", format!("!{a}")));
    }
    out.push(case("Bool", "() == ()"));
    out.push(case("Bool", "() != ()"));

    // Strings compare by content, not by handle.
    for (a, b) in [("abc", "abc"), ("abc", "abd"), ("abc", "ab"), ("", "")] {
        for op in ["==", "!="] {
            out.push(case(
                "Bool",
                format!("region r {{ String.new@r(\"{a}\") {op} String.new@r(\"{b}\") }}"),
            ));
        }
    }

    // Each value type in each container position, next to each other type.
    for ty in VALUE_TYPES {
        let v = &samples(ty)[1];
        let w = &samples(ty)[0];
        for other in VALUE_TYPES {
            let o = &samples(other)[1];
            out.push(case(ty, format!("fst(({v}, {o}))")));
            out.push(case(ty, format!("snd(({o}, {v}))")));
            out.push(case(ty, format!("let p = ({o}, {v})\n  p.1")));
            out.push(case(ty, format!("let p = ({v}, {o})\n  p.0")));
            out.push(case(ty, format!("snd(fst((({o}, {v}), {o})))")));
            for (i, t) in [
                format!("({v}, {o}, {o})"),
                format!("({o}, {v}, {o})"),
                format!("({o}, {o}, {v})"),
            ]
            .iter()
            .enumerate()
            {
                out.push(case(ty, format!("let t = {t}\n  t.{i}")));
            }
            // Sum payload, on either side of a sum whose other side is `other`.
            out.push(case(
                ty,
                format!("case inl[{other}]({v}) of\n    inl(a) -> a\n    inr(b) -> {w}\n  end"),
            ));
            out.push(case(
                ty,
                format!("case inr[{other}]({v}) of\n    inl(a) -> {w}\n    inr(b) -> b\n  end"),
            ));
        }
        out.push(case(ty, format!("let xs = [{w}, {v}]\n  xs[1]")));
        out.push(case(ty, format!("let xs = [{w}, {v}]\n  xs[0]")));
        // An index out of range, or negative, fails on both paths.
        out.push(case(ty, format!("let xs = [{w}, {v}]\n  xs[2]")));
        out.push(case(ty, format!("let xs = [{w}, {v}]\n  xs[-1]")));
        out.push(case(ty, format!("fst(copy({v}))")));
        out.push(case(ty, format!("snd(copy({v}))")));
        out.push(case(ty, format!("if true then {v} else {w}")));
        out.push(case(ty, format!("if false then {v} else {w}")));
        out.push(case(ty, format!("let x = {v}\n  x")));
        out.push(case(ty, format!("let! x = {v}\n  x")));
        out.push(case(
            ty,
            format!("match Some(1) of\n  | None => {w}\n  | Some(n) => {v}\n  end"),
        ));
    }

    // Each value type as a closure parameter and as a closure result, next
    // to each other type (v2 plan rung E9). A closure function has the
    // wasm type of its parameter and of its result.
    for ty in VALUE_TYPES {
        let v = &samples(ty)[1];
        for other in VALUE_TYPES {
            let o = &samples(other)[1];
            // A lambda: parameter `other`, result `ty`.
            out.push(case(ty, format!("let f = fn(x: {other}) -> {v}\n  f({o})")));
            // The result is a captured value.
            out.push(case(
                ty,
                format!("let k = {v}\n  let f = fn(x: {other}) -> k\n  f({o})"),
            ));
            // A lambda in a lambda: the first parameter is captured.
            out.push(case(
                ty,
                format!("let f = fn(a: {ty}) -> fn(b: {other}) -> a\n  f({v})({o})"),
            ));
            // A named function as a value, with 1 argument at a time.
            out.push(case(
                ty,
                format!("let f = first_{ty}_{other}\n  f({v})({o})"),
            ));
            out.push(case(
                ty,
                format!("let f = first_{ty}_{other}({v})\n  f({o})"),
            ));
        }
        // A closure as an argument: a lambda, then a named function.
        out.push(case(ty, format!("apply_{ty}(fn(x: {ty}) -> x, {v})")));
        out.push(case(ty, format!("apply_{ty}(same_{ty}, {v})")));
    }
    out
}

/// Cases with a known answer (`None`: both paths must fail). Agreement
/// alone would also hold if both paths were wrong the same way.
fn pinned() -> Vec<(Case, Option<&'static str>)> {
    let e308 = format!("1{}.0", "0".repeat(308));
    vec![
        // An I64 literal outside the I32 range, and a negative I64 result.
        (
            case("I64", "5000000000 + 5000000000"),
            Some("10000000000i64"),
        ),
        (case("I64", "-(5000000000)"), Some("-5000000000i64")),
        // Integer arithmetic wraps at the type limits.
        (case("I32", "2147483647 + 1"), Some("-2147483648")),
        (case("I32", "-2147483648 - 1"), Some("2147483647")),
        (case("I32", "-(-2147483648)"), Some("-2147483648")),
        (
            case("I64", "9223372036854775807 + 9223372036854775807"),
            Some("-2i64"),
        ),
        (
            case("I64", "-(-9223372036854775808)"),
            Some("-9223372036854775808i64"),
        ),
        // `/` and `%` by zero, and `MIN / -1`, fail; `MIN % -1` is 0.
        (case("I32", "1 / 0"), None),
        (case("I32", "1 % 0"), None),
        (case("I32", "-2147483648 / -1"), None),
        (case("I32", "-2147483648 % -1"), Some("0")),
        (
            case("I64", "-9223372036854775808 / (4999999999 - 5000000000)"),
            None,
        ),
        (
            case("I64", "-9223372036854775808 % (4999999999 - 5000000000)"),
            Some("0i64"),
        ),
        // Float literals, arithmetic and exact remainder, in both widths.
        (case("F32", "1.5f32 + 0.25f32"), Some("1.75f32")),
        (case("F32", "5.5f32 % 2.0f32"), Some("1.5f32")),
        (case("F32", "-(1.5f32)"), Some("-1.5f32")),
        (case("F64", "1.5 + 2.25"), Some("3.75")),
        (case("F64", "1.0 % 0.1"), Some("0.09999999999999995")),
        (case("F64", "-(0.0) % 1.0"), Some("-0")),
        (case("F64", format!("{e308} % 3.0")), Some("2")),
        (case("F64", "5.5 % (1.0 / 0.0)"), Some("5.5")),
        (case("F64", "5.5 % 0.0"), Some("NaN")),
        (case("F64", "-(1.5)"), Some("-1.5")),
        // Containers keep the full width of an element.
        (case("I64", "snd((1, 5000000000))"), Some("5000000000i64")),
        (
            case("I64", "let xs = [5000000000, 6000000000]\n  xs[1]"),
            Some("6000000000i64"),
        ),
        (case("F64", "let xs = [1.5, 2.5]\n  xs[1]"), Some("2.5")),
        (case("I32", "let t = (1, 2, 3)\n  t.2"), Some("3")),
        (case("I32", "fst(snd((1, (2, 3))))"), Some("2")),
        // Strings: length, and equality by content.
        (
            case(
                "I32",
                "region r {\n    let! s = String.new@r(\"hi\")\n    String.len(s)\n  }",
            ),
            Some("2"),
        ),
        (
            case(
                "Bool",
                "region r { String.new@r(\"abc\") == String.new@r(\"abc\") }",
            ),
            Some("true"),
        ),
        // A closure keeps the full width of its parameter, of its result
        // and of a captured value (v2 plan rung E9).
        (
            case("I64", "let f = fn(x: I64) -> x + x\n  f(5000000000)"),
            Some("10000000000i64"),
        ),
        (
            case("F64", "let f = fn(x: F64) -> x + 1.5\n  f(40.5)"),
            Some("42"),
        ),
        (
            case("F32", "let f = fn(x: F32) -> x + 1.5f32\n  f(40.5f32)"),
            Some("42f32"),
        ),
        (
            case(
                "I64",
                "let k = 5000000000\n  let f = fn(x: I32) -> k + k\n  f(1)",
            ),
            Some("10000000000i64"),
        ),
        // A named function as a value takes its arguments 1 at a time.
        (
            case("I64", "let f = first_I64_F64(5000000000)\n  f(1.5)"),
            Some("5000000000i64"),
        ),
        (case("F64", "apply_F64(same_F64, 2.5)"), Some("2.5")),
    ]
}

/// The module: `data Option`, the functions that the closure cases call,
/// then one function per case.
fn module_source(cases: &[Case]) -> String {
    let mut src = String::from("module matrix\n\ndata Option(a) = None | Some(a)\n\n");
    for ty in VALUE_TYPES {
        src.push_str(&format!("fn same_{ty}(x: {ty}): {ty} = x\n\n"));
        src.push_str(&format!(
            "fn apply_{ty}(f: {ty} -> {ty}, x: {ty}): {ty} = f(x)\n\n"
        ));
        for other in VALUE_TYPES {
            src.push_str(&format!(
                "fn first_{ty}_{other}(a: {ty}, b: {other}): {ty} = a\n\n"
            ));
        }
    }
    for (i, c) in cases.iter().enumerate() {
        src.push_str(&format!("fn c{i}(): {} =\n  {}\n\n", c.ty, c.expr));
    }
    src
}

/// A wasm result, printed the way the interpreter prints a value.
fn show(ty: &str, val: Val) -> String {
    match (ty, val) {
        ("Unit", _) => "()".to_string(),
        ("Bool", Val::I32(n)) => (n != 0).to_string(),
        ("I32", Val::I32(n)) => n.to_string(),
        ("I64", Val::I64(n)) => format!("{n}i64"),
        ("F32", Val::F32(bits)) => format!("{}f32", f32::from_bits(bits)),
        ("F64", Val::F64(bits)) => f64::from_bits(bits).to_string(),
        (ty, val) => panic!("result {val:?} does not have the wasm type of {ty}"),
    }
}

/// Load a program through the driver, as one merged module. The closure
/// cases need the flag `--unstable-core`.
fn load(src: &str) -> ephapax_syntax::Module {
    let stdlib = ephapax_driver::stdlib_dir(None);
    let features = ephapax_driver::Features {
        unstable_core: true,
    };
    ephapax_driver::load_source_with(src, "matrix", None, stdlib.as_deref(), features)
        .unwrap_or_else(|e| panic!("the matrix module must load: {e}"))
        .into_merged()
        .expect("the matrix module merges")
}

/// A linker with the print functions of `env`, which do nothing here.
fn linker(engine: &Engine) -> Linker<()> {
    let mut linker = Linker::new(engine);
    linker.func_wrap("env", "print_i32", |_: i32| {}).unwrap();
    linker
        .func_wrap("env", "print_string", |_: i32, _: i32| {})
        .unwrap();
    linker
}

#[test]
fn wasm_and_interpreter_agree_on_the_type_operation_matrix() {
    let (pinned_cases, expected): (Vec<Case>, Vec<_>) = pinned().into_iter().unzip();
    let n_pinned = pinned_cases.len();
    let mut cases = pinned_cases;
    cases.extend(cases_matrix());
    let module = load(&module_source(&cases));
    let wasm = ephapax_wasm::compile_module(&module).expect("the matrix module must compile");
    wasmparser::validate(&wasm).expect("the matrix module must be valid wasm");

    let engine = Engine::default();
    let compiled = Module::new(&engine, &wasm).expect("wasmtime loads the module");
    let linker = linker(&engine);
    let mut interp = Interpreter::new();
    interp.load_module(&module);

    let mut disagreements = Vec::new();
    let mut values = 0;
    for (i, c) in cases.iter().enumerate() {
        let name = format!("c{i}");

        let mut store = Store::new(&engine, ());
        let instance = linker.instantiate(&mut store, &compiled).unwrap();
        let func = instance.get_func(&mut store, &name).unwrap();
        let mut results = [Val::I32(0)];
        let wasm_out = func
            .call(&mut store, &[], &mut results)
            .ok()
            .map(|()| show(c.ty, results[0]));

        let interp_out = interp.call(&name, vec![]).ok().map(|v| v.to_string());
        if interp_out.is_none() {
            // An error can leave bindings behind: start clean.
            interp = Interpreter::new();
            interp.load_module(&module);
        }

        values += usize::from(wasm_out.is_some());
        if i < n_pinned && wasm_out.as_deref() != expected[i] {
            disagreements.push(format!(
                "{}: `{}`\n    wasm:     {:?}\n    expected: {:?}",
                c.ty,
                c.expr.replace('\n', " "),
                wasm_out,
                expected[i]
            ));
        }
        if wasm_out != interp_out {
            disagreements.push(format!(
                "{}: `{}`\n    wasm:        {:?}\n    interpreter: {:?}",
                c.ty,
                c.expr.replace('\n', " "),
                wasm_out,
                interp_out
            ));
        }
    }

    println!(
        "typed codegen matrix: {} cases, {} with a value, {} that fail on both paths",
        cases.len(),
        values,
        cases.len() - values
    );
    // Most cases compute a value; only a zero divisor, `MIN / -1` and a
    // list index out of range fail.
    assert!(
        values * 10 > cases.len() * 9,
        "too few cases produce a value"
    );
    assert!(
        disagreements.is_empty(),
        "{} of {} cases disagree:\n{}",
        disagreements.len(),
        cases.len(),
        disagreements.join("\n")
    );
}

/// The interpreter has no `extern`, so a value passed through a host
/// identity function is compared with the same value not passed through.
#[test]
fn extern_parameters_and_results_keep_their_type() {
    let host = [
        ("I32", "id_i32"),
        ("I64", "id_i64"),
        ("F32", "id_f32"),
        ("F64", "id_f64"),
    ];
    let mut src = String::from("module ext\n\nextern \"env\" {\n");
    for (ty, name) in host {
        src.push_str(&format!("  fn {name}(x: {ty}): {ty}\n"));
    }
    src.push_str("}\n\n");
    let mut cases = Vec::new();
    for (ty, name) in host {
        for v in samples(ty) {
            src.push_str(&format!(
                "fn c{n}(): {ty} =\n  {name}({v})\n\nfn c{m}(): {ty} =\n  {v}\n\n",
                n = cases.len(),
                m = cases.len() + 1
            ));
            cases.push(ty);
            cases.push(ty);
        }
    }

    let wasm = ephapax_wasm::compile_module(&load(&src)).expect("extern module compiles");
    wasmparser::validate(&wasm).expect("valid wasm");
    let engine = Engine::default();
    let compiled = Module::new(&engine, &wasm).unwrap();
    let mut linker = linker(&engine);
    linker.func_wrap("env", "id_i32", |x: i32| x).unwrap();
    linker.func_wrap("env", "id_i64", |x: i64| x).unwrap();
    linker.func_wrap("env", "id_f32", |x: f32| x).unwrap();
    linker.func_wrap("env", "id_f64", |x: f64| x).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = linker.instantiate(&mut store, &compiled).unwrap();

    let mut run = |i: usize| {
        let func = instance.get_func(&mut store, &format!("c{i}")).unwrap();
        let mut results = [Val::I32(0)];
        func.call(&mut store, &[], &mut results).unwrap();
        show(cases[i], results[0])
    };
    for i in (0..cases.len()).step_by(2) {
        assert_eq!(run(i), run(i + 1), "case {i} ({})", cases[i]);
    }
}
