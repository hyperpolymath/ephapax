// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// generics.rs, v2 plan rung E7 gate (generic functions).
//
// A generic function is checked one time, with each type parameter as an
// opaque linear type. The program then gets one monomorphic copy of the
// function for each set of type arguments it is used with, and the
// generic definition is removed: codegen and the interpreter see
// monomorphic functions only.

use std::path::Path;
use std::process::{Command, Output};

use ephapax_syntax::Decl;

/// Run the `ephapax` binary with `args`, in the directory `dir`.
fn ephapax(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_ephapax"))
        .current_dir(dir)
        .args(args)
        .output()
        .expect("spawn ephapax")
}

/// Write the program `text` to the file `name` in `dir`.
fn write(dir: &Path, name: &str, text: &str) {
    std::fs::write(dir.join(name), text).expect("write program");
}

/// `id` used at three types, with two inputs for each: every copy
/// returns its input, as wasm and in the interpreter.
#[test]
fn a_generic_function_runs_at_each_type_it_is_used_with() {
    let tmp = tempfile::tempdir().expect("tempdir");
    for (ty, input, want) in [
        ("I32", "3", "3"),
        ("I32", "41", "41"),
        ("I64", "5000000000", "5000000000i64"),
        ("I64", "6000000000", "6000000000i64"),
        ("F64", "2.5", "2.5"),
        ("F64", "0.25", "0.25"),
    ] {
        write(
            tmp.path(),
            "g.eph",
            &format!("module g\n\nfn id<a>(x: a): a = x\n\nfn main(): {ty} = id({input})\n"),
        );
        for args in [&["run", "g.eph"][..], &["run", "--interp", "g.eph"]] {
            let out = ephapax(tmp.path(), args);
            assert_eq!(
                String::from_utf8_lossy(&out.stdout).trim(),
                want,
                "id({input}) at {ty} under {args:?}:\n{}",
                String::from_utf8_lossy(&out.stderr)
            );
        }
    }

    // An upper-case type parameter, also in an annotation of the body.
    write(
        tmp.path(),
        "upper.eph",
        "module upper\n\nfn apply<T>(x: T): T =\n  let f = fn(y: T) -> y\n  f(x)\n\n\
         fn main(): I32 = apply(3)\n",
    );
    for args in [&["run", "upper.eph"][..], &["run", "--interp", "upper.eph"]] {
        let out = ephapax(tmp.path(), args);
        assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "3", "{args:?}");
    }

    // A generic function of another module, and one that calls another
    // generic function.
    write(
        tmp.path(),
        "lib.eph",
        "module lib\n\npub fn id<a>(x: a): a = x\n\npub fn twice<a>(x: a): a = id(id(x))\n",
    );
    write(
        tmp.path(),
        "app.eph",
        "module app\n\nimport lib\n\nfn main(): F64 = twice(1.5)\n",
    );
    for args in [&["run", "app.eph"][..], &["run", "--interp", "app.eph"]] {
        let out = ephapax(tmp.path(), args);
        assert_eq!(
            String::from_utf8_lossy(&out.stdout).trim(),
            "1.5",
            "{args:?}"
        );
    }
}

/// A call can give its type arguments: `id[I32](3)`. The checker takes
/// them from the brackets, so a type parameter that no argument fixes
/// has a value.
#[test]
fn a_call_can_give_its_type_arguments() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let id = "fn id<a>(x: a): a = x\n\n";
    // (declarations, type and body of `main`, output)
    for (decls, ty, main, want) in [
        (id, "I32", "id[I32](3)", "3"),
        (id, "I32", "id[I32](41)", "41"),
        (id, "F64", "id[F64](2.5)", "2.5"),
        // Two type parameters.
        (
            "fn pair<a, b>(p: (a, b)): (a, b) = p\n\n",
            "I64",
            "snd(pair[I32, I64]((1, 6000000000)))",
            "6000000000i64",
        ),
        // A type parameter of the caller as a type argument, in lower
        // case and in upper case. In `g`, `a` is a variable too.
        (
            "fn id<a>(x: a): a = x\n\nfn g<a>(a: a): a = id[a](a)\n\n\
             fn wrap<T>(x: T): T = id[T](x)\n\n",
            "I32",
            "g(8) * 10 + wrap[I32](5)",
            "85",
        ),
        // A region type as a type argument.
        (
            id,
            "I32",
            "region r {\n    let! s = String.new@r(\"hello\")\n    String.len(id[String@r](s))\n  }",
            "5",
        ),
        // Brackets with one name that is not a type parameter are an
        // index, as before: the call is a call of the list element.
        (
            "",
            "I32",
            "let fs = [fn(x: I32) -> x + 1, fn(x: I32) -> x + 2] in\n  let i = 1 in\n  fs[i](3)",
            "5",
        ),
    ] {
        write(
            tmp.path(),
            "app.eph",
            &format!("module app\n\n{decls}fn main(): {ty} =\n  {main}\n"),
        );
        for args in [&["run", "app.eph"][..], &["run", "--interp", "app.eph"]] {
            let out = ephapax(tmp.path(), args);
            assert_eq!(
                String::from_utf8_lossy(&out.stdout).trim(),
                want,
                "{main} under {args:?}:\n{}",
                String::from_utf8_lossy(&out.stderr)
            );
        }
    }

    // No argument fixes `a`: the brackets do.
    write(
        tmp.path(),
        "zero.eph",
        "module zero\n\nfn zero<a>(): I32 = 7\n\nfn main(): I32 = zero[I64]()\n",
    );
    for args in [&["run", "zero.eph"][..], &["run", "--interp", "zero.eph"]] {
        let out = ephapax(tmp.path(), args);
        assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "7", "{args:?}");
    }

    // A type argument of a function of another module, with and without
    // the module qualifier.
    write(
        tmp.path(),
        "lib.eph",
        "module lib\n\npub fn id<a>(x: a): a = x\n",
    );
    write(
        tmp.path(),
        "use.eph",
        "module use\n\nimport lib\n\nfn main(): I32 = lib.id[I32](4) + id[I32](5)\n",
    );
    for args in [&["run", "use.eph"][..], &["run", "--interp", "use.eph"]] {
        let out = ephapax(tmp.path(), args);
        assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "9", "{args:?}");
    }
}

/// The merged program has one monomorphic function for each set of type
/// arguments, and no generic function.
#[test]
fn a_program_has_one_copy_for_each_set_of_type_arguments() {
    let tmp = tempfile::tempdir().expect("tempdir");
    write(
        tmp.path(),
        "two.eph",
        "module two\n\nfn id<a>(x: a): a = x\n\nfn main(): I64 =\n  let n = id(7)\n  id(6000000000)\n",
    );
    let merged = ephapax_driver::load_program(&tmp.path().join("two.eph"), None)
        .expect("loads")
        .into_merged()
        .expect("merges");
    let mut functions = Vec::new();
    for decl in &merged.decls {
        if let Decl::Fn {
            name, type_params, ..
        } = decl
        {
            assert!(type_params.is_empty(), "`{name}` is still generic");
            functions.push(name.as_str());
        }
    }
    assert_eq!(functions, ["main", "id<I32>", "id<I64>"]);
}

/// What the checker refuses in a generic program, each with a named
/// `TypeError`, on `check` and on `compile`.
#[test]
fn generic_programs_the_checker_refuses() {
    let tmp = tempfile::tempdir().expect("tempdir");
    // (program after the module header, text of the error)
    for (program, error) in [
        // A value of a type-parameter type can be linear in a use of the
        // function: no second use, and no discard.
        (
            "fn dup<a>(x: a): (a, a) = (x, x)\n\nfn main(): I32 = fst(dup(3))\n",
            "Linear variable `x` used more than once",
        ),
        (
            "fn k<a>(x: a): I32 = 0\n\nfn main(): I32 = k(3)\n",
            "Linear variable `x` not consumed",
        ),
        // Each call needs its own copy of `f`: copies without end.
        (
            "fn f<a>(x: a): I32 = f((x, 1))\n\nfn main(): I32 = f(3)\n",
            "Polymorphic recursion",
        ),
        // Nothing in the call fixes `a`.
        (
            "fn zero<a>(): I32 = 0\n\nfn main(): I32 = zero()\n",
            "Cannot infer a type argument of the generic function `zero`",
        ),
        // Explicit type arguments: the wrong type, a function that is not
        // generic, the wrong number.
        (
            "fn id<a>(x: a): a = x\n\nfn main(): I32 = id[I64](3)\n",
            "Type mismatch: expected Base(I64), found Base(I32)",
        ),
        (
            "fn inc(x: I32): I32 = x + 1\n\nfn main(): I32 = inc[I32](3)\n",
            "`inc` is not a generic function and cannot take type arguments",
        ),
        (
            "fn id<a>(x: a): a = x\n\nfn main(): I32 = id[I32, I64](3)\n",
            "The generic function `id` has 1 type parameter(s), but the call gives 2 type argument(s)",
        ),
        // No call gives the entry point its type arguments.
        (
            "fn main<a>(): I32 = 0\n",
            "`main` is the entry point of a program and cannot have type parameters",
        ),
    ] {
        write(tmp.path(), "bad.eph", &format!("module bad\n\n{program}"));
        for args in [&["check", "bad.eph"][..], &["compile", "bad.eph"]] {
            let out = ephapax(tmp.path(), args);
            let stderr = String::from_utf8_lossy(&out.stderr);
            assert!(
                !out.status.success() && stderr.contains("Type error") && stderr.contains(error),
                "{args:?} on:\n{program}\nexit {:?}, stderr:\n{stderr}",
                out.status.code()
            );
        }
    }
}

/// Only the `main` of the root module is the entry point. A generic
/// `main` of an imported module is a function like any other; the same
/// module as the root of a program is refused.
#[test]
fn a_generic_main_of_an_imported_module_is_not_an_entry_point() {
    let tmp = tempfile::tempdir().expect("tempdir");
    write(
        tmp.path(),
        "lib.eph",
        "module lib\n\nfn main<a>(x: a): a = x\n\npub fn keep(n: I32): I32 = main(n)\n",
    );
    for input in ["7", "11"] {
        write(
            tmp.path(),
            "app.eph",
            &format!("module app\n\nimport lib\n\nfn main(): I32 = keep({input})\n"),
        );
        for args in [&["run", "app.eph"][..], &["run", "--interp", "app.eph"]] {
            let out = ephapax(tmp.path(), args);
            assert_eq!(
                String::from_utf8_lossy(&out.stdout).trim(),
                input,
                "{args:?}:\n{}",
                String::from_utf8_lossy(&out.stderr)
            );
        }
    }

    let out = ephapax(tmp.path(), &["check", "lib.eph"]);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !out.status.success() && stderr.contains("cannot have type parameters"),
        "exit {:?}, stderr:\n{stderr}",
        out.status.code()
    );
}

/// A limit of the typed lowering that only a copy at a wide type shows
/// (here a lambda with an F64 parameter) is a load error on `check` too.
#[test]
fn check_sees_the_limits_of_the_monomorphic_copies() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let program = |ty: &str, input: &str| {
        format!(
            "module lam\n\nfn apply<a>(x: a): a =\n  let f = fn(y: a) -> y\n  f(x)\n\n\
             fn main(): {ty} = apply({input})\n"
        )
    };
    write(tmp.path(), "lam.eph", &program("I32", "3"));
    assert!(ephapax(tmp.path(), &["check", "lam.eph"]).status.success());

    write(tmp.path(), "lam.eph", &program("F64", "2.5"));
    for args in [&["check", "lam.eph"][..], &["compile", "lam.eph"]] {
        let out = ephapax(tmp.path(), args);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            !out.status.success() && stderr.contains("Codegen error") && stderr.contains("lambda"),
            "{args:?}: exit {:?}, stderr:\n{stderr}",
            out.status.code()
        );
    }
}
