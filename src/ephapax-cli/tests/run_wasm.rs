// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// run_wasm.rs, v2 plan rung E4 gate.
//
// `ephapax run` compiles the program and executes the wasm (wasmtime,
// in-process), forwarding its trailing arguments through the host imports
// `stdlib/Argv.eph` declares. The interpreter is `run --interp`; it is
// incomplete, and tests/interp-known-failures.txt lists the compiling
// corpus files on which it disagrees with the wasm path.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// The root of the repository.
fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root")
}

/// Run the `ephapax` binary with `args`, in the directory `dir`.
fn ephapax(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_ephapax"))
        .current_dir(dir)
        .args(args)
        .output()
        .expect("spawn ephapax")
}

/// stdout of a successful `ephapax <args>`, trimmed.
fn stdout_of(dir: &Path, args: &[&str]) -> String {
    let out = ephapax(dir, args);
    assert!(
        out.status.success(),
        "ephapax {args:?} failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

/// Paths (one per line, `#` comments) in a repo-root-relative list file.
fn list(root: &Path, file: &str) -> BTreeSet<String> {
    std::fs::read_to_string(root.join(file))
        .unwrap_or_else(|e| panic!("read {file}: {e}"))
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(str::to_string)
        .collect()
}

/// Probe p1 (data/match, recursion, `let!`): 40 + 2 + 120.
#[test]
fn run_executes_the_compiled_wasm() {
    let tmp = tempfile::tempdir().expect("tempdir");
    std::fs::copy(
        repo_root().join("tests/probes/p1.eph.txt"),
        tmp.path().join("p1.eph"),
    )
    .expect("stage p1");
    assert_eq!(stdout_of(tmp.path(), &["run", "p1.eph"]), "162");
    // A bare file argument runs it the same way.
    assert_eq!(stdout_of(tmp.path(), &["p1.eph"]), "162");
}

/// An .eph program cannot yet read bytes out of a raw buffer, so it
/// reports the argument count and byte lengths; the bytes `argv_arg_get`
/// copies are checked host-side (src/runner.rs).
#[test]
fn run_forwards_arguments_through_argv() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let write = |name: &str, body: &str| {
        let src = format!("module {name}\n\nimport Argv\n\nfn main(): I32 = {body}\n");
        std::fs::write(tmp.path().join(format!("{name}.eph")), src).expect("write program");
    };
    // 1000 * argc + byte length of argv[1] (-1 when there is none).
    write(
        "count_len",
        "Argv.argv_count() * 1000 + Argv.argv_arg_len(1)",
    );
    write("arg0_len", "Argv.argv_arg_len(0)");
    write("last_len", "Argv.argv_arg_len(Argv.argv_count() - 1)");

    let run = |args: &[&str]| stdout_of(tmp.path(), args);
    // No arguments: argv is just the program path, so argc is 1.
    assert_eq!(run(&["run", "count_len.eph"]), "999");
    assert_eq!(run(&["run", "count_len.eph", "hello"]), "2005");
    assert_eq!(run(&["run", "count_len.eph", "ab", "c", "héllo"]), "4002");
    // argv[0] is the program path as given.
    assert_eq!(
        run(&["run", "arg0_len.eph", "x"]),
        "arg0_len.eph".len().to_string()
    );
    // Byte length, not character count: "héllo" is 6 bytes of UTF-8.
    assert_eq!(run(&["run", "last_len.eph", "ab", "c", "héllo"]), "6");
}

/// `run` and `run --interp` must give the same result on every compiling
/// corpus file, except the listed known failures. The list is a ratchet:
/// an entry that starts to agree must be removed.
#[test]
fn interpreter_and_wasm_agree_except_known_failures() {
    let root = repo_root();
    let known = list(&root, "tests/interp-known-failures.txt");
    let mut disagree = BTreeSet::new();
    for rel in list(&root, "tests/eph-corpus-compiles.txt") {
        let wasm = ephapax(&root, &["run", &rel]);
        let interp = ephapax(&root, &["run", "--interp", &rel]);
        if (wasm.status.success(), &wasm.stdout) != (interp.status.success(), &interp.stdout) {
            disagree.insert(rel);
        }
    }
    assert_eq!(
        disagree, known,
        "interpreter/wasm disagreements differ from tests/interp-known-failures.txt"
    );
}

/// A selective import (`import lib(inc)`) compiles and runs. Codegen
/// type-checks the merged module on its own; the import used to be kept
/// there and did not resolve.
#[test]
fn selective_import_runs() {
    let tmp = tempfile::tempdir().expect("tempdir");
    std::fs::write(
        tmp.path().join("lib.eph"),
        "module lib\n\npub fn inc(n: I32): I32 = n + 1\n",
    )
    .expect("write lib");
    std::fs::write(
        tmp.path().join("app.eph"),
        "module app\n\nimport lib(inc)\n\nfn main(): I32 = inc(41)\n",
    )
    .expect("write app");
    assert_eq!(stdout_of(tmp.path(), &["run", "app.eph"]), "42");
}

/// The entry point is the `main` of the module that was asked for. A
/// `main` in an imported module is not run.
#[test]
fn run_does_not_execute_the_main_of_an_imported_module() {
    let tmp = tempfile::tempdir().expect("tempdir");
    std::fs::write(
        tmp.path().join("lib.eph"),
        "module lib\n\npub fn inc(n: I32): I32 = n + 1\n\nfn main(): I32 = 99\n",
    )
    .expect("write lib");
    std::fs::write(
        tmp.path().join("app.eph"),
        "module app\n\nimport lib\n\nfn twice(n: I32): I32 = inc(inc(n))\n",
    )
    .expect("write app");
    for args in [&["run", "app.eph"][..], &["run", "--interp", "app.eph"]] {
        assert_eq!(stdout_of(tmp.path(), args), "", "{args:?}");
    }
}

/// Each module calls its own function when two modules use one name. The
/// merge used to keep one `helper` for both modules.
#[test]
fn each_module_calls_its_own_function_of_a_shared_name() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let write =
        |name: &str, text: &str| std::fs::write(tmp.path().join(name), text).expect("write module");
    // `helper` is private in each module.
    write(
        "deep.eph",
        "module deep\n\nfn helper(n: I32): I32 = n + 100\n\n\
         pub fn deep_val(n: I32): I32 = helper(n)\n\n\
         pub fn shadow(helper: I32): I32 = helper + 1000\n\n\
         pub fn pick(n: I32): I32 = n + 1\n",
    );
    write(
        "mid.eph",
        "module mid\n\nimport deep\n\nfn helper(n: I32): I32 = n + 1\n\n\
         pub fn mid_val(n: I32): I32 = helper(n) + deep_val(0)\n\n\
         pub fn pick(n: I32): I32 = n + 2\n",
    );
    // 2 + 100.
    write(
        "app.eph",
        "module app\n\nimport mid\n\nfn main(): I32 = mid_val(1)\n",
    );
    // The root has its own `helper` too: 8 + 100.
    write(
        "own.eph",
        "module own\n\nimport deep\n\nfn helper(n: I32): I32 = n + 7\n\n\
         fn main(): I32 = helper(1) + deep_val(0)\n",
    );
    // Two imports export `pick`: the later import is the one in scope.
    write(
        "later.eph",
        "module later\n\nimport deep\nimport mid\n\nfn main(): I32 = pick(0)\n",
    );
    for (file, want) in [("app.eph", "102"), ("own.eph", "108"), ("later.eph", "2")] {
        for args in [&["run", file][..], &["run", "--interp", file]] {
            assert_eq!(stdout_of(tmp.path(), args), want, "{args:?}");
        }
    }

    // `shadow` in `deep` has a parameter with the name of the function
    // that the merge renames; the parameter still shadows the function.
    write(
        "param.eph",
        "module param\n\nimport deep\n\nfn helper(n: I32): I32 = n\n\n\
         fn main(): I32 = shadow(0)\n",
    );
    for args in [&["run", "param.eph"][..], &["run", "--interp", "param.eph"]] {
        assert_eq!(stdout_of(tmp.path(), args), "1000", "{args:?}");
    }
}

/// `let (a, b, c) = e` binds the 3 parts of a tuple. The parser used to
/// make a chain of pair patterns for 3 or more names, which no tuple
/// value has as its type: a type error.
#[test]
fn a_binder_with_3_or_more_names_binds_a_tuple() {
    let tmp = tempfile::tempdir().expect("tempdir");
    // (declarations, type and body of `main`, output)
    for (decls, ty, main, want) in [
        ("", "I32", "let (a, b, c) = (1, 2, 3) in\n  a + b * c", "7"),
        ("", "I32", "let (a, b, c) = (5, 4, 3) in\n  a - b - c", "-2"),
        (
            "fn three(): (I32, I32, I32) = (1, 2, 3)\n",
            "I32",
            "let (a, b, c) = three()\n  a + b * c",
            "7",
        ),
        // 4 parts, each at its own type; `_` for a part that is not linear.
        (
            "fn four(): (I32, I64, F64, I32) = (1, 6000000000, 2.5, 4)\n",
            "I64",
            "let (a, b, _, d) = four()\n  b",
            "6000000000i64",
        ),
        // A linear part is bound, and consumed one time.
        (
            "",
            "I32",
            "region r {\n    let! s = String.new@r(\"hello\")\n    \
             let (a, t, c) = (1, s, 3)\n    a + String.len(t) + c\n  }",
            "9",
        ),
        // 2 names are a pair, as before.
        ("", "I32", "let (a, b) = (1, 2) in\n  a + b", "3"),
    ] {
        std::fs::write(
            tmp.path().join("tuple.eph"),
            format!("module tuple\n\n{decls}\nfn main(): {ty} =\n  {main}\n"),
        )
        .expect("write program");
        for args in [&["run", "tuple.eph"][..], &["run", "--interp", "tuple.eph"]] {
            assert_eq!(stdout_of(tmp.path(), args), want, "{main} under {args:?}");
        }
    }

    // `_` over a linear part is a discard of a linear value.
    std::fs::write(
        tmp.path().join("discard.eph"),
        "module discard\n\nfn main(): I32 =\n  region r {\n    \
         let! s = String.new@r(\"hello\")\n    let (a, _, c) = (1, s, 3)\n    a + c\n  }\n",
    )
    .expect("write program");
    let out = ephapax(tmp.path(), &["check", "discard.eph"]);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !out.status.success() && stderr.contains("Type error"),
        "exit {:?}, stderr:\n{stderr}",
        out.status.code()
    );
}

/// The interpreter calls a function with 0, 2 or 3 parameters by its
/// name, a parameter shadows a function of the same name, and a borrow of
/// a string is not a use. It used to stop on each of these programs
/// ("Not a function", "Unbound variable", "Linear value used after
/// consumption"); wasm ran them.
#[test]
fn the_interpreter_calls_and_borrows_as_wasm_does() {
    let tmp = tempfile::tempdir().expect("tempdir");
    // (declarations, `main` body, output)
    for (decls, main, want) in [
        ("fn seven(): I32 = 7\n", "seven() + seven()", "14"),
        ("fn add(a: I32, b: I32): I32 = a + b\n", "add(3, 4)", "7"),
        (
            "fn add(a: I32, b: I32): I32 = a + b\n",
            "add(add(1, 2), 30)",
            "33",
        ),
        (
            "fn add3(a: I32, b: I32, c: I32): I32 = a + b * c\n",
            "add3(1, 2, 3)",
            "7",
        ),
        // The order of the parameters: 10 - 3, not 3 - 10.
        ("fn sub(a: I32, b: I32): I32 = a - b\n", "sub(10, 3)", "7"),
        (
            "fn helper(n: I32): I32 = n + 100\n\nfn use_it(helper: I32): I32 = helper + 1\n",
            "use_it(5) + helper(0)",
            "106",
        ),
        (
            "",
            "region r {\n    let! s = String.new@r(\"hello\")\n    \
             let n = String.len(&s)\n    n + String.len(s)\n  }",
            "10",
        ),
        // A local name of the caller is not in scope in the function it
        // calls: `g` in `f` is the function, not the `g` of `main`.
        (
            "fn g(): I32 = 7\n\nfn f(x: I32): I32 = g() + x\n",
            "let g = 0 in f(1) + g",
            "8",
        ),
    ] {
        std::fs::write(
            tmp.path().join("calls.eph"),
            format!("module calls\n\n{decls}\nfn main(): I32 =\n  {main}\n"),
        )
        .expect("write program");
        for args in [&["run", "calls.eph"][..], &["run", "--interp", "calls.eph"]] {
            assert_eq!(stdout_of(tmp.path(), args), want, "{main} under {args:?}");
        }
    }
}

/// `M.Ctor(args)` builds a value of a data type of the imported module
/// `M`, with 0, 1 or 2 fields. The desugarer used to read `M.Ctor` as a
/// constructor with no arguments, then refuse the arguments.
#[test]
fn a_qualified_constructor_takes_its_arguments() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let write =
        |name: &str, text: &str| std::fs::write(tmp.path().join(name), text).expect("write module");
    write(
        "shapes.eph",
        "module shapes\n\npub data Shape = Dot | Seg(I32) | Rect(I32, I32)\n\n\
         pub fn area(s: Shape): I32 =\n  \
         match s of | Dot => 1 | Seg(n) => n | Rect(w, h) => w * h end\n",
    );
    for (shape, want) in [
        ("shapes.Dot", "1"),
        ("shapes.Dot()", "1"),
        ("shapes.Seg(5)", "5"),
        ("shapes.Seg(7)", "7"),
        ("shapes.Rect(3, 4)", "12"),
        ("shapes.Rect(4, 5)", "20"),
    ] {
        write(
            "app.eph",
            &format!("module app\n\nimport shapes\n\nfn main(): I32 = shapes.area({shape})\n"),
        );
        for args in [&["run", "app.eph"][..], &["run", "--interp", "app.eph"]] {
            assert_eq!(stdout_of(tmp.path(), args), want, "{shape} under {args:?}");
        }
    }

    // (call, text of the load error)
    for (shape, error) in [
        (
            "shapes.Seg(5, 6)",
            "constructor `Seg` expects 1 arguments, got 2",
        ),
        ("other.Seg(5)", "`other` is not an imported module"),
    ] {
        write(
            "bad.eph",
            &format!("module bad\n\nimport shapes\n\nfn main(): I32 = shapes.area({shape})\n"),
        );
        let out = ephapax(tmp.path(), &["compile", "bad.eph"]);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            !out.status.success() && stderr.contains(error),
            "{shape}: exit {:?}, stderr:\n{stderr}",
            out.status.code()
        );
    }
}

/// A module names a data type and its constructors when it declares
/// them, or when it imports the module that declares them and the type is
/// `pub` (owner decision 2026-11-10: the rule of functions). Each module
/// used to see each data type of each module loaded before it.
#[test]
fn a_module_names_a_data_type_only_through_a_pub_import() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let write =
        |name: &str, text: &str| std::fs::write(tmp.path().join(name), text).expect("write module");
    // `Inner` and `Secret` are private. `Outer` is public and has a
    // private type in its field.
    write(
        "lib.eph",
        "module lib\n\ndata Inner = I(I32)\n\npub data Outer = O(Inner)\n\n\
         pub data Box = MkBox(I32)\n\ndata Secret = Hidden(I32)\n\n\
         type Count = I32\n\npub data Tally = T(Count)\n\n\
         pub fn total(t: Tally): I32 = match t of | T(n) => n end\n\n\
         pub fn mk(n: I32): Outer = O(I(n))\n\n\
         pub fn get(o: Outer): I32 = match o of | O(i) => match i of | I(n) => n end end\n\n\
         pub fn unbox(b: Box): I32 = match b of | MkBox(v) => v end\n\n\
         pub fn secret(n: I32): Secret = Hidden(n)\n",
    );
    write(
        "deep.eph",
        "module deep\n\npub data Far = MkFar(I32)\n\npub fn far(n: I32): Far = MkFar(n)\n",
    );
    write(
        "mid.eph",
        "module mid\n\nimport deep\n\npub fn through(n: I32): Far = far(n)\n",
    );

    // (imports and declarations, `main` body, output)
    for (head, main, want) in [
        (
            "import lib\n",
            "unbox(MkBox(9)) + unbox(lib.MkBox(1))",
            "10",
        ),
        // An import list names the type; the constructors come with it.
        ("import lib(Box, unbox)\n", "unbox(MkBox(9))", "9"),
        (
            "import lib(Box)\n",
            "match MkBox(4) of | MkBox(v) => v end",
            "4",
        ),
        // `Outer` has the `Inner` of `lib` in its field, also in a module
        // that has its own `Inner`.
        (
            "import lib\n\ndata Inner = Mine(I64)\n\nfn pass(o: Outer): Outer = o\n",
            "get(pass(mk(5)))",
            "5",
        ),
        // Not a recursive type: this `Inner` is not the `Inner` in `Outer`.
        (
            "import lib\n\ndata Inner = Wrap(Outer)\n",
            "match Wrap(mk(6)) of | Wrap(o) => get(o) end",
            "6",
        ),
        // `Tally` has the `Count` of `lib` in its field, also in a module
        // that has its own alias `Count`.
        (
            "import lib\n\ntype Count = Bool\n\nfn yes(c: Count): Count = c\n",
            "if yes(true) then total(T(7)) else 0",
            "7",
        ),
        // A declaration of the module shadows an imported one.
        (
            "import lib\n\ndata Box = MkBox(I32, I32)\n",
            "match MkBox(3, 4) of | MkBox(a, b) => a + b end",
            "7",
        ),
    ] {
        write(
            "app.eph",
            &format!("module app\n\n{head}\nfn main(): I32 = {main}\n"),
        );
        for args in [&["run", "app.eph"][..], &["run", "--interp", "app.eph"]] {
            assert_eq!(stdout_of(tmp.path(), args), want, "{main} under {args:?}");
        }
    }

    // (imports and declarations, `main` body, text of the load error)
    for (head, main, error) in [
        // A private data type: its constructor and its name.
        (
            "import lib\n",
            "match secret(3) of | Hidden(n) => n end",
            "unknown constructor `Hidden`",
        ),
        (
            "import lib\n",
            "lib.Hidden(3)",
            "unknown constructor `Hidden`",
        ),
        (
            "import lib\n\nfn keep(s: Secret): Secret = s\n",
            "0",
            "unknown type `Secret`",
        ),
        // The import list does not name the type.
        (
            "import lib(unbox)\n",
            "unbox(MkBox(9))",
            "unknown constructor `MkBox`",
        ),
        // The list names only the type: no function comes with it.
        ("import lib(Box)\n", "unbox(MkBox(9))", "unbox"),
        // A data type of a module that this module does not import.
        (
            "import mid\n",
            "match through(3) of | MkFar(n) => n end",
            "unknown constructor `MkFar`",
        ),
    ] {
        write(
            "bad.eph",
            &format!("module bad\n\n{head}\nfn main(): I32 = {main}\n"),
        );
        let out = ephapax(tmp.path(), &["compile", "bad.eph"]);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            !out.status.success() && stderr.contains(error),
            "{head}{main}: exit {:?}, stderr:\n{stderr}",
            out.status.code()
        );
    }
}

/// A constructor of a `data` type with type parameters gets its type
/// arguments from the use of the value. The annotation of the injection
/// had the type parameter itself, which is no type at the constructor:
/// `None` was not an `Option(I32)`, and `L(1)` was not an
/// `Either(I32, Bool)`.
#[test]
fn a_constructor_gets_its_type_arguments_from_its_use() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let write =
        |name: &str, text: &str| std::fs::write(tmp.path().join(name), text).expect("write module");
    let option = "data Option(a) = None | Some(a)\n\n";
    let either = "data Either(a, b) = L(a) | R(b)\n\n";
    let three = "data T(a) = A(a) | B(a) | C(a)\n\n";
    let or = "fn or(o: Option(I32), d: I32): I32 = match o of | None => d | Some(n) => n end\n\n";

    // (declarations, `main` type, `main` body, output)
    for (decls, ty, main, want) in [
        // As a result, as an argument, and with no annotation.
        (
            format!("{option}{or}fn none(): Option(I32) = None\n\n"),
            "I32",
            "or(none(), 40) + or(None, 2)",
            "42",
        ),
        (
            option.to_string(),
            "I32",
            "let o = None in match o of | None => 42 | Some(n) => n end",
            "42",
        ),
        // The arms of the `match` fix the type after the constructor and
        // the scrutinee are checked. (The type table kept the type as
        // not known, and the wasm module was not valid.)
        (
            option.to_string(),
            "I64",
            "let o = None in match o of | None => 5000000000 | Some(n) => n end",
            "5000000000i64",
        ),
        (
            option.to_string(),
            "F64",
            "let o = None in match o of | None => 1.5 | Some(n) => n end",
            "1.5",
        ),
        // The 2 branches of an `if` give the 2 sides of the sum.
        (
            format!("{option}{or}"),
            "I32",
            "or(if true then None else Some(1), 42)",
            "42",
        ),
        // In a generic function, with a type parameter of another name.
        (
            format!(
                "{option}{or}fn none<T>(): Option(T) = None\n\n\
                 fn is(o: Option(Bool)): Bool = match o of | None => true | Some(b) => b end\n\n"
            ),
            "I32",
            "if is(none()) then or(none(), 42) else 0",
            "42",
        ),
        // A constructor in a constructor.
        (
            format!(
                "{option}fn deep(o: Option(Option(I32))): I32 =\n  match o of\n  | None => 1\n  \
                 | Some(i) => match i of | None => 2 | Some(n) => n end\n  end\n\n"
            ),
            "I32",
            "deep(None) + deep(Some(None)) + deep(Some(Some(39)))",
            "42",
        ),
        // 2 type parameters, each side at its width.
        (
            format!(
                "{either}fn pick(e: Either(I64, F64)): I64 =\n  \
                 match e of | L(n) => n | R(x) => 5000000000 - 4999999999 end\n\n"
            ),
            "I64",
            "pick(L(5000000000)) + pick(R(1.5))",
            "5000000001i64",
        ),
        // 3 constructors: each annotation of the chain.
        (
            format!(
                "{three}fn f(t: T(I32)): I32 =\n  \
                 match t of | A(n) => n | B(n) => n + 1 | C(n) => n + 2 end\n\n"
            ),
            "I32",
            "f(A(10)) + f(B(10)) + f(C(9))",
            "32",
        ),
    ] {
        write(
            "app.eph",
            &format!("module app\n\n{decls}fn main(): {ty} = {main}\n"),
        );
        for args in [&["run", "app.eph"][..], &["run", "--interp", "app.eph"]] {
            assert_eq!(stdout_of(tmp.path(), args), want, "{main} under {args:?}");
        }
    }

    // A use at another type is a type error, as before.
    write(
        "bad.eph",
        &format!("module bad\n\n{three}fn g(t: T(Bool)): I32 = 0\n\nfn main(): I32 = g(B(1))\n"),
    );
    let out = ephapax(tmp.path(), &["check", "bad.eph"]);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !out.status.success() && stderr.contains("Type mismatch"),
        "exit {:?}, stderr:\n{stderr}",
        out.status.code()
    );
}

/// A `type` alias and an extern type follow the rule of data types (owner
/// decision 2026-11-10): a module names one when it declares it, or when
/// it imports the module that declares it. An alias must also be `pub`;
/// an extern type is public, as an extern function is. Each module used
/// to see each alias and each extern type of the program.
#[test]
fn a_module_names_an_alias_or_an_extern_type_only_through_an_import() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let write =
        |name: &str, text: &str| std::fs::write(tmp.path().join(name), text).expect("write module");
    write(
        "lib.eph",
        "module lib\n\npub type Meters = I32\n\ntype Feet = I32\n\n\
         pub fn double(m: Meters): Meters = m + m\n\n\
         pub fn feet(n: I32): Feet = n\n",
    );
    write(
        "host.eph",
        "module host\n\nextern \"c\" {\n    type Handle\n    fn open(n: I32): Handle\n    \
         fn close(h: Handle): I32\n}\n",
    );
    write(
        "mid.eph",
        "module mid\n\nimport host\n\npub fn via(n: I32): I32 = close(open(n))\n",
    );
    let keep = "fn keep(m: Meters): Meters = m\n";
    let pass = "fn pass(h: Handle): Handle = h\n";

    // (imports and declarations, `main` body, output)
    for (head, main, want) in [
        (format!("import lib\n\n{keep}"), "double(keep(4))", "8"),
        // An import list names the alias.
        (
            format!("import lib(Meters, double)\n\n{keep}"),
            "double(keep(4))",
            "8",
        ),
        // A function of `lib` has the private alias in its signature.
        ("import lib\n".to_string(), "feet(3)", "3"),
        // A declaration of the module shadows an imported alias.
        (
            "import lib\n\ndata Meters = M(I32)\n".to_string(),
            "match M(5) of | M(n) => n end",
            "5",
        ),
    ] {
        write(
            "app.eph",
            &format!("module app\n\n{head}\nfn main(): I32 = {main}\n"),
        );
        for args in [&["run", "app.eph"][..], &["run", "--interp", "app.eph"]] {
            assert_eq!(stdout_of(tmp.path(), args), want, "{main} under {args:?}");
        }
    }

    // (imports and declarations, text of the load error; `None`: it compiles).
    // The host of `run` does not have `open`, so these programs do not run.
    let main = "close(pass(open(1)))";
    for (head, error) in [
        (format!("import host\n\n{pass}"), None),
        (format!("import host(Handle, open, close)\n\n{pass}"), None),
        // The import list does not name the type.
        (
            format!("import host(open, close)\n\n{pass}"),
            Some("unknown type `Handle`"),
        ),
        // An extern type of a module that this module does not import.
        (
            format!("import mid\n\n{pass}"),
            Some("unknown type `Handle`"),
        ),
        // A private alias, and an alias that the import list does not name.
        (
            "import lib\n\nfn keep(f: Feet): Feet = f\n".to_string(),
            Some("unknown type `Feet`"),
        ),
        (
            format!("import lib(double)\n\n{keep}"),
            Some("unknown type `Meters`"),
        ),
    ] {
        let body = if head.contains("Handle") { main } else { "0" };
        write(
            "app.eph",
            &format!("module app\n\n{head}\nfn main(): I32 = {body}\n"),
        );
        let out = ephapax(tmp.path(), &["compile", "app.eph"]);
        let stderr = String::from_utf8_lossy(&out.stderr);
        match error {
            None => assert!(out.status.success(), "{head}: stderr:\n{stderr}"),
            Some(error) => assert!(
                !out.status.success() && stderr.contains(error),
                "{head}: exit {:?}, stderr:\n{stderr}",
                out.status.code()
            ),
        }
    }
}

/// v2 plan rung E7: an arm with a false guard gives the value to the next
/// arm, as wasm and in the interpreter. The desugarer used to take a
/// guarded constructor arm without a look at its guard.
#[test]
fn a_false_guard_gives_the_value_to_the_next_arm() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let write = |name: &str, text: &str| {
        std::fs::write(tmp.path().join(name), text).expect("write program")
    };
    let opt = "data Opt = None | Some(I32)\n\n";
    // (declarations, `main` body, output)
    for (decls, main, want) in [
        // The guard selects between two arms of one constructor.
        (
            format!(
                "{opt}fn pick(o: Opt): I32 =\n  \
                 match o of | Some(x) if x > 5 => 1 | Some(x) => 2 | None => 0 end\n"
            ),
            "pick(Some(9)) * 100 + pick(Some(3)) * 10 + pick(None)",
            "120",
        ),
        // A guard that is always false: the wildcard arm takes the value.
        (
            format!("{opt}fn pick(o: Opt): I32 = match o of | Some(x) if false => 1 | _ => 7 end\n"),
            "pick(Some(9)) * 10 + pick(None)",
            "77",
        ),
        // The wildcard arm reads the outer `x`, not the `x` of the arm
        // before it.
        (
            format!(
                "{opt}fn pick(o: Opt): I32 =\n  let x = 40 in\n  \
                 match o of | Some(x) if x > 5 => x | _ => x end\n"
            ),
            "pick(Some(9)) * 100 + pick(Some(3))",
            "940",
        ),
        // Three constructors, two guards on one of them, a wildcard field.
        (
            "data Shape = Dot | Seg(I32) | Rect(I32, I32)\n\n\
             fn f(s: Shape): I32 =\n  match s of\n  \
             | Rect(w, h) if w > h => 1\n  | Rect(w, h) if w == h => 2\n  | Rect(_, _) => 3\n  \
             | Seg(n) if n > 0 => 4\n  | Dot => 5\n  | _ => 6\n  end\n"
                .to_string(),
            "f(Rect(3, 2)) * 100000 + f(Rect(2, 2)) * 10000 + f(Rect(1, 2)) * 1000 \
             + f(Seg(1)) * 100 + f(Seg(0)) * 10 + f(Dot)",
            "123465",
        ),
        // A literal in a constructor pattern can refuse the value too.
        (
            format!(
                "{opt}fn f(o: Opt): I32 =\n  match o of\n  \
                 | Some(0) if true => 1\n  | Some(7) => 2\n  | Some(n) if n > 100 => 3\n  \
                 | Some(_) => 4\n  | None => 5\n  end\n"
            ),
            "f(Some(0)) * 10000 + f(Some(7)) * 1000 + f(Some(200)) * 100 + f(Some(8)) * 10 + f(None)",
            "12345",
        ),
        // A data type with one constructor.
        (
            "data Box = MkBox(I32)\n\n\
             fn f(b: Box): I32 = match b of | MkBox(v) if v > 0 => 1 | MkBox(v) => 0 end\n"
                .to_string(),
            "f(MkBox(4)) * 10 + f(MkBox(0))",
            "10",
        ),
        // No constructor: literal, variable and pair patterns.
        (
            "fn f(n: I32): I32 =\n  \
             match n of | 0 => 10 | x if x > 5 => 20 | 3 if false => 30 | _ => 40 end\n\n\
             fn g(p: (I32, I32)): I32 = match p of | (a, b) if a > b => a | (a, b) => b end\n"
                .to_string(),
            "f(0) * 100000 + f(9) * 10000 + f(3) * 1000 + g((3, 9)) * 10 + g((7, 2))",
            "1240097",
        ),
    ] {
        write(
            "guard.eph",
            &format!("module guard\n\n{decls}\nfn main(): I32 = {main}\n"),
        );
        for args in [&["run", "guard.eph"][..], &["run", "--interp", "guard.eph"]] {
            assert_eq!(stdout_of(tmp.path(), args), want, "{main} under {args:?}");
        }
    }

    // A linear payload: the arm after a false guard binds it again, and
    // each arm consumes it one time.
    for (k, want) in [("7", "105"), ("3", "5")] {
        write(
            "linear.eph",
            &format!(
                "module linear\n\ndata Entry = Empty | Named(String@r, I32)\n\n\
                 fn main(): I32 =\n  region r {{\n    let! s = String.new@r(\"hello\")\n    \
                 let e = Named(s, {k})\n    match e of\n    \
                 | Named(n, k) if k > 5 => String.len(n) + 100\n    \
                 | Named(n, k) => String.len(n)\n    | Empty => 0\n    end\n  }}\n"
            ),
        );
        for args in [
            &["run", "linear.eph"][..],
            &["run", "--interp", "linear.eph"],
        ] {
            assert_eq!(stdout_of(tmp.path(), args), want, "k = {k} under {args:?}");
        }
    }

    // A guard that consumes a linear value: a false guard gives the value
    // to the next arm, which would use it a second time. `s` is from
    // outside the match; `n` is a part of the scrutinee.
    for (scrutinee, guard, name) in [
        ("Named(t, 3)", "eat(s)", "s"),
        ("Named(s, 3)", "eat(n)", "n"),
    ] {
        write(
            "consume.eph",
            &format!(
                "module consume\n\ndata Entry = Empty | Named(String@r, I32)\n\n\
                 fn eat(s: String@r): Bool = let n = String.len(s) in n > 100\n\n\
                 fn main(): I32 =\n  region r {{\n    let! s = String.new@r(\"hello\")\n    \
                 let! t = String.new@r(\"other\")\n    match {scrutinee} of\n    \
                 | Named(n, k) if {guard} => String.len(n)\n    \
                 | Named(n, k) => String.len(n) + String.len(s) + String.len(t)\n    \
                 | Empty => 0\n    end\n  }}\n"
            ),
        );
        let out = ephapax(tmp.path(), &["check", "consume.eph"]);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            !out.status.success()
                && stderr.contains(&format!("The guard of a match arm consumes `{name}`")),
            "{guard}: exit {:?}, stderr:\n{stderr}",
            out.status.code()
        );
    }

    // (match, text of the load error)
    for (matched, error) in [
        // A guarded arm does not cover its constructor.
        (
            "match o of | Some(x) if x > 5 => 1 | None => 0 end",
            "non-exhaustive match: missing constructor `Some`",
        ),
        (
            "match W(o) of | W(Some(x)) if x > 5 => 1 | _ => 0 end",
            "the constructor pattern `Some` inside another pattern is not supported",
        ),
    ] {
        write(
            "bad.eph",
            &format!(
                "module bad\n\n{opt}data Wrap = W(Opt)\n\n\
                 fn f(o: Opt): I32 = {matched}\n\nfn main(): I32 = f(None)\n"
            ),
        );
        let out = ephapax(tmp.path(), &["compile", "bad.eph"]);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            !out.status.success() && stderr.contains(error),
            "{matched}: exit {:?}, stderr:\n{stderr}",
            out.status.code()
        );
    }
}

/// A match with no guard honours a literal inside a constructor pattern.
/// The desugarer used to take the pattern inside as a wildcard, and to
/// keep only the last arm of a constructor: `Some(0)` matched each
/// `Some`, or was lost. A constructor inside a constructor pattern has
/// no lowering yet: it is refused by name, not taken as a wildcard.
#[test]
fn a_pattern_inside_a_constructor_pattern_is_not_a_wildcard() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let opt = "data Opt = None | Some(I32)\n\n";
    // (declarations, `main` body, output)
    for (decls, main, want) in [
        (
            format!(
                "{opt}fn f(o: Opt): I32 = match o of | Some(0) => 1 | Some(n) => 2 | None => 3 end\n"
            ),
            "f(Some(0)) * 100 + f(Some(5)) * 10 + f(None)",
            "123",
        ),
        (
            "data P = MkP(I32, I32)\n\n\
             fn f(p: P): I32 = match p of | MkP(0, y) => y | MkP(x, 0) => x | MkP(x, y) => x + y end\n"
                .to_string(),
            "f(MkP(0, 7)) * 100 + f(MkP(4, 0)) * 10 + f(MkP(2, 3))",
            "745",
        ),
    ] {
        std::fs::write(
            tmp.path().join("inside.eph"),
            format!("module inside\n\n{decls}\nfn main(): I32 = {main}\n"),
        )
        .expect("write program");
        for args in [&["run", "inside.eph"][..], &["run", "--interp", "inside.eph"]] {
            assert_eq!(stdout_of(tmp.path(), args), want, "{main} under {args:?}");
        }
    }

    // (declarations and match, text of the error)
    for (program, error) in [
        // `Some(5)` has no arm.
        (
            format!("{opt}fn f(o: Opt): I32 = match o of | Some(0) => 1 | None => 3 end\n"),
            "NonExhaustiveMatch",
        ),
        (
            format!(
                "{opt}data Wrap = W(Opt)\n\n\
                 fn f(w: Wrap): I32 = match w of | W(Some(x)) => 1 | W(None) => 0 end\n"
            ),
            "the constructor pattern `Some` inside another pattern is not supported",
        ),
    ] {
        std::fs::write(
            tmp.path().join("bad.eph"),
            format!("module bad\n\n{program}\nfn main(): I32 = 0\n"),
        )
        .expect("write program");
        let out = ephapax(tmp.path(), &["compile", "bad.eph"]);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            !out.status.success() && stderr.contains(error),
            "exit {:?}, stderr:\n{stderr}",
            out.status.code()
        );
    }
}

/// A pattern can name a constructor with its module: `shapes.Rect(w, h)`,
/// as an expression can since `a_qualified_constructor_takes_its_arguments`.
/// The module must be an import, and the type must be `pub`.
#[test]
fn a_pattern_can_name_a_constructor_with_its_module() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let write =
        |name: &str, text: &str| std::fs::write(tmp.path().join(name), text).expect("write module");
    write(
        "shapes.eph",
        "module shapes\n\npub data Shape = Dot | Seg(I32) | Rect(I32, I32)\n\n\
         data Hidden = H(I32)\n",
    );
    // (function body, `main` body, output)
    for (body, main, want) in [
        (
            "match s of | shapes.Dot => 1 | shapes.Seg(n) => n | shapes.Rect(w, h) => w * h end",
            "area(shapes.Rect(3, 4)) * 100 + area(Seg(5)) * 10 + area(shapes.Dot)",
            "1251",
        ),
        // With a guard, and next to a pattern with no module.
        (
            "match s of | shapes.Seg(n) if n > 3 => 1 | Seg(n) => 2 | _ => 0 end",
            "area(Seg(5)) * 100 + area(Seg(1)) * 10 + area(Dot)",
            "120",
        ),
    ] {
        write(
            "app.eph",
            &format!(
                "module app\n\nimport shapes\n\nfn area(s: Shape): I32 =\n  {body}\n\n\
                 fn main(): I32 = {main}\n"
            ),
        );
        for args in [&["run", "app.eph"][..], &["run", "--interp", "app.eph"]] {
            assert_eq!(stdout_of(tmp.path(), args), want, "{body} under {args:?}");
        }
    }

    // (pattern, text of the load error)
    for (pattern, error) in [
        ("other.Dot", "`other` is not an imported module"),
        ("shapes.H(v)", "unknown constructor `H`"),
    ] {
        write(
            "bad.eph",
            &format!(
                "module bad\n\nimport shapes\n\n\
                 fn f(s: Shape): I32 = match s of | {pattern} => 1 | _ => 0 end\n\n\
                 fn main(): I32 = f(Dot)\n"
            ),
        );
        let out = ephapax(tmp.path(), &["compile", "bad.eph"]);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            !out.status.success() && stderr.contains(error),
            "{pattern}: exit {:?}, stderr:\n{stderr}",
            out.status.code()
        );
    }
}

/// A pair pattern binds each component at its own type: a destructuring
/// `let`, and a constructor with several fields (a right-nested pair).
/// Patterns used to read every component as an i32.
#[test]
fn pair_patterns_bind_each_component_at_its_type() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let record = "data S = S(F32, I64, I32, F64)\n\n";
    let matched = |ty: &str, field: &str| {
        format!(
            "{record}fn main(): {ty} =\n  match S(1.5f32, 9000000000, 3, 0.25) of\n  \
             | S(a, b, c, d) => {field}\n  end\n"
        )
    };
    for (program, want) in [
        (
            "fn main(): I64 =\n  let (a, b) = (1, 5000000000)\n  b\n".to_string(),
            "5000000000i64",
        ),
        (
            "fn main(): F64 =\n  let (a, b) = (2.5, 7)\n  a\n".to_string(),
            "2.5",
        ),
        (matched("F32", "a"), "1.5f32"),
        (matched("I64", "b"), "9000000000i64"),
        (matched("I32", "c"), "3"),
        (matched("F64", "d"), "0.25"),
    ] {
        std::fs::write(
            tmp.path().join("pat.eph"),
            format!("module pat\n\n{program}"),
        )
        .expect("write program");
        for args in [&["run", "pat.eph"][..], &["run", "--interp", "pat.eph"]] {
            assert_eq!(stdout_of(tmp.path(), args), want, "{args:?}:\n{program}");
        }
    }
}

/// The binder of a `case` arm is in scope in that arm only. It used to
/// stay bound after the `case`, so a later use of an outer variable of
/// the same name read the binder.
#[test]
fn an_arm_binder_does_not_replace_an_outer_variable() {
    let tmp = tempfile::tempdir().expect("tempdir");
    for (payload, value, arm, want) in [
        ("I32", "7", "x", "12"),
        // The binder has another wasm type than the outer variable.
        ("I64", "7000000000", "1", "6"),
    ] {
        std::fs::write(
            tmp.path().join("scope.eph"),
            format!(
                "module scope\n\ndata Opt = Yes({payload}) | No\n\nfn main(): I32 =\n  \
                 let x = 5\n  let r = match Yes({value}) of\n    | Yes(x) => {arm}\n    \
                 | No => 0\n    end\n  r + x\n"
            ),
        )
        .expect("write program");
        for args in [&["run", "scope.eph"][..], &["run", "--interp", "scope.eph"]] {
            assert_eq!(
                stdout_of(tmp.path(), args),
                want,
                "{payload} under {args:?}"
            );
        }
    }
}
