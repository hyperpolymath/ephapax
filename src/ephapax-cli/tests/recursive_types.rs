// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// recursive_types.rs: v2 plan rung E9, recursive types (decision D7).
//
// A `data` type that refers to itself is an iso-recursive type
// `mu X. T` in the core. The desugarer puts a `fold` at each constructor
// and an `unfold` at each `match`. A value of the type is a pointer to
// its unfolding (a sum cell, a pair), so `fold` and `unfold` do nothing
// at run time. Each program here runs as wasm and in the interpreter,
// with the flag `--unstable-core`, and the 2 must print the expected
// value.

use std::path::Path;
use std::process::{Command, Output};

/// Run the `ephapax` binary with `args`, in the directory `dir`.
fn ephapax(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_ephapax"))
        .current_dir(dir)
        .args(args)
        .output()
        .expect("spawn ephapax")
}

/// Write each program (name, text, output) into `dir` and run it as wasm
/// and in the interpreter, with the flag `--unstable-core`.
fn each_runs(dir: &Path, programs: &[(&str, String, &str)]) {
    for (name, text, want) in programs {
        let file = format!("{name}.eph");
        std::fs::write(dir.join(&file), text).expect("write program");
        for mode in [&["run"][..], &["run", "--interp"]] {
            let args: Vec<&str> = [mode, &["--unstable-core", file.as_str()]].concat();
            let out = ephapax(dir, &args);
            assert!(
                out.status.success(),
                "{name} under {args:?} failed:\n{}",
                String::from_utf8_lossy(&out.stderr)
            );
            let stdout = String::from_utf8_lossy(&out.stdout);
            assert_eq!(stdout.trim(), *want, "{name} under {args:?}");
        }
    }
}

/// `check` refuses `text` with a message that has `error` in it.
fn check_refuses(name: &str, text: &str, error: &str) {
    let tmp = tempfile::tempdir().expect("tempdir");
    let file = format!("{name}.eph");
    std::fs::write(tmp.path().join(&file), text).expect("write program");
    let out = ephapax(tmp.path(), &["check", "--unstable-core", &file]);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !out.status.success() && stderr.contains(error),
        "{name}: exit {:?}, stderr:\n{stderr}",
        out.status.code()
    );
}

/// A list of I32, and the sum of its elements.
const INT_LIST: &str = "data IntList = Nil | Cons(I32, IntList)\n\n\
    fn sum(l: IntList): I32 = match l of | Nil => 0 | Cons(h, t) => h + sum(t) end\n\n";

/// The acceptance program of the rung (the sum of an IntList), and the
/// other uses of a `data` type that refers to itself.
#[test]
fn a_recursive_data_type_runs() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let with_list = |rest: &str| format!("{INT_LIST}{rest}\n");
    each_runs(
        tmp.path(),
        &[
            (
                "sum",
                with_list("fn main(): I32 = sum(Cons(1, Cons(2, Cons(3, Nil))))"),
                "6",
            ),
            // A function makes the value, 1 cell for each call.
            (
                "range",
                with_list(
                    "fn range(n: I32): IntList = if n == 0 then Nil else Cons(n, range(n - 1))\n\n\
                     fn main(): I32 = sum(range(20))",
                ),
                "210",
            ),
            (
                "append",
                with_list(
                    "fn append(a: IntList, b: IntList): IntList =\n  \
                     match a of | Nil => b | Cons(h, t) => Cons(h, append(t, b)) end\n\n\
                     fn main(): I32 = sum(append(Cons(1, Cons(2, Nil)), Cons(30, Cons(9, Nil))))",
                ),
                "42",
            ),
            // With a closure, and with a named function as a value.
            (
                "map",
                with_list(
                    "fn map(f: I32 -> I32, l: IntList): IntList =\n  \
                     match l of | Nil => Nil | Cons(h, t) => Cons(f(h), map(f, t)) end\n\n\
                     fn apply(f: IntList -> I32, l: IntList): I32 = f(l)\n\n\
                     fn main(): I32 = apply(sum, map(fn(x: I32) -> x * 2, Cons(1, Cons(20, Nil))))",
                ),
                "42",
            ),
            // A guard, a literal in a pattern, and an arm for each constructor.
            (
                "guard",
                with_list(
                    "fn pos(l: IntList): I32 =\n  match l of\n  \
                     | Cons(h, t) if h > 0 => 1 + pos(t)\n  | Cons(h, t) => pos(t)\n  \
                     | Nil => 0\n  end\n\n\
                     fn zeros(l: IntList): I32 =\n  match l of\n  \
                     | Cons(0, t) => 1 + zeros(t)\n  | Cons(h, t) => zeros(t)\n  | Nil => 0\n  end\n\n\
                     fn empty(l: IntList): Bool = match l of | Nil => true | _ => false end\n\n\
                     fn main(): I32 =\n  let l = Cons(1, Cons(0, Cons(5, Nil)))\n  \
                     if empty(l) then 0 else pos(l) * 10 + zeros(l)",
                ),
                "21",
            ),
            // In a pair, in a list, and captured by a closure.
            (
                "inside",
                with_list(
                    "fn main(): I32 =\n  let p = (Cons(20, Nil), Cons(1, Nil))\n  \
                     let xs = [Cons(10, Nil), Cons(2, Nil)]\n  let l = Cons(9, Nil)\n  \
                     let f = fn(n: I32) -> n + sum(l)\n  \
                     f(sum(p.0) + sum(p.1) + sum(xs[0]) + sum(xs[1]))",
                ),
                "42",
            ),
            // 3 constructors, 2 of them with the type in a field.
            (
                "tree",
                "data T = A | B(I32, T) | C(T, T)\n\n\
                 fn size(t: T): I32 =\n  match t of\n  | A => 1\n  | B(n, r) => n + size(r)\n  \
                 | C(l, r) => size(l) + size(r)\n  end\n\n\
                 fn main(): I32 = size(C(B(30, A), C(B(8, A), A)))\n"
                    .to_string(),
                "41",
            ),
            // The constructor with the field is not the last one.
            (
                "first_ctor",
                "data Wrap = W(I32, Wrap) | End\n\n\
                 fn depth(w: Wrap): I32 = match w of | End => 0 | W(n, r) => n + depth(r) end\n\n\
                 fn main(): I32 = depth(W(40, W(2, End)))\n"
                    .to_string(),
                "42",
            ),
            (
                "nat",
                "data Nat = Z | S(Nat)\n\n\
                 fn to_i(n: Nat): I32 = match n of | Z => 0 | S(m) => 1 + to_i(m) end\n\n\
                 fn add(a: Nat, b: Nat): Nat = match a of | Z => b | S(m) => S(add(m, b)) end\n\n\
                 fn main(): I32 = to_i(add(S(S(Z)), S(Z)))\n"
                    .to_string(),
                "3",
            ),
            // A `type` alias in the cycle is transparent: the recursion is
            // that of the `data` type.
            (
                "alias",
                "type P = (I32, T)\n\ndata T = End | More(P)\n\n\
                 fn depth(t: T): I32 = match t of | End => 0 | More(p) => 1 + depth(p.1) end\n\n\
                 fn of_pair(p: P): I32 = depth(p.1)\n\n\
                 fn main(): I32 = of_pair((1, More((2, More((3, End))))))\n"
                    .to_string(),
                "2",
            ),
        ],
    );
}

/// A `data` type with type parameters that refers to itself. The type
/// arguments of a constructor come from its use: `Nil` is a list of I64
/// in one place and a list of lists in another.
#[test]
fn a_recursive_data_type_with_type_parameters_runs() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let with_list = |rest: &str| format!("data List(a) = Nil | Cons(a, List(a))\n\n{rest}\n");
    each_runs(
        tmp.path(),
        &[
            (
                "bool",
                with_list(
                    "fn all(l: List(Bool)): Bool =\n  \
                     match l of | Nil => true | Cons(h, t) => h && all(t) end\n\n\
                     fn main(): I32 = if all(Cons(true, Cons(true, Nil))) then 42 else 0",
                ),
                "42",
            ),
            // An element keeps its width in the cell.
            (
                "i64",
                with_list(
                    "fn sum(l: List(I64)): I64 =\n  match l of\n  \
                     | Nil => 5000000000 - 5000000000\n  | Cons(h, t) => h + sum(t)\n  end\n\n\
                     fn main(): I64 = sum(Cons(5000000000, Cons(5000000000, Nil)))",
                ),
                "10000000000i64",
            ),
            (
                "f64",
                with_list(
                    "fn sum(l: List(F64)): F64 =\n  \
                     match l of | Nil => 0.0 | Cons(h, t) => h + sum(t) end\n\n\
                     fn main(): F64 = sum(Cons(1.5, Cons(40.5, Nil)))",
                ),
                "42",
            ),
            // A list of lists: the type is an argument of itself.
            (
                "nested",
                with_list(
                    "fn len(l: List(List(I32))): I32 =\n  \
                     match l of | Nil => 0 | Cons(h, t) => 1 + len(t) end\n\n\
                     fn main(): I32 = len(Cons(Cons(1, Nil), Cons(Nil, Nil)))",
                ),
                "2",
            ),
            // A recursive type as the argument of a recursive type.
            (
                "rose",
                with_list(
                    "data Rose = R(I32, List(Rose))\n\n\
                     fn size(r: Rose): I32 = match r of | R(v, kids) => 1 + sizes(kids) end\n\n\
                     fn sizes(l: List(Rose)): I32 =\n  \
                     match l of | Nil => 0 | Cons(h, t) => size(h) + sizes(t) end\n\n\
                     fn main(): I32 = size(R(1, Cons(R(2, Nil), Cons(R(3, Nil), Nil))))",
                ),
                "3",
            ),
            // A generic function: 1 copy for each element type.
            (
                "generic",
                with_list(
                    "fn rev<T>(l: List(T), acc: List(T)): List(T) =\n  \
                     match l of | Nil => acc | Cons(h, t) => rev(t, Cons(h, acc)) end\n\n\
                     fn head(l: List(I32)): I32 = match l of | Nil => 0 | Cons(h, t) => h end\n\n\
                     fn first(l: List(Bool)): Bool =\n  \
                     match l of | Nil => false | Cons(h, t) => h end\n\n\
                     fn main(): I32 =\n  \
                     if first(rev(Cons(false, Cons(true, Nil)), Nil))\n  \
                     then head(rev(Cons(1, Cons(42, Nil)), Nil))\n  else 0",
                ),
                "42",
            ),
            // No annotation gives the type: the uses of the value do.
            (
                "from_use",
                with_list(
                    "fn main(): I32 =\n  let l = Cons(40, Cons(2, Nil))\n  \
                     match l of\n  | Nil => 0\n  \
                     | Cons(h, t) => match t of | Nil => h | Cons(g, u) => h + g end\n  end",
                ),
                "42",
            ),
        ],
    );
}

/// A module names a recursive `data` type of another module by the rule
/// of each `data` type: an import, and `pub`.
#[test]
fn a_recursive_data_type_crosses_a_module() {
    let tmp = tempfile::tempdir().expect("tempdir");
    std::fs::write(
        tmp.path().join("lib.eph"),
        "module lib\n\npub data IntList = Nil | Cons(I32, IntList)\n\n\
         pub data List(a) = LNil | LCons(a, List(a))\n\n\
         pub fn sum(l: IntList): I32 = match l of | Nil => 0 | Cons(h, t) => h + sum(t) end\n\n\
         pub fn one(n: I32): IntList = Cons(n, Nil)\n\n\
         pub data Tree = Leaf | Node(I32, Forest)\n\n\
         pub data Forest = FNil | FCons(Tree, Forest)\n\n\
         pub fn size(t: Tree): I32 =\n  \
         match t of | Leaf => 0 | Node(v, kids) => v + sizes(kids) end\n\n\
         pub fn sizes(f: Forest): I32 =\n  \
         match f of | FNil => 0 | FCons(t, rest) => size(t) + sizes(rest) end\n",
    )
    .expect("write module");
    let app = |name: &str, head: &str, main: &str| {
        format!("module {name}\n\n{head}\nfn main(): I32 = {main}\n")
    };
    each_runs(
        tmp.path(),
        &[
            (
                "plain",
                app("plain", "import lib\n", "sum(Cons(40, one(2)))"),
                "42",
            ),
            (
                "qualified",
                app(
                    "qualified",
                    "import lib\n",
                    "sum(lib.Cons(40, lib.Cons(2, lib.Nil)))",
                ),
                "42",
            ),
            (
                "listed",
                app(
                    "listed",
                    "import lib(IntList, sum)\n\n\
                     fn len(l: IntList): I32 = match l of | Nil => 0 | Cons(h, t) => 1 + len(t) end\n",
                    "sum(Cons(40, Nil)) + len(Cons(1, Cons(2, Nil)))",
                ),
                "42",
            ),
            (
                "parameters",
                app(
                    "parameters",
                    "import lib\n\nfn count(l: List(Bool)): I32 =\n  match l of\n  \
                     | LNil => 0\n  | LCons(h, t) => (if h then 1 else 0) + count(t)\n  end\n",
                    "count(LCons(true, LCons(false, LCons(true, LNil))))",
                ),
                "2",
            ),
            // 2 types that refer to each other, in a type of this module.
            (
                "each_other",
                app(
                    "each_other",
                    "import lib\n\ndata Wrap = W(Tree, Forest) | Stop\n\n\
                     fn total(w: Wrap): I32 =\n  \
                     match w of | Stop => 0 | W(t, f) => size(t) + sizes(f) end\n",
                    "total(W(Node(40, FNil), FCons(Node(2, FNil), FNil)))",
                ),
                "42",
            ),
            // A declaration of the module hides the imported type.
            (
                "hidden",
                app(
                    "hidden",
                    "import lib\n\ndata IntList = Mine(I32)\n",
                    "match Mine(42) of | Mine(n) => n end",
                ),
                "42",
            ),
        ],
    );
}

/// A recursive type with a linear component is linear: a value is used
/// 1 time, each part of it is consumed, and it cannot leave its region.
#[test]
fn a_recursive_type_keeps_the_linear_rules() {
    let list = "data SList = SNil | SCons(String@r, SList)\n\n";
    let tmp = tempfile::tempdir().expect("tempdir");
    each_runs(
        tmp.path(),
        &[(
            "consumed",
            format!(
                "{list}fn total(l: SList): I32 =\n  match l of\n  | SNil => 0\n  \
                 | SCons(s, t) => String.len(&s) + (let _ = drop(s) in total(t))\n  end\n\n\
                 fn main(): I32 =\n  region r {{\n    \
                 total(SCons(String.new@r(\"ab\"), SCons(String.new@r(\"abc\"), SNil)))\n  }}\n"
            ),
            "5",
        )],
    );

    // (name, functions, error)
    for (name, functions, error) in [
        (
            "used_2_times",
            "fn two(l: SList): (SList, SList) = (l, l)\n\nfn main(): I32 = 0\n",
            "Linear variable `l` used more than once",
        ),
        (
            "tail_not_consumed",
            "fn first(l: SList): I32 =\n  \
             match l of | SNil => 0 | SCons(s, t) => let _ = drop(s) in 1 end\n\n\
             fn main(): I32 = 0\n",
            "Linear variable `t` not consumed",
        ),
        (
            "not_used",
            "fn ignore(l: SList): I32 = 0\n\nfn main(): I32 = 0\n",
            "Linear variable `l` not consumed",
        ),
        (
            "leaves_its_region",
            "fn main(): I32 =\n  let l = region r { SCons(String.new@r(\"ab\"), SNil) }\n  0\n",
            "escapes region `r`",
        ),
    ] {
        check_refuses(name, &format!("{list}{functions}"), error);
    }

    // A recursive type with no linear component is not linear.
    each_runs(
        tmp.path(),
        &[(
            "shared",
            format!(
                "{INT_LIST}fn main(): I32 =\n  let l = Cons(20, Cons(1, Nil))\n  sum(l) + sum(l)\n"
            ),
            "42",
        )],
    );
}

/// `data` types that refer to each other. They become nested recursive
/// types, in the order of their names, and the unfolding of each one has
/// the types of the others in it as they are. So a field of a
/// constructor has the type that its declaration names: each program
/// here passes the type checker, and then runs.
#[test]
fn data_types_that_refer_to_each_other_run() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let forest = "fn size(t: Tree): I32 =\n  \
        match t of | Leaf => 0 | Node(v, kids) => v + sizes(kids) end\n\n\
        fn sizes(f: Forest): I32 =\n  \
        match f of | FNil => 0 | FCons(t, rest) => size(t) + sizes(rest) end\n\n";
    let mut programs = vec![
        // The first type by name (`Forest`) is the one that is folded.
        (
            "forest".to_string(),
            format!(
                "data Tree = Leaf | Node(I32, Forest)\n\n\
                 data Forest = FNil | FCons(Tree, Forest)\n\n{forest}\
                 fn grow(n: I32): Tree =\n  if n == 0 then Leaf\n  \
                 else Node(n, FCons(grow(n - 1), FCons(grow(n - 1), FNil)))\n\n\
                 fn main(): I32 = size(grow(4))\n"
            ),
            "26",
        ),
        // A type with 1 constructor in the cycle.
        (
            "even_odd".to_string(),
            "data Even = Zero | SuccE(Odd)\n\ndata Odd = SuccO(Even)\n\n\
             fn even(e: Even): I32 = match e of | Zero => 0 | SuccE(o) => 1 + odd(o) end\n\n\
             fn odd(o: Odd): I32 = match o of | SuccO(e) => 1 + even(e) end\n\n\
             fn main(): I32 = even(SuccE(SuccO(SuccE(SuccO(Zero)))))\n"
                .to_string(),
            "4",
        ),
        // No type of the cycle refers to itself.
        (
            "no_self".to_string(),
            "data A = MkA(B) | EndA\n\ndata B = MkB(I32, A)\n\n\
             fn sa(a: A): I32 = match a of | EndA => 0 | MkA(b) => sb(b) end\n\n\
             fn sb(b: B): I32 = match b of | MkB(n, a) => n + sa(a) end\n\n\
             fn main(): I32 = sa(MkA(MkB(40, MkA(MkB(2, EndA)))))\n"
                .to_string(),
            "42",
        ),
        // Type parameters, and an element that is not 32 bits wide.
        (
            "parameters".to_string(),
            "data Tree(a) = Leaf | Node(a, Forest(a))\n\n\
             data Forest(a) = FNil | FCons(Tree(a), Forest(a))\n\n\
             fn size(t: Tree(I64)): I64 =\n  match t of\n  \
             | Leaf => 5000000000 - 5000000000\n  | Node(v, kids) => v + sizes(kids)\n  end\n\n\
             fn sizes(f: Forest(I64)): I64 =\n  match f of\n  \
             | FNil => 5000000000 - 5000000000\n  | FCons(t, rest) => size(t) + sizes(rest)\n  \
             end\n\n\
             fn main(): I64 = size(Node(5000000000, FCons(Node(5000000000, FNil), FNil)))\n"
                .to_string(),
            "10000000000i64",
        ),
        // A linear component: each string is consumed 1 time.
        (
            "linear".to_string(),
            "data STree = SLeaf | SNode(String@r, SForest)\n\n\
             data SForest = SNil | SCons(STree, SForest)\n\n\
             fn len(t: STree): I32 =\n  match t of\n  | SLeaf => 0\n  \
             | SNode(s, kids) => String.len(&s) + (let _ = drop(s) in lens(kids))\n  end\n\n\
             fn lens(f: SForest): I32 =\n  \
             match f of | SNil => 0 | SCons(t, rest) => len(t) + lens(rest) end\n\n\
             fn main(): I32 =\n  region r {\n    \
             len(SNode(String.new@r(\"ab\"), SCons(SNode(String.new@r(\"abc\"), SNil), SNil)))\n  \
             }\n"
            .to_string(),
            "5",
        ),
    ];
    // 3 types, where each one refers to the 2 others. Each order of the 3
    // names is another nesting of the 3 recursive types.
    for [a, b, c] in [
        ["X", "Y", "Z"],
        ["X", "Z", "Y"],
        ["Y", "X", "Z"],
        ["Y", "Z", "X"],
        ["Z", "X", "Y"],
        ["Z", "Y", "X"],
    ] {
        programs.push((
            format!("cycle_{a}{b}{c}"),
            format!(
                "data {a} = L{a} | N{a}(I32, {b}, {c})\n\n\
                 data {b} = L{b} | N{b}({c}, {a}, I32)\n\n\
                 data {c} = L{c} | N{c}({a}, {b}, {c})\n\n\
                 fn s{a}(x: {a}): I32 =\n  \
                 match x of | L{a} => 1 | N{a}(n, p, q) => n + s{b}(p) + s{c}(q) end\n\n\
                 fn s{b}(x: {b}): I32 =\n  \
                 match x of | L{b} => 2 | N{b}(p, q, n) => n + s{c}(p) + s{a}(q) end\n\n\
                 fn s{c}(x: {c}): I32 =\n  \
                 match x of | L{c} => 3 | N{c}(p, q, r) => s{a}(p) + s{b}(q) + s{c}(r) end\n\n\
                 fn main(): I32 =\n  \
                 s{a}(N{a}(10, N{b}(L{c}, N{a}(5, L{b}, L{c}), 20),\n    \
                 N{c}(L{a}, L{b}, N{c}(L{a}, N{b}(L{c}, L{a}, 1), L{c}))))\n"
            ),
            "55",
        ));
    }
    let programs: Vec<(&str, String, &str)> = programs
        .iter()
        .map(|(name, text, want)| (name.as_str(), text.clone(), *want))
        .collect();
    each_runs(tmp.path(), &programs);

    // The linear rules hold for each type of a cycle.
    let strings = "data STree = SLeaf | SNode(String@r, SForest)\n\n\
        data SForest = SNil | SCons(STree, SForest)\n\n";
    for (name, ty) in [("forest_2_times", "SForest"), ("tree_2_times", "STree")] {
        check_refuses(
            name,
            &format!("{strings}fn two(x: {ty}): ({ty}, {ty}) = (x, x)\n\nfn main(): I32 = 0\n"),
            "Linear variable `x` used more than once",
        );
    }
    // A `Tree` is not a `Forest`, and a `Forest` is not a `Tree`: in a
    // constructor of the folded type (`FCons`), and in a constructor of
    // the type that is not folded (`Node`).
    let forest = "data Tree = Leaf | Node(I32, Forest)\n\n\
        data Forest = FNil | FCons(Tree, Forest)\n\n\
        fn size(t: Tree): I32 = match t of | Leaf => 0 | Node(v, kids) => v end\n\n";
    for (name, main, want) in [
        (
            "forest_as_tree",
            "match FCons(FNil, FNil) of | FNil => 0 | FCons(t, rest) => 1 end",
            "Type mismatch",
        ),
        (
            "tree_as_forest",
            "size(Node(1, Leaf))",
            "constructor `Node`",
        ),
    ] {
        check_refuses(name, &format!("{forest}fn main(): I32 = {main}\n"), want);
    }
}

/// The interpreter builds and reads a list of 100000 elements. A value
/// shares its parts, so the read of a variable does not copy the list,
/// and no step uses native recursion. (With boxed parts, a list of 2000
/// elements needed 3 GB, and one of 20000 aborted the process.)
#[test]
fn the_interpreter_runs_a_long_list() {
    let tmp = tempfile::tempdir().expect("tempdir");
    std::fs::write(
        tmp.path().join("long.eph"),
        "data List = Nil | Cons(I32, List)\n\n\
         fn build(n: I32): List = if n == 0 then Nil else Cons(n, build(n - 1))\n\n\
         fn length(l: List): I32 =\n  match l of\n  | Nil => 0\n  \
         | Cons(x, rest) => 1 + length(rest)\n  end\n\n\
         fn main(): I32 = length(build(100000))\n",
    )
    .expect("write program");
    let out = ephapax(
        tmp.path(),
        &["run", "--interp", "--unstable-core", "long.eph"],
    );
    assert_eq!(
        (
            out.status.code(),
            String::from_utf8_lossy(&out.stdout).trim()
        ),
        (Some(0), "100000"),
        "stderr:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
}

/// The recursive forms that have no lowering yet are refused by name.
#[test]
fn a_recursive_form_with_no_lowering_is_refused_by_name() {
    // 5 `data` types that each refer to each of the 5: the nested
    // recursive type of the last one by name needs 8 million bodies. And
    // 300 `data` types in a ring: the types nest too deep. Without the
    // limit, the first does not end and the second overflows the stack.
    let dense: String = (0..5)
        .map(|i| format!("data T{i} = L{i} | N{i}(T0, T1, T2, T3, T4)\n\n"))
        .collect();
    let ring: String = (0..300)
        .map(|i| format!("data T{i} = L{i} | N{i}(T{})\n\n", (i + 1) % 300))
        .collect();
    for (name, types, ty) in [("dense_cycle", dense, "T4"), ("deep_ring", ring, "T0")] {
        check_refuses(
            name,
            &format!("{types}fn f(t: {ty}): I32 = 0\n\nfn main(): I32 = 0\n"),
            &format!("the type `{ty}` is too large"),
        );
    }
    check_refuses(
        "other_arguments",
        "data Grow(a) = Stop | More(Grow((a, a)))\n\n\
         fn f(t: Grow(I32)): I32 = 0\n\nfn main(): I32 = 0\n",
        "recursive type `Grow` refers to itself with other type arguments",
    );
    check_refuses(
        "alias_only",
        "type A = (I32, B)\n\ntype B = (I32, A)\n\nfn f(t: A): I32 = 0\n\nfn main(): I32 = 0\n",
        "only a `data` type can refer to itself",
    );
}

/// A recursive `data` type is behind the flag `--unstable-core`: without
/// it, each command refuses the program by name. A declaration with no
/// use is not a use of the flag.
#[test]
fn a_recursive_data_type_is_behind_the_flag() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let write = |name: &str, text: &str| {
        std::fs::write(tmp.path().join(name), text).expect("write program")
    };
    write(
        "sum.eph",
        &format!("{INT_LIST}fn main(): I32 = sum(Cons(1, Nil))\n"),
    );
    // No function has the type in its signature: the body shows it.
    write(
        "body.eph",
        "data IntList = Nil | Cons(I32, IntList)\n\n\
         fn main(): I32 = match Cons(1, Nil) of | Nil => 0 | Cons(h, t) => h end\n",
    );
    for file in ["sum.eph", "body.eph"] {
        for command in [&["check"][..], &["compile"], &["run"], &["run", "--interp"]] {
            let args: Vec<&str> = [command, &[file]].concat();
            let out = ephapax(tmp.path(), &args);
            let stderr = String::from_utf8_lossy(&out.stderr);
            assert!(
                !out.status.success()
                    && stderr.contains("behind the flag `--unstable-core`")
                    && stderr.contains("the recursive type `IntList`"),
                "{args:?}: exit {:?}, stderr:\n{stderr}",
                out.status.code()
            );
        }
    }

    write(
        "declared.eph",
        "data IntList = Nil | Cons(I32, IntList)\n\nfn main(): I32 = 42\n",
    );
    let out = ephapax(tmp.path(), &["run", "declared.eph"]);
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "42");
}
