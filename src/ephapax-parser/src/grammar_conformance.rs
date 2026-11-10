// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
//! One normative grammar (v2 plan rung E7).
//!
//! `spec/ephapax-v2-grammar.ebnf` has 2 parts:
//!
//! 1. The parser grammar. This module makes it from `ephapax.pest`, and
//!    a test fails when the 2 files are not the same grammar. Each rule
//!    is in the parse tree of a fixture.
//! 2. The productions of the v2 design that the parser does not have by
//!    that name. Each one has a mark: `[ALIAS rule]` (the parser has the
//!    construct as `rule`) or `[UNIMPLEMENTED]` with a fixture that the
//!    parser refuses.
//!
//! So no production is unaccounted for. To write part 1 again after a
//! change of `ephapax.pest`:
//!
//! ```text
//! UPDATE_GRAMMAR=1 cargo test -p ephapax-parser grammar_conformance
//! ```

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use pest::Parser as _;
use pest_meta::ast::{Expr, RuleType};

use crate::{parse_module, parse_surface_module, EphapaxParser, Rule};

const PEST: &str = include_str!("ephapax.pest");
const BEGIN: &str = "(* BEGIN GENERATED: the parser grammar, from ephapax.pest. Do not edit. *)";
const END: &str = "(* END GENERATED *)";

/// Rules that are in the grammar and never in a parse tree, with the
/// reason. Each other rule must be in the parse tree of a fixture.
const NO_PAIR: &[(&str, &str)] = &[
    ("WHITESPACE", "silent"),
    ("COMMENT", "silent"),
    ("string_inner", "inside the atomic rule `string`"),
    ("escape", "inside the atomic rule `string`"),
    ("keyword", "only in the lookahead of `identifier`"),
    ("keyword_boundary", "only in the lookahead of `identifier`"),
];

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn ebnf_path() -> PathBuf {
    repo().join("spec/ephapax-v2-grammar.ebnf")
}

fn pest_rules() -> BTreeMap<String, (RuleType, Expr)> {
    let pairs = pest_meta::parser::parse(pest_meta::parser::Rule::grammar_rules, PEST)
        .expect("ephapax.pest parses");
    pest_meta::parser::consume_rules(pairs)
        .expect("ephapax.pest is a valid grammar")
        .into_iter()
        .map(|rule| (rule.name, (rule.ty, rule.expr)))
        .collect()
}

/// A terminal. EBNF has no escapes: a control character has a name.
fn terminal(text: &str) -> String {
    match text {
        "\n" => "? LF ?".into(),
        "\r" => "? CR ?".into(),
        "\t" => "? TAB ?".into(),
        _ if text.contains('"') => format!("'{text}'"),
        _ => format!("\"{text}\""),
    }
}

/// The alternatives of a choice, in order.
fn alternatives(expr: &Expr) -> Vec<&Expr> {
    match expr {
        Expr::Choice(left, right) => {
            let mut all = alternatives(left);
            all.extend(alternatives(right));
            all
        }
        other => vec![other],
    }
}

/// EBNF text of a pest expression. `level` is where the text goes: 0 in
/// a choice, 1 in a sequence, 2 where one item must stand.
fn ebnf(expr: &Expr, level: u8) -> String {
    let (text, own) = match expr {
        Expr::Str(text) => (terminal(text), 2),
        Expr::Range(from, to) => (format!("? {} to {} ?", terminal(from), terminal(to)), 2),
        Expr::Ident(name) => (name.clone(), 2),
        Expr::PosPred(inner) => (format!("&( {} )", ebnf(inner, 0)), 2),
        Expr::NegPred(inner) => (format!("!( {} )", ebnf(inner, 0)), 2),
        Expr::Seq(left, right) => (format!("{} , {}", ebnf(left, 1), ebnf(right, 1)), 1),
        Expr::Choice(..) => {
            let parts: Vec<String> = alternatives(expr).iter().map(|e| ebnf(e, 1)).collect();
            (parts.join(" | "), 0)
        }
        Expr::Opt(inner) => (format!("[ {} ]", ebnf(inner, 0)), 2),
        Expr::Rep(inner) => (format!("{{ {} }}", ebnf(inner, 0)), 2),
        Expr::RepOnce(inner) => (format!("{{ {} }}-", ebnf(inner, 0)), 2),
        // snip: the other pest forms (counted repeats, the stack) are not
        // in ephapax.pest. One that arrives shows as it is, for a review.
        other => (format!("? pest: {other:?} ?"), 2),
    };
    if own < level {
        format!("( {text} )")
    } else {
        text
    }
}

/// One rule as an EBNF production.
fn production(name: &str, ty: RuleType, expr: &Expr) -> String {
    let note = match ty {
        RuleType::Normal => "",
        RuleType::Silent => " (* silent: no node in the parse tree *)",
        RuleType::Atomic => " (* atomic: no white space between the parts *)",
        RuleType::CompoundAtomic => " (* compound atomic *)",
        RuleType::NonAtomic => " (* non-atomic *)",
    };
    let one_line = format!("{name} = {} ;{note}", ebnf(expr, 0));
    let parts = alternatives(expr);
    if one_line.len() <= 96 || parts.len() == 1 {
        return one_line;
    }
    let indent = " ".repeat(name.len() + 1);
    let parts: Vec<String> = parts.iter().map(|e| ebnf(e, 1)).collect();
    format!(
        "{name} = {}\n{indent};{note}",
        parts.join(&format!("\n{indent}| "))
    )
}

/// The name of the rule that a line of `ephapax.pest` starts, if any.
fn rule_start(line: &str) -> Option<&str> {
    let (name, rest) = line.split_once('=')?;
    let name = name.trim_end();
    let named = !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    let opens = rest.trim_start().trim_start_matches(['_', '@', '$', '!']);
    (named && !line.starts_with(' ') && opens.starts_with('{')).then_some(name)
}

/// `{` minus `}` in a line of a rule, outside strings and comments.
fn brace_depth(line: &str) -> i32 {
    let (mut depth, mut quote, mut chars) = (0, None, line.chars().peekable());
    while let Some(c) = chars.next() {
        match (quote, c) {
            (Some(_), '\\') => {
                chars.next();
            }
            (Some(q), _) if c == q => quote = None,
            (Some(_), _) => {}
            (None, '"' | '\'') => quote = Some(c),
            (None, '/') if chars.peek() == Some(&'/') => break,
            (None, '{') => depth += 1,
            (None, '}') => depth -= 1,
            (None, _) => {}
        }
    }
    depth
}

/// Part 1 of the specification grammar: each rule of `ephapax.pest` in
/// the order of that file, with the comments of that file.
fn generated() -> String {
    let rules = pest_rules();
    let mut out = String::new();
    let mut comment: Vec<String> = Vec::new();
    let flush = |comment: &mut Vec<String>, out: &mut String| {
        for line in comment.drain(..) {
            out.push_str(&format!("(* {} *)\n", line.replace("*)", "* )")));
        }
    };
    let mut lines = PEST.lines();
    while let Some(line) = lines.next() {
        if let Some(text) = line.strip_prefix("//") {
            // A line of `=` or `-` is a banner of the pest file, and the
            // specification file has its own licence lines.
            let text = text.trim();
            let banner = text.chars().all(|c| c == '=' || c == '-');
            if !banner && !text.starts_with("SPDX-") && !text.starts_with("Owner:") {
                comment.push(text.replace('\u{2014}', "-"));
            }
        } else if let Some(name) = rule_start(line) {
            flush(&mut comment, &mut out);
            let (ty, expr) = &rules[name];
            out.push_str(&production(name, *ty, expr));
            out.push('\n');
            let mut depth = brace_depth(line);
            while depth > 0 {
                depth += brace_depth(lines.next().expect("the rule has an end"));
            }
        } else if !comment.is_empty() {
            // The end of a paragraph of comments.
            flush(&mut comment, &mut out);
            out.push('\n');
        } else if !out.ends_with("\n\n") {
            out.push('\n');
        }
    }
    out.trim_end().to_string() + "\n"
}

/// The 3 parts of the specification file: before part 1, part 1, after.
fn split(text: &str) -> (&str, &str, &str) {
    let (head, rest) = text.split_once(BEGIN).expect("the BEGIN GENERATED line");
    let (part, tail) = rest.split_once(END).expect("the END GENERATED line");
    (head, part, tail)
}

/// The names of the productions that a grammar text defines, in order. A
/// production starts at the start of a line.
fn defined(text: &str) -> Vec<&str> {
    text.lines()
        .filter_map(|line| {
            let (name, _) = line.split_once('=')?;
            let name = name.trim_end();
            let named = !name.is_empty()
                && !line.starts_with(' ')
                && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
            named.then_some(name)
        })
        .collect()
}

#[test]
fn the_specification_grammar_says_what_the_parser_accepts() {
    let path = ebnf_path();
    let text = std::fs::read_to_string(&path).expect("read the specification grammar");
    let (head, part, tail) = split(&text);
    let want = format!("\n\n{}\n", generated());
    if std::env::var_os("UPDATE_GRAMMAR").is_some() && part != want {
        std::fs::write(&path, format!("{head}{BEGIN}{want}{END}{tail}"))
            .expect("write the specification grammar");
        return;
    }
    assert!(
        part == want,
        "spec/ephapax-v2-grammar.ebnf is not the grammar of ephapax.pest. Run:\n  \
         UPDATE_GRAMMAR=1 cargo test -p ephapax-parser grammar_conformance"
    );
    // Each rule of the parser is a production, one time.
    let names = defined(part);
    let rules = pest_rules();
    assert_eq!(names.len(), rules.len());
    assert!(names.iter().all(|name| rules.contains_key(*name)));
}

/// Each `.eph` file below `dir`.
fn eph_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            eph_files(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "eph") {
            out.push(path);
        }
    }
}

/// The rules in the parse tree of `source`, parsed from the rule `entry`.
fn rules_in(entry: Rule, source: &str) -> Option<BTreeSet<String>> {
    let pairs = EphapaxParser::parse(entry, source).ok()?;
    Some(
        pairs
            .flatten()
            .map(|pair| format!("{:?}", pair.as_rule()))
            .collect(),
    )
}

/// Part 1: each rule of the parser is in the parse tree of a fixture, or
/// it is in [`NO_PAIR`].
#[test]
fn each_parser_rule_is_in_a_fixture() {
    let mut seen = BTreeSet::new();
    let fixtures = repo().join("tests/v2-grammar");
    let mut files = Vec::new();
    eph_files(&fixtures.join("productions"), &mut files);
    assert!(
        !files.is_empty(),
        "no fixture in tests/v2-grammar/productions"
    );
    for file in &files {
        let source = std::fs::read_to_string(file).expect("read fixture");
        let rules = rules_in(Rule::module, &source)
            .unwrap_or_else(|| panic!("{} does not parse", file.display()));
        seen.extend(rules);
    }
    // The 2 other entry points of the grammar.
    seen.extend(rules_in(Rule::expression_only, "1 + 2").expect("an expression parses"));
    seen.extend(rules_in(Rule::module_header, "module a.b\nfn").expect("a header parses"));

    let no_pair: BTreeSet<&str> = NO_PAIR.iter().map(|(name, _)| *name).collect();
    let wrong: Vec<String> = pest_rules()
        .into_keys()
        .filter(|name| seen.contains(name) == no_pair.contains(name.as_str()))
        .collect();
    assert!(
        wrong.is_empty(),
        "these rules are in no fixture and not in NO_PAIR, or in both: {wrong:?}. \
         Add a fixture to tests/v2-grammar/productions, or correct NO_PAIR."
    );
}

/// Part 2: each production that is not a rule of the parser has a mark.
/// An `[ALIAS rule]` names a rule of the parser. The parser refuses the
/// fixture of an `[UNIMPLEMENTED]` production.
#[test]
fn each_design_production_is_an_alias_or_is_refused() {
    let text = std::fs::read_to_string(ebnf_path()).expect("read the specification grammar");
    let (head, part, tail) = split(&text);
    assert!(defined(head).is_empty(), "a production before part 1");

    let rules = pest_rules();
    // Names that the parser grammar uses and pest defines.
    let builtins: BTreeSet<&str> = PEST
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .filter(|word| word.starts_with("ASCII_"))
        .collect();
    let mut names: BTreeSet<&str> = defined(part).into_iter().collect();
    let mut mark: Option<&str> = None;
    let (mut aliases, mut refused) = (0, 0);
    for line in tail.lines() {
        if let Some(rest) = line.strip_prefix("(* [") {
            mark = Some(rest);
            continue;
        }
        let Some(&name) = defined(line).first() else {
            continue;
        };
        assert!(names.insert(name), "`{name}` has 2 definitions");
        let mark = mark
            .take()
            .unwrap_or_else(|| panic!("`{name}` has no mark: it is unaccounted for"));
        if let Some(rest) = mark.strip_prefix("ALIAS ") {
            let rule = rest.split(']').next().unwrap_or_default();
            assert!(
                rules.contains_key(rule) || builtins.contains(rule),
                "`{name}` is an alias of `{rule}`, which the parser does not have"
            );
            aliases += 1;
        } else {
            let fixture = mark
                .strip_prefix("UNIMPLEMENTED] refused: ")
                .and_then(|rest| rest.split(' ').next())
                .unwrap_or_else(|| panic!("`{name}`: the mark `{mark}` is not a known mark"));
            let source = std::fs::read_to_string(repo().join(fixture))
                .unwrap_or_else(|_| panic!("`{name}`: no fixture {fixture}"));
            assert!(
                parse_surface_module(&source, "fixture").is_err()
                    && parse_module(&source, "fixture").is_err(),
                "`{name}` has the mark UNIMPLEMENTED, but the parser accepts {fixture}"
            );
            refused += 1;
        }
    }
    assert!(mark.is_none(), "a mark with no production after it");
    // 0 productions unaccounted for: a rule of the parser, an alias, or
    // a production that the parser refuses.
    assert_eq!(names.len(), rules.len() + aliases + refused);
}
