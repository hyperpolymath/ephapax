// SPDX-License-Identifier: PMPL-1.0-or-later
// Tree-sitter grammar for Ephapax — dyadic linear/affine language

module.exports = grammar({
  name: 'ephapax',

  extras: $ => [
    /\s/,
    $.comment,
  ],

  word: $ => $.identifier,

  conflicts: $ => [
    [$.type_expr, $.expr],
    [$.call_expr, $.region_alloc],
  ],

  rules: {
    source_file: $ => repeat($.declaration),

    // --- Comments ---
    comment: $ => seq('//', /.*/),

    // --- Identifiers ---
    identifier: $ => /[a-z_][a-zA-Z0-9_]*/,
    type_identifier: $ => /[A-Z][a-zA-Z0-9_]*/,
    module_path: $ => seq(
      $.type_identifier,
      repeat(seq('.', $.type_identifier))
    ),

    // --- Literals ---
    literal: $ => choice(
      $.integer,
      $.float,
      $.boolean,
      $.string,
      $.char,
      $.unit
    ),

    integer: $ => choice(
      /[0-9][0-9_]*/,
      /0x[0-9a-fA-F][0-9a-fA-F_]*/,
      /0b[01][01_]*/,
      /0o[0-7][0-7_]*/
    ),

    float: $ => /[0-9][0-9_]*\.[0-9][0-9_]*([eE][+-]?[0-9][0-9_]*)?/,

    boolean: $ => choice('true', 'false'),

    string: $ => seq(
      '"',
      repeat(choice(
        /[^"\\]+/,
        $.escape_sequence
      )),
      '"'
    ),

    char: $ => seq(
      "'",
      choice(/[^'\\]/, $.escape_sequence),
      "'"
    ),

    escape_sequence: $ => /\\(n|r|t|\\|"|'|x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\})/,

    unit: $ => '()',

    // --- Declarations ---
    declaration: $ => choice(
      $.fn_decl,
      $.type_decl,
      $.module_decl,
      $.import_decl,
    ),

    fn_decl: $ => seq(
      'fn',
      field('name', $.identifier),
      optional($.type_params),
      '(',
      optional($.params),
      ')',
      '->',
      field('return_type', $.type_expr),
      field('body', $.block),
    ),

    type_params: $ => seq(
      '<',
      $.type_param,
      repeat(seq(',', $.type_param)),
      '>'
    ),

    type_param: $ => seq(
      $.type_identifier,
      optional(seq(':', $.type_identifier))
    ),

    params: $ => seq(
      $.param,
      repeat(seq(',', $.param))
    ),

    param: $ => seq(
      field('name', $.identifier),
      ':',
      field('type', $.type_expr)
    ),

    type_decl: $ => seq(
      'type',
      field('name', $.type_identifier),
      optional($.type_params),
      '=',
      field('value', $.type_expr)
    ),

    module_decl: $ => seq(
      'module',
      field('name', $.module_path),
      field('body', $.block)
    ),

    import_decl: $ => seq(
      'import',
      $.module_path
    ),

    // --- Expressions ---
    expr: $ => choice(
      $.let_expr,
      $.let_linear_expr,
      $.region_expr,
      $.if_expr,
      $.match_expr,
      $.lambda_expr,
      $.binary_expr,
      $.call_expr,
      $.region_alloc,
      $.borrow_expr,
      $.copy_expr,
      $.block,
      $.literal,
      $.identifier,
      seq('(', $.expr, ')'),
    ),

    // Affine let binding
    let_expr: $ => prec.right(seq(
      'let',
      field('pattern', $.pattern),
      '=',
      field('value', $.expr),
      optional(choice(
        seq('in', field('body', $.expr)),
        seq(';', field('body', $.expr)),
      ))
    )),

    // Linear let binding — the ! is the key dyadic marker
    let_linear_expr: $ => prec.right(seq(
      'let!',
      field('pattern', $.pattern),
      '=',
      field('value', $.expr),
      optional(choice(
        seq('in', field('body', $.expr)),
        seq(';', field('body', $.expr)),
      ))
    )),

    // Region block
    region_expr: $ => seq(
      'region',
      field('name', $.identifier),
      ':',
      field('body', $.block)
    ),

    // Region-scoped allocation: Foo.new@r(args)
    region_alloc: $ => seq(
      field('callee', $.module_path),
      '.',
      field('method', $.identifier),
      '@',
      field('region', $.identifier),
      '(',
      optional($.args),
      ')'
    ),

    if_expr: $ => prec.right(seq(
      'if',
      field('condition', $.expr),
      field('then', $.block),
      optional(seq(
        'else',
        field('else', choice($.block, $.if_expr))
      ))
    )),

    match_expr: $ => seq(
      'match',
      field('subject', $.expr),
      '{',
      repeat($.match_arm),
      '}'
    ),

    match_arm: $ => seq(
      field('pattern', $.pattern),
      '=>',
      field('body', $.expr),
      optional(',')
    ),

    lambda_expr: $ => seq(
      'fn',
      '(',
      optional($.params),
      ')',
      optional(seq('->', $.type_expr)),
      choice(
        field('body', $.block),
        seq('=>', field('body', $.expr)),
      )
    ),

    binary_expr: $ => choice(
      ...[
        ['+', 6], ['-', 6], ['*', 7], ['/', 7], ['%', 7],
        ['==', 4], ['!=', 4], ['<', 5], ['>', 5], ['<=', 5], ['>=', 5],
        ['&&', 3], ['||', 2], ['++', 6],
      ].map(([op, prec_val]) =>
        prec.left(prec_val, seq(
          field('left', $.expr),
          field('operator', op),
          field('right', $.expr),
        ))
      )
    ),

    call_expr: $ => prec(8, seq(
      field('callee', $.expr),
      '(',
      optional($.args),
      ')'
    )),

    args: $ => seq(
      $.expr,
      repeat(seq(',', $.expr))
    ),

    borrow_expr: $ => prec(9, seq('&', $.expr)),

    copy_expr: $ => seq('copy', '(', $.expr, ')'),

    // --- Block ---
    block: $ => seq(
      '{',
      repeat($.stmt),
      optional(field('result', $.expr)),
      '}'
    ),

    stmt: $ => choice(
      seq($.expr, ';'),
      $.let_expr,
      $.let_linear_expr,
    ),

    // --- Patterns ---
    pattern: $ => choice(
      '_',
      $.identifier,
      $.literal,
      $.constructor_pattern,
      $.tuple_pattern,
    ),

    constructor_pattern: $ => seq(
      $.type_identifier,
      '(',
      $.pattern,
      repeat(seq(',', $.pattern)),
      ')'
    ),

    tuple_pattern: $ => seq(
      '(',
      $.pattern,
      ',',
      $.pattern,
      repeat(seq(',', $.pattern)),
      ')'
    ),

    // --- Type Expressions ---
    type_expr: $ => choice(
      $.type_identifier,
      $.generic_type,
      $.tuple_type,
      $.fn_type,
      $.ref_type,
      $.region_type,
      $.primitive_type,
    ),

    generic_type: $ => seq(
      $.type_identifier,
      '<',
      $.type_expr,
      repeat(seq(',', $.type_expr)),
      '>'
    ),

    tuple_type: $ => seq(
      '(',
      $.type_expr,
      repeat(seq(',', $.type_expr)),
      ')'
    ),

    fn_type: $ => prec.right(1, seq(
      $.type_expr,
      '->',
      $.type_expr,
    )),

    ref_type: $ => seq('&', $.type_expr),

    region_type: $ => seq($.type_expr, '@', $.identifier),

    primitive_type: $ => choice(
      'i32', 'i64', 'f32', 'f64', 'bool', 'String', '()',
    ),
  }
});
