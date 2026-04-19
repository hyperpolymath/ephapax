
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | VAR
    | STRING of 
# 9 "src/parser.mly"
       (string)
# 16 "src/parser.ml"
  
    | SESSIONTYPE
    | SESSION
    | SEND
    | RPAREN
    | RECEIVE
    | RBRACE
    | LPAREN
    | LITERAL
    | LBRACE
    | INTEGER of 
# 8 "src/parser.mly"
       (int)
# 30 "src/parser.ml"
  
    | IDENT of 
# 7 "src/parser.mly"
       (string)
# 35 "src/parser.ml"
  
    | EOF
    | DELEGATE
    | COMMA
    | COLON
    | CLOSE
    | ARROW
  
end

include MenhirBasics

# 3 "src/parser.mly"
  
open Ast

# 52 "src/parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState00 : ('s, _menhir_box_program) _menhir_state
    (** State 00.
        Stack shape : <empty>.
        Start symbol: program. *)

  | MenhirState05 : (('s, _menhir_box_program) _menhir_cell1_SESSION _menhir_cell0_IDENT, _menhir_box_program) _menhir_state
    (** State 05.
        Stack shape : SESSION IDENT.
        Start symbol: program. *)

  | MenhirState07 : (('s, _menhir_box_program) _menhir_cell1_IDENT, _menhir_box_program) _menhir_state
    (** State 07.
        Stack shape : IDENT.
        Start symbol: program. *)

  | MenhirState11 : ((('s, _menhir_box_program) _menhir_cell1_SESSION _menhir_cell0_IDENT, _menhir_box_program) _menhir_cell1_role_list, _menhir_box_program) _menhir_state
    (** State 11.
        Stack shape : SESSION IDENT role_list.
        Start symbol: program. *)

  | MenhirState18 : (('s, _menhir_box_program) _menhir_cell1_IDENT _menhir_cell0_IDENT _menhir_cell0_IDENT, _menhir_box_program) _menhir_state
    (** State 18.
        Stack shape : IDENT IDENT IDENT.
        Start symbol: program. *)

  | MenhirState25 : (('s, _menhir_box_program) _menhir_cell1_message, _menhir_box_program) _menhir_state
    (** State 25.
        Stack shape : message.
        Start symbol: program. *)

  | MenhirState28 : (('s, _menhir_box_program) _menhir_cell1_SEND, _menhir_box_program) _menhir_state
    (** State 28.
        Stack shape : SEND.
        Start symbol: program. *)

  | MenhirState31 : (('s, _menhir_box_program) _menhir_cell1_SESSION _menhir_cell0_IDENT, _menhir_box_program) _menhir_state
    (** State 31.
        Stack shape : SESSION IDENT.
        Start symbol: program. *)

  | MenhirState35 : (('s, _menhir_box_program) _menhir_cell1_RECEIVE, _menhir_box_program) _menhir_state
    (** State 35.
        Stack shape : RECEIVE.
        Start symbol: program. *)

  | MenhirState39 : (('s, _menhir_box_program) _menhir_cell1_DELEGATE, _menhir_box_program) _menhir_state
    (** State 39.
        Stack shape : DELEGATE.
        Start symbol: program. *)

  | MenhirState41 : (('s, _menhir_box_program) _menhir_cell1_CLOSE, _menhir_box_program) _menhir_state
    (** State 41.
        Stack shape : CLOSE.
        Start symbol: program. *)

  | MenhirState57 : ((('s, _menhir_box_program) _menhir_cell1_SEND, _menhir_box_program) _menhir_cell1_expr _menhir_cell0_IDENT, _menhir_box_program) _menhir_state
    (** State 57.
        Stack shape : SEND expr IDENT.
        Start symbol: program. *)

  | MenhirState65 : (('s, _menhir_box_program) _menhir_cell1_decl, _menhir_box_program) _menhir_state
    (** State 65.
        Stack shape : decl.
        Start symbol: program. *)


and ('s, 'r) _menhir_cell1_decl = 
  | MenhirCell1_decl of 's * ('s, 'r) _menhir_state * 
# 18 "src/parser.mly"
      (Ast.decl)
# 125 "src/parser.ml"


and ('s, 'r) _menhir_cell1_expr = 
  | MenhirCell1_expr of 's * ('s, 'r) _menhir_state * 
# 23 "src/parser.mly"
      (Ast.expr)
# 132 "src/parser.ml"


and ('s, 'r) _menhir_cell1_message = 
  | MenhirCell1_message of 's * ('s, 'r) _menhir_state * 
# 22 "src/parser.mly"
      (Ast.message)
# 139 "src/parser.ml"


and ('s, 'r) _menhir_cell1_role_list = 
  | MenhirCell1_role_list of 's * ('s, 'r) _menhir_state * 
# 20 "src/parser.mly"
      (string list)
# 146 "src/parser.ml"


and ('s, 'r) _menhir_cell1_CLOSE = 
  | MenhirCell1_CLOSE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_DELEGATE = 
  | MenhirCell1_DELEGATE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_IDENT = 
  | MenhirCell1_IDENT of 's * ('s, 'r) _menhir_state * 
# 7 "src/parser.mly"
       (string)
# 159 "src/parser.ml"


and 's _menhir_cell0_IDENT = 
  | MenhirCell0_IDENT of 's * 
# 7 "src/parser.mly"
       (string)
# 166 "src/parser.ml"


and ('s, 'r) _menhir_cell1_RECEIVE = 
  | MenhirCell1_RECEIVE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_SEND = 
  | MenhirCell1_SEND of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_SESSION = 
  | MenhirCell1_SESSION of 's * ('s, 'r) _menhir_state

and _menhir_box_program = 
  | MenhirBox_program of 
# 16 "src/parser.mly"
      (Ast.program)
# 182 "src/parser.ml"
 [@@unboxed]

let _menhir_action_01 =
  fun _1 ->
    (
# 40 "src/parser.mly"
                 ( SessionDecl _1 )
# 190 "src/parser.ml"
     : 
# 18 "src/parser.mly"
      (Ast.decl)
# 194 "src/parser.ml"
    )

let _menhir_action_02 =
  fun _1 ->
    (
# 41 "src/parser.mly"
         ( ExprDecl _1 )
# 202 "src/parser.ml"
     : 
# 18 "src/parser.mly"
      (Ast.decl)
# 206 "src/parser.ml"
    )

let _menhir_action_03 =
  fun _1 ->
    (
# 35 "src/parser.mly"
         ( [_1] )
# 214 "src/parser.ml"
     : 
# 17 "src/parser.mly"
      (Ast.decl list)
# 218 "src/parser.ml"
    )

let _menhir_action_04 =
  fun _1 _2 ->
    (
# 36 "src/parser.mly"
                   ( _1 :: _2 )
# 226 "src/parser.ml"
     : 
# 17 "src/parser.mly"
      (Ast.decl list)
# 230 "src/parser.ml"
    )

let _menhir_action_05 =
  fun _2 _4 ->
    (
# 75 "src/parser.mly"
    ( Session(_2, _4) )
# 238 "src/parser.ml"
     : 
# 23 "src/parser.mly"
      (Ast.expr)
# 242 "src/parser.ml"
    )

let _menhir_action_06 =
  fun _3 _5 _7 ->
    (
# 77 "src/parser.mly"
    ( Send(_3, _5, _7) )
# 250 "src/parser.ml"
     : 
# 23 "src/parser.mly"
      (Ast.expr)
# 254 "src/parser.ml"
    )

let _menhir_action_07 =
  fun _3 _5 ->
    (
# 79 "src/parser.mly"
    ( Receive(_3, _5) )
# 262 "src/parser.ml"
     : 
# 23 "src/parser.mly"
      (Ast.expr)
# 266 "src/parser.ml"
    )

let _menhir_action_08 =
  fun _3 ->
    (
# 81 "src/parser.mly"
    ( Close(_3) )
# 274 "src/parser.ml"
     : 
# 23 "src/parser.mly"
      (Ast.expr)
# 278 "src/parser.ml"
    )

let _menhir_action_09 =
  fun _3 _5 _7 ->
    (
# 83 "src/parser.mly"
    ( Delegate(_3, _5, _7) )
# 286 "src/parser.ml"
     : 
# 23 "src/parser.mly"
      (Ast.expr)
# 290 "src/parser.ml"
    )

let _menhir_action_10 =
  fun _2 ->
    (
# 84 "src/parser.mly"
              ( Var(_2) )
# 298 "src/parser.ml"
     : 
# 23 "src/parser.mly"
      (Ast.expr)
# 302 "src/parser.ml"
    )

let _menhir_action_11 =
  fun _2 ->
    (
# 85 "src/parser.mly"
                    ( Literal(Int(_2)) )
# 310 "src/parser.ml"
     : 
# 23 "src/parser.mly"
      (Ast.expr)
# 314 "src/parser.ml"
    )

let _menhir_action_12 =
  fun _1 _3 _5 ->
    (
# 65 "src/parser.mly"
                                      ( {
      msg_sender = _1;
      msg_receiver = _3;
      msg_type = _5
    } )
# 326 "src/parser.ml"
     : 
# 22 "src/parser.mly"
      (Ast.message)
# 330 "src/parser.ml"
    )

let _menhir_action_13 =
  fun _1 ->
    (
# 60 "src/parser.mly"
            ( [_1] )
# 338 "src/parser.ml"
     : 
# 21 "src/parser.mly"
      (Ast.message list)
# 342 "src/parser.ml"
    )

let _menhir_action_14 =
  fun _1 _2 ->
    (
# 61 "src/parser.mly"
                         ( _1 :: _2 )
# 350 "src/parser.ml"
     : 
# 21 "src/parser.mly"
      (Ast.message list)
# 354 "src/parser.ml"
    )

let _menhir_action_15 =
  fun _1 ->
    (
# 31 "src/parser.mly"
                  ( _1 )
# 362 "src/parser.ml"
     : 
# 16 "src/parser.mly"
      (Ast.program)
# 366 "src/parser.ml"
    )

let _menhir_action_16 =
  fun _1 ->
    (
# 55 "src/parser.mly"
          ( [_1] )
# 374 "src/parser.ml"
     : 
# 20 "src/parser.mly"
      (string list)
# 378 "src/parser.ml"
    )

let _menhir_action_17 =
  fun _1 _3 ->
    (
# 56 "src/parser.mly"
                          ( _1 :: _3 )
# 386 "src/parser.ml"
     : 
# 20 "src/parser.mly"
      (string list)
# 390 "src/parser.ml"
    )

let _menhir_action_18 =
  fun _2 _4 _6 ->
    (
# 47 "src/parser.mly"
    ( {
        s_name = _2;
        s_roles = _4;
        s_protocol = _6
      } )
# 402 "src/parser.ml"
     : 
# 19 "src/parser.mly"
      (Ast.session_decl)
# 406 "src/parser.ml"
    )

let _menhir_action_19 =
  fun _1 ->
    (
# 89 "src/parser.mly"
          ( TypeVar _1 )
# 414 "src/parser.ml"
     : 
# 24 "src/parser.mly"
      (Ast.typ)
# 418 "src/parser.ml"
    )

let _menhir_action_20 =
  fun _2 _4 ->
    (
# 90 "src/parser.mly"
                                              ( SessionType(ref {
      s_name = _2;
      s_roles = _4;
      s_protocol = []  (* Will be filled during type checking *)
    }) )
# 430 "src/parser.ml"
     : 
# 24 "src/parser.mly"
      (Ast.typ)
# 434 "src/parser.ml"
    )

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | VAR ->
        "VAR"
    | STRING _ ->
        "STRING"
    | SESSIONTYPE ->
        "SESSIONTYPE"
    | SESSION ->
        "SESSION"
    | SEND ->
        "SEND"
    | RPAREN ->
        "RPAREN"
    | RECEIVE ->
        "RECEIVE"
    | RBRACE ->
        "RBRACE"
    | LPAREN ->
        "LPAREN"
    | LITERAL ->
        "LITERAL"
    | LBRACE ->
        "LBRACE"
    | INTEGER _ ->
        "INTEGER"
    | IDENT _ ->
        "IDENT"
    | EOF ->
        "EOF"
    | DELEGATE ->
        "DELEGATE"
    | COMMA ->
        "COMMA"
    | COLON ->
        "COLON"
    | CLOSE ->
        "CLOSE"
    | ARROW ->
        "ARROW"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37"]
  
  let _menhir_run_63 : type  ttv_stack. ttv_stack -> _ -> _menhir_box_program =
    fun _menhir_stack _v ->
      let _1 = _v in
      let _v = _menhir_action_15 _1 in
      MenhirBox_program _v
  
  let rec _menhir_goto_decl_list : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState00 ->
          _menhir_run_63 _menhir_stack _v
      | MenhirState65 ->
          _menhir_run_66 _menhir_stack _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_66 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_decl -> _ -> _menhir_box_program =
    fun _menhir_stack _v ->
      let MenhirCell1_decl (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_04 _1 _2 in
      _menhir_goto_decl_list _menhir_stack _v _menhir_s
  
  let rec _menhir_run_01 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _2 = _v in
          let _v = _menhir_action_10 _2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_expr : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState41 ->
          _menhir_run_42 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState39 ->
          _menhir_run_44 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState35 ->
          _menhir_run_50 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState28 ->
          _menhir_run_54 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState57 ->
          _menhir_run_58 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState00 ->
          _menhir_run_62 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState65 ->
          _menhir_run_62 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_42 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_CLOSE -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_CLOSE (_menhir_stack, _menhir_s) = _menhir_stack in
          let _3 = _v in
          let _v = _menhir_action_08 _3 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_44 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_DELEGATE -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v_0 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | COMMA ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | IDENT _v_1 ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      (match (_tok : MenhirBasics.token) with
                      | RPAREN ->
                          let _tok = _menhir_lexer _menhir_lexbuf in
                          let MenhirCell1_DELEGATE (_menhir_stack, _menhir_s) = _menhir_stack in
                          let (_3, _7, _5) = (_v, _v_1, _v_0) in
                          let _v = _menhir_action_09 _3 _5 _7 in
                          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
                      | _ ->
                          _eRR ())
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_50 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_RECEIVE -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v_0 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | RPAREN ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let MenhirCell1_RECEIVE (_menhir_stack, _menhir_s) = _menhir_stack in
                  let (_3, _5) = (_v, _v_0) in
                  let _v = _menhir_action_07 _3 _5 in
                  _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_54 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_SEND as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expr (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | COMMA ->
                  let _menhir_s = MenhirState57 in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | VAR ->
                      _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | SESSION ->
                      _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | SEND ->
                      _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | RECEIVE ->
                      _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | LITERAL ->
                      _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | DELEGATE ->
                      _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | CLOSE ->
                      _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_29 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_SESSION (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              let _menhir_s = MenhirState31 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | IDENT _v ->
                  _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_06 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_IDENT (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState07 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | RPAREN ->
          let _1 = _v in
          let _v = _menhir_action_16 _1 in
          _menhir_goto_role_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_role_list : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState07 ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState05 ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState18 ->
          _menhir_run_19 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState31 ->
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_08 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_IDENT -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_IDENT (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _3 = _v in
      let _v = _menhir_action_17 _1 _3 in
      _menhir_goto_role_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_09 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_SESSION _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACE ->
          let _menhir_stack = MenhirCell1_role_list (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState11 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v ->
              _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | CLOSE | DELEGATE | EOF | LITERAL | RECEIVE | SEND | SESSION | VAR ->
          let MenhirCell0_IDENT (_menhir_stack, _2) = _menhir_stack in
          let MenhirCell1_SESSION (_menhir_stack, _menhir_s) = _menhir_stack in
          let _4 = _v in
          let _v = _menhir_action_05 _2 _4 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_12 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_IDENT (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ARROW ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v_0 ->
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v_0) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | COLON ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  (match (_tok : MenhirBasics.token) with
                  | SESSIONTYPE ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      (match (_tok : MenhirBasics.token) with
                      | IDENT _v ->
                          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
                          let _tok = _menhir_lexer _menhir_lexbuf in
                          (match (_tok : MenhirBasics.token) with
                          | LPAREN ->
                              let _menhir_s = MenhirState18 in
                              let _tok = _menhir_lexer _menhir_lexbuf in
                              (match (_tok : MenhirBasics.token) with
                              | IDENT _v ->
                                  _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
                              | _ ->
                                  _eRR ())
                          | _ ->
                              _eRR ())
                      | _ ->
                          _eRR ())
                  | IDENT _v_3 ->
                      let _tok = _menhir_lexer _menhir_lexbuf in
                      let _1 = _v_3 in
                      let _v = _menhir_action_19 _1 in
                      _menhir_goto_type_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
                  | _ ->
                      _eRR ())
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_type_expr : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_IDENT _menhir_cell0_IDENT -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell0_IDENT (_menhir_stack, _3) = _menhir_stack in
      let MenhirCell1_IDENT (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _5 = _v in
      let _v = _menhir_action_12 _1 _3 _5 in
      match (_tok : MenhirBasics.token) with
      | IDENT _v_0 ->
          let _menhir_stack = MenhirCell1_message (_menhir_stack, _menhir_s, _v) in
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState25
      | RBRACE ->
          let _1 = _v in
          let _v = _menhir_action_13 _1 in
          _menhir_goto_message_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_message_list : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState11 ->
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
      | MenhirState25 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_23 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_SESSION _menhir_cell0_IDENT, _menhir_box_program) _menhir_cell1_role_list -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_role_list (_menhir_stack, _, _4) = _menhir_stack in
      let MenhirCell0_IDENT (_menhir_stack, _2) = _menhir_stack in
      let MenhirCell1_SESSION (_menhir_stack, _menhir_s) = _menhir_stack in
      let _6 = () in
      let _v = _menhir_action_18 _2 _4 _6 in
      let _1 = _v in
      let _v = _menhir_action_01 _1 in
      _menhir_goto_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_decl : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | VAR ->
          let _menhir_stack = MenhirCell1_decl (_menhir_stack, _menhir_s, _v) in
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState65
      | SESSION ->
          let _menhir_stack = MenhirCell1_decl (_menhir_stack, _menhir_s, _v) in
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState65
      | SEND ->
          let _menhir_stack = MenhirCell1_decl (_menhir_stack, _menhir_s, _v) in
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState65
      | RECEIVE ->
          let _menhir_stack = MenhirCell1_decl (_menhir_stack, _menhir_s, _v) in
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState65
      | LITERAL ->
          let _menhir_stack = MenhirCell1_decl (_menhir_stack, _menhir_s, _v) in
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState65
      | DELEGATE ->
          let _menhir_stack = MenhirCell1_decl (_menhir_stack, _menhir_s, _v) in
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState65
      | CLOSE ->
          let _menhir_stack = MenhirCell1_decl (_menhir_stack, _menhir_s, _v) in
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState65
      | EOF ->
          let _1 = _v in
          let _v = _menhir_action_03 _1 in
          _menhir_goto_decl_list _menhir_stack _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_03 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_SESSION (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              let _menhir_s = MenhirState05 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | IDENT _v ->
                  _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_27 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_SEND (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState28 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VAR ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SESSION ->
              _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SEND ->
              _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RECEIVE ->
              _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LITERAL ->
              _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DELEGATE ->
              _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CLOSE ->
              _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_34 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_RECEIVE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState35 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VAR ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SESSION ->
              _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SEND ->
              _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RECEIVE ->
              _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LITERAL ->
              _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DELEGATE ->
              _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CLOSE ->
              _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_36 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | INTEGER _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _2 = _v in
          let _v = _menhir_action_11 _2 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_38 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_DELEGATE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState39 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VAR ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SESSION ->
              _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SEND ->
              _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RECEIVE ->
              _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LITERAL ->
              _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DELEGATE ->
              _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CLOSE ->
              _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_40 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_CLOSE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_s = MenhirState41 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VAR ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SESSION ->
              _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | SEND ->
              _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | RECEIVE ->
              _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LITERAL ->
              _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | DELEGATE ->
              _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | CLOSE ->
              _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_26 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_message -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_message (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _2 = _v in
      let _v = _menhir_action_14 _1 _2 in
      _menhir_goto_message_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_19 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_IDENT _menhir_cell0_IDENT _menhir_cell0_IDENT -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell0_IDENT (_menhir_stack, _2) = _menhir_stack in
      let _4 = _v in
      let _v = _menhir_action_20 _2 _4 in
      _menhir_goto_type_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
  
  and _menhir_run_32 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_SESSION _menhir_cell0_IDENT -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell0_IDENT (_menhir_stack, _2) = _menhir_stack in
      let MenhirCell1_SESSION (_menhir_stack, _menhir_s) = _menhir_stack in
      let _4 = _v in
      let _v = _menhir_action_05 _2 _4 in
      _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_58 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_SEND, _menhir_box_program) _menhir_cell1_expr _menhir_cell0_IDENT -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell0_IDENT (_menhir_stack, _5) = _menhir_stack in
          let MenhirCell1_expr (_menhir_stack, _, _3) = _menhir_stack in
          let MenhirCell1_SEND (_menhir_stack, _menhir_s) = _menhir_stack in
          let _7 = _v in
          let _v = _menhir_action_06 _3 _5 _7 in
          _menhir_goto_expr _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_62 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _1 = _v in
      let _v = _menhir_action_02 _1 in
      _menhir_goto_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  let _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState00 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SESSION ->
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | SEND ->
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | RECEIVE ->
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LITERAL ->
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | DELEGATE ->
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | CLOSE ->
          _menhir_run_40 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | _ ->
          _eRR ()
  
end

let program =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_program v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
