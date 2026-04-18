
(* The type of tokens. *)

module rec Ast : sig
  type program
  type decl
  type session_decl
  type message
  type expr
  type typ
  type literal
end

and Parser : sig
  type token = 
  | VAR
  | STRING of (string)
  | SESSIONTYPE
  | SESSION
  | SEND
  | RPAREN
  | RECEIVE
  | RBRACE
  | LPAREN
  | LITERAL
  | LBRACE
  | INTEGER of (int)
  | IDENT of (string)
  | EOF
  | DELEGATE
  | COMMA
  | COLON
  | CLOSE
  | ARROW

  (* This exception is raised by the monolithic API functions. *)
  exception Error

  (* The monolithic API. *)
  val program: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.program)
end
