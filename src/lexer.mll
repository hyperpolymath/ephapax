{(* Ephapax Lexer - Extended with Choreographic Sessions *)

open Parser

}

rule token = parse
  | [' ' '\t' '\r' '\n'] { token lexbuf }
  | ['0'-'9']+ { INTEGER (int_of_string (Lexing.lexeme lexbuf)) }
  | ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']* {
      match Lexing.lexeme lexbuf with
      | "session" -> SESSION
      | "send" -> SEND
      | "receive" -> RECEIVE
      | "close" -> CLOSE
      | "delegate" -> DELEGATE
      | id -> IDENT id
    }
  | '"' [^ '"']* '"' { STRING (String.sub (Lexing.lexeme lexbuf) 1 (String.length (Lexing.lexeme lexbuf) - 2)) }
  | "->" { ARROW }
  | ":" { COLON }
  | "," { COMMA }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "var" { VAR }
  | "literal" { LITERAL }
  | "sessiontype" { SESSIONTYPE }
  | eof { EOF }
