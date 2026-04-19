(* Ephapax Parser - Extended with Choreographic Sessions *)

%{
open Ast
%}

%token <string> IDENT
%token <int> INTEGER
%token <string> STRING
%token EOF

%token SESSION SEND RECEIVE CLOSE DELEGATE
%token ARROW COLON COMMA LPAREN RPAREN LBRACE RBRACE
%token VAR LITERAL SESSIONTYPE

%type <Ast.program> program
%type <Ast.decl list> decl_list
%type <Ast.decl> decl
%type <Ast.session_decl> session_decl
%type <string list> role_list
%type <Ast.message list> message_list
%type <Ast.message> message
%type <Ast.expr> expr
%type <Ast.typ> type_expr

%start program

%%

program:
  | decl_list EOF { $1 }
;

decl_list:
  | decl { [$1] }
  | decl decl_list { $1 :: $2 }
;

decl:
  | session_decl { SessionDecl $1 }
  | expr { ExprDecl $1 }
;

(* Session type declaration *)
session_decl:
  | SESSION IDENT LPAREN role_list RPAREN LBRACE message_list RBRACE
    { {
        s_name = $2;
        s_roles = $4;
        s_protocol = $6
      } }
;

role_list:
  | IDENT { [$1] }
  | IDENT COMMA role_list { $1 :: $3 }
;

message_list:
  | message { [$1] }
  | message message_list { $1 :: $2 }
;

message:
  | IDENT ARROW IDENT COLON type_expr { {
      msg_sender = $1;
      msg_receiver = $3;
      msg_type = $5
    } }
;

(* Session expressions *)
expr:
  | SESSION IDENT LPAREN role_list RPAREN
    { Session($2, $4) }
  | SEND LPAREN expr COMMA IDENT COMMA expr RPAREN
    { Send($3, $5, $7) }
  | RECEIVE LPAREN expr COMMA IDENT RPAREN
    { Receive($3, $5) }
  | CLOSE LPAREN expr RPAREN
    { Close($3) }
  | DELEGATE LPAREN expr COMMA IDENT COMMA IDENT RPAREN
    { Delegate($3, $5, $7) }
  | VAR IDENT { Var($2) }
  | LITERAL INTEGER { Literal(Int($2)) }
;

type_expr:
  | IDENT { TypeVar $1 }
  | SESSIONTYPE IDENT LPAREN role_list RPAREN { SessionType(ref {
      s_name = $2;
      s_roles = $4;
      s_protocol = []  (* Will be filled during type checking *)
    }) }
;
