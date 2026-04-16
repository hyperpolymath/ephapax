(** Ephapax AST - Extended with Choreographic Sessions *)

(** Literal values *)
type literal =
  | Int of int
  | String of string
  | Bool of bool

(** Type expressions *)
type typ =
  | TypeVar of string
  | SessionType of session_decl ref  (* Use reference to break circularity *)

(** Session type declaration *)
and session_decl = {
  s_name: string;
  s_roles: string list;
  s_protocol: message list;
}

(** Message in a session protocol *)
and message = {
  msg_sender: string;
  msg_receiver: string;
  msg_type: typ;
}

(** Expression types *)
type expr =
  | Session of string * string list
  | Send of expr * string * expr
  | Receive of expr * string
  | Close of expr
  | Delegate of expr * string * string
  | Var of string
  | Literal of literal

(** Program declarations *)
type decl =
  | SessionDecl of session_decl
  | ExprDecl of expr

(** Complete program *)
type program = decl list
