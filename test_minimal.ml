type typ =
  | TypeVar of string
  | SessionType of string * string list

type literal =
  | Int of int
  | String of string
  | Bool of bool

type message = {
  msg_sender: string;
  msg_receiver: string;
  msg_type: typ;
}

type session_decl = {
  s_name: string;
  s_roles: string list;
  s_protocol: message list;
}
