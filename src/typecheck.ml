(** Ephapax Type Checker - Choreographic Session Extension *)

open Ast

exception TypeError of string

(** Environment type *)
type env = {
  sessions: (string, session_decl) Hashtbl.t;
  types: (string, typ) Hashtbl.t;
  (* other environment fields *)
}

(** Initialize environment *)
let initial_env () = {
  sessions = Hashtbl.create 16;
  types = Hashtbl.create 16;
}

(** Add session to environment *)
let add_session env name sdecl =
  Hashtbl.add env.sessions name sdecl

(** Get session from environment *)
let get_session env name =
  try Hashtbl.find env.sessions name
  with Not_found -> raise (TypeError ("Unknown session: " ^ name))

(** Check if type is linear *)
let rec is_linear_type env = function
  | TypeVar name -> (* lookup type definition *) true
  | SessionType _ -> true
  | _ -> false

(** Check session declaration *)
let check_session_decl env sdecl =
  (* Check role uniqueness *)
  let roles = sdecl.s_roles in
  let unique_roles = List.sort_uniq String.compare roles in
  if List.length roles <> List.length unique_roles then
    raise (TypeError ("Duplicate roles in session " ^ sdecl.s_name));

  (* Check all message types are linear *)
  List.iter (fun msg ->
    if not (is_linear_type env msg.msg_type) then
      raise (TypeError "Session messages must have linear types")
  ) sdecl.s_protocol;

  (* Add to environment *)
  add_session env sdecl.s_name sdecl

(** Check send expression *)
let check_send env (Send(sess, receiver, value)) =
  (* In a real implementation, we would:
     1. Get the type of 'sess' expression
     2. Verify it's a SessionType
     3. Extract the session_decl ref
     4. Perform the send operation
     
     For now, we'll simulate this with a mock session *)
  let mock_sdecl = ref {
    s_name = "Transfer";
    s_roles = ["Alice"; "Bob"];
    s_protocol = [
      { msg_sender = "Alice"; msg_receiver = "Bob"; msg_type = TypeVar "Token" };
      { msg_sender = "Bob"; msg_receiver = "Alice"; msg_type = TypeVar "Receipt" }
    ]
  } in
  let sdecl = !mock_sdecl in
  (* Find expected message *)
  let expected = List.find (fun m -> m.msg_receiver = receiver) sdecl.s_protocol in
  (* Check value type *)
  let value_ty = (* check_expr env value *) TypeVar "Token" in
  if not ((* subtype value_ty expected.msg_type *) true) then
    raise (TypeError "Value type doesn't match protocol");
  (* Return updated session type with remaining messages *)
  SessionType(ref {
    s_name = sdecl.s_name;
    s_roles = sdecl.s_roles;
    s_protocol = List.filter (fun m -> m.msg_sender <> expected.msg_sender || m.msg_receiver <> expected.msg_receiver) sdecl.s_protocol
  })

(** Check receive expression *)
let check_receive env (Receive(sess, sender)) =
  (* Mock session for demonstration *)
  let mock_sdecl = ref {
    s_name = "Transfer";
    s_roles = ["Alice"; "Bob"];
    s_protocol = [
      { msg_sender = "Alice"; msg_receiver = "Bob"; msg_type = TypeVar "Token" };
      { msg_sender = "Bob"; msg_receiver = "Alice"; msg_type = TypeVar "Receipt" }
    ]
  } in
  let sdecl = !mock_sdecl in
  let expected = List.find (fun m -> m.msg_sender = sender) sdecl.s_protocol in
  expected.msg_type

(** Check close expression *)
let check_close env (Close(sess)) =
  (* Mock session for demonstration *)
  let mock_sdecl = ref {
    s_name = "Transfer";
    s_roles = ["Alice"; "Bob"];
    s_protocol = []  (* Empty protocol = complete *)
  } in
  let sdecl = !mock_sdecl in
  if not (List.is_empty sdecl.s_protocol) then
    raise (TypeError "Session not complete");
  (* Return unit type *)
  TypeVar "()"

(** Check delegate expression *)
let check_delegate env (Delegate(sess, old_role, new_role)) =
  (* Mock session for demonstration *)
  let mock_sdecl = ref {
    s_name = "Transfer";
    s_roles = ["Alice"; "Bob"];
    s_protocol = []
  } in
  let sdecl = !mock_sdecl in
  if not (List.mem old_role sdecl.s_roles) then
    raise (TypeError ("Role " ^ old_role ^ " not in session"));
  (* Return updated session with replaced role *)
  SessionType(ref {
    s_name = sdecl.s_name;
    s_roles = List.map (fun r -> if r = old_role then new_role else r) sdecl.s_roles;
    s_protocol = sdecl.s_protocol
  })
