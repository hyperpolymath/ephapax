(** Type checker tests for choreographic sessions *)

open OUnit2
open Typecheck
open Ast

let test_valid_session ctx =
  let env = initial_env () in
  let sdecl = {
    s_name = "Transfer";
    s_roles = ["Alice"; "Bob"];
    s_protocol = [
      { msg_sender = "Alice"; msg_receiver = "Bob"; msg_type = TypeVar "Token" };
      { msg_sender = "Bob"; msg_receiver = "Alice"; msg_type = TypeVar "Receipt" }
    ]
  } in
  assert_command (check_session_decl env sdecl);
  assert_equal ~printer:(fun x -> x) "Transfer" sdecl.s_name

let test_duplicate_roles ctx =
  let env = initial_env () in
  let sdecl = {
    s_name = "Bad";
    s_roles = ["Alice"; "Alice"];
    s_protocol = []
  } in
  assert_raises (TypeError "Duplicate roles") (fun () -> check_session_decl env sdecl)

let test_nonlinear_message ctx =
  let env = initial_env () in
  let sdecl = {
    s_name = "Bad";
    s_roles = ["A"; "B"];
    s_protocol = [
      { msg_sender = "A"; msg_receiver = "B"; msg_type = TypeVar "Int" }
    ]
  } in
  assert_raises (TypeError "must have linear types") (fun () -> check_session_decl env sdecl)

let test_send_receive ctx =
  let env = initial_env () in
  let sdecl = {
    s_name = "Transfer";
    s_roles = ["Alice"; "Bob"];
    s_protocol = [
      { msg_sender = "Alice"; msg_receiver = "Bob"; msg_type = TypeVar "Token" }
    ]
  } in
  check_session_decl env sdecl;
  
  (* Test send *)
  let send_expr = Send(Var "s", "Bob", Var "token") in
  let result_ty = check_send env send_expr in
  match result_ty with
  | SessionType("Transfer", ["Alice"; "Bob"]) -> ()
  | _ -> assert_failure "Send should return updated session"

let test_close_incomplete ctx =
  let env = initial_env () in
  let sdecl = {
    s_name = "Transfer";
    s_roles = ["Alice"; "Bob"];
    s_protocol = [
      { msg_sender = "Alice"; msg_receiver = "Bob"; msg_type = TypeVar "Token" }
    ]
  } in
  check_session_decl env sdecl;
  
  (* Try to close incomplete session *)
  let close_expr = Close(Var "s") in
  assert_raises (TypeError "not complete") (fun () -> check_close env close_expr)

let suite =
  "Choreographic Sessions" >::: [
    "valid_session" >:: test_valid_session;
    "duplicate_roles" >:: test_duplicate_roles;
    "nonlinear_message" >:: test_nonlinear_message;
    "send_receive" >:: test_send_receive;
    "close_incomplete" >:: test_close_incomplete;
  ]

let () =
  run_test_tt_main suite
