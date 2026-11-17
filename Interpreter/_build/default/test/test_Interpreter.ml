open Interpreter.Typedefs

let test_str_of_expr () =
  let examples = [
    ("Const",    Const "5");
    ("Var",      Var "x");
    ("Fun",      Fun ("x", Var "x"));
    ("App",      App (Var "f", Var "x"));
    ("Pair",     Pair (Var "a", Var "b"));
    ("Unit",     Unit);
    ("LetPair",  LetPair ("p", "q", Pair (Var "a", Var "b"), Var "p"));
    ("Injl",     Injl (Const "0"));
    ("Injr",     Injr (Const "1"));
    ("Match",    Match (Var "x", ("a", Var "a"), ("b", Var "b")));
    ("Rec",      Rec ("f", "x", App (Var "f", Var "x"), App (Var "f", Unit)));
  ] in

  List.iter (fun (label, expr) ->
    Printf.printf "%-8s -> %s\n" label (str_of_expr expr)
  ) examples

let run_substitute_test name x y m =
  Printf.printf "=== %s ===\n" name;
  Printf.printf "Target: Replace '%s' with '%s'\n" x (str_of_expr y);
  Printf.printf "Before: %s\n" (str_of_expr m);
  let result = substitute x y m in
  Printf.printf "After:  %s\n\n" (str_of_expr result)

(* The test cases *)
let run_all_substitute_tests () =
  let y_val = Var "y" in

  run_substitute_test "Const & Unit (No substitution)" 
    "x" y_val (Pair (Const "5", Unit));
    
  run_substitute_test "Var (Direct substitution)" 
    "x" y_val (Var "x");

  run_substitute_test "App & Inj (Recursive substitution)" 
    "x" y_val (App (Injl (Var "x"), Injr (Var "x")));


  
  run_substitute_test "Fun (Standard substitution)" 
    "x" y_val (Fun ("a", Pair(Var "x", Var "a")));

  run_substitute_test "Fun (Shadowing - x is bound)" 
    "x" y_val (Fun ("x", Pair(Var "x", Var "a")));

  run_substitute_test "Fun (Capture Avoidance - rename a to a1)" 
    "x" (Var "a") (Fun ("a", App (Var "x", Var "a")));



  run_substitute_test "LetPair (Standard substitution)" 
    "x" y_val (LetPair ("a", "b", Var "x", Pair(Var "x", Var "a")));

  run_substitute_test "LetPair (Shadowing v1 - e1 substitutes, e2 does not)" 
    "x" y_val (LetPair ("x", "b", Var "x", Pair(Var "x", Var "b")));

  run_substitute_test "LetPair (Capture Avoidance - rename b to b1 in e2)" 
    "x" (Var "b") (LetPair ("a", "b", Var "x", Pair(Var "x", Var "b")));



  run_substitute_test "Match (Standard substitution)" 
    "x" y_val (Match (Var "x", ("a", Var "x"), ("b", Var "x")));

  run_substitute_test "Match (Shadowing v1 - substitute in e, skip e1, substitute in e2)" 
    "x" y_val (Match (Var "x", ("x", Var "x"), ("b", Var "x")));

  run_substitute_test "Match (Capture Avoidance v2 - rename b to b1 in e2)" 
    "x" (Var "b") (Match (Var "x", ("a", Var "x"), ("b", Pair(Var "x", Var "b"))));


    
  run_substitute_test "Rec (Standard substitution)" 
    "x" y_val (Rec ("f", "v", App(Var "x", Var "v"), App(Var "f", Var "x")));

  run_substitute_test "Rec (Shadowing f - skip both e1 and e2)" 
    "x" y_val (Rec ("x", "v", App(Var "x", Var "v"), App(Var "x", Var "a")));

  run_substitute_test "Rec (Shadowing v - skip e1, substitute in e2)" 
    "x" y_val (Rec ("f", "x", App(Var "x", Var "f"), App(Var "f", Var "x")));

  run_substitute_test "Rec (Capture Avoidance f & v - rename f and v)" 
    "x" (Var "f") (Rec ("f", "v", App(Var "x", Var "f"), App(Var "x", Var "f")))

let () = run_all_substitute_tests ()

(* substitute "x" with (Const "5") in m *)
(* let res = substitute "x" (Const "5") m in

print_endline res *)
