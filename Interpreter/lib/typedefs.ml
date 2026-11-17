open Mathdef
let _ = Random.init(0) (* <- change as req. for testing / use self_init *)

type var = string

type expr = 
| Const of string 
| Var of var 
| Fun of var * expr
| App of expr * expr
| Pair of expr * expr
| Unit
| LetPair of var * var * expr * expr
| Injl of expr
| Injr of expr
| Match of expr * (var * expr) * (var * expr)
| Rec of var * var * expr * expr

type typ =
| Qbit
| Exp of typ
| Lpop of typ * typ
| Top
| Tensor of typ * typ
| Oplus of typ * typ

let bit = Oplus(Top, Top)

type quantum_array = Complex.t array
type state = quantum_array * var list * expr

let init_array : quantum_array = [| {re = 1.0; im = 0.0 } |]
let init_state m : state = (init_array, [], m)

let rec is_value e =
  match e with
  | Const _ | Var _ | Fun _ | Unit -> true
  | Pair (e1, e2) -> is_value e1 && is_value e2
  | Injl e' | Injr e' -> is_value e'
  | _ -> false

let counter = ref 0
let new_var v =
  incr counter;
  v ^ string_of_int !counter

let rec free e : var list =
  match e with
  | Const _ | Unit -> []
  | Var v -> [v]
  | App (e1, e2) | Pair (e1, e2) -> (free e1) @ (free e2)
  | Injl e | Injr e -> free e
  
  | Fun (v, body) -> 
      List.filter (fun x -> x <> v) (free body)
      
  | LetPair (v1, v2, e1, e2) ->
      (free e1) @ 
      (List.filter (fun x -> x <> v1 && x <> v2) (free e2))
      
  | Match (e, (v1, e1), (v2, e2)) ->
      (free e) @ 
      (List.filter (fun x -> x <> v1) (free e1)) @ 
      (List.filter (fun x -> x <> v2) (free e2))
      
  | Rec (f, v, e1, e2) ->
      (List.filter (fun x -> x <> f && x <> v) (free e1)) @
      (List.filter (fun x -> x <> f) (free e2))

let rec str_of_expr e : string =
  match e with
  | Const c -> c
  | Var v -> v
  | Fun(v, e) -> "\\" ^ v ^ "." ^ str_of_expr e
  | App(e1, e2) -> str_of_expr e1 ^ " " ^ str_of_expr e2
  | Pair(e1, e2) -> "<" ^ str_of_expr e1 ^ ", " ^ str_of_expr e2 ^ ">"
  | Unit -> "*"
  | LetPair (v1, v2, e1, e2) -> "let <" ^ v1 ^ ", " ^ v2 ^ "> = " ^ str_of_expr e1 ^ " in " ^ str_of_expr e2
  | Injl e' -> "Injl" ^ str_of_expr e'
  | Injr e' -> "Injr" ^ str_of_expr e'
  | Match (e', (v1, e1), (v2, e2)) ->
    "match " ^ str_of_expr e' ^ " with (" ^ v1 ^ " -> " ^ str_of_expr e1 ^ " | " ^ v2 ^ " -> " ^ str_of_expr e2 ^ ")"
  | Rec (f, v, e1, e2) -> "let rec " ^ f ^ " " ^ v ^ " = " ^ str_of_expr e1 ^ " in " ^ str_of_expr e2

(* sub x with y in m *)
let rec substitute (x : var) (y : expr) (m : expr) =
  match m with
  (* x never appears *)
  | Const _ | Unit -> m

  | Var v ->
    if v = x then y else m
    
  | App (e1, e2) ->
    App (substitute x y e1, substitute x y e2)
      
  | Pair (e1, e2) ->
    Pair (substitute x y e1, substitute x y e2)
        
  | Injl e ->
    Injl (substitute x y e)
          
  | Injr e ->
    Injr (substitute x y e)
            
  | Fun (v, body) ->
    (* if x is reused then bind only on the outer function not inside the function 
      -> this approach to shadowing keeps it O(1) instead of O(N) *)
    if v = x then m
    (* else check if v is free and rename if necessary *)
    else (
      let free_vars = free y in
        if (List.mem v free_vars) then (
          let new_x = new_var v in 
          let new_body = substitute v (Var new_x) body in 
            Fun (new_x, substitute x y new_body)
        ) else Fun (v, substitute x y body)
    )

  | LetPair (v1, v2, e1, e2) ->
    (* e1 is in the outer scope so it can be safely updated *)
    let e1' = (substitute x y e1) in
    (* shadowing condition *)
      if x = v1 || x = v2 then 
        LetPair (v1, v2, e1', e2)

    (* check if v1 or v2 are free and rename accordingly *)
      else (
        let free_vars = free y in
        let v1freecheck = List.mem v1 free_vars in
        let v2freecheck = List.mem v2 free_vars in

        if v1freecheck || v2freecheck then (
          let new_v1 = if v1freecheck then new_var v1 else v1 in
          let new_v2 = if v2freecheck then new_var v2 else v2 in
          let new_e2 = substitute v1 (Var new_v1) (substitute v2 (Var new_v2) e2) in
            LetPair (new_v1, new_v2, e1', substitute x y new_e2)
        )

    (* if not free then substitution is safe*)
        else LetPair (v1, v2, e1', substitute x y e2)
      )

  | Match (e, (v1, e1), (v2, e2)) ->
    (* e is in the outer scope so it can be safely updated *)

    let e' = (substitute x y e) in
    let free_vars = free y in
    let v1freecheck = List.mem v1 free_vars in
    let v2freecheck = List.mem v2 free_vars in

    (* rename v1 in e1 if v1 is free in y *)
      let (v1', e1') = (
        if x = v1 then (v1, e1)
        else if v1freecheck then
          let new_v1 = (new_var v1) in
          let new_e1 = substitute v1 (Var new_v1) e1 in
          (new_v1, (substitute x y new_e1))
        else
          (v1, (substitute x y e1))) 
        in
        
    (* rename v2 in e2 if v2 is free in y *)
    let (v2', e2') = (
      if x = v2 then (v2, e2)
      else if v2freecheck then
        let new_v2 = (new_var v2) in
        let new_e2 = substitute v2 (Var new_v2) e2 in
          (new_v2, (substitute x y new_e2))
      else
        (v2, (substitute x y e2))) 
    in

    Match (e', (v1', e1'), (v2', e2'))

  | Rec (f, v, e1, e2) ->
    if x = f then Rec(f, v, e1, e2)
    
    else
      let free_vars = free y in
      let f_freecheck = List.mem f free_vars in
      let v_freecheck = List.mem v free_vars in

      let (f', e1', e2') =
        if f_freecheck then
          let new_f = new_var f in
            (new_f, (substitute f (Var new_f) e1), (substitute f (Var new_f) e2))
        else
          (f, e1, e2)
      in

      let (v', e1'') =
        if x = v then (v, e1')
        else if v_freecheck then
          let new_v = new_var v in
          let new_e1' = (substitute v (Var new_v) e1') in
            (new_v, substitute x y new_e1')
        else
          (v, substitute x y e1')
        in

      Rec (f', v', e1'', (substitute x y e2'))

let rec reduce (s : state) : state =
  match s with
  (* classical reduction rules *)
  | (q, l, App (Fun (x, m), v)) when is_value v ->
    let m' = substitute x v m in
      (q, l, m')

  | (q, l, LetPair (x, y, Pair(v, w), n)) when is_value (Pair(v,w)) ->
    let n' = substitute x v n in
    let n'' = substitute y w n' in
      (q, l, n'')

  | (q, l, Match (Injl v, (x, m), (y, n))) when is_value v ->
    let m' = substitute x v m in
      (q, l, m')
    
  | (q, l, Match (Injr w, (x, m), (y, n))) when is_value w ->
    let n' = substitute y w n in
      (q, l, n')

  | (q, l, Rec (f, x, m, n)) ->
    let new_f = Fun(x, Rec(f, x, m, m)) in
    let n' = substitute f new_f n in
      (q, l, n')

  (* quantum reduction rules *)
  | (q, l, App(Const "new", Injr Unit)) ->
    let new_a = new_var "a" in
    let new_q = Mathdef.vec_kron_prod q (Mathdef.q0) in
    let new_l = new_a :: l in
      (new_q, new_l, Var new_a)
  
  | (q, l, App(Const "new", Injl Unit)) ->
    let new_a = new_var "a" in
    let new_q = Mathdef.vec_kron_prod q (Mathdef.q1) in
    let new_l = new_a :: l in
      (new_q, new_l, Var new_a)

  | (q, l, App(Const "meas", Var v)) ->
    (* Q = alpha|Q_0> + beta|Q_1> *)
    let pos = 
      match (List.find_index (( = ) v) l) with
      | None -> invalid_arg "Specified qubit does not exist"
      | Some i -> i
    in
    let len = Array.length q in

    (* 1 left shifted by the index of the qubit gives the bit we need to filter by to reconstruct the desired qubit probabilities
        from the state vector (using logical and later) *)
    let mask = 1 lsl pos in

    let (prob_0, prob_1) = (ref 0.0, ref 0.0) in

    for k = 0 to (len - 1) do
      let prob = Complex.norm2 q.(k) in
      if (k land mask = 0) then
        prob_0 := !prob_0 +. prob
      else
        prob_1 := !prob_1 +. prob
      done;

    let roll = Random.float 1.0 in
    let new_q = Array.make len ({ Complex.re = 0.0; im = 0.0 }) in
    
    if roll < !prob_0 || !prob_1 = 0.0 then
      (* Outcome |Q_0> *)
      let alpha = sqrt !prob_0 in
      let c_alpha = {Complex.re = alpha; im = 0.0} in
      for k = 0 to (len - 1) do
        if (k land mask = 0) then
          new_q.(k) <- Complex.div q.(k) c_alpha
        done;
      
      (new_q, l, Injr Unit)

    else
      (* Outcome |Q_1> *)
      let beta = sqrt !prob_1 in
      let c_beta = {Complex.re = beta; im = 0.0} in
      for k = 0 to (len - 1) do
        if (k land (1 lsl pos) <> 0) then
          new_q.(k) <- Complex.div q.(k) c_beta
        done;
      
      (new_q, l, Injl Unit)

  (* congruence reduction rules - reducing the second term to a value before reducing the first *)
  | (q, l, App(m, n)) when not (is_value n) ->
    let (q', l', n') = reduce (q, l, n) in
      (q', l', App(m, n'))
  
  | (q, l, App(m, n)) when not (is_value m) ->
    let (q', l', m') = reduce (q, l, m) in
      (q', l', App(m', n))

  | (q, l, Pair(m1, m2)) when not (is_value m2) ->
    let (q', l', m2') = reduce (q, l, m2) in
      (q', l', Pair(m1, m2'))

  | (q, l, Pair(m1, m2)) when not (is_value m1) ->
    let (q', l', m1') = reduce (q, l, m1) in
      (q', l', Pair(m1', m2))

  | (q, l, Injl(m)) when not (is_value m) ->
    let (q', l', m') = reduce (q, l, m) in
      (q', l', Injl(m'))

  | (q, l, Injr(m)) when not (is_value m) ->
    let (q', l', m') = reduce (q, l, m) in
      (q', l', Injr(m'))

  | (q, l, Match(p, (x, m), (y, n))) when not (is_value p) ->
    let (q', l', p') = reduce (q, l, p) in
      (q', l', Match(p', (x, m), (y, n)))

  | (q, l, LetPair(x, y, m, n)) when not (is_value m) ->
    let (q', l', m') = reduce (q, l, m) in
      (q', l', LetPair(x, y, m', n))

  (* escape clause to avoid missing pattern match errors while building *)
  | (q, l, m) -> (q, l, m)

let rec eval (s : state) : state =
  let (q, l, m) = s in
  if is_value m then s
  else
    let s' = reduce s in
    if s = s' then s (* to stop infinite loops on stuck expressions *)
    else eval s

(* let plingsubtype expr1 expr2 =
  match (expr1, expr2) with
  | (Exp _, _) -> True
  |  *)