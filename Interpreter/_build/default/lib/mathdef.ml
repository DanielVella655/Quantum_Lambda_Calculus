open Complex
let c0 = {re = 0.0; im = 0.0} (* complex 0 *)
let q0 = [|{re = 1.0; im = 0.0}; {re = 0.0; im = 0.0}|]  (* quantum 0 *)
let q1 = [|{re = 0.0; im = 0.0}; {re = 1.0; im = 0.0}|]  (* quantum 1 *)

type m = Complex.t array array
type v = Complex.t array

module QMatrix = struct
  let create rows cols : m =
    Array.make_matrix rows cols c0
  end

let mat_mul (a : m) (b : m) : m =
  (* c_ij = \sum_{k} a_ik * b_kj *)
  let (rows_a, cols_a) = (Array.length a, Array.length a.(0)) in
  let (rows_b, cols_b) = (Array.length b, Array.length b.(0)) in
    if cols_a <> rows_b then invalid_arg "Matrix dimension mismatch";

  let res = QMatrix.create rows_a cols_b in
    for i = 0 to rows_a - 1 do
      for j = 0 to cols_b - 1 do
        let sum = ref c0 in
          for k = 0 to cols_a - 1 do
            sum := add !sum (mul a.(i).(k) b.(k).(j))
          done;
        res.(i).(j) <- !sum
      done;
    done;
  res

let mat_vec_mul (a : m) (b : v) : v =
  let (rows_a, cols_a) = (Array.length a, Array.length a.(0)) in
  let len_b = Array.length b in
    if cols_a <> len_b then invalid_arg "Matrix dimension mismatch";

  let res = Array.make rows_a c0 in
    for i = 0 to rows_a - 1 do
      let sum = ref c0 in
        for j = 0 to len_b - 1 do
          sum := add !sum (mul a.(i).(j) b.(j))
        done;
      res.(i) <- !sum
      done;
  res

(* $ (A \otimes B)_{(i\cdot p +k, j \cdot q + l)} = A_{i,j} \times B_{k,l} $
where
\begin{itemize}
  \item $1 \le i \le m$ and $1 \le j \le n$ index matrix $A$
  \item $1 \le k \le p$ and $1 \le l \le q$ index matrix $B$
\end{itemize} *)

let kron_prod (a : m) (b : m) : m =
let (rows_a, cols_a) = (Array.length a, Array.length a.(0)) in
let (rows_b, cols_b) = (Array.length b, Array.length b.(0)) in
let res = QMatrix.create (rows_a * rows_b) (cols_a * cols_b) in
  for i = 0 to rows_a - 1 do
    for j = 0 to cols_a - 1 do
      let elem_a = a.(i).(j) in
      for k = 0 to rows_b - 1 do
        for l = 0 to cols_b - 1 do
          res.(i * rows_b + k).(j * cols_b + l) <- mul elem_a b.(k).(l)
          done;
        done;
      done;
    done;
res

let vec_kron_prod (a : v) (b : v) : v =
  let n1 = Array.length a in
  let n2 = Array.length b in
  let res = Array.make (n1 * n2) c0 in
    for i = 0 to n1 - 1 do
      for j = 0 to n2 - 1 do
        res.(i * n2 + j) <- mul a.(i) b.(j)
        done;
      done;
  res

