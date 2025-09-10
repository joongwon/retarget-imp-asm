open Codelib
open Dom
open Adom

let lift_int (n : int) = .<n>.
let lift_string (s : string) = .<s>.
let transpose_code_fn (f : 'a code -> 'b code) : ('a -> 'b) code =
  .<fun x -> .~(f .<x>.)>.

let run c =
  try
    Runnative.add_search_path "_build/default/bin/.main.eobjs/byte";
    Runnative.run_native (close_code ~csp:CSP_ok c)
  with
  | Env.Error e -> Format.printf "%a\n" Env.report_error e; failwith "Code generation failed"

let antp_ms1_step aval_c_cache =
  let open Adom in
  let rec aval_e (e : S.Pgm.exp) (m : Mem.t code) : Val.t code =
    let m = genlet ~name:"m" m in
    match e with
    | Int n ->
        (.<Val.abstract n>.)
    | Bop (bop, e1, e2) ->
      let v1 = aval_e e1 m in
      let v2 = aval_e e2 m in
      (match bop with
       | Add -> .<Val.Op.add .~v1 .~v2>.
       | Sub -> .<Val.Op.sub .~v1 .~v2>.
       | Mul -> .<Val.Op.mul .~v1 .~v2>.
       | Eq -> .<Val.Op.eq .~v1 .~v2>.)
    | Uop (uop, e') ->
      let v = aval_e e' m in
      (match uop with
       | Not -> .<Val.Op.not .~v>.)
    | Read e' ->
      let addr = aval_e e' m in
      (.<Mem.Op.read .~m .~addr>.)
  and aval_c (c : S.Pgm.cmd) (m : Mem.t code) : Mem.t code =
    let m = genlet ~name:"m" m in
    match c with
    | Skip -> m
    | Write (e1, e2) ->
      let addr = aval_e e1 m in
      let v = aval_e e2 m in
      .<Mem.Op.write .~m .~addr .~v>.
    | Seq (c1, c2) ->
      let m' = aval_c c1 m in
      aval_c c2 m'
    | If (e, c1, c2) ->
      let m1 = aval_c c1 (filter_nonzero e m) in
      let m2 = aval_c c2 (filter_zero e m) in
      .<Mem.join .~m1 .~m2>.
    | While (e, c') ->
      let m_body = aval_c c' (filter_nonzero e m) in
      let m_loop = .<.~(aval_c_cache c) .~m_body>. in
      .<Mem.join .~(filter_zero e m) .~m_loop>.
  and filter_zero (e : S.Pgm.exp) (m : Mem.t code) : Mem.t code =
    let m = genlet ~name:"m" m in
    let v = aval_e e m in
    .<if Val.leq (Val.abstract 0) .~v then .~m else Mem.bot>.
  and filter_nonzero (e : S.Pgm.exp) (m : Mem.t code) : Mem.t code =
    let m = genlet ~name:"m" m in
    let v = aval_e e m in
    .<if Val.leq .~v (Val.abstract 0) then Mem.bot else .~m>.
  in
  fun c -> (aval_c c |> transpose_code_fn)

let (key_of_s, s_of_key) = Fix.mk_key ()

let antp_mt1_step_code =
  Fix.dissolve ~of_key:s_of_key ~key_of:key_of_s antp_ms1_step
  |> Fix_staged.memo ~lift_key:lift_int ~init:(key_of_s intp_st)
let _ = Format.printf "Generated code for antp_mt1_step':\n%a\n" print_code antp_mt1_step_code
let antp_mt1_step = run antp_mt1_step_code

let antp_mt1_indexed =
  let key_of_m m = match m with Some (v::_) -> Some v | _ -> None in
  Fix.solve ~d:(module Mem) ~key_of:key_of_m antp_mt1_step

let antp_mt1 p i =
  (p, i)
  |> encode
  |> antp_mt1_indexed (key_of_s intp_st)
  |> decode

