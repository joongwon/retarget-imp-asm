open Codelib
open Dom
open Adom

let antp_ms1_step aval_c_cache =
  let open Adom in
  let rec aval_e (e : S.Pgm.exp) (m : Mem.t code) : Val.t code =
    let m = genlet m in
    match e with
    | Int n ->
        (.<Val.abstract n>.)
    | Bop (bop, e1, e2) ->
      let v1 = aval_e e1 m in
      let v2 = aval_e e2 m in
      (match bop with
       | Add -> .<Val.add .~v1 .~v2>.
       | Sub -> .<Val.sub .~v1 .~v2>.
       | Mul -> .<Val.mul .~v1 .~v2>.
       | Eq -> .<Val.eq .~v1 .~v2>.)
    | Uop (uop, e') ->
      let v = aval_e e' m in
      (match uop with
       | Not -> .<Val.not .~v>.)
    | Read e' ->
      let addr = aval_e e' m in
      (.<Mem.read .~m .~addr>.)
  and aval_c (c : S.Pgm.cmd) (m : Mem.t code) : Mem.t code =
    let m = genlet m in
    match c with
    | Skip -> m
    | Write (e1, e2) ->
      let addr = aval_e e1 m in
      let v = aval_e e2 m in
      .<Mem.write .~m .~addr .~v>.
    | Seq (c1, c2) ->
      let m' = aval_c c1 m in
      aval_c c2 m'
    | If (e, c1, c2) ->
      let v = aval_e e m in
      let m1 = aval_c c1 .<filter_nonzero .~v .~m>. in
      let m2 = aval_c c2 .<filter_zero .~v .~m>. in
      .<Mem.join .~m1 .~m2>.
    | While (e, c') ->
      let v = aval_e e m in
      let m_body = aval_c c' .<filter_nonzero .~v .~m>.in
      let m_loop = .<.~(aval_c_cache c) .~m_body>. in
      .<Mem.join (filter_zero .~v .~m) .~m_loop>.
  in
  aval_c

let run c =
  try
    Runnative.add_search_path "_build/default/bin/.main.eobjs/byte";
    Runnative.run_native (close_code ~csp:CSP_ok c)
  with
  | Env.Error e -> Format.printf "%a\n" Env.report_error e; failwith "Code generation failed"

let key_of_s = Fix.mk_key_of ()
let antp_mt1_step'_code = Fix_staged.(dissolve ~lift_key:lift_int ~key_of:key_of_s antp_ms1_step intp_st)
let _ = Format.printf "Generated code for antp_mt1_step':\n%a\n" print_code antp_mt1_step'_code
let antp_mt1_step' = run antp_mt1_step'_code

let antp_mt1_indexed =
  let key_of_m m = match m with Some (v::_) -> Some v | _ -> None in
  Fix.solve ~d:(module Mem) ~key_of:key_of_m antp_mt1_step'

let antp_mt1 p i =
  (p, i)
  |> encode
  |> antp_mt1_indexed (key_of_s intp_st)
  |> decode

