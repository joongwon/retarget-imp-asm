open Dom
open Adom

let antp_ms0_step aval_c_cache =
  let rec aval_e (e : S.Pgm.exp) (m : Mem.t) : Val.t =
    match e with
    | Int n -> Val.abstract n
    | Bop (bop, e1, e2) -> (
        let v1 = aval_e e1 m in
        let v2 = aval_e e2 m in
        match bop with
        | Add -> Val.add v1 v2
        | Sub -> Val.sub v1 v2
        | Mul -> Val.mul v1 v2
        | Eq -> Val.eq v1 v2)
    | Uop (uop, e') -> (
        let v = aval_e e' m in
        match uop with Not -> Val.not v)
    | Read e' ->
        let addr = aval_e e' m in
        Mem.read m addr
  and aval_c (c : S.Pgm.cmd) (m : Mem.t) : Mem.t =
    match c with
    | Skip -> m
    | Write (e1, e2) ->
        let addr = aval_e e1 m in
        let v = aval_e e2 m in
        Mem.write m addr v
    | Seq (c1, c2) ->
        let m' = aval_c c1 m in
        aval_c c2 m'
    | If (e, c1, c2) ->
        let v = aval_e e m in
        let m1 = aval_c c1 (filter_nonzero v m) in
        let m2 = aval_c c2 (filter_zero v m) in
        Mem.join m1 m2
    | While (e, c') ->
        let v = aval_e e m in
        let m_body = aval_c c' (filter_nonzero v m) in
        let m_loop = aval_c_cache c m_body in
        Mem.join (filter_zero v m) m_loop
  in
  aval_c

let antp_mt0 (p : T.Pgm.t) (i : Val.t) : Val.t =
  let key_of_m m = match m with Some (v :: _) -> Some v | _ -> None in
  let antp_ms0 = Fix.solve ~d:(module Mem) ~key_of:key_of_m antp_ms0_step in
  (p, i) |> encode |> antp_ms0 intp_st |> decode
