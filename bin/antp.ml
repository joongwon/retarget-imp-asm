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
        | Add -> Val.Op.add v1 v2
        | Sub -> Val.Op.sub v1 v2
        | Mul -> Val.Op.mul v1 v2
        | Eq -> Val.Op.eq v1 v2)
    | Uop (uop, e') -> (
        let v = aval_e e' m in
        match uop with Not -> Val.Op.not v)
    | Read e' ->
        let addr = aval_e e' m in
        Mem.Op.read m addr
  and aval_c (c : S.Pgm.cmd) (m : Mem.t) : Mem.t =
    match c with
    | Skip -> m
    | Write (e1, e2) ->
        let addr = aval_e e1 m in
        let v = aval_e e2 m in
        Mem.Op.write m addr v
    | Seq (c1, c2) ->
        let m' = aval_c c1 m in
        aval_c c2 m'
    | If (e, c1, c2) ->
        let m1 = aval_c c1 (filter_nonzero e m) in
        let m2 = aval_c c2 (filter_zero e m) in
        Mem.join m1 m2
    | While (e, c') ->
        let m_body = aval_c c' (filter_nonzero e m) in
        let m_loop = aval_c_cache c m_body in
        Mem.join (filter_zero e m) m_loop
  and filter_zero (e : S.Pgm.exp) (m : Mem.t) : Mem.t =
    let v = aval_e e m in
    if Val.leq (Val.abstract 0) v then m else Mem.bot
  and filter_nonzero (e : S.Pgm.exp) (m : Mem.t) : Mem.t =
    let v = aval_e e m in
    if Val.leq v (Val.abstract 0) then Mem.bot else m
  in
  aval_c

let key_of_s, s_of_key = Fix.mk_key ()
let antp_mt0_step = Fix.dissolve ~key_of:key_of_s ~of_key:s_of_key antp_ms0_step

let antp_mt0_indexed =
  let key_of_m m = match m with Some (v :: _) -> Some v | _ -> None in
  Fix.solve ~d:(module Mem) ~key_of:key_of_m antp_mt0_step

let antp_mt0 p i =
  (p, i) |> encode |> antp_mt0_indexed (key_of_s intp_st) |> decode
