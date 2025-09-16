open Dom
open Adom

let antp_ms0_step : ((S.Pgm.cmd * Mem.t -> Mem.t) * (S.Pgm.exp * Mem.t -> Val.t)) Fix.trfun
    =
 fun (aval_c, aval_e) ->
   let filter_zero (e : S.Pgm.exp) (m : Mem.t) : Mem.t =
    let v = aval_e (e, m) in
    if Val.leq (Val.abstract 0) v then m else Mem.bot
   in
   let filter_nonzero (e : S.Pgm.exp) (m : Mem.t) : Mem.t =
    let v = aval_e (e, m) in
    if Val.leq v (Val.abstract 0) then Mem.bot else m
  in
  (fun (c, m) ->
    match c with
    | Skip -> m
    | Write (e1, e2) ->
        let addr = aval_e (e1, m) in
        let v = aval_e (e2, m) in
        Mem.Op.write m addr v
    | Seq (c1, c2) ->
        let m' = aval_c (c1, m) in
        aval_c (c2, m')
    | If (e, c1, c2) ->
        let m1 = aval_c (c1, filter_nonzero e m) in
        let m2 = aval_c (c2, filter_zero e m) in
        Mem.join m1 m2
    | While (e, c') ->
        let m_body = aval_c (c', filter_nonzero e m) in
        let m_loop = aval_c (c, m_body) in
        Mem.join (filter_zero e m) m_loop),
  (fun (e, m) ->
    (* Format.printf "EXP: %a\nMEM: %a\n" S.Pgm.pp_exp e Mem.pp m; *)
    match e with
    | Int n -> Val.abstract n
    | Bop (bop, e1, e2) -> (
        let v1 = aval_e (e1, m) in
        let v2 = aval_e (e2, m) in
        match bop with
        | Add -> Val.Op.add v1 v2
        | Sub -> Val.Op.sub v1 v2
        | Mul -> Val.Op.mul v1 v2
        | Eq -> Val.Op.eq v1 v2)
    | Uop (uop, e') -> (
        let v = aval_e (e', m) in
        match uop with Not -> Val.Op.not v)
    | Read e' ->
        let addr = aval_e (e', m) in
        Mem.Op.read m addr)

module CmdSet = Set.Make (struct
  type t = S.Pgm.cmd

  let compare = Stdlib.compare
end)

module ExpSet = Set.Make (struct
  type t = S.Pgm.exp

  let compare = Stdlib.compare
end)

let antp_ms0_steps : ((CmdSet.t * Mem.t -> Mem.t) * (ExpSet.t * Mem.t -> Val.t)) Fix.trfun
    =
 fun (aval_cs, aval_es) ->
  let aval_c (c, m) = aval_cs (CmdSet.singleton c, m) in
  let aval_e (e, m) = aval_es (ExpSet.singleton e, m) in
  let (aval_c', aval_e') = antp_ms0_step (aval_c, aval_e) in
  (fun (cs, m) ->
    cs
    |> CmdSet.elements
    |> List.map (fun c -> aval_c' (c, m))
    |> List.fold_left Mem.join Mem.bot),
  (fun (es, m) ->
    es
    |> ExpSet.elements
    |> List.map (fun e -> aval_e' (e, m))
    |> List.fold_left Val.join Val.bot)

let (antp_ms0_c, antp_ms0_e) : (CmdSet.t * Mem.t -> Mem.t) * (ExpSet.t * Mem.t -> Val.t) =
(*
let (antp_ms0_c, antp_ms0_e) : (S.Pgm.cmd * Mem.t -> Mem.t) * (S.Pgm.exp * Mem.t -> Val.t) =
*)
  let solve init =
    let step = antp_ms0_steps in
    (*
    let step = antp_ms0_step in
    *)
    let cache_in = (Hashtbl.create 17, Hashtbl.create 17) in
    let cache_out = (Hashtbl.create 17, Hashtbl.create 17) in
    let key = (fun (cs, m) -> (cs, m)), (fun (es, m) -> (es, m)) in
    let i_leq =
      (fun (cs1, m1) (cs2, m2) -> CmdSet.subset cs1 cs2 && Mem.leq m1 m2),
      (fun (es1, m1) (es2, m2) -> ExpSet.subset es1 es2 && Mem.leq m1 m2)
      (*
      (fun (_cs1, m1) (_cs2, m2) -> (assert (_cs1 = _cs2); Mem.leq m1 m2)),
      (fun (_es1, m1) (_es2, m2) -> (assert (_es1 = _es2); Mem.leq m1 m2))
      *)
    in
    let i_join =
      (fun (cs1, m1) (_cs2, m2) -> (assert (cs1 = _cs2); (cs1, Mem.join m1 m2))),
      (fun (es1, m1) (_es2, m2) -> (assert (es1 = _es2); (es1, Mem.join m1 m2)))
    in
    let stable = ref false in
    let update h ?(on_update = fun _ _ _ -> ()) ~leq ~join k v =
      match Hashtbl.find_opt h k with
      | None ->
          begin
            on_update "NEW" None v;
            Hashtbl.replace h k v;
            stable := false
          end
      | Some v_old ->
          if not (leq v v_old) then begin
            on_update "UPD" (Some v_old) (join v_old v);
            Hashtbl.replace h k (join v_old v);
            stable := false
          end
    in
    let read_c i =
      let k = fst key i in
      update (fst cache_in) ~leq:(fst i_leq) ~join:(fst i_join) k i
      (*
        ~on_update:(fun s old v -> Format.printf "[read_c] %s: %a\n  ↦ from %a\n    to %a\n" s S.Pgm.pp_cmd k Mem.pp (old |> Option.map snd |> Option.value ~default:Mem.bot) (Mem.pp) (snd v))*);
      Hashtbl.find_opt (fst cache_out) k |> Option.value ~default:Mem.bot
    in
    let read_e i =
      let k = snd key i in
      update (snd cache_in) ~leq:(snd i_leq) ~join:(snd i_join) k i
        (* ~on_update:(fun s -> Format.printf "[read_e] %s: %a\n" s S.Pgm.pp_exp k) *);
      Hashtbl.find_opt (snd cache_out) k |> Option.value ~default:Val.bot
    in
    let read = (read_c, read_e) in
    begin match init with
    | Either.Left i ->
        let k = fst key i in
        Hashtbl.replace (fst cache_in) k i
    | Either.Right i ->
        let k = snd key i in
        Hashtbl.replace (snd cache_in) k i
    end;
    stable := false;
    while not !stable do
      stable := true;
      fst cache_in |> Hashtbl.iter (fun k i ->
        let o = fst (step read) i in
        update (fst cache_out) ~leq:Mem.leq ~join:Mem.join k o
          (*~on_update:(fun s -> Format.printf "[out_c] %s: %a\n" s S.Pgm.pp_cmd k)*));
      snd cache_in |> Hashtbl.iter (fun k i ->
        let o = snd (step read) i in
        update (snd cache_out) ~leq:Val.leq ~join:Val.join k o
        (*
          ~on_update:(fun s -> Format.printf "[out_e] %s: %a\n" s S.Pgm.pp_exp k)
      *));
    done;
    Either.map ~left:read_c ~right:read_e init
  in
  (fun i -> solve (Either.Left i) |> Either.find_left |> Option.get),
  (fun i -> solve (Either.Right i) |> Either.find_right |> Option.get)

let antp_mt0 p i =
  let i_s = encode (p, i) in
  let o_s = antp_ms0_c (CmdSet.singleton intp_st, i_s) in
  (*
  let o_s = antp_ms0_c (intp_st, i_s) in
  *)
  decode o_s
