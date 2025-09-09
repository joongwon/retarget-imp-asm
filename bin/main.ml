open Codelib
open Dom

let antp_ms0_step aval_c_cache =
  let open Abstract in
  let rec aval_e (e : S.Pgm.exp) (m : Abstract.Mem.t) : Abstract.Val.t =
    match e with
    | Int n -> Val.abstract n
    | Bop (bop, e1, e2) ->
      let v1 = aval_e e1 m in
      let v2 = aval_e e2 m in
      (match bop with
       | Add -> Val.add v1 v2
       | Sub -> Val.sub v1 v2
       | Mul -> Val.mul v1 v2
       | Eq -> Val.eq v1 v2)
    | Read e' ->
      let addr = aval_e e' m in
      Mem.read m addr
  and aval_c (c : S.Pgm.cmd) (m : Abstract.Mem.t) : Abstract.Mem.t =
    (*
      Format.printf "  +-CMD: %a\n" S.Pgm.pp_cmd c;
      Format.printf "  |   IN: %a\n" Abstract.Mem.pp m;
      *)
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

module type D = sig
  type t
  val bot : t
  val leq : t -> t -> bool
  val join : t -> t -> t
  val widen : t -> t -> t
end

type 't d = (module D with type t = 't)

let solve (type b)
          ~(d : b d)
          ~(key : 'a -> b -> 'c)
          ~(of_key : 'c -> 'a)
          (step : ('a -> b -> b) -> ('a -> b -> b))
          (c : 'a)
          (m : b) : b =
  let module D = (val d) in
  let cache_in = Hashtbl.create 17 in
  let cache_out = Hashtbl.create 17 in
  let deps_tbl = Hashtbl.create 17 in
  let rec loop todos =
    if List.length todos = 0 then ()
    else
      let new_todos = ref [] in
      List.iter (fun k ->
        let c = of_key k in
        let m_in = Hashtbl.find_opt cache_in k |> Option.value ~default:D.bot in
        (* Format.printf "  IN: %a\n" Abstract.Mem.pp m_in; *)
        let m_out = step (fun c m_in ->
          let k_sub = key c m_in in
          let m_in_old = Hashtbl.find_opt cache_in k_sub |> Option.value ~default:D.bot in
          let m_out_old = Hashtbl.find_opt cache_out k_sub |> Option.value ~default:D.bot in
          if not (D.leq m_in m_in_old) then begin
            new_todos := k_sub :: !new_todos;
            if k_sub <> k then begin
              let deps = Hashtbl.find_opt deps_tbl k_sub |> Option.value ~default:[] in
              Hashtbl.replace deps_tbl k_sub ((k :: deps) |> List.sort_uniq compare);
            end;
            Hashtbl.replace cache_in k_sub (D.widen m_in_old m_in);
          end;
          (*
          Format.printf "    IN(new): %a\n" Abstract.Mem.pp m_in;
          Format.printf "    IN(old): %a\n" Abstract.Mem.pp m_in_old;
          Format.printf "    OUT(old): %a\n" Abstract.Mem.pp m_out_old;
          *)
          m_out_old
        ) c m_in in
        (* Format.printf "  OUT: %a\n" Abstract.Mem.pp m_out; *)
        let m_out_old = Hashtbl.find_opt cache_out k |> Option.value ~default:D.bot in
        if not (D.leq m_out m_out_old) then begin
          Hashtbl.replace cache_out k (D.join m_out_old m_out);
          new_todos := (Hashtbl.find_opt deps_tbl k |> Option.value ~default:[]) @ !new_todos;
        end
      ) todos;
      loop (!new_todos |> List.sort_uniq compare)
  in
  let k = key c m in
  Hashtbl.replace cache_in k m;
  loop [k];
  Hashtbl.find_opt cache_out k |> Option.value ~default:D.bot

let antp_ms1_step1 aval_c_cache =
  let open Abstract in
  let rec aval_e (e : S.Pgm.exp) (m : Abstract.Mem.t code) : Abstract.Val.t code =
    let m = genlet m in
    match e with
    | Int n -> (.<Val.abstract n>.)
    | Bop (bop, e1, e2) ->
      let v1 = aval_e e1 m in
      let v2 = aval_e e2 m in
      (match bop with
       | Add -> .<Val.add .~v1 .~v2>.
       | Sub -> .<Val.sub .~v1 .~v2>.
       | Mul -> .<Val.mul .~v1 .~v2>.
       | Eq -> .<Val.eq .~v1 .~v2>.)
    | Read e' ->
      let addr = aval_e e' m in
      (.<Mem.read .~m .~addr>.)
  and aval_c (c : S.Pgm.cmd) (m : Abstract.Mem.t code) : Abstract.Mem.t code =
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

let lift_int (n : int) = .<n>.

let antp_ms1_step c =
  let body cache n m =
    let key_tbl = Hashtbl.create 17 in
    let pgm_tbl = Hashtbl.create 17 in
    let next_key = ref 0 in
    let rec loop todos =
      if List.length todos = 0 then ()
      else
        let new_todos = ref [] in
        List.iter (fun c ->
          let pgm = antp_ms1_step1 (fun c' ->
            match Hashtbl.find_opt key_tbl c' with
            | Some k' -> .<.~cache .~(lift_int k')>.
            | None ->
                let k' = !next_key in
                next_key := !next_key + 1;
                Hashtbl.add key_tbl c' k';
                new_todos := c' :: !new_todos;
                .<.~cache k'>.) c in
          let k = Hashtbl.find key_tbl c in
          Hashtbl.add pgm_tbl k (pgm m);
        ) todos;
        loop (!new_todos |> List.sort_uniq compare)
    in
    Hashtbl.add key_tbl c 0;
    loop [c];
    Hashtbl.fold
      (fun k pgm acc -> .<if .~n = .~(lift_int k) then .~pgm else .~acc>.)
      pgm_tbl
      .<invalid_arg "antp_ms1_step: invalid key">.
  in
  .<fun cache n m -> .~(body .<cache>. .<n>. .<m>.)>.


let intp_st : S.Pgm.t =
  While (Read (Read (Int 0)),
         Seq (If (Bop (Eq, Read (Read (Int 0)), Int 1),
                  Write (Int 1, Bop (Add, Read (Int 1), Read (Bop (Add, Read (Int 0), Int 1)))),
              If (Bop (Eq, Read (Read (Int 0)), Int 2),
                  Write (Int 1, Bop (Mul, Read (Int 1), Read (Bop (Add, Read (Int 0), Int 1)))),
                  Skip)),
              Write (Int 0, Bop (Add, Read (Int 0), Int 2))))

let antp_ms0 =
  let key c m = (c, match m with Some (v::_) -> Some v | _ -> None) in
  let of_key k = fst k in
  solve ~d:(module Abstract.Mem) ~key ~of_key antp_ms0_step

let antp_mt0 p i =
  (p, i)
  |> encode
  |> Abstract.Mem.abstract
  |> antp_ms0 intp_st
  |> decode

let antp_mt1_step_code = antp_ms1_step intp_st
let antp_mt1_step =
  Format.printf "Generating code for antp_mt1_step...";
  let f =
    try
      Runnative.add_search_path "_build/default/bin/.main.eobjs/byte";
      Runnative.run_native (close_code ~csp:CSP_ok antp_mt1_step_code)
    with
    | Env.Error e -> Format.printf "%a\n" Env.report_error e; failwith "Code generation failed"
  in
  Format.printf "Code generated.";
  f
let antp_mt1_indexed =
  let key n m = (n, match m with Some (v::_) -> Some v | _ -> None) in
  let of_key k = fst k in
  solve ~d:(module Abstract.Mem) ~key ~of_key antp_mt1_step

let antp_mt1 p i =
  (p, i)
  |> encode
  |> Abstract.Mem.abstract
  |> antp_mt1_indexed 0
  |> decode

let main () =
  let p : T.Pgm.t = [Add 1; Mul 2; Add 3] in
  let i = 10 in
  let res0 = antp_mt0 p i in
  Format.printf "antp_mt0: %a\n" Abstract.Val.pp res0;
  let res1 = antp_mt1 p i in
  Format.printf "antp_mt1: %a\n" Abstract.Val.pp res1;
;;

let () = main ()
