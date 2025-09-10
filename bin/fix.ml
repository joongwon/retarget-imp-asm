module type D = sig
  type t

  val bot : t
  val leq : t -> t -> bool
  val join : t -> t -> t
  val widen : t -> t -> t
end

type 't d = (module D with type t = 't)

let solve (type b) ~(d : b d) ~(key_of : b -> 'c)
    (step : ('a -> b -> b) -> 'a -> b -> b) (c : 'a) (m : b) : b =
  let module D = (val d) in
  let cache_in = Hashtbl.create 17 in
  let cache_out = Hashtbl.create 17 in
  let deps_tbl = Hashtbl.create 17 in
  let rec loop todos =
    if List.length todos = 0 then ()
    else
      let new_todos = ref [] in
      List.iter
        (fun ((c, _) as k) ->
          let m_in =
            Hashtbl.find_opt cache_in k |> Option.value ~default:D.bot
          in
          (* Format.printf "  IN: %a\n" Adom.Mem.pp m_in; *)
          let m_out =
            step
              (fun c' m_in' ->
                let k' = (c', key_of m_in') in
                let m_in_old =
                  Hashtbl.find_opt cache_in k' |> Option.value ~default:D.bot
                in
                let m_out_old =
                  Hashtbl.find_opt cache_out k' |> Option.value ~default:D.bot
                in
                if not (D.leq m_in' m_in_old) then (
                  new_todos := k' :: !new_todos;
                  (if k' <> k then
                     let deps =
                       Hashtbl.find_opt deps_tbl k' |> Option.value ~default:[]
                     in
                     Hashtbl.replace deps_tbl k'
                       (k :: deps |> List.sort_uniq compare));
                  Hashtbl.replace cache_in k' (D.widen m_in_old m_in'));
                m_out_old)
              c m_in
          in
          let m_out_old =
            Hashtbl.find_opt cache_out k |> Option.value ~default:D.bot
          in
          if not (D.leq m_out m_out_old) then (
            Hashtbl.replace cache_out k (D.join m_out_old m_out);
            new_todos :=
              (Hashtbl.find_opt deps_tbl k |> Option.value ~default:[])
              @ !new_todos))
        todos;
      loop (!new_todos |> List.sort_uniq compare)
  in
  let k = (c, key_of m) in
  Hashtbl.replace cache_in k m;
  loop [ k ];
  Hashtbl.find_opt cache_out k |> Option.value ~default:D.bot

let mk_key (type a) () : (a -> int) * (int -> a) =
  let tbl = Hashtbl.create 17 in
  let next = ref 0 in
  ( (fun c ->
      match Hashtbl.find_opt tbl c with
      | Some k -> k
      | None ->
          let k = !next in
          incr next;
          Hashtbl.add tbl c k;
          k),
    fun k ->
      Option.get
      @@ Hashtbl.fold (fun c k' acc -> if k = k' then Some c else acc) tbl None
  )

let dissolve (type key arg data) ~(of_key : key -> arg) ~(key_of : arg -> key)
    (step : (arg -> data) -> arg -> data) : (key -> data) -> key -> data =
 fun cache n -> step (fun n' -> cache (key_of n')) (of_key n)
