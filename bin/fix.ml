module type D = sig
  type t

  val bot : t
  val leq : t -> t -> bool
  val join : t -> t -> t
  val widen : t -> t -> t
end

type 't d = (module D with type t = 't)

let solve (type b) ~(d : b d) ~(key_of : b -> 'c)
    (step : ('a -> b -> b) -> 'a -> b -> b) (c0 : 'a) (m_in0 : b) : b =
  let module D = (val d) in
  let cache_in = Hashtbl.create 17 in
  let cache_out = Hashtbl.create 17 in
  let k = (c0, key_of m_in0) in
  Hashtbl.replace cache_in k m_in0;
  let changed = ref true in
  while
    !changed
  do
    changed := false;
    cache_in |> Hashtbl.iter (fun ((c, _) as k) m_in ->
      Format.printf "  IN: %a\n" Adom.Mem.pp (Obj.magic m_in);
      let m_out =
        step
          (fun c' m_in' ->
            let k' = (c', key_of m_in') in
            let m_in_old' =
              Hashtbl.find_opt cache_in k' |> Option.value ~default:D.bot
            in
            if not (D.leq m_in' m_in_old') then begin
              Hashtbl.replace cache_in k' (D.join m_in_old' m_in');
              changed := true;
            end;
            Hashtbl.find_opt cache_out k' |> Option.value ~default:D.bot)
          c m_in
      in
      Format.printf "  OUT: %a\n" Adom.Mem.pp (Obj.magic m_out);
      let m_out_old =
        Hashtbl.find_opt cache_out k |> Option.value ~default:D.bot
      in
      if not (D.leq m_out m_out_old) then begin
        Hashtbl.replace cache_out k (D.widen m_out_old m_out);
        changed := true;
      end);
  done;
  step
    (fun c' m_in' ->
      let k' = (c', key_of m_in') in
      Hashtbl.find_opt cache_out k' |> Option.value ~default:D.bot)
    c0 m_in0

(*
let solve (type b) ~(d : b d) ~(key_of : b -> 'c)
    (step : ('a -> b -> b) -> 'a -> b -> b) (c : 'a) (m : b) : b =
  let module D = (val d) in
  let cache_in = Hashtbl.create 17 in
  let cache_out = Hashtbl.create 17 in
  let deps_tbl = Hashtbl.create 17 in
  let todos = Queue.create () in
  let k = (c, key_of m) in
  Queue.add k todos;
  Hashtbl.replace cache_in k m;
  while not (Queue.is_empty todos) do
    let (c, _) as k = Queue.pop todos in
    let m_in =
      Hashtbl.find_opt cache_in k |> Option.value ~default:D.bot
    in
    (* Format.printf "  IN: %a\n" Adom.Mem.pp m_in; *)
    let m_out =
      step
        (fun c' m_in' ->
          let k' = (c', key_of m_in') in
          let m_in_old' =
            Hashtbl.find_opt cache_in k' |> Option.value ~default:D.bot
          in
          if not (D.leq m_in' m_in_old') then begin
            Queue.add k' todos;
            Hashtbl.replace cache_in k' (D.widen m_in_old' m_in');
            let deps =
              Hashtbl.find_opt deps_tbl k' |> Option.value ~default:[]
            in
            Hashtbl.replace deps_tbl k'
              (k :: deps |> List.sort_uniq compare);
          end;
          Hashtbl.find_opt cache_out k' |> Option.value ~default:D.bot)
        c m_in
    in
    let m_out_old =
      Hashtbl.find_opt cache_out k |> Option.value ~default:D.bot
    in
    if not (D.leq m_out m_out_old) then begin
      Hashtbl.replace cache_out k (D.join m_out_old m_out);
      Hashtbl.find_opt deps_tbl k
      |> Option.value ~default:[]
      |> List.to_seq
      |> Queue.add_seq todos;
    end
  done;
  Hashtbl.find_opt cache_out k |> Option.value ~default:D.bot
  *)

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
