open Codelib

let hashtbl_find_staged (type a c)
    ~(lift_key : c -> c code)
    (tbl : (c, a code) Hashtbl.t) : (c -> a) code =
  .<fun k -> .~(
    Hashtbl.fold
      (fun k' v acc -> .<if k = .~(lift_key k') then .~v else .~acc>.)
      tbl
      .<raise Not_found>.)>.

let memo (type key data)
    ~(lift_key : key -> key code)
    ~(init : key)
    (step : (key -> data code) -> (key -> data code))
    : ((key -> data) -> (key -> data)) code =
  .<fun cache -> .~(
    let table = Hashtbl.create 17 in
    (*
    let todos = Queue.create () in
    Queue.add init todos;
    while not (Queue.is_empty todos) do
      let k = Queue.pop todos in
      if not (Hashtbl.mem table k) then
        let v = step (fun k' ->
          if not (Hashtbl.mem table k') then Queue.add k' todos;
          .<cache .~(lift_key k')>.) k
        in
        Hashtbl.replace table k v;
    done;
    *)
    let rec loop k =
      if Hashtbl.mem table k then
        Hashtbl.find table k
      else begin
        Hashtbl.replace table k .<cache .~(lift_key k)>.;
        let v = step loop k in
        Hashtbl.replace table k v;
        .<cache .~(lift_key k)>.
      end
    in
    loop init |> ignore;
    .<fun k -> .~(
    Hashtbl.fold
      (fun k' v acc -> .<if k = .~(lift_key k') then .~v else .~acc>.)
      table
      .<raise Not_found>.
    )>.
  )>.
