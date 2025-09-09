open Codelib

let lift_int (n : int) = .<n>.
let lift_string (s : string) = .<s>.

let hashtbl_find_staged (type a c)
    ~(lift_key : c -> c code)
    (tbl : (c, a code) Hashtbl.t) : (c -> a) code =
  .<fun k -> .~(
    Hashtbl.fold
      (fun k' v acc -> .<if k = .~(lift_key k') then .~v else .~acc>.)
      tbl
      .<raise Not_found>.)>.

let dissolve (type a b c)
    ~(lift_key : c -> c code)
    ~(key_of : a -> c)
    (step : (a -> (b -> b) code) -> (a -> b code -> b code))
    (n0 : a) : ((c -> b -> b) -> (c -> b -> b)) code =
  .<fun cache -> .~(
    let table = Hashtbl.create 17 in
    let rec loop todos =
      if List.length todos = 0 then ()
      else
        let new_todos = ref [] in
        List.iter (fun n ->
          let f = step (fun n' ->
            let k' = key_of n' in
            if not (Hashtbl.mem table k') then
              new_todos := n' :: !new_todos;
            .<cache .~(lift_key k')>.) n
          in
          Hashtbl.replace table (key_of n) .<fun x -> .~(f .<x>.)>.;
        ) todos;
        loop (!new_todos |> List.sort_uniq compare)
    in
    loop [n0];
    hashtbl_find_staged ~lift_key table)>.
