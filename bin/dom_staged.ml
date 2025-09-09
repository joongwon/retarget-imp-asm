open Codelib
open Dom

let _ = (.<()>.)

type 't hybrid = V of 't | C of 't code

let to_code (lift : 't -> 't code) (h : 't hybrid) : 't code =
  match h with
  | V v -> lift v
  | C c -> c

let genleth (x : 't hybrid) : 't hybrid =
  match x with
  | V v -> V v
  | C c -> C (Codelib.genlet c)

let rec lift_list (lift : 't -> 't code) (lst : 't list) : 't list code =
  match lst with
  | [] -> .<[]>.
  | x :: xs ->
      let x = lift x in
      let xs = lift_list lift xs in
      .< .~x :: .~xs >.

let lift_option (lift : 't -> 't code) (o : 't option) : 't option code =
  (match o with
  | None -> .<None>.
  | Some v ->
      let v = lift v in
      .<Some .~v>.)

module Staged = struct
  module Val = struct
    open Abstract.Val

    let lift_bound (b : bound) : bound code =
      match b with
      | Inf -> .<Inf>.
      | Fin n -> .<Fin n>.

    let lift (v : t) : t code =
      match v with
      | Bot -> .<Bot>.
      | Intv (Fin n, Fin m) when n = m -> .<abstract n>.
      | Intv (l, u) ->
          let l = lift_bound l in
          let u = lift_bound u in
          .<Intv (.~l, .~u)>.

    let abstract (v : S.Val.t hybrid) : t hybrid =
      match v with
      | V v -> V (abstract v)
      | C c -> C .<abstract .~c>.
  end

  module Mem = struct
    open Abstract.Mem

    let lift (m : t) : t code =
      lift_option (lift_list Val.lift) m
  end
end

