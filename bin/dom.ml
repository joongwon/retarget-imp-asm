module T = struct
  module Pgm = struct
    type inst = Add of int | Mul of int
    type proc = inst list
    type t = proc
  end
  module Val = struct
    type t = int
  end
  module Input = Val
  module Output = Val
end

module S = struct
  module Pgm = struct
    type bop = Add | Sub | Mul | Eq
    type exp =
      | Int of int
      | Bop of bop * exp * exp
      | Read of exp
    type cmd =
      | Write of exp * exp
      | Seq of cmd * cmd
      | If of exp * cmd * cmd
      | While of exp * cmd
      | Skip
    type t = cmd
    let rec pp_exp fmt e =
      match e with
      | Int n -> Format.fprintf fmt "%d" n
      | Bop (b, e1, e2) ->
        let b_str = match b with
          | Add -> "+"
          | Sub -> "-"
          | Mul -> "*"
          | Eq -> "=="
        in
        Format.fprintf fmt "(%a %s %a)" pp_exp e1 b_str pp_exp e2
      | Read e' ->
        Format.fprintf fmt "M[%a]" pp_exp e'
    let rec pp_cmd fmt c =
      match c with
      | Skip -> Format.fprintf fmt "skip"
      | Write (e1, e2) ->
        Format.fprintf fmt "M[%a] := %a" pp_exp e1 pp_exp e2
      | Seq (c1, c2) ->
        Format.fprintf fmt "%a; %a" pp_cmd c1 pp_cmd c2
      | If (e, c1, c2) ->
        Format.fprintf fmt "if %a then %a else %a" pp_exp e pp_cmd c1 pp_cmd c2
      | While (e, c') ->
        Format.fprintf fmt "while %a do %a" pp_exp e pp_cmd c'
  end
  module Val = struct
    type t = int
  end
  module Mem = struct
    type t = Val.t list
  end
  module Input = Mem
  module Output = Mem
end

let encode : T.Pgm.t * T.Input.t -> S.Input.t =
  fun (prog, input) ->
    let rec encode_p (p : T.Pgm.t) =
      match p with
      | [] -> [0; 0] (* halt *)
      | Add n :: p' -> 1 :: n :: encode_p p'
      | Mul n :: p' -> 2 :: n :: encode_p p'
    in
    let code = encode_p prog in
    2 :: input :: code

let map2 f o1 o2 =
  match (o1, o2) with
  | Some x1, Some x2 -> Some (f x1 x2)
  | _ -> None

module Abstract = struct
  module Val = struct
    type bound = Inf | Fin of int
    type t =
      | Intv of bound * bound
      | Bot (* empty *)

    let pp fmt v =
      match v with
      | Bot -> Format.fprintf fmt "⊥"
      | Intv (l, u) ->
        let l_str = match l with Inf -> "-∞" | Fin n -> string_of_int n in
        let u_str = match u with Inf -> "∞" | Fin n -> string_of_int n in
        Format.fprintf fmt "[%s, %s]" l_str u_str

    let bot : t = Bot

    let abstract (v : S.Val.t) : t =
      Intv (Fin v, Fin v)

    let join (i1 : t) (i2 : t) : t =
      match (i1, i2) with
      | Bot, i | i, Bot -> i
      | Intv (l1, u1), Intv (l2, u2) ->
        let l = match (l1, l2) with
          | Inf, _ | _, Inf -> Inf
          | Fin n1, Fin n2 -> Fin (min n1 n2)
        in
        let u = match (u1, u2) with
          | Inf, _ | _, Inf -> Inf
          | Fin n1, Fin n2 -> Fin (max n1 n2)
        in
        Intv (l, u)

    let widen (iold : t) (inew : t) : t =
      match (iold, inew) with
      | Bot, i | i, Bot -> i
      | Intv (l1, u1), Intv (l2, u2) ->
        let l = match (l1, l2) with
          | Inf, _ -> Inf
          | Fin n1, Fin n2 when n2 < n1 -> Inf
          | Fin n1, Fin _ -> Fin n1
          | Fin _, Inf -> Inf
        in
        let u = match (u1, u2) with
          | Inf, _ -> Inf
          | Fin n1, Fin n2 when n2 > n1 -> Inf
          | Fin n1, Fin _ -> Fin n1
          | Fin _, Inf -> Inf
        in
        Intv (l, u)

    let meet (i1 : t) (i2 : t) : t =
      match (i1, i2) with
      | Bot, _ | _, Bot -> Bot
      | Intv (l1, u1), Intv (l2, u2) ->
        let l = match (l1, l2) with
          | Inf, x | x, Inf -> x
          | Fin n1, Fin n2 -> Fin (max n1 n2)
        in
        let u = match (u1, u2) with
          | Inf, x | x, Inf -> x
          | Fin n1, Fin n2 -> Fin (min n1 n2)
        in
        match (l, u) with
        | Fin n1, Fin n2 when n1 > n2 -> Bot
        | _ -> Intv (l, u)

    let leq (i1 : t) (i2 : t) : bool =
      match (i1, i2) with
      | Bot, _ -> true
      | _, Bot -> false
      | Intv (l1, u1), Intv (l2, u2) ->
        let lower_ok = match (l1, l2) with
          | Inf, _ -> true
          | Fin _, Inf -> false
          | Fin n1, Fin n2 -> n2 <= n1
        in
        let upper_ok = match (u1, u2) with
          | Inf, _ -> true
          | Fin _, Inf -> false
          | Fin n1, Fin n2 -> n1 <= n2
        in
        lower_ok && upper_ok

    let add (i1 : t) (i2 : t) : t =
      let add_bound b1 b2 = match (b1, b2) with
        | Fin n1, Fin n2 -> Fin (n1 + n2)
        | Fin _, inf | inf, Fin _ -> inf
        | inf, _ -> inf
      in
      match (i1, i2) with
      | Bot, _ | _, Bot -> Bot
      | Intv (l1, u1), Intv (l2, u2) ->
        Intv (add_bound l1 l2, add_bound u1 u2)

    let sub (i1 : t) (i2 : t) : t =
      match (i1, i2) with
      | Bot, _ | _, Bot -> Bot
      | Intv (l1, u1), Intv (l2, u2) ->
        let l = match (l1, u2) with
          | Inf, _ | _, Inf -> Inf
          | Fin n1, Fin n2 -> Fin (n1 - n2)
        in
        let u = match (u1, l2) with
          | Inf, _ | _, Inf -> Inf
          | Fin n1, Fin n2 -> Fin (n1 - n2)
        in
        Intv (l, u)

    let mul (i1 : t) (i2 : t) : t =
      match (i1, i2) with
      | Bot, _ | _, Bot -> Bot
      | Intv (l1, u1), Intv (l2, u2) ->
          let l1 = match l1 with Inf -> `MInf | Fin n -> `Fin n in
          let u1 = match u1 with Inf -> `PInf | Fin n -> `Fin n in
          let l2 = match l2 with Inf -> `MInf | Fin n -> `Fin n in
          let u2 = match u2 with Inf -> `PInf | Fin n -> `Fin n in
          let bmul b1 b2 =
            match (b1, b2) with
            | `Fin n1, `Fin n2 -> `Fin (n1 * n2)
            | `PInf, `Fin n | `Fin n, `PInf when n > 0 -> `PInf
            | `PInf, `Fin n | `Fin n, `PInf when n < 0 -> `MInf
            | `PInf, `Fin _ | `Fin _, `PInf -> `Fin 0
            | `MInf, `Fin n | `Fin n, `MInf when n < 0 -> `PInf
            | `MInf, `Fin n | `Fin n, `MInf when n > 0 -> `MInf
            | `MInf, `Fin _ | `Fin _, `MInf -> `Fin 0
            | `PInf, `MInf | `MInf, `PInf -> `MInf
            | `PInf, `PInf -> `PInf
            | `MInf, `MInf -> `PInf
          in
          let blte b1 b2 =
            match (b1, b2) with
            | `MInf, _ -> true
            | _, `PInf -> true
            | `Fin n1, `Fin n2 -> n1 <= n2
            | _ -> false
          in
          let cands = [bmul l1 l2; bmul l1 u2; bmul u1 l2; bmul u1 u2] in
          let l = List.fold_left (fun acc b -> if blte b acc then b else acc) `PInf cands in
          let u = List.fold_left (fun acc b -> if blte acc b then b else acc) `MInf cands in
          match (l, u) with
          | `PInf, _ | _, `MInf -> Bot
          | (`MInf | `Fin _) as l, ((`PInf | `Fin _) as u) ->
              Intv (
                (match l with `MInf -> Inf | `Fin n -> Fin n),
                (match u with `PInf -> Inf | `Fin n -> Fin n)
              )

    let eq (i1 : t) (i2 : t) : t =
      match (i1, i2) with
      | Bot, _ | _, Bot -> Bot
      | Intv (Fin l1, Fin u1), Intv (Fin l2, Fin u2) when l1 = u1 && l2 = u2 && l1 = l2 ->
        Intv (Fin 1, Fin 1)
      | _ when meet i1 i2 = Bot -> Intv (Fin 0, Fin 0)
      | _ -> Intv (Fin 0, Fin 1)

  end

  module Mem = struct
    type t = Val.t list option
    let pp fmt m =
      match m with
      | None -> Format.fprintf fmt "⊥"
      | Some lst ->
        Format.fprintf fmt "[";
        List.iteri (fun i v ->
          if i > 0 then Format.fprintf fmt "; ";
          Val.pp fmt v
        ) lst;
        Format.fprintf fmt "]"

    let abstract (m : S.Mem.t) : t =
      Some (List.map Val.abstract m)
    let read (m : t) (addr : Val.t) : Val.t =
      match m, addr with
      | None, _ | _, Bot -> Val.bot
      | Some m, Intv (l, u) ->
        let filter = match l, u with
          | Fin a, Fin b -> fun i -> a <= i && i <= b
          | Fin a, Inf -> fun i -> a <= i
          | Inf, Fin b -> fun i -> i <= b
          | Inf, Inf -> fun _ -> true
        in
        let candidates = List.filteri (fun i _ -> filter i) m in
        List.fold_left Val.join Val.bot candidates

    let write (m : t) (addr : Val.t) (v : Val.t) : t =
      match m, addr, v with
      | None, _, _ | _, Bot, _ | _, _, Bot -> None
      | Some m, Intv (l, u), v ->
        let sz = List.length m in
        let cnt, filter = match l, u with
          | Fin a, Fin b ->
              (Int.min sz b - Int.max 0 a + 1),
              fun i -> a <= i && i <= b
          | Fin a, Inf ->
              (sz - Int.max 0 a),
              fun i -> a <= i
          | Inf, Fin b ->
              (Int.min sz b + 1),
              fun i -> i <= b
          | Inf, Inf ->
              sz,
              fun _ -> true
        in
        if cnt = 0 then
          None
        else if cnt = 1 then
          Some (List.mapi (fun i old_v -> if filter i then v else old_v) m)
        else
          Some (List.mapi (fun i old_v -> if filter i then Val.join old_v v else old_v) m)

    let join (m1 : t) (m2 : t) : t =
      match (m1, m2) with
      | None, m | m, None -> m
      | Some m1, Some m2 ->
        Some (List.map2 Val.join m1 m2)

    let widen (mold : t) (mnew : t) : t =
      match (mold, mnew) with
      | None, m | m, None -> m
      | Some m1, Some m2 ->
        Some (List.map2 Val.widen m1 m2)

    let bot : t = None

    let leq (m1 : t) (m2 : t) : bool =
      match (m1, m2) with
      | None, _ -> true
      | _, None -> false
      | Some m1, Some m2 ->
        List.for_all2 Val.leq m1 m2
  end

  let filter_zero (v : Val.t) (m : Mem.t) : Mem.t =
    if Val.leq (Val.abstract 0) v then m else Mem.bot

  let filter_nonzero (v : Val.t) (m : Mem.t) : Mem.t =
    if Val.leq v (Val.abstract 0) then Mem.bot else m

end

let decode : Abstract.Mem.t -> Abstract.Val.t =
  fun m ->
    match m with
    | Some (_ :: v :: _) -> v
    | _ -> Abstract.Val.bot
