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
    type uop = Not

    type exp =
      | Int of int
      | Bop of bop * exp * exp
      | Uop of uop * exp
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
          let b_str =
            match b with Add -> "+" | Sub -> "-" | Mul -> "*" | Eq -> "=="
          in
          Format.fprintf fmt "(%a %s %a)" pp_exp e1 b_str pp_exp e2
      | Uop (u, e') ->
          let u_str = match u with Not -> "!" in
          Format.fprintf fmt "(%s%a)" u_str pp_exp e'
      | Read e' -> Format.fprintf fmt "M[%a]" pp_exp e'

    let rec pp_cmd fmt c =
      match c with
      | Skip -> Format.fprintf fmt "skip"
      | Write (e1, e2) -> Format.fprintf fmt "M[%a] := %a" pp_exp e1 pp_exp e2
      | Seq (c1, c2) -> Format.fprintf fmt "%a; %a" pp_cmd c1 pp_cmd c2
      | If (e, c1, c2) ->
          Format.fprintf fmt "if %a then %a else %a" pp_exp e pp_cmd c1 pp_cmd
            c2
      | While (e, c') -> Format.fprintf fmt "while %a do %a" pp_exp e pp_cmd c'
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

let intp_st : S.Pgm.t =
  Seq
    ( While
        ( Bop (Sub, Read (Int 0), Int 2),
          Write (Int 0, Bop (Add, Read (Int 0), Int 1)) ),
      While
        ( Read (Read (Int 0)),
          Seq
            ( If
                ( Bop (Eq, Read (Read (Int 0)), Int 1),
                  Write
                    ( Int 1,
                      Bop
                        ( Add,
                          Read (Int 1),
                          Read (Bop (Add, Read (Int 0), Int 1)) ) ),
                  If
                    ( Bop (Eq, Read (Read (Int 0)), Int 2),
                      Write
                        ( Int 1,
                          Bop
                            ( Mul,
                              Read (Int 1),
                              Read (Bop (Add, Read (Int 0), Int 1)) ) ),
                      Skip ) ),
              Write (Int 0, Bop (Add, Read (Int 0), Int 2)) ) ) )
