open Dom
open Antp
open Antp_staged

let main () =
  let p : T.Pgm.t = [ Add 1; Mul 2; Add 3 ] in
  let i = Adom.Val.intv 10 12 in
  Format.printf "Running antp_mt0...";
  let res0 = antp_mt0 p i in
  Format.printf "antp_mt0: %a\n" Adom.Val.pp res0;
  Format.printf "Running antp_mt1...";
  let res1 = antp_mt1 p i in
  Format.printf "antp_mt1: %a\n" Adom.Val.pp res1

let () = main ()
