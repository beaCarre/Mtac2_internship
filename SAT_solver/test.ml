open Dpll

module MyLiteral = 
struct 
  type t = int
  let mk_not b = -b
  let compare b1 b2 =
    compare b1 b2
end

module MyFnc = 
struct
  type formule = int list list
  module L = MyLiteral
  let make f = f
end

module MySat = Sat (MyFnc)

let _ =
   print_endline 
     (if MySat.dpll [[1;2;3];[-1;-2;-3]]
     then"OK"
     else "KO")
  
