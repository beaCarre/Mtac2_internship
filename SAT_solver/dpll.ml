(** module LITERAL : manipulant les litéraux **)
module type LITERAL = 
sig
  type t (* le type du litéral *)
  val mk_not : t -> t (* négation *)
  val compare : t -> t -> int (* comparaison de deux litéraux *)
end


(** module FNC : prenant un litéral **)
module type FNC = 
sig
  type formule (* le type de la formule *)
  module L : LITERAL (* le litéral associé *)
  val make : formule -> L.t list list (* transformant la formule en liste de littéraux *)
end


(** module Sat : prenant une FNC et définissant les règles d'inférence **)
module Sat (Fnc : FNC) =
struct
  exception Unsat (*  *)
  exception Sat

  module L : Fnc.L
  module S : Set.Make(L)
  type t = {gamma : S.t; delta : L.t list}

  let rec assume env l =
    if S.mem l env.gamma then env
    else bcp { gamma = S.add l env.gamma; delta = env.delat}

  and bcp env =
    List.fold_left 
      (fun env l ->
	try 
	  let l = List.filter
	    (fun f -> 
	      if S.mem f env.gamma 
	      then raise Exit;
	      not (S.mem (L.mk_not f) env.gamma)
	    ) l
	  in 
	  match l with 
	      [] -> rise Unsat
	    | [f] -> assume env f
	    | _ -> {env with delta = l :: env.delta}
	with Exit -> env
      )
      {env with delta=[]} env.delta
  
  let rec unsat env =
    try
      match env.delta with
	  [] -> raise Sat
	| ([_] | []) :: _ -> assert false
	| ( a:: _) :: _ -> 
	  (try unsat (assume env a) with Unsat -> ());
	  unsat (assume env (L.mk_not a))
    with Unsat -> ()

  let dpll f =
    try
      unsat (bcp {gamma = S.empty; delta = Fnc.make f}); false
    with Sat -> true | Unsat -> false

end
			     

	    
	  
    

      
