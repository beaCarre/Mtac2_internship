
(** module LITERAL : manipule les litéraux **)
module type LITERAL = 
sig
  type t (* le type du litéral *)
  val mk_not : t -> t (* négation *)
  val compare : t -> t -> int (* comparaison de deux litéraux *)
end


(** module FNC : décrit la formule et prend un litéral **)
module type FNC = 
sig
  type formule (* le type de la formule *)
  module L : LITERAL (* le litéral associé *)
  val make : formule -> L.t list list (* transformant la formule en liste de littéraux *)
end

(** module Sat : prend une FNC et définit les règles d'inférence **)
module Sat (Fnc : FNC) =
struct
  module L = Fnc.L
  module S = Set.Make(L)
  module M = Map.Make(L)

  exception Unsat of S.t (*  *)
  exception Sat
    
  type t = {gamma : S.t M.t ; delta : (L.t list * S.t) list} 

  (** dispatch :  **)
  let dispatch d = List.map (fun l -> l,d)

  (** assume : **)
  let rec assume env (l,d) = 
    if M.mem l env.gamma then env
    else bcp { gamma = M.add l d env.gamma ; 
	       delta = env.delta}

  (** bcp :  **)
  and bcp env =
    List.fold_left 
      (fun env (l,d) ->
	try 
	  let l = List.filter
	    (fun f -> 
	      if M.mem f env.gamma 
	      then raise Exit;
	      not (M.mem (L.mk_not f) env.gamma)
	    ) l
	  in 
	  match l with 
	      [] -> raise (Unsat d)
	    | [f] -> assume env (f,d)
	    | _ -> {env with delta = (l,d) :: env.delta}
	with Exit -> env
      )
      {env with delta=[]} env.delta
      
  (** unsat :  **)
  let rec unsat env =
    try
      match env.delta with
	  [] -> raise Sat
	| ([_],_ | [],_) :: _ -> assert false
	| (( a:: _),_) :: _ -> 
	  let d = 
	    try unsat (assume env (a,S.singleton a)) 
	    with Unsat d -> d
	  in
	  if not (S.mem a d) 
	  then d
	  else unsat (assume env (L.mk_not a, S.remove a d))
    with Unsat d -> d

  (** dpll :  **)
  let dpll f =
    try
      let _ =
	unsat (bcp {gamma = M.empty; delta = dispatch S.empty (Fnc.make f)})
      in false
    with Sat -> true | Unsat _ -> false

end
