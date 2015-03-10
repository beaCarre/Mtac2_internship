
(** module LITERAL : manipule les lit�raux **)
module type LITERAL = 
sig
  type t (* le type du lit�ral *)
  val mk_not : t -> t (* n�gation *)
  val compare : t -> t -> int (* comparaison de deux lit�raux *)
end


(** module FNC : d�crit la formule et prend un lit�ral **)
module type FNC = 
sig
  type formule (* le type de la formule *)
  module L : LITERAL (* le lit�ral associ� *)
  val make : formule -> L.t list list (* transformant la formule en liste de litt�raux *)
end

(** module Sat : prend une FNC et d�finit les r�gles d'inf�rence **)
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
