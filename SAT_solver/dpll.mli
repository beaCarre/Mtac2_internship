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
  val make : formule -> L.t list list (* transformant la formule en liste de liste de littéraux *)
end


(** module Sat : prend une FNC et définit les règles d'inférence **)
module Sat : functor (Fnc:FNC) ->
sig
  module L : LITERAL
  module S : Set.S
  module M : Map.S
  type t  (* environnement *)
  val dispatch : S.t -> L.t list -> (L.t * S.t) list
  val assume : t -> L.t * S.t -> t
  val bcp : t -> t
  val unsat : t -> S.t
  val dpll : Fnc.formule -> bool
end
