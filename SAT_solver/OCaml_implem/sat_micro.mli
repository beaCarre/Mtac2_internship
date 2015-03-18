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
  val make : formule -> L.t list list (* transformant la formule en liste de liste de litt�raux *)
end


(** module Sat : prend une FNC et d�finit les r�gles d'inf�rence **)
module Sat : functor (Fnc:FNC) ->
sig
  module L : LITERAL
  module S : Set.S
  type t  (* environnement *)
  val assume : t -> L.t -> t
  val bcp : t -> t
  val unsat : t -> unit
  val dpll : Fnc.formule -> bool
end
