Require Import List.

(** type LITERAL : manipule les litéraux **)
Module Type LITERAL.
  Parameter t:Set.
  Parameter mk_not: t -> t. 
  Parameter compare : t -> t -> nat.
End LITERAL.

Module Type FNC.
  Declare Module L: LITERAL.
  Parameter formule:Set.
  Parameter make : formule -> list (list L.t) .
End FNC.

Module Sat (Fnc:FNC).
  Import Fnc.
  Record env := {gamma : list Fnc.L.t ; delta : list (list Fnc.L.t) }.

  Definition dpll (e:env) : Set :=
    
  
  



End Sat.

