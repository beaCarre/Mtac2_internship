Require Import List.
Require Import Bool.


(** type LITERAL : manipule les litéraux **)
Module Type LITERAL. 
  Require Import FSets.
  Parameter t:Set.
  Parameter mk_not: t -> t. 
  Axiom mk_not_invol : forall l:t, mk_not (mk_not l ) = l.
  Parameter eq :  t -> t -> Prop.
  Parameter lt :  t -> t -> Prop.
  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
End LITERAL.

Module Type FNC.
  Require Import FSets.
  Declare Module L: LITERAL.
  Parameter formule:Set.
  Declare Module LSet : FSetInterface.S with Module E := L.
  Declare Module CSet : FSetInterface.S with Module E := LSet.
  Parameter make : formule -> CSet.t .
End FNC.


Module Sat (Fnc:FNC).
  Import Fnc.
  Record env := {gamma : LSet.t ; delta : CSet.t }.

  Inductive derivable : env -> Type :=
  | DAssume : forall (e:env) (l:L.t), 
               CSet.In (LSet.singleton l) e.(delta) -> 
               derivable {| gamma:= LSet.add l e.(gamma) ; delta:= CSet.remove (LSet.singleton l) e.(delta)|}
  | DUnsat : forall (e:env) (l:L.t), 
              derivable {|gamma:=LSet.add l e.(gamma) ;delta:=e.(delta)|} -> 
              derivable {|gamma:=LSet.add (L.mk_not l) e.(gamma) ;delta:=e.(delta)|} 
  | DBcpRed : forall (e:env) (l:L.t) (C:LSet.t),              
                LSet.In l e.(gamma)-> LSet.In l C -> CSet.In C e.(delta) ->
                derivable {|gamma:=e.(gamma) ;delta:= CSet.remove C e.(delta)|} -> 
                derivable {|gamma:=e.(gamma) ;delta:=e.(delta)|}
  | DBcpElim : forall (e:env) (l:L.t) (C:LSet.t),              
                LSet.In l e.(gamma)-> LSet.In (L.mk_not l) C -> CSet.In C e.(delta) ->
                derivable {|gamma:=e.(gamma) ;delta:= CSet.add (LSet.remove (L.mk_not l) C) e.(delta)|} -> 
                derivable {|gamma:=e.(gamma) ;delta:=e.(delta)|}               
  | DConflict : forall (e:env),
                 CSet.In LSet.empty e.(delta) ->
                 derivable {|gamma:=e.(gamma) ;delta:=e.(delta)|}.

Check derivable {|gamma:= LSet.empty ; delta := CSet.empty|}.
Check derivable_ind.
Check derivable_rec.
  Check derivable_rect.

  Parameter model : L.t -> Prop.

  Axiom safe_model : forall (l:L.t), model l  <->  ~(model (L.mk_not l)).

  Check model.

  Definition sat_clause  (C : LSet.t) : Prop :=
    exists l:L.t , LSet.In l C -> model l .

  Definition sat_goal (D : CSet.t) : Prop :=
    forall C:LSet.t, CSet.In C D -> sat_clause C.

  Definition unsatisfiable (D : CSet.t) :=
    ~sat_goal D.

  Definition submodel (G : LSet.t) :=
forall l:L.t, LSet.In l G -> model l.

  Definition incompatible (e : env) : Prop := 
    submodel e.(gamma) -> ~sat_goal e.(delta).

  Check derivable.
  Check incompatible.
  Check incompatible{|gamma:= LSet.empty ; delta := CSet.empty|} .
  Check derivable {|gamma:= LSet.empty ; delta := CSet.empty|}.

  Theorem soundness :
    forall S : env, derivable S -> incompatible S.
  Admitted.
    


Theorem completeness : 
  forall S : env, incompatible S -> derivable S.
 Admitted.


  Inductive Res : Type :=
    Sat : LSet.t -> Res
  | Unsat.
  
  
  (* Fixpoint proof_search (e : env) n { struct n } : Res := *)
  (*   match n with *)
  (*     | O => Sat LSet.empty  (* Absurd case *) *)
  (*     | S n 0 => *)
  (*         if e.(delta) = CSet.empty *)
  (*         then Sat e.(gamma) (* Model found! *) *)
  (*         else *)
  (*           if Cset.In LSet.empty e.(delta) *)
  (*           then Unsat       (* Rule AConflict *) *)
  (*           else ... end . *)


(* Theorem proof_unsat : *)
(* forall n S, proof_search S n = Unsat => derivable S. *)
  
  



End Sat.

