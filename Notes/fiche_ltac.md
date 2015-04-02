
TACTIQUES LTAC :
================

******************************************************************************************

abstract *expr* [using *ident*] :
---------------------------------
Crée un lemme auxiliaire appelé curentgoal[|ident]_subproofn

******************************************************************************************

absurd *term* :
---------------
*term* est uen proposition P de type Prop. absurd applique False-elim 
qui génère comme sous-buts de prouver par contradiction ~P et P.
Cette tactique est utiles dans les preuves par cas, lorsque certains
cas sont impossibles. 

******************************************************************************************

admit :
-------
Admet le but courant avec un axiom. Permet de sauter temporairement un
sous-but. 
*Print Assumptions* permet d'afficher les buts pas encore prouvés.
Un sous-but admis est nommé *ident_admittedn*.

******************************************************************************************

apply *term* :
-------------
Essaie de matcher le but courant avec le type de term.
Si ça match, cela retourne toutes les prémisses (non
dépendantes) du type de *term*, en sous-buts.
Sinon, si la conclusion est un type inductif isomorphe à un tuple, 
chaque élément du tuple est récursivement matché.

La tactique dépend d'une unification de premier-ordre avec types
dépendants.
Sauf dans le cas où la conclusion du type de *term* est de la forme
*(P t1 ... tn)*, avec *P* à instancier, 
si le but est de la forme *(fun x => Q) u1 ... un* et que *ti* et *ui*
s'unifient, alors *P* est pris pour être (fun x => Q).
Sinon elle essaie de définir *P* en abstrayant *t1...tn dans le but.

__apply *term* with *([ref1 :=] term1) ... ([refn :=] termn)* :__

apply, avec les valeurs pour instancier les prémisses.

__eapply *term* :__

Comme apply, mais s'il n'y a pas d'instanciation déductible pour au moins l'une
des variables, ajoute des existencielles (de la forme ?n) encore à instancier.

__simple apply *term* :__

Comme apply, sans les conversions.

__apply *term* in *ident* :__

*ident* est une hypothese du contexte.
Cette tactique essaie de matcher la conclusion du type de *ident* avec
une premisse non-dépendante du type de *term*.

La déclaration de l'hypothèse *ident* est remplacée par la conclusion
du type de *term*. La tactique retourne autant de sous-buts que le
nombre des prémisses non-dépendantes du type de *term* et des
prémisses non dépendantes du type de *ident*.

Si la conclusion du type de *term* ne matche pas le but et que la
conclusion est un type inductif isomorphe à un type tuple, alors le
tuple est récursivement décomposé.

******************************************************************************************

assert ( [*ident* :] *form* ) :
-------------------------------
assert (H : U) ajoute une nouvelle hypothèse de nom H, déclarant U
comme but cournt, et ouvre un nouveau sous-but U2.

__assert *form* as *intro_pattern* :__

Si *intro_pattern* est une introduction de nom ( *?, ?ident*
ou un identifieur ), l'hypothèse est nommée selon ce pattern. 

si *intro_pattern* est une introduction de disjonction/conjonction ( |,
',' ou & ), c'ets comme assert puis détruit l'hypothèse résultante e
utilisant cette introduction.

__assert *form* by *tactic* :__

Comme assert, mais applique *tactic* pour résoudre le sous-but généré
par assert.

******************************************************************************************

assumption :
------------
Cherche dans le contexte local une hypothèse dont le type est le même
que le but. Si la recherche a aboutit, le sous-but est prouvé.

__eassumption :__

Comme assumption mais peut gérer les buts avec des meta-variables.

******************************************************************************************

auto :
------
Essaie de résoudre le but courant à la prolog.
D'abord avec la tactique *assumption*, pui le réduit à un but atomique
en utilisant intros et prenant ces nouvelles hypothèses comme des
indices. Après il regarde la liste associée au symbol de tête du but
et essaie de les appliquer. Puis on recommence.

Par défaut auto utilise seulement les hypothèses du but courant et les
indices de la base de donnée nommée "core".

__auto with *ident1 ... identn* :__

Comme auto, mais avec les indices *ident1 ... identn* en plus.

__auto using *lemma1, ... lemman* :__

Comme auto, mais avec les lemmes donnés en plus.

******************************************************************************************

autorewrite with *ident1 ...identn* :
-------------------------------------
Réécrit à partir de *ident1 ...identn*.
Chaque base de règles de réécriture *identi* est appliquée au sous-but
principal, jusqu'à ce que ça échoue. Si toutes les règles de la base
ont été exécutées et que le sou-but a progressé, alors on les
réexécute encore. S'il n'a pas progressé, on passe à la base suivante.

Les bases de règles de réécriture sont construite à partir de la
commande vernacular "Hint Rewrite".

Warning: Cette tactique peut boucler si on construit un système de
réécriture qui ne termine pas.

__autorewrite with *ident1...identn* using *tactic* :__

Idem, mais on applique la tactique *tactic* après chaque pas de
réécriture.

__autorewrite with *ident1...identn* in *qualid* :__

Idem, mais avec l'hypothèse *qualid*.

******************************************************************************************
 
autounfold  with *ident1...identn* :
------------------------------------
Déroule les constantes déclarée par un "Hint Unfold". ??

******************************************************************************************

case *term* :
-------------
Gère les analyses par cas sans récursion, en utilisant un principe
d'élimination, non récursif, et pas en fonction des hypothèses. ??

__case *term* with *bindings_list* :__

Pour ajouter des instances explicites des premisses du type de *term*

******************************************************************************************

case_eq *term* :
----------------
Analyse par cas, mais retenir la forme de base du *term*, par egalité
entre la forme de base et les résultats de l'analyse par cas.

******************************************************************************************

cbv *flag1...flagn* :
----------------------
call-by-value. (celle des langages ML: les arguments d'une fonction
appelée sont d'abord évalués, en utilisant la réduction faible).

Les flags sont *beta delta iota zeta*.
cbv. = cbv beta delta iota zeta.


******************************************************************************************

change *term* :
---------------
*change U* remplace la but courant T avec U, avec U bien formé et T et
U convertibles.

__ change *term1* with *term2* :__

remplace *term1* avec *term2*. Ils doivent être convertibles.

__ change *term1* at *num1...numi* with *term2* :__

remplace de la 1ère à la i-ème occurence de *term1* avec *term2*.

__ change *term1* in *ident* :__

applique change sur l'hypothèse *ident*.

******************************************************************************************

classical_left, classical_right :
---------------------------------
Comme *left* et *right*, mais en logique classique.
Seulement sur disjonctions.

******************************************************************************************

clear *ident* :
---------------
Efface l'hypothèse *ident* du contexte local du but courant.

__clearbody *ident* :__

*ident* doit être une définition locale.
*ident* devient alors une assumption.

__clear dependent *ident* :__

Efface aussi toute les hypothèses qui dépendent de *ident*.

******************************************************************************************

cofix *ident* :
---------------
Lance une preuve par coinduction. *ident* est le nom de l'hypothèse de
coinduction. 
La vérification de la correction de son utilisation est faite au
moment de l'enregistrtement du lemme dans l'environnement.
Pour savoir si l'utilisation de l'hypothèse de coinduction à un moment
donné : *Guarded*.

******************************************************************************************

compare *term1* *term2* :
-------------------------
compare les deux objets d'un type de données inductif.
Si G est le but courant, ça rend les deux sous-buts : 
*term1=term2 -> G* et *~term1=term2 -> G*.
Le type de *term1* et *term2*doivent satisfaire les même
restrictions.

******************************************************************************************

compute :
---------
comme cbv ??


******************************************************************************************

congruence :
------------
??

******************************************************************************************

constr_eq *term1* *term2* :
---------------------------
Vérifie si les termes sont égaux, modulo l'alpha conversions et les casts.

******************************************************************************************

constructor *num* :
-------------------
La conclusion du but doit être un type inductif I.
*num* doit être inférieur ou égal au nombre de constructeur de I.
Equivalent à intros ; apply  (num-ième constructeur de I).

******************************************************************************************

contradict *ident* :
--------------------
*ident* une hypothèse H :

H:¬A |- B devient |- A

H:¬A |- ¬B devient H: B |- A

H: A |- B devient |- ¬A

H: A |- ¬B devient H: B |- ¬A 

******************************************************************************************

contradiction :
---------------
Cherche une hypothèse dans le contexte qui est équivalent à *False*.
Equivalent à *intros; elimtype False; assumption.*
 
******************************************************************************************

cut *form* :

cutrewrite -> *term1* = *term2* 

decide equality

******************************************************************************************

decompose *[qualid1...qualidn] term* :
--------------------------------------
Décompose récursivement une proposition complexe, pour obtenir un
proposition atomic.

******************************************************************************************

decompose record *term *:
-------------------------
Déompose les types record (type inductif avec un constructeur,  comme
*and*, *exists* et les *Record*.

******************************************************************************************

decompose sum *term* :
----------------------
Décompose les types Somme (comme *or*).

******************************************************************************************

dependent destruction

dependent induction

dependent induction ... generalizing

dependent inversion

dependent inversion ... as 

dependent inversion ... as ... with

dependent inversion ... with

dependent inversion_clear

dependent inversion_clear ... as

dependent inversion_clear ... as ... with

dependent inversion_clear ... with

dependent rewrite ->

dependent rewrite <-


******************************************************************************************

destruct *term* :
-----------------
*term* doit être un type inductif ou coinductif.
Génère un sous-but pour chaque constructeur du type.
Pas d'hypothèse d'induction générée.

Si l'argument ne dépend pas de la conclusion ni d'une hypothèse,
il est remplacé par la forme du constructeur approprié dans chaques
sous-buts résultant. Si celle-ci est non-dépendante, la structure
inductive ou co-inductive de l'argument est explosée. 

Cas spéciaux :

* Si le *term* est un identifieur lié à une variable quantifiée de la
  conclusion du but : *intros until ident; destruct ident*.

* Si le *term* est un num : *intros until num* puis *destruct* sur la
  dernière hypothèse introduite.

* Si le *term* est un pattern dont les trous sont "_", ça vérifie que
  tous les sous-terms matchant le pattern dans la conclusion et dans
  les hypothèses soient compatibles, puis lance l'analyse par cas en
  utilisant ce pattern.

******************************************************************************************

discriminate

discrR

do

double induction

eapply

eapply ... in

eassumption

eauto

ecase

econstructor

edestruct

ediscriminate

eelim

eexact

eexists

einduction

einjection

eleft

******************************************************************************************

elim *term* :
-------------
*term* doit être une type inductif. Le destructeur approprié est
choisi selon le type du but, et l'applique avec *apply*.

Ex : Si le contexte de preuve contient *n:nat* et le but courant est *T*
de type *Prop*, *elim n* équivaut à *apply nat_ind with (n:=n)*.

__elim *term1* using *term2* :__

Permet de donner un prédicat d'élimination explicite qui n'est pas le
standard

__elimtype *form* :__

*form* doit être inductif. *elimtype I* équivaut à : "cut I. intro Hn;
 elim Hn; clear Hn." Hn n'apparait pas dans le contexte des sous-buts.

Si t est un term de type inductif I et qu'il n'apparait pas dans le
but, *elim t* équivaut à *elimtype I; 2:exact t.* 



******************************************************************************************

erewrite

eright

esimplify_eq

esplit

evar


******************************************************************************************

exact *term* :
--------------
Rend le term de preuve exact du but. T le but, p le *term* de type U,
alors *exact p* réussit ssi T et U sont convertibles.

******************************************************************************************

exfalso

******************************************************************************************

exists *bindings_list* :
------------------------
This applies only if I has a single constructor. It is then equivalent
to intros; constructor 1 with bindings_list. It is typically used in
the case of an existential quantification exists x, P(x). 

******************************************************************************************

f_equal

fail

field

field_simplify

field_simplify_eq

first

firstorder

firstorder tactic

firstorder using

firstorder with

fix

fold

fourier

functional induction

functional inversion

******************************************************************************************

generalize *term* :
-------------------
It generalizes the conclusion with respect to one of its subterms.
If the goal is G and t is a subterm of type T in the goal, then
generalize t replaces the goal by forall (x:T), G' where G' is
obtained from G by replacing all occurrences of t by x. The name of
the variable (here n) is chosen based on T. 

__generalize dependent :__

This generalizes term but also all hypotheses that depend on term. It
clears the generalized hypotheses.

******************************************************************************************


has_evar

hnf

idtac


******************************************************************************************

induction :
-----------
*term* doit être un type inductif.
Génère un sous-but pour chaque constructeur du type.

Si l'argument dépend dans conclusion et dans des hypothèses,
il est remplacé par la forme du constructeur approprié dans chaques
sous-buts résultant,  et les hypothèses d'inductions sont ajoutées au
contexte local.

Cas spéciaux :

* Si le *term* est un identifieur lié à une variable quantifiée de la
  conclusion du but : *intros until ident; induction ident*.

* Si le *term* est un num : *intros until num* puis *induction* sur la
  dernière hypothèse introduite.

* Si le *term* est un pattern dont les trous sont "_", ça vérifie que
  tous les sous-terms matchant le pattern dans la conclusion et dans
  les hypothèses soient compatibles, puis lance l'induction en
  utilisant ce pattern.


******************************************************************************************

injection :
-----------
basée sur le fait que les constructeurs de sets inductifs sont des
injections : si (c t1) et (c t2) sont deux termes égaux, alors t1 et
t2 sont égaux.

Si le term est une preuve d'une conclusion term1 = term2, alors
l'injection est appliquée aussi profondément que possible, pour
dériver l'égalité de tous les sous-termes.

Ex : from (S (S n))=(S (S (S m))) we may derive n=(S m).

*term1* et *term2* doivent être des éléments d'un enxemble inductif,
 et doivent être ni égaux.

******************************************************************************************

instantiate


******************************************************************************************

intro [*ident*] :
-----------------
If the goal is a product, the tactic implements the
"Lam" rule given in Section 4.21. 
If the goal starts with a let
binder, then the tactic implements a mix of the "Let" and "Conv". 

If the current goal is a dependent product forall x:T, U (resp let x:=t in
U) then intro puts x:T (resp x:=t) in the local context. The new
subgoal is U. 

If the goal is a non-dependent product T -> U, then it puts in the
local context either Hn:T (if T is of type Set or Prop) or Xn:T (if
the type of T is Type). The optional index n is such that Hn or Xn is
a fresh identifier. In both cases, the new subgoal is U. 

If the goal is neither a product nor starting with a let definition,
the tactic intro applies the tactic red until the tactic intro can be
applied or the goal is not reducible. 


__intro after :__

__intro at bottom :__

__intro at top :__

__intro before :__

__intros :__

__intros intro_pattern :__

__intros until :__


******************************************************************************************

intuition :
-----------


******************************************************************************************

inversion :
-----------

__inversion ... as :__

__inversion ... as ... in :__

__inversion ... in :__

__inversion ... using :__

__inversion ... using ... in :__

__inversion_clear :__

__inversion_clear ... as :__

__inversion_clear ... as ... in:__

__inversion_clear ... in :__


******************************************************************************************

is_var :
--------

is_evar :
---------

******************************************************************************************

lazy :
------

******************************************************************************************

left :
------


******************************************************************************************

legacy field

legacy ring

lia

lra

move

nia

nsatz

omega

pattern

pose

pose proof

progress

psatz

quote

red

refine

reflexivity

remember

rename

repeat

replace ... with

revert

revert dependent

rewrite

rewrite ->

rewrite <-

rewrite ... at

rewrite ... by

rewrite ... in

right

ring

ring_simplify

rtauto

set

setoid_replace

simpl

simpl ... in

simple apply

simple apply ... in

simple destruct

simple eapply ... in

simple induction

simple inversion

simple inversion ... as

simplify_eq

solve

specialize

split

split_Rabs

split_Rmult

stepl

stepr

subst

symmetry

symmetry in



tauto

timeout

transitivity

trivial

try



unfold

unfold ... in

unify



vm_compute