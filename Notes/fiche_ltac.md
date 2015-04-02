
TACTIQUES LTAC :
================

******************************************************************************************

abstract *expr* [using *ident*] :
---------------------------------
Cr�e un lemme auxiliaire appel� curentgoal[|ident]_subproofn

******************************************************************************************

absurd *term* :
---------------
*term* est uen proposition P de type Prop. absurd applique False-elim 
qui g�n�re comme sous-buts de prouver par contradiction ~P et P.
Cette tactique est utiles dans les preuves par cas, lorsque certains
cas sont impossibles. 

******************************************************************************************

admit :
-------
Admet le but courant avec un axiom. Permet de sauter temporairement un
sous-but. 
*Print Assumptions* permet d'afficher les buts pas encore prouv�s.
Un sous-but admis est nomm� *ident_admittedn*.

******************************************************************************************

apply *term* :
-------------
Essaie de matcher le but courant avec le type de term.
Si �a match, cela retourne toutes les pr�misses (non
d�pendantes) du type de *term*, en sous-buts.
Sinon, si la conclusion est un type inductif isomorphe � un tuple, 
chaque �l�ment du tuple est r�cursivement match�.

La tactique d�pend d'une unification de premier-ordre avec types
d�pendants.
Sauf dans le cas o� la conclusion du type de *term* est de la forme
*(P t1 ... tn)*, avec *P* � instancier, 
si le but est de la forme *(fun x => Q) u1 ... un* et que *ti* et *ui*
s'unifient, alors *P* est pris pour �tre (fun x => Q).
Sinon elle essaie de d�finir *P* en abstrayant *t1...tn dans le but.

__apply *term* with *([ref1 :=] term1) ... ([refn :=] termn)* :__

apply, avec les valeurs pour instancier les pr�misses.

__eapply *term* :__

Comme apply, mais s'il n'y a pas d'instanciation d�ductible pour au moins l'une
des variables, ajoute des existencielles (de la forme ?n) encore � instancier.

__simple apply *term* :__

Comme apply, sans les conversions.

__apply *term* in *ident* :__

*ident* est une hypothese du contexte.
Cette tactique essaie de matcher la conclusion du type de *ident* avec
une premisse non-d�pendante du type de *term*.

La d�claration de l'hypoth�se *ident* est remplac�e par la conclusion
du type de *term*. La tactique retourne autant de sous-buts que le
nombre des pr�misses non-d�pendantes du type de *term* et des
pr�misses non d�pendantes du type de *ident*.

Si la conclusion du type de *term* ne matche pas le but et que la
conclusion est un type inductif isomorphe � un type tuple, alors le
tuple est r�cursivement d�compos�.

******************************************************************************************

assert ( [*ident* :] *form* ) :
-------------------------------
assert (H : U) ajoute une nouvelle hypoth�se de nom H, d�clarant U
comme but cournt, et ouvre un nouveau sous-but U2.

__assert *form* as *intro_pattern* :__

Si *intro_pattern* est une introduction de nom ( *?, ?ident*
ou un identifieur ), l'hypoth�se est nomm�e selon ce pattern. 

si *intro_pattern* est une introduction de disjonction/conjonction ( |,
',' ou & ), c'ets comme assert puis d�truit l'hypoth�se r�sultante e
utilisant cette introduction.

__assert *form* by *tactic* :__

Comme assert, mais applique *tactic* pour r�soudre le sous-but g�n�r�
par assert.

******************************************************************************************

assumption :
------------
Cherche dans le contexte local une hypoth�se dont le type est le m�me
que le but. Si la recherche a aboutit, le sous-but est prouv�.

__eassumption :__

Comme assumption mais peut g�rer les buts avec des meta-variables.

******************************************************************************************

auto :
------
Essaie de r�soudre le but courant � la prolog.
D'abord avec la tactique *assumption*, pui le r�duit � un but atomique
en utilisant intros et prenant ces nouvelles hypoth�ses comme des
indices. Apr�s il regarde la liste associ�e au symbol de t�te du but
et essaie de les appliquer. Puis on recommence.

Par d�faut auto utilise seulement les hypoth�ses du but courant et les
indices de la base de donn�e nomm�e "core".

__auto with *ident1 ... identn* :__

Comme auto, mais avec les indices *ident1 ... identn* en plus.

__auto using *lemma1, ... lemman* :__

Comme auto, mais avec les lemmes donn�s en plus.

******************************************************************************************

autorewrite with *ident1 ...identn* :
-------------------------------------
R��crit � partir de *ident1 ...identn*.
Chaque base de r�gles de r��criture *identi* est appliqu�e au sous-but
principal, jusqu'� ce que �a �choue. Si toutes les r�gles de la base
ont �t� ex�cut�es et que le sou-but a progress�, alors on les
r�ex�cute encore. S'il n'a pas progress�, on passe � la base suivante.

Les bases de r�gles de r��criture sont construite � partir de la
commande vernacular "Hint Rewrite".

Warning: Cette tactique peut boucler si on construit un syst�me de
r��criture qui ne termine pas.

__autorewrite with *ident1...identn* using *tactic* :__

Idem, mais on applique la tactique *tactic* apr�s chaque pas de
r��criture.

__autorewrite with *ident1...identn* in *qualid* :__

Idem, mais avec l'hypoth�se *qualid*.

******************************************************************************************
 
autounfold  with *ident1...identn* :
------------------------------------
D�roule les constantes d�clar�e par un "Hint Unfold". ??

******************************************************************************************

case *term* :
-------------
G�re les analyses par cas sans r�cursion, en utilisant un principe
d'�limination, non r�cursif, et pas en fonction des hypoth�ses. ??

__case *term* with *bindings_list* :__

Pour ajouter des instances explicites des premisses du type de *term*

******************************************************************************************

case_eq *term* :
----------------
Analyse par cas, mais retenir la forme de base du *term*, par egalit�
entre la forme de base et les r�sultats de l'analyse par cas.

******************************************************************************************

cbv *flag1...flagn* :
----------------------
call-by-value. (celle des langages ML: les arguments d'une fonction
appel�e sont d'abord �valu�s, en utilisant la r�duction faible).

Les flags sont *beta delta iota zeta*.
cbv. = cbv beta delta iota zeta.


******************************************************************************************

change *term* :
---------------
*change U* remplace la but courant T avec U, avec U bien form� et T et
U convertibles.

__ change *term1* with *term2* :__

remplace *term1* avec *term2*. Ils doivent �tre convertibles.

__ change *term1* at *num1...numi* with *term2* :__

remplace de la 1�re � la i-�me occurence de *term1* avec *term2*.

__ change *term1* in *ident* :__

applique change sur l'hypoth�se *ident*.

******************************************************************************************

classical_left, classical_right :
---------------------------------
Comme *left* et *right*, mais en logique classique.
Seulement sur disjonctions.

******************************************************************************************

clear *ident* :
---------------
Efface l'hypoth�se *ident* du contexte local du but courant.

__clearbody *ident* :__

*ident* doit �tre une d�finition locale.
*ident* devient alors une assumption.

__clear dependent *ident* :__

Efface aussi toute les hypoth�ses qui d�pendent de *ident*.

******************************************************************************************

cofix *ident* :
---------------
Lance une preuve par coinduction. *ident* est le nom de l'hypoth�se de
coinduction. 
La v�rification de la correction de son utilisation est faite au
moment de l'enregistrtement du lemme dans l'environnement.
Pour savoir si l'utilisation de l'hypoth�se de coinduction � un moment
donn� : *Guarded*.

******************************************************************************************

compare *term1* *term2* :
-------------------------
compare les deux objets d'un type de donn�es inductif.
Si G est le but courant, �a rend les deux sous-buts : 
*term1=term2 -> G* et *~term1=term2 -> G*.
Le type de *term1* et *term2*doivent satisfaire les m�me
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
V�rifie si les termes sont �gaux, modulo l'alpha conversions et les casts.

******************************************************************************************

constructor *num* :
-------------------
La conclusion du but doit �tre un type inductif I.
*num* doit �tre inf�rieur ou �gal au nombre de constructeur de I.
Equivalent � intros ; apply  (num-i�me constructeur de I).

******************************************************************************************

contradict *ident* :
--------------------
*ident* une hypoth�se H :

H:�A |- B devient |- A

H:�A |- �B devient H: B |- A

H: A |- B devient |- �A

H: A |- �B devient H: B |- �A 

******************************************************************************************

contradiction :
---------------
Cherche une hypoth�se dans le contexte qui est �quivalent � *False*.
Equivalent � *intros; elimtype False; assumption.*
 
******************************************************************************************

cut *form* :

cutrewrite -> *term1* = *term2* 

decide equality

******************************************************************************************

decompose *[qualid1...qualidn] term* :
--------------------------------------
D�compose r�cursivement une proposition complexe, pour obtenir un
proposition atomic.

******************************************************************************************

decompose record *term *:
-------------------------
D�ompose les types record (type inductif avec un constructeur,  comme
*and*, *exists* et les *Record*.

******************************************************************************************

decompose sum *term* :
----------------------
D�compose les types Somme (comme *or*).

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
*term* doit �tre un type inductif ou coinductif.
G�n�re un sous-but pour chaque constructeur du type.
Pas d'hypoth�se d'induction g�n�r�e.

Si l'argument ne d�pend pas de la conclusion ni d'une hypoth�se,
il est remplac� par la forme du constructeur appropri� dans chaques
sous-buts r�sultant. Si celle-ci est non-d�pendante, la structure
inductive ou co-inductive de l'argument est explos�e. 

Cas sp�ciaux :

* Si le *term* est un identifieur li� � une variable quantifi�e de la
  conclusion du but : *intros until ident; destruct ident*.

* Si le *term* est un num : *intros until num* puis *destruct* sur la
  derni�re hypoth�se introduite.

* Si le *term* est un pattern dont les trous sont "_", �a v�rifie que
  tous les sous-terms matchant le pattern dans la conclusion et dans
  les hypoth�ses soient compatibles, puis lance l'analyse par cas en
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
*term* doit �tre une type inductif. Le destructeur appropri� est
choisi selon le type du but, et l'applique avec *apply*.

Ex : Si le contexte de preuve contient *n:nat* et le but courant est *T*
de type *Prop*, *elim n* �quivaut � *apply nat_ind with (n:=n)*.

__elim *term1* using *term2* :__

Permet de donner un pr�dicat d'�limination explicite qui n'est pas le
standard

__elimtype *form* :__

*form* doit �tre inductif. *elimtype I* �quivaut � : "cut I. intro Hn;
 elim Hn; clear Hn." Hn n'apparait pas dans le contexte des sous-buts.

Si t est un term de type inductif I et qu'il n'apparait pas dans le
but, *elim t* �quivaut � *elimtype I; 2:exact t.* 



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
alors *exact p* r�ussit ssi T et U sont convertibles.

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
*term* doit �tre un type inductif.
G�n�re un sous-but pour chaque constructeur du type.

Si l'argument d�pend dans conclusion et dans des hypoth�ses,
il est remplac� par la forme du constructeur appropri� dans chaques
sous-buts r�sultant,  et les hypoth�ses d'inductions sont ajout�es au
contexte local.

Cas sp�ciaux :

* Si le *term* est un identifieur li� � une variable quantifi�e de la
  conclusion du but : *intros until ident; induction ident*.

* Si le *term* est un num : *intros until num* puis *induction* sur la
  derni�re hypoth�se introduite.

* Si le *term* est un pattern dont les trous sont "_", �a v�rifie que
  tous les sous-terms matchant le pattern dans la conclusion et dans
  les hypoth�ses soient compatibles, puis lance l'induction en
  utilisant ce pattern.


******************************************************************************************

injection :
-----------
bas�e sur le fait que les constructeurs de sets inductifs sont des
injections : si (c t1) et (c t2) sont deux termes �gaux, alors t1 et
t2 sont �gaux.

Si le term est une preuve d'une conclusion term1 = term2, alors
l'injection est appliqu�e aussi profond�ment que possible, pour
d�river l'�galit� de tous les sous-termes.

Ex : from (S (S n))=(S (S (S m))) we may derive n=(S m).

*term1* et *term2* doivent �tre des �l�ments d'un enxemble inductif,
 et doivent �tre ni �gaux.

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