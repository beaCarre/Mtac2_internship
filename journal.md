
********************************************************************************
REUNION : vendredi 27 mars
================================================================================
-> struct coq :
--------------
* kernel : "trusted base", partie critique, typecheck constr 
* parsing : vernacular, ltac, gallina
* printing : ast
* pretyping : inference sur evar
     * typing
     * check
     * reduction_ops (WH red) :
          * iota : destr / fix
	  * delta : derouler def globale
	  * zeta : derouler def locales
 	  * eta : f comme Kf.fx
	  * beta
* proofs : maintient etat de constr du terme de preuve
     * proofview (au dessus refiner)
          * voir "7 refinment primitives" !
	  * voir au dessus de "6 tactic monad"  
     * refiner 
* tactics (dont coretactics : tactiques de base de ltac)
* checker : deuxième checker
* toplevel : coqtop interactif
* stm : complement toplevel ( asynchrone des commandes toplevel)
* intf : communication coqide/coqtop
* dev
* plugins
* theories : lib de base de coq (arith etc)
* grammar : parser avant parser
* lib : modules ocaml en +, utiles pour coq
* library : traitement modules coq (.vo), logique, preuves, estensiosn de syntaxe

-> mtac2 :
----------
* run.ml : interprète de ltac
    -> run' (gamma : contexte, sigma : map evar, t : term coq qui produit l'ast de mtac)
    * reduire t pour faire apparaitre symbole de tête
      (constr n) : n-ième constr (mfix, mmatch etc)
      (nth n) : n-ième param du constructeur

-> à faire :
Lister toutes les tactiques de ltac (+ semantique) (+ reflechir en mtac2)

********************************************************************************




Du 19 au 27 mars
================================================================================
* // O'Jacaré
* finir lecture papier mtac
* installation mtac2





********************************************************************************
REUNION : jeudi 19 mars
================================================================================
* MTac2 : Permettrai d'avoir des fonctions partielles, terminaison si finit pas, ref...
    
    * pre-inference : vérifie avant si term de tactique complets ou pas grâce au contexte
      et si pas le cas, crée de nouveaux buts.
      
    * moteur de preuve : construction du terme de preuve

    * evar : ajoute une nouvelle definition dans le contexte dans le "proof flow" 
    ( = trou dans les termes de tactique)

    * proofview : preuve, qui evolue, et les mécanismes associés

* But ultime : se passer de ltac. Mais il faudrait pouvoir "mimer" toutes les tactiques de ltac en mtac

    -> les faire petit à petit

* changer "branchement" de mtac. Pour le moment, appelé lors de la pré-inférence de ltac.
    -> il faudrait pouvoir dire au début d'une preuve que ça ne va être que du mtac
    -> pour au final pouvoir se passer de ltac.

* ? traduction de mtac vers ltac par exemple (mtac t) -> (apply (run t)).
********************************************************************************





Du 11 au 18 mars
================================================================================
* lecture mtac

* avancé dans micro-sat en coq

* td et tp en coq





********************************************************************************
REUNION : mercredi 11 mars
================================================================================
* presentation sat-micro

* formalisation sat-micro en coq
    * fnc, literal, var (entier), dpll 
    * faire fonction courtes pour code propre et générique
    * pas forcément tout prouver

* continuer à lire papiers mtac2 !
********************************************************************************





Du 4 au 11 mars
================================================================================
* notes Sat-micro

* implémentation Sat-micro (DPLL+retour en arrière non chronologique)

* TP1, TP2 mpri_2-7-2

* TD1, TD2 Letouzey

* Lecture du chapitre 1 et 2 du cours de A. Miquel      
    (Preuves assistées par ordinateur)

* Lecture du papier de SAT-Micro





********************************************************************************
REUNION : mercredi 4 mars
================================================================================
* Changer format du journal (-> md)

* avancer sur SAT-Macro : 
    * préparer présentation de l'article 
    * implémenter en OCaml (plus tard en coq)
    
* Faire en // les td de Pierre Letouzet.
********************************************************************************
    
    
    

Du 2 au 4 mars
================================================================================
* lecture de *SAT-micro* commencée

* mise en place de la *fiche ltac*

* Qu'est-ce qu'une *tactique* ?
  -> une tactique réduit un but en un ou plusieur sous-but.

* Comment est structuré coq ?
    * *Gallina* = language de spécification
    * terme (Gallina) = programme 
     	   	      | propriété sur programme 
		      | preuve de propriété
    * term => Calculus of Inductive Constructions (CIC) 
    * assistant de preuve interactif
    * the vernacular = langage de commandes pour accéder
    * mode interactif vs mode compilé vs proofgeneral ...
    * 

* lecture de https://www.mpi-sws.org/~neelk/mtac.pdf
  -> Gros manque de connaissances 
  -> retour au Reference Manual de coq (https://coq.inria.fr/refman/index.html)

* depot créé, journal commencé.
    
    
    
********************************************************************************
REUNION : lundi 2 mars
================================================================================
* lire papiers (Mtac, SAT-micro, )
* créer dépôt sur github
* journal.txt à la racine du dépôt
    * faire le point sur chaque rdv
    * permet de garder une trace
    * suivi par l'encadrant
    * permet de reformuler pour assurer la comprehension
* maitriser coq :
    * ltac -> fiches sur chaque tactique + exemple(s)
* en || : SAT-solver (SAT-micro), pour application et maitrise de coq
  (voir proof-by-reflexion) problème NP-complet, déterminer si une
  formule propositionnelle est satisfiable, 
********************************************************************************
