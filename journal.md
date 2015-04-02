

********************************************************************************
REUNION : jeudi 3 avril
================================================================================

********************************************************************************



Du 27 mars au 3 avril
================================================================================
* exos/tuto http://www.cis.upenn.edu/~bcpierce/sf/current/toc.html
* liste tactiques (avec compr�hension au passage) 


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
* checker : deuxi�me checker
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
* run.ml : interpr�te de ltac
    -> run' (gamma : contexte, sigma : map evar, t : term coq qui produit l'ast de mtac)
    * reduire t pour faire apparaitre symbole de t�te
      (constr n) : n-i�me constr (mfix, mmatch etc)
      (nth n) : n-i�me param du constructeur

-> � faire :
Lister toutes les tactiques de ltac (+ semantique) (+ reflechir en mtac2)

********************************************************************************




Du 19 au 27 mars
================================================================================
* // O'Jacar�
* finir lecture papier mtac
* installation mtac2





********************************************************************************
REUNION : jeudi 19 mars
================================================================================
* MTac2 : Permettrai d'avoir des fonctions partielles, terminaison si finit pas, ref...
    
    * pre-inference : v�rifie avant si term de tactique complets ou pas gr�ce au contexte
      et si pas le cas, cr�e de nouveaux buts.
      
    * moteur de preuve : construction du terme de preuve

    * evar : ajoute une nouvelle definition dans le contexte dans le "proof flow" 
    ( = trou dans les termes de tactique)

    * proofview : preuve, qui evolue, et les m�canismes associ�s

* But ultime : se passer de ltac. Mais il faudrait pouvoir "mimer" toutes les tactiques de ltac en mtac

    -> les faire petit � petit

* changer "branchement" de mtac. Pour le moment, appel� lors de la pr�-inf�rence de ltac.
    -> il faudrait pouvoir dire au d�but d'une preuve que �a ne va �tre que du mtac
    -> pour au final pouvoir se passer de ltac.

* ? traduction de mtac vers ltac par exemple (mtac t) -> (apply (run t)).
********************************************************************************





Du 11 au 18 mars
================================================================================
* lecture mtac

* avanc� dans micro-sat en coq

* td et tp en coq





********************************************************************************
REUNION : mercredi 11 mars
================================================================================
* presentation sat-micro

* formalisation sat-micro en coq
    * fnc, literal, var (entier), dpll 
    * faire fonction courtes pour code propre et g�n�rique
    * pas forc�ment tout prouver

* continuer � lire papiers mtac2 !
********************************************************************************





Du 4 au 11 mars
================================================================================
* notes Sat-micro

* impl�mentation Sat-micro (DPLL+retour en arri�re non chronologique)

* TP1, TP2 mpri_2-7-2

* TD1, TD2 Letouzey

* Lecture du chapitre 1 et 2 du cours de A. Miquel      
    (Preuves assist�es par ordinateur)

* Lecture du papier de SAT-Micro





********************************************************************************
REUNION : mercredi 4 mars
================================================================================
* Changer format du journal (-> md)

* avancer sur SAT-Macro : 
    * pr�parer pr�sentation de l'article 
    * impl�menter en OCaml (plus tard en coq)
    
* Faire en // les td de Pierre Letouzet.
********************************************************************************
    
    
    

Du 2 au 4 mars
================================================================================
* lecture de *SAT-micro* commenc�e

* mise en place de la *fiche ltac*

* Qu'est-ce qu'une *tactique* ?
  -> une tactique r�duit un but en un ou plusieur sous-but.

* Comment est structur� coq ?
    * *Gallina* = language de sp�cification
    * terme (Gallina) = programme 
     	   	      | propri�t� sur programme 
		      | preuve de propri�t�
    * term => Calculus of Inductive Constructions (CIC) 
    * assistant de preuve interactif
    * the vernacular = langage de commandes pour acc�der
    * mode interactif vs mode compil� vs proofgeneral ...
    * 

* lecture de https://www.mpi-sws.org/~neelk/mtac.pdf
  -> Gros manque de connaissances 
  -> retour au Reference Manual de coq (https://coq.inria.fr/refman/index.html)

* depot cr��, journal commenc�.
    
    
    
********************************************************************************
REUNION : lundi 2 mars
================================================================================
* lire papiers (Mtac, SAT-micro, )
* cr�er d�p�t sur github
* journal.txt � la racine du d�p�t
    * faire le point sur chaque rdv
    * permet de garder une trace
    * suivi par l'encadrant
    * permet de reformuler pour assurer la comprehension
* maitriser coq :
    * ltac -> fiches sur chaque tactique + exemple(s)
* en || : SAT-solver (SAT-micro), pour application et maitrise de coq
  (voir proof-by-reflexion) probl�me NP-complet, d�terminer si une
  formule propositionnelle est satisfiable, 
********************************************************************************
