(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * AbsOperations.ML --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 2000-2003 University Freiburg, Germany
 *
 * HOL-Z is free software; you can redistribute it and/or modify it under   
 * the terms of the GNU General Public License as published by the Free       
 * Software Foundation; either version 2 of the License, or (at your option)  
 * any later version.                                                         
 *                                                                            
 * HOL-Z is distributed in the hope that it will be useful, but WITHOUT ANY 
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS 
 * FOR A PARTICULAR PURPOSE. See the GNU General Public License for more 
 * details.                                                              
 *                                                                            
 * You should have received a copy of the GNU General Public License along    
 * with this program; if not, write to the Free Software Foundation, Inc.,    
 * 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.                  
 ******************************************************************************)
(* $Id: AbsOperations.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* General setup of AbsOperations *)
open AbsOperations;

toToplevel axdefs; 
toToplevel schemes;



(* This function shall keep the basic    *)
(* instructions which are normally       *)
(* always executed at the beginning of a *)
(* DF - proof.                           *)
(* Actions like stripping off schema     *)
(* quantification and atomization of the *)
(* assumptions of the deadlock freeness  *)                 
(* proof-obligations are carried out     *)
(* here.                                 *)

fun openDFobligation nameOfDef = ((stripS_tac 1) 
			    THEN 
			    (intro_pre_tac [nameOfDef] 1)
			    THEN
			    (etac DECL_E 1)
			    THEN
			    (REPEAT (etac conjE 1))
			     );

(* atomize assumptions *)

(* These functions simplify the last     *)
(* few steps on goals like they typically*)
(* appear, dealing with metavariables and*)
(* z-goals.                              *)

(* atomize assumptions *)

fun atomizePrem i = (REPEAT (etac conjE i));

fun atomizePremSolve i = (atomizePrem i)
			     THEN
			     TRY(assume_tac i);



(* maybe two main functions:             *)
(* one to atomize into subgoals          *)
(* another one to try ba/refl and so on. *)
(* first shall be always correct, second *)
(* only for the trivial                  *)
(* df-proof-obligations.                 *)


(* first, atomize goals *)

val atomizeSubgoals = (REPEAT (
			  SOMEGOAL(fn x => (rtac conjI x))));

val rewrAtomSubgoals = ((rewrite_goals_tac [XI_def, 
					    DELTA_def,
					    theta_def, 
					    DECL_def])
			 THEN(atomizeSubgoals));

fun reflexN x = (rtac refl x);

fun trivN i = (assume_tac i ORELSE reflexN i);

val trivAll = (REPEAT( SOMEGOAL trivN));

(* try refl on any goal *)
(* , also ba            *)

val eraseTrivialsRiscy = (
			  (rewrAtomSubgoals) 
			      THEN
			      (trivAll)
			      );

(* first only use convert2hol_tac to *)
(* solve (not to simplify) subgoals. *)
  

fun APP_IF_BETTER tac i thm = 
   ((tac i) 
	THEN 
	(COND 
	     (has_fewer_prems (nprems_of thm)) 
	     all_tac 
	     no_tac)) thm;


fun do_improve thms = TRYALL( APP_IF_BETTER (convert2hol_tac thms));

 	


(* ******************************************************************** *)
(*  									*)
(* 	Lemmas good for Deadlockfreeness				*)
(*  									*)
(* by Harald Hiss	         					*)
(*  									*)
(* ******************************************************************** *)



goal thy "!!A B. [| A : X <--> Y; B : X <--> Y |] ==> A (+) B : X <--> Y";
by(convert2hol_tac[func_overrid_def, Un_def, rel_def] 1);
auto();
qed"oplMem";


goal thy "!! A B. [| A : T; B : T; T = X <--> Y |] ==> (A Un B) : T";
auto();
by(convert2hol_tac [Un_def, rel_def] 1);
auto();
qed"unMem";


goal thy "!! A B. [| A : T; B : T ; T = X <--> Y |] ==> (A (+) B) : T";
auto();
br oplMem 1;
ba 1;
ba 1;
qed"oplMemSubst";


goal thy "!! x y . [| T = A <--> B ; f: T ; x: A ; y:B |] ==> (f (+) {x |--> y}) : T";
auto();
br oplMemSubst 1;
ba 1;
br refl 2;
by(convert2hol_tac [maplet_def, rel_def] 1);
auto();
qed"oplMemSubstSingleton";


goal thy "!! A B . [| A : T; B : T; T = X -|-> Y |] ==> A (+) B : T";
auto();
qed"pfunOplDomSubst";

goal thy "!! A B . [|B : T; T = X -|-> Y |] ==> A <: B : T";
by(convert2hol_tac [dom_restr_def, partial_func_def, rel_def] 1);
auto();
qed"domRestr_inDom";

(* Lemmas to handle equations *)
(* using Un and (+)           *)

zgoal thy "dom (A (+) B) = (dom A) Un (dom B)";
auto();
qed"oplDomUn";

zgoal thy "dom (A (+) B) Un dom C = (dom (A) Un dom (B)) Un dom (C)";
auto();
qed("oplDomUnMultiple");

zgoal thy "(dom (A) Un dom (B)) Un dom (C) = dom (B) Un (dom (A) Un dom (C))";
auto();
qed("DomUnMultipleKomm");

zgoal thy " A = B =+=> C Un A = C Un B";
auto();
qed"eqWithUnion";

zgoal thy "A Un B = B Un A";
auto();
qed"UnKomm";

zgoal thy
"x ~: dom B =+=> (A (+) B) %^ x = A %^ x";
auto();
qed"applOpl";

zgoal thy
"(R:T)/\\(T = x -|-> Y) =+=> ((A <: R) : T)";
by(stripS_tac 1);
by(convert2hol_tac[partial_func_def, rel_def, dom_restr_def] 1);
auto();
qed"domRestrDistr";

val domRestrDistrS = (stripS domRestrDistr);
