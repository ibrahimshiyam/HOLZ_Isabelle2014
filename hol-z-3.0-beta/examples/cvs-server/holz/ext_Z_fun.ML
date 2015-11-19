(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ext_Z_fun.ML --- 
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
(* $Id: ext_Z_fun.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* some abbreviations which ease *)
(* using z specific lemmata.     *)

(* still experimental: beta contraction, split translation *)
(* [--> automatic removal of induction-introduction-case]  *)

fun contractVec i 
  = 
  (asm_full_simp_tac 
       (HOL_ss addsimps 
	       [split_def, theta_def, fst_conv, snd_conv])) i;

(* develop function which allows canonized *)
(* treatment of schemata:                  *)
(* eg. SNAME_def, or:                      *)
(* InitabsState1 ==> InitAbsState (?x21, ?x34, ?x32, wc, ?x17, ?x15) *)

(* status: still exploring. Not sure wether it is really useful.
Maybe should be implemented as a tactic?
fun canonizeSchema x 
  = (asm_full_simplify (HOL_ss addsimps[SNAME_def]) x);
*)
fun removeSNAME x 
  = (asm_full_simplify (HOL_ss addsimps[SNAME_def]) x);

val removeSNAME_tac  
  = fn i => (asm_full_simp_tac (HOL_ss addsimps[SNAME_def]) i);

(* set up some additional search *)
(* functionality.                *)

(* think of findI modulo stripS  !  *)

(* ... think of better schema which *)
(* more comfortably and obviously ( *)
(* concerning restriction           *)
(* functionality) allows querying.  *)

fun fstIsMatch aStringList (aName, aThm) 
  = exists (fn x => (isSubstringOf x aName)) aStringList;

(* search and/restrictive wrt. aStringList *)

fun sndIsMatch aStringList (aName, aThm) 
  =
  let 
      val thmString = (string_of_thm aThm);
  in
     ( forall (fn x => isSubstringOf x (thmString)) aStringList)
  end;

fun findByName_thy aStringList aThy
	       = filter (fstIsMatch aStringList) (thms_of aThy);

fun findByName aStringList
	       = (findByName_thy aStringList thy);

fun findByThy aThy = (thms_of aThy);

fun getThmNames_of_Thy aThy = map fst (thms_of aThy);

(* restrict search on thms containing *)
(* certain strings (wrt. the pretty   *)
(* printing mechanism of isabelle)    *)

fun thms_of_thy_substr aStringList aThy
  = filter (sndIsMatch aStringList) (thms_of aThy);

(* sample for usage:              *)
(* 
> findByName_thy ["modify"] SysArchSec.thy;
val it =
   [("SysArchSec.modifyR_def",
         "modifyR ==
            modify /\ +..
             filename? : Abs_Name; newData? : Abs_Data
            |--
             filename? |--> newData? : Ainvents
            -.."),
      ("SysArchSec.modifyR_implies_repPtab_invariant",
         "|- modifyR =+=> rep_permtab = rep_permtab' /\ rep = rep'"),
      ("SysArchSec.modifyR_implies_rep_invariant",
         "|- modifyR =+=> rep = rep'"),
      ("SysArchSec.modifyR_invariant_absPwd",
...
*)

(* imported from Isabelle2002 *)

(*instantiate variables in the whole state*)
val instantiate_tac = PRIMITIVE o read_instantiate;

(* the sorry tactic. Dont use too *)
(* frequently.                    *)
(* Disadvantage: uses False as    *)
(* assumption!                    *)
(* qed will complain.             *)

fun sorry i = 
    (br ((assume_ax thy "False") RS FalseE) i);

fun sqed aString = bind_thm(aString, (uresult()));

(* A simple atomizer function.        *)
(* Maybe create a more common version *)
(* of it lateron.                     *)
(* Be sure you really want to remove  *)
(* the ex. quant. in the premises.    *)

(* fast_tac (empty_cs addSEs [conjE]) *)
(* only succeeds if it solves the goal*)
(* unlike atomization!                *)
(* by (safe_tac (empty_cs addSEs [conjE])) ; *)
(* ... does something similar! (but on all subgoals? *)

fun atomizePrem_ex i = 
    (REPEAT 
	 (
	  (etac exE i)
	      ORELSE
	      (etac bexE i)
	      ORELSE
	      (etac conjE i)
	      ));

(* Makes a nice proof-finish.         *)

val AtomizePremSolveAll = ALLGOALS (fn i => (atomizePremSolve i));

(* still experimental *)
fun simpleDivideCases i =
    (REPEAT
	 ((etac disjE i)
	      THEN
	      (defer_tac i))
	 );


(* duplicate assumption *)
(* /use string match    *)

fun duplPrem aString i =
    (
     (rtac mp i)
     THEN
     (guidedAssumption [aString] (i+1))
     THEN
     (rtac impI i)
     );

(* make a projection from *)
(* the assumptions/use    *)
(* string match           *)

fun projectPrems aStringList i =
    (
     (atomizePrem i)
	 THEN
	 (filterPrems_keep aStringList i)
     );


(* Ideas for future extensions *)
(*  of isabelle/HOL-Z :        *)
(*                             *)
(* - proof repair template:    *)
(* allow adding assumptions    *)
(* without destroying an       *)
(* existing proof pattern      *)
(* not sure: explore wether    *)
(* this could also be handled  *)
(* using assume_ax?            *)
(*                             *)
(* - provide more comfort for  *)
(* interactive TP: allow the   *)
(* user to introduce labels in *)
(* proof states and to jump to *)
(* those labels.               *)
(*                             *)
(* - extend lemma search       *)
(* functionality               *)
(*                             *)
