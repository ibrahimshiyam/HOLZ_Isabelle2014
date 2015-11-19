(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * Rel_Refinement.thy --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 2000-2003 University Freiburg, Germany
 *               2003-2007 ETH Zurich, Switzerland
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
(* $Id: Rel_Refinement.thy 8130 2008-06-16 11:19:30Z wolff $ *)

header{* Analysis by Data (Relational) Refinement *}

theory  Rel_Refinement
imports BBSpec

begin

section{* Setting up the Relational Refinement *}

text{* Now we set the default abstraction relation in the refinement package;
       this setting is a pre-requisite to the future
       generation of refinement related proof obligations.*} 

set_abs "Abs"


text{* Now comes the core of proof obligation
       generation based on the Forward-Simulation
       Refinement Method for Z (see Spivey's Book
       or "Using Z")*}
 
refine_init InitBirthdayBook InitBirthdayBook1
refine_op   AddBirthday      AddBirthday1

show_po Rel_Refinement.fwRefinementInit_BirthdayBook_1
show_po Rel_Refinement.fwRefinementOp_AddBirthday_2
list_po

show_po BBSpec.ccOp_AddBirthday_1 
        BBSpec.ccOp_AddBirthday1_1 
        BBSpec.ccState_BirthdayBook_1 
        BBSpec.ccState_BirthdayBook1_1 
        Rel_Refinement.fwRefinementOp_AddBirthday_1 
        Rel_Refinement.fwRefinementOp_AddBirthday_2 
        Rel_Refinement.fwRefinementInit_BirthdayBook_1

text{* We perform a final check of the proof obligations; however, we filter
       out certain classes of proof-obligations. *}
 
check_po except ccOp ccState fwRefinementFunctional 
                fwRefinementOp fwRefinementInit

text{* In this example, we actually filter out \textbf{all} obligations.
*} 

text{* In contrast, the toplevel command:
\begin{verbatim}
check_po
\end{verbatim}
would result in a failure:
\begin{verbatim}
*** There are 7 unproven proof-obligations (can not ignore!). 
*** Check failed.
*** At command "check_po".
\end{verbatim}
*}




section{* Proofs of the Init-Condition of the Refinement *}


(* dcpo_po  BBSpec.fwRefinementInit_BirthdayBook_1 *)
po Rel_Refinement.fwRefinementInit_BirthdayBook_1
txt{* To show: *}
txt{* @{subgoals} *}
txt{* We perform structural simplification by eliminating
      Schema-Calculus-Constructs.*}
apply zstrip
txt{* Now we follow the brute force approach: 
     unfolding all schema definitions \ldots *}
apply(zunfold InitBirthdayBook1_def InitBirthdayBook_def
               Abs_def BirthdayBook_def)
txt{* Conversion to plain HOL and using the simplifier just
      finds the witness $(\{\},\{\})$ automatically. *}
apply(simp add: Z2HOL)
discharged


section{* Proof of the First Operation-Refinement-Condition *}


text{* In the following, we introduce three lemmas that allow the reduction
   of the first refinement condition to the simplified version above.

   We provide three auxilliary lemmas.

   \textbf{First}: the syntactic precondition over leagal states implies 
   the semantic precondition for AddBirthday1: *}

zlemma lemma1 : 
"BirthdayBook1 \<and> (\<forall> i\<in>1..hwm. name? \<noteq> (names\<rappll>i\<rapplr>)) \<longrightarrow> pre AddBirthday1"
txt{* We start with elementary Z-logical massage: *}
apply(zstrip,zintro_pre AddBirthday1_def)
apply(simp add: DECL_def DELTA_def, rule conjI)
txt{* \ldots and split the declarations from body. *}
txt{* In particular, we take the prescribed successor state 
      and propagate it in proof. *}
apply(rule_tac [2] conjI | rule_tac [2] refl)+
txt{* \ldots proves that the successor state fulfills state invariant. *}
apply(zunfold BirthdayBook1_def)
apply(simp add: Ball_def maplet_def zpred_def, auto)
txt{* \ldots does its best to make it simpler *}
txt{* auto reduces the proof to a "proof by contradiction" scheme ...
   Mostly, it has to do with 
   \begin{verbatim} 
          (names (+) {(hwm + 1, name?)}) %^ i =
          (names (+) {(hwm + 1, name?)}) %^ j;
   \end{verbatim}
   while we know that \verb+names %^ i ~= names %^ j+.
   We bring this goal in the end of the assumption list: *}   
apply(rotate_tac 1)
txt{* Now comes the proof idea: We split up a case-distinction tree
   for the cases that i and j refer to the new element \ldots
   \verb+rotate_tac+ brings these clauses in front in the assumption list
   and makes them visible for the rewriter. *}
apply(case_tac [1] "x=(hwm+1)")
apply(case_tac [1] "xa=(hwm+1)")
apply(case_tac [3] "xa=(hwm+1)")
txt{* Since we know already that \verb+i~=j+ and
    \verb+ALL i: #1 .. hwm. name? ~= names %^ i+, 
  these four cases can be reduced ad absurdum. *}
apply(auto simp: zpred_def)
done


text{* \textbf{Second}: The semantic precondition of the
   abstract operation implies syntactic precondition *}
zlemma lemma2 : "pre AddBirthday \<longrightarrow> name? \<notin> known"
by(zstrip,zelim_pre,zunfold AddBirthday_def,auto)


text{* here comes a structural proof for the first main goal: 
   use the above three Z-lemmas in order to reduce the main goal
   to the simplified version of it above. The technique
   applies the stripS converter to bring Z-lemmas on-thy-fly
   into HOL form and introduce them into the proof by Isabelle
   standard tactics. *}


po Rel_Refinement.fwRefinementOp_AddBirthday_1 
txt{* To show: *}
txt{* @{subgoals} *}
txt{* After structural normalization: *}
apply(zstrip, clarify)
txt{* \ldots we use the lemmas 1) to 3) by weakening assumptions
      and reducing conclusions. *}
apply(zrule lemma1,zdrule lemma2,zdrule Abs_def[zpred [1]])
apply(auto simp: Z2HOL)
discharged

section{* Proof of the Second Operation-Refinement-Condition *}

text{* To establish the second refinement condition, we need
       two auxilliary lemmas: *}

zlemma  lemma4:
" (AddBirthday \<and> Abs \<and> AddBirthday1) \<longrightarrow> 
   known` = {n. \<exists> i \<in> 1 .. hwm`. n = names` %^ i}"
txt{* After structural normalization \ldots *}
apply(zstrip, clarify)
txt{* \ldots we unfold the definitions: *}
apply(simp add: set_simps prod_simps Z2HOL AddBirthday_def AddBirthday1_def Abs_def
                BirthdayBook_def BirthdayBook1_def,clarify) 
apply(simp add: Dom_Union image_def asSet_def maplet_def)
txt{* We apply our main idea: 
      apply reasoning via set extensionality and split equivalence
      into both directions ... *}
apply(rule set_ext,simp,rule iffI)
txt{* Proof $\Longrightarrow$:*}
apply(erule disjE)
apply(rule_tac x="hwm+1" in bexI) 
apply(simp add: override_apply numb_range_mem in_naturals)
apply(rule numb_range_mem)
apply(simp_all add: in_naturals)
apply(erule bexE)
apply(rule_tac x=xa in bexI)
apply(subst override_apply2) 
apply(simp_all add: numb_range_def) 
txt{* Proof $\Longleftarrow$:*}
apply(erule exE)
apply(case_tac "i=hwm+1", simp)
apply(rule disjI2)
apply(rule_tac x=i in exI)
apply auto
done



zlemma lemma5 :
" (AddBirthday \<and> Abs \<and> AddBirthday1) \<longrightarrow>  
  (\<forall> i\<in>1 .. hwm`. birthday`%^(names`%^i) = dates`%^i)"
txt{* After structural simplification and unfolding definitions :*}
apply(zstrip, clarify)
apply(simp add: set_simps prod_simps Z2HOL AddBirthday_def AddBirthday1_def Abs_def
                BirthdayBook_def BirthdayBook1_def,clarify) 
apply(simp add: Dom_Union image_def asSet_def maplet_def)
txt{* we proceed by case distinction: either the
      accessed element is the last element: *}
apply(case_tac "i=hwm+1",auto)
txt{* \ldots or it is before. *} 
apply(subst dom_insert_apply)
apply(auto simp: zpred_def)
done

text{* By the way, the attribute zstip can also be used to
       convert a zlemma into a HOL-theorem, such that it is amenable
       to forward proof: *}

thm lemma5[zstrip]



po Rel_Refinement.fwRefinementOp_AddBirthday_2 
txt{* To show: *}
txt{* @{subgoals} *}
txt{* After structural simplification: *}
apply(zstrip, clarify)
apply(zelim_pre, zintro_sch_ex)
txt{* \ldots we use the equations to construct the trivial successor
      state. *}
apply(rule_tac [2] refl)
prefer 2 
(*apply(subgoal_tac "BirthdayBook(birthday_96,known_96)")*)
apply(subgoal_tac "BirthdayBook(birthday',known')")
apply(rotate_tac 1, assumption)
txt{* We have to prove:*}
txt{* @{subgoals} *}
txt{* \ldots which boils down to extracting this
      knowledge from schema $AddBirthday$:*}
apply(zunfold AddBirthday_def)
apply(tactic "full_expand_schema_tac [thm\"AddBirthday_def\"] 1") 
     (* must remain during reminiscent simplifications *)
apply(drule DECL_D1)
apply(simp add: Z2HOL)
txt{* Moreover, we have to prove:*}
txt{* @{subgoals} *}
txt{* The validity of the transition of $AddBirthday$ follows
      from the assumptions. *}
apply simp
txt{* It remains to show $Abs'$. We unfold several schemas:*}
apply(zunfold (0) Abs_def)
apply(rule DECL_I, zunfold Abs_def AddBirthday_def)
apply(drule DECL_D1) back
apply(simp add: set_simps prod_simps Z2HOL)
txt{* \ldots and achieve *}
txt{* @{subgoals} *}
txt{* For the latter, we simply apply lemmas 4) and 5). *}
apply(rule conjI)
apply(simp add: image_def asSet_def maplet_def)
apply(zrule lemma4, auto)
apply(zrule lemma5, auto)
discharged

section{* Global Checks *}

text{* Now we check that all refinement conditions have indeed
       been proven: *}

check_po except ccOp ccState

text{* This concludes the refinement proof based on Forward Simulation
       in the style of Spivey for the Birthdaybook example. *} 

end
