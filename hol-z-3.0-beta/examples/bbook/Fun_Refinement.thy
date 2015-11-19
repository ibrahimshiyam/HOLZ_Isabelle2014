(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * Fun_Refinement.thy --- 
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
(* $Id: Fun_Refinement.thy 8132 2008-06-16 12:25:34Z wolff $ *)

header{* Analysis by Functional Refinement *}

theory  Fun_Refinement
imports BBSpec

begin

section{* Setting up the functional refinement *}

text{* Now we set the default abstraction relation in the refinement package;
       this setting is a pre-requisite to the future
       generation of refinement related proof obligations.*} 

set_abs "Abs"[functional]

text{* At this place, we add the directive "[functional]" in order to
       indicate that the abstraction relation is in fact a function.

       This results in the additional proof obligation that the
       abstraction relation is in fact a function, but leads to
       simpler proof obligations over
       this abstraction relation later. 
*}


text{* Now comes the core of proof obligation
       generation based on the Forward-Simulation
       Refinement Method for Z (see Spivey's Book
       or "Using Z")*}
 
refine_init InitBirthdayBook InitBirthdayBook1
refine_op   AddBirthday      AddBirthday1

show_po Fun_Refinement.fwRefinementInit_BirthdayBook_1
show_po Fun_Refinement.fwRefinementOp_AddBirthday_2
list_po

show_po BBSpec.ccOp_AddBirthday_1 
        BBSpec.ccOp_AddBirthday1_1 
        BBSpec.ccState_BirthdayBook_1 
        BBSpec.ccState_BirthdayBook1_1
        Fun_Refinement.fwRefinementFunctional_Abs_1
        Fun_Refinement.fwRefinementOp_AddBirthday_1 
        Fun_Refinement.fwRefinementOp_AddBirthday_2 
        Fun_Refinement.fwRefinementInit_BirthdayBook_1

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


section{* Proof of Functionality of the Abstraction Relation *}

lemma lemma1: 
 "\<lbrakk> BirthdayBook1 (dates, hwm, names); i \<in> ( 1 \<upto> hwm); ia \<in> ( 1 \<upto> hwm); 
    names\<rappll>i\<rapplr> = names\<rappll>ia\<rapplr> \<rbrakk> 
  \<Longrightarrow> dates\<rappll>i\<rapplr> = dates\<rappll>ia\<rapplr>"
apply(zunfold BirthdayBook1_def, simp add: Z2HOL, clarify)
apply(case_tac "i=ia",auto)
done

lemma lemma2:
" (a \<in> (rel_appl names) ` (1 \<upto> hwm)) = (\<exists>i\<in>1 \<upto> hwm. names\<rappll>i\<rapplr> = a)"
apply(auto simp:Z2HOL)
done


po "Fun_Refinement.fwRefinementFunctional_Abs_1"
apply(zstrip)
apply(simp add:Z2HOL Ex1_def)
apply(rule_tac x="{(x,y).\<exists> i\<in> (1 .. hwm). x = names %^ i \<and> y = dates %^ i}" in exI)
apply(rule_tac x="(rel_appl names) ` (asSet(\<lambda>i. i : ( 1 .. hwm)))" in exI)
apply(zunfold Abs_def BirthdayBook_def)
apply(simp add: Z2HOL Ex1_def)
apply(safe, simp_all)
apply(simp only:pfun_def rel_def, auto intro!: lemma1)+
apply(subst ZFun.beta_apply_pfun[of _ NAME DATE]) 
prefer 3
apply(rule refl)
apply(auto)
apply(rule pfunI)
apply(simp add:rel_def)
apply auto
apply(auto intro!: lemma1)
prefer 2
apply(rule_tac t="dates %^ i" in subst)
prefer 2
apply(erule ZFun.rel_apply_in_rel,auto)
apply(drule_tac x=aa in eqset_imp_iff,auto)
apply(rule_tac x=x in bexI, auto)
discharged



section{* Proofs of the Init-Condition of the Refinement *}


(* dcpo_po  BBSpec.fwRefinementInit_BirthdayBook_1 *)
po Fun_Refinement.fwRefinementInit_BirthdayBook_1
txt{* To show: *}
txt{* @{subgoals} *}
txt{* We perform structural simplification by eliminating
      Schema-Calculus-Constructs.*}
apply zstrip
txt{* Now we follow the brute force approach: 
     unfolding all schema definitions \ldots *}
apply(zunfold InitBirthdayBook1_def InitBirthdayBook_def Abs_def BirthdayBook_def)
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

zlemma lemma3 : 
"BirthdayBook1 \<and> (\<forall> i\<in>1\<upto>hwm. name? \<noteq> (names\<rappll>i\<rapplr>)) \<longrightarrow> pre AddBirthday1"
txt{* We start with elementary Z-logical massage: *}
apply(zstrip, zintro_pre AddBirthday1_def)
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


zlemma lemma4 : "pre AddBirthday \<longrightarrow> name? \<notin> known"
by(zstrip,zelim_pre,zunfold AddBirthday_def,auto)



text{* here comes a structural proof for the first main goal: 
   use the above three Z-lemmas in order to reduce the main goal
   to the simplified version of it above. The technique
   applies the stripS converter to bring Z-lemmas on-thy-fly
   into HOL form and introduce them into the proof by Isabelle
   standard tactics. *}


po Fun_Refinement.fwRefinementOp_AddBirthday_1 
txt{* To show: *}
txt{* @{subgoals} *}
txt{* After structural normalization: *}
apply(zstrip, clarify)
txt{* \ldots we use the lemmas 1) to 3) by weakening assumptions
      and reducing conclusions. *}
apply(zrule lemma3,zdrule lemma4,zdrule Abs_def[zpred [1]])
apply(auto simp: Z2HOL)
discharged

section{* Proof of the Second Operation-Refinement-Condition *}

text{* To establish the second refinement condition, we need
       two auxilliary lemmas: *}


lemma lemma6:
"BirthdayBook (birthday, known) \<Longrightarrow> birthday : NAME \<pfun> DATE"
by(zstrip, zunfold BirthdayBook_def,simp add: Z2HOL)

text{* Notice that you actually \emph{can} use the ' symbol in the lexis;
       However, this works in the standard HOL parser and has nothing to
       do with the Z stroke convention ... *}
lemma lemma7:
"\<lbrakk> BirthdayBook (birthday, {a. \<exists>i\<in>1 \<upto> hwm. names\<rappll>i\<rapplr> = a});
    BirthdayBook (birthday'a, {a. \<exists>i\<in>1 \<upto> hwm'. names'\<rappll>i\<rapplr> = a});
    BirthdayBook1 (dates, hwm, names); BirthdayBook1 (dates', hwm', names');
    AddBirthday1 (dateI, dates, dates', hwm, hwm', nameI, names, names');
    BirthdayBook (birthday', known');
    \<forall>i\<in>1 \<upto> hwm. names\<rappll>i\<rapplr>  \<noteq>  nameI;
    birthday' = insert (nameI, dateI) birthday;
    \<forall>i\<in>1 \<upto> hwm. birthday %^ (names\<rappll>i\<rapplr>) = dates\<rappll>i\<rapplr>;
    \<forall>i\<in>1 \<upto> hwm'. birthday'a %^ (names'\<rappll>i\<rapplr>) = dates'\<rappll>i\<rapplr> \<rbrakk>
  \<Longrightarrow> \<dom> birthday'a = insert nameI (\<dom> birthday)"

apply(subgoal_tac "nameI ~: dom birthday")
apply(simp add: insert_is_pfun)
apply(zunfold BirthdayBook_def,simp add: Z2HOL)
apply((erule conjE)+, drule sym, simp) 
apply(zunfold AddBirthday1_def BirthdayBook1_def,simp add: maplet_def Z2HOL,clarify)
defer 1
apply(zunfold BirthdayBook_def,simp add: maplet_def Z2HOL,clarify)
apply(drule_tac t="dom ?Z" in sym)+
apply(simp,blast)

txt{* we reorient the two crucial equalities in the assumptions: *}
apply(thin_tac "?X")
apply(drule_tac t="dom ?Z" in sym)+
apply(rule set_ext, simp,safe,simp)
apply(case_tac "i=hwm+1",simp)
apply(rotate_tac -2)
apply(erule_tac x=i in ballE,simp)
txt{* ... which yields a contradiction *}
apply(simp add: zpred_def) 
apply(rule_tac x="hwm+1" in bexI,simp, simp, 
      simp add: numb_range_def in_naturals[symmetric])
apply(rule_tac x=i in bexI)
apply(thin_tac "ALL x:?S. ?P x")+
apply(thin_tac "?T = ?U")+
apply(subst oplus_by_pair_apply2, simp add: numb_range_def,simp)
apply(simp add: numb_range_def)
done

lemma lemma8:
"\<lbrakk> BirthdayBook (birthday, {a. \<exists>i\<in>1 \<upto> hwm. names %^ i = a});
    BirthdayBook (birthday'a, {a. \<exists>i\<in>1 \<upto> hwm. names' %^ i = a});
    BirthdayBook1 (dates, hwm, names); BirthdayBook1 (dates', hwm', names');
    AddBirthday1 (dateI, dates, dates', hwm, hwm', nameI, names, names');
    BirthdayBook (birthday', known');
    \<forall>i\<in>1 \<upto> hwm. names %^ i \<noteq>  nameI;
    birthday' = insert (nameI, dateI) birthday;
    \<forall>i\<in>1 \<upto> hwm. birthday %^ (names %^ i) = dates %^ i;
    \<forall>i\<in>1 \<upto> hwm'. birthday'a %^ (names' %^ i) = dates' %^ i; 
    i \<in> \<dom> birthday'a; \<dom> birthday'a = \<dom> (insert (nameI, dateI) birthday) \<rbrakk>
 \<Longrightarrow> birthday'a\<rappll>i\<rapplr> = insert (nameI, dateI) birthday\<rappll>i\<rapplr>"
apply(subgoal_tac "nameI ~: dom birthday")
apply(simp add: insert_is_pfun)
apply(zunfold BirthdayBook_def,simp add: Z2HOL)
apply((erule conjE)+, drule sym, simp) 
apply(zunfold AddBirthday1_def,zunfold BirthdayBook1_def,simp add: maplet_def Z2HOL,clarify)
defer 1
apply(zunfold BirthdayBook_def,simp add: maplet_def Z2HOL,clarify)
apply(drule_tac t="dom ?Z" in sym)+
apply(simp,blast)
apply(erule disjE, simp, (thin_tac "?T<:?S = ?U")+)
txt{* Case A: $i$ is equal to $hwm + 1$. Tis boils down to: *}
txt{* @{subgoals [goals_limit=1]} *}
apply(drule_tac x="nameI" in eqset_imp_iff) 
apply(simp,safe, thin_tac "?X")
apply(erule_tac x="hwm+1" and A="1..hwm +1" in ballE,simp)
apply(simp add: numb_range_def in_naturals[symmetric])
txt{* Case B: $i$ is less to $hwm + 1$, i.e. in the domain of $birthdaybook$: *}
txt{* @{subgoals [goals_limit=1]} *}
apply(thin_tac "?X", (thin_tac "?T \<dres>?S = ?U")+)
apply(drule_tac x=i in eqset_imp_iff) back
apply(simp, safe)
apply(rule_tac A="1 .. hwm+1" and x = i in ballE)
apply assumption 
apply(subgoal_tac "((names \<oplus> {(hwm + 1, nameI)})\<rappll>i\<rapplr>) = names\<rappll>i\<rapplr>", simp)
apply(subst oplus_by_pair_apply2)
apply(simp add: numb_range_def in_naturals[symmetric])
apply(rotate_tac 1)
apply(erule_tac x=i in ballE,simp,simp)
apply(subst oplus_by_pair_apply2)
txt{* The proof conclusion is somewhat messy. The proof state is so cluttered
      up with facts, that it takes the automated procedures quite some
      time wo find the contradiction here. Thinning the assumption lists 
      therefore greatly improves the proof speed. *}
apply((thin_tac "ALL x:?S. ?P x")+, (thin_tac "?T = ?U")+,(thin_tac "?X : ?Y \<fun> ?Z")+,
      simp add: numb_range_def in_naturals[symmetric], simp)
apply((thin_tac "ALL x:?S. ?P x")+, (thin_tac "?T = ?U")+,(thin_tac "?X : ?Y \<fun> ?Z")+,
      thin_tac "?X",thin_tac "?X",thin_tac "?X",thin_tac "?X", thin_tac "?X")
apply(simp add: numb_range_def in_naturals[symmetric])
done


po Fun_Refinement.fwRefinementOp_AddBirthday_2 
txt{* To show: *}
txt{* @{subgoals} *}
txt{* After structural simplification: *}
apply(zstrip, clarify, zelim_pre)
apply(zunfold Abs_def AddBirthday_def,
      simp_all add: Z2HOL rel_appl_norm maplet_def,clarify)
txt{* This leads to the proof-state presented in Spivey proof (pp. 141): *}
txt{* @{subgoals} *}
txt{* Now we apply, as suggested in pp. 14, the extensionality rule
      on partial functions: *}
apply(rule pfun_ext)
txt{* Extensionality works only under condition that 
      both sides are in fact partial functions. Spiveys proof
      misses this detail. *}
apply(erule lemma6)+
txt{* Now we reach the mail case distinction shown on page 14: 
      we have to show that both domains are equal, and that they
      are pointwise equal: *}
txt{* We first treat the domain equality: @{subgoals [goals_limit=1]} *}
apply(simp (no_asm)) 
apply(rule_tac birthday'="insert (name?, date?) birthday" in lemma7,simp_all)
txt{* Now comes the part with the pointwise argument: @{subgoals [goals_limit=1]} *}
apply(rule_tac birthday'a="birthday'a" and birthday'="insert (name?, date?) birthday" 
      in lemma8,simp_all)
discharged


section{* Global Checks *}

text{* Now we check that all refinement conditions have indeed
       been proven: *}

check_po except ccOp ccState

text{* This concludes the refinement proof based on Forward Simulation
       in the style of Spivey for the Birthdaybook example. *} 

end
