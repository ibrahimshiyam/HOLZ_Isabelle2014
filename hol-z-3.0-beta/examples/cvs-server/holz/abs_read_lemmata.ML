(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_read_lemmata.ML --- 
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
(* $Id: abs_read_lemmata.ML 6746 2007-08-03 07:25:55Z brucker $ *)


(* ========================== *)

(* This file contains lemmata *)
(* for the induction step     *)
(* of the proof of the read   *)
(* property.                  *)

(* operations:                *)
(* abs_cd                     *)
(* abs_loginR                 *)
(* modifyR                    *)
(* abs_add                    *)

zgoal SysArchSec.thy "        \
\ (%Xi RepositoryState) =+=>  \
\ (wc = wc') =+=>             \
\ (wc, rep, rep_permtab)      \
\  : AReadProp_  =+=>         \
\ (wc', rep', rep_permtab')   \
\  : AReadProp_   ";
by(stripS_tac 1);
by(res_inst_tac [("t", "wc'"),
		 ("s", "wc")] subst 1);

ba 1;
by(res_inst_tac [("t", "rep'"),
		 ("s", "rep")] subst 1);
by(convert2hol_tac [XI_def] 1);
by(res_inst_tac [("t", "rep_permtab'"),
		 ("s", "rep_permtab")] subst 1);
by(convert2hol_tac [XI_def] 1);
ba 1;
qed"XiRepState_eqWc_implies_AReadProp_Invariant";


(* induction step for abs_loginR *)

zgoal SysArchSec.thy "        \
\  abs_loginR   =+=>          \
\ (wc, rep, rep_permtab)      \
\  : AReadProp_  =+=>         \
\ (wc', rep', rep_permtab')   \
\  : AReadProp_   ";
by(stripS_tac 1);
zbr XiRepState_eqWc_implies_AReadProp_Invariant 1;
ba 3;
zbr abs_loginR_Imp_thetaRepState 1;
ba 1;
zbd abs_loginR_invariant_wc 1;
ba 1;
qed"abs_loginR_AReadProp";


(* induction step for abs_cd  *)

zgoal SysArchSec.thy "        \
\  abs_cd       =+=>          \
\ (wc, rep, rep_permtab)      \
\  : AReadProp_  =+=>         \
\ (wc', rep', rep_permtab')   \
\  : AReadProp_   ";
by(stripS_tac 1);
zbr XiRepState_eqWc_implies_AReadProp_Invariant 1;
ba 3;
zbr abs_cd_implies_XiRepState 1;
ba 1;
zbd abs_cd_invariant_wc 1;
ba 1;
qed"abs_cd_AReadProp";

(* Lemma for ind-step on modifyR *)
zgoal SysArchSec.thy "        \
\ modifyR =+=>                \
\ (n, (wc' %^ n)) ~: Ainvents \
\ =+=>                        \
\ ((wc %^ n)=(wc' %^ n))";
by(stripS_tac 1);
br ccontr 1;
by(duplPrem "modifyR" 1);
zbd modifyR_implies_modify 1;
zbd modify_chWc_implies_fileq 1;
ba 1;
(* by(hyp_subst_tac 1); *)
zbd modifyR_wcDiff_Ainvents 1;
ba 1;
bd notE 1;
ba 1;
ba 1;
qed"modifyR_invariant_unInvData";


(* induction step for modifyR *)

zgoal SysArchSec.thy "        \
\ modifyR =+=>                \
\ (wc, rep, rep_permtab)      \
\  : AReadProp_  =+=>         \
\ (wc', rep', rep_permtab')   \
\  : AReadProp_ ";
by(stripS_tac 1);
(* exchange AReadProp in the goal *)
zbr replace_AReadProp 1;
zbd (modifyR_valid_AbsStateS
     ZRS
     AbsState_implies_ClientState
     ZRS
     type_wc) 1;
ba 1;
zbd (modifyR_valid_AbsStateS
     ZRS
     AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_rep) 1;
ba 1;
zbd (modifyR_valid_AbsStateS
     ZRS
     AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_repPtb) 1;
ba 1;
(* exchange AReadProp in the assumptions *)
br mp 1;
by(guidedAssumption ["AReadProp"] 2);
by(res_inst_tac [("t",
		  "(wc, rep, rep_permtab) : AReadProp_")] 
		subst 1);
br sym 1;
br instantiateARead_def 1;
(* set constraints from unfolding the prop *)
zbd (modifyR_valid_AbsState
     ZRS
     AbsState_implies_ClientState
     ZRS
     type_wc) 1;
ba 1;
zbd (modifyR_valid_AbsState
     ZRS
     AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_rep) 1;
ba 1;
zbd (modifyR_valid_AbsState
     ZRS
     AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_repPtb) 1;
ba 1;
br impI 1;
(* - replaced both occurences of   *)
(* AProp   ----                    *)
br ballI 1;
(* =============================== *)
(* case distinction:               *)
(* wc %^ n = wc' %^ n              *)
by(case_tac "wc %^ n = wc' %^ n" 1);
(* =============================== *)
(* 1. case: wc %^ n = wc' %^ n     *)
by(res_inst_tac [("s", "wc %^ n"), 
		 ("t", "wc' %^ n")] 
		subst 1);
ba 1;
(* l 24 *)
br mp 1;
zbr modifyR_implies_modify 2;
ba 2;
br impI 1;
zbd modifyR_implies_repPtab_invariant 1;
by(atomizePrem 1);


by(res_inst_tac [("t", "rep'"),
		 ("s", "rep")] 
		subst
		1 );
ba 1;
by(res_inst_tac [("t", "rep_permtab'"),
		 ("s", "rep_permtab")] 
		subst
		1 );
ba 1;
by(res_inst_tac [("x", "n")] 
		bspec 1);
ba 1;
br subsetD 1;
ba 2;
br equalityD2 1;
zbd modify_domWc_invariant 1;
ba 1;
(* =============================== *)
(* 2. case: wc %^ n ~= wc' %^ n    *)
br disjI1 1;
br ccontr 1;
zbd  modifyR_invariant_unInvData 1;
ba 1;
by(res_inst_tac [("P", 
		  "wc %^ n = wc' %^ n")] notE 1);
by(AtomizePremSolveAll);
qed"modifyR_AReadProp";



(* HH *)

(* induction step for abs_addR *)

zgoal SysArchSec.thy "        \
\ abs_addR =+=>               \
\ (wc, rep, rep_permtab)      \
\  : AReadProp_  =+=>         \
\ (wc', rep', rep_permtab')   \
\  : AReadProp_ ";
by(stripS_tac 1);
zbr replace_AReadProp 1;
(* Set Cons. *)
zbd (abs_addR_valid_AbsStateS
     ZRS
     AbsState_implies_ClientState
     ZRS
     type_wc) 1;
ba 1;
zbd (abs_addR_valid_AbsStateS
	 ZRS
	 AbsState_implies_repSC) 1;
ba 1;
zbd (abs_addR_valid_AbsStateS
	 ZRS
	 AbsState_implies_repPtabSC) 1;
ba 1;

(* /Set Cons. *)
br mp 1;
by(guidedAssumption ["AReadProp"] 2);
by(res_inst_tac [("t",
		  "(wc, rep, rep_permtab) : AReadProp_")] 
		subst 1);
br sym 1;
br instantiateARead_def 1;
(* Set Cons. *)
zbd (abs_addR_valid_AbsState
     ZRS
     AbsState_implies_ClientState
     ZRS
     type_wc) 1;
ba 1;
zbd (abs_addR_valid_AbsState
	 ZRS
	 AbsState_implies_repSC) 1;
ba 1;
zbd (abs_addR_valid_AbsState
	 ZRS
	 AbsState_implies_repPtabSC) 1;
ba 1;
(* /Set Cons. *)
br impI 1;
br ballI 1;
(* Case dist.: n in dom newfiles? *)
by(case_tac "n : dom newfiles_63" 1);
br disjI1 1;

zbd abs_addR_newfiles_Ainvents 1;
ba 1;
ba 1;
(* second case: n~: dom newfiles?*)
br mp 1;
zbd abs_addR_implies_abs_add 2;
by(guidedAssumption ["add"] 2);
zbd abs_addR_implies_repPtab_invariant 1;
br impI 1;
by(duplPrem "abs_add" 1);
zbd abs_add_invariant_wc 1;
ba 1;
ba 1;
by(atomizePrem 1);
by(hyp_subst_tac 1);
by(res_inst_tac [("t", "wc' %^ n"), 
		 ("s", "wc %^ n")] subst 1);
ba 1;
by(res_inst_tac [("A", "dom wc"),
		 ("x", "n")] bspec 1);
ba 1;
zbd abs_add_domWc 1;
by(AtomizePremSolveAll);
qed"abs_addR_AReadProp";


