(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_read_ci_lemmata.ML --- 
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
(* $Id: abs_read_ci_lemmata.ML 6746 2007-08-03 07:25:55Z brucker $ *)


(* The main part of this lemma consists of    *)
(* reusing the main Lemmata for the cases     *)
(* modified file and new file of the proof of *)
(* AWriteSec.                                 *)

(* The assumption Aservice-step could be      *)
(* concluded from abs_ciR but this is a proof *)
(* loop.                                      *)



zgoal SysArchSec.thy "(%theta AbsState'', %theta AbsState) :   \
\  AtransR                                                     \
\ =+=>                                                         \
\ (%theta AbsState'') : InitAbsState                           \
\ =+=>                                                         \
\   ((%theta AbsState, %theta AbsState') :                     \
\    {.AService @ (%theta AbsState, %theta AbsState').} )      \
\ =+=>                                                         \
\  abs_ciR                                                     \
\               =+=>                                           \
\ (wc, rep, rep_permtab)                                       \
\  : AReadProp_                                                \
\               =+=>                                           \
\  (wc', rep', rep_permtab')                                   \
\  : AReadProp_   ";

by(stripS_tac 1);
(* open the goal *)
(* exchange AReadProp in the goal *)
zbr replace_AReadProp 1;
zbd (abs_ciR_valid_AbsStateS
     ZRS
     AbsState_implies_ClientState
     ZRS
     type_wc) 1;
ba 1;
zbd (abs_ciR_valid_AbsStateS
     ZRS
     AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_rep) 1;
ba 1;
zbd (abs_ciR_valid_AbsStateS
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
zbd (abs_ciR_valid_AbsState
     ZRS
     AbsState_implies_ClientState
     ZRS
     type_wc) 1;
ba 1;
zbd (abs_ciR_valid_AbsState
     ZRS
     AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_rep) 1;
ba 1;
zbd (abs_ciR_valid_AbsState
     ZRS
     AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_repPtb) 1;
ba 1;
br impI 1;
(* - replaced both occurences of     *)
(* AProp   ----                      *)
br ballI 1;
by(case_tac "n : dom rep" 1);
(* fall1 :       n ~: dom rep *)
by(removeTheta_tac 2);
zbd (abs_ciR_implies_abs_ci
	 ZRS
	 abs_ci_invariant_wc) 2;
by(hyp_subst_tac 2);
zbd (removeTheta wc_Ainvents) 2;
by(convert2hol_tac []  2);
ba 2;
ba 2;
br disjI1 2;
ba 2;
(* fall2:       n : dom rep *)
br mp 1;
by(guidedAssumption ["n : dom wc'"] 2);
by(res_inst_tac [("t", "wc'"), 
		 ("s", "wc")] subst 1);
zbd (abs_ciR_implies_abs_ci 
	 ZRS 
	 abs_ci_invariant_wc) 1;
ba 1;
br impI 1;
by(res_inst_tac [("t", "rep_permtab' %^ n"), 
		 ("s", "rep_permtab %^ n")] subst 1);
zbd abs_ciR_implies_abs_ci 1;
zbr abs_ci_repPtab_invariant 1;
ba 2;
ba 1;

by(res_inst_tac [("t", "authtab %^ rep'"), 
		 ("s", "authtab %^ rep")] subst 1);
by(res_inst_tac [("x", "n"), ("A", "dom wc")] bspec 2);
ba 2;
ba 2;

zbd auth_invariant 1;
ba 1;
ba 1;
ba 1;

qed"abs_ciR_AReadProp";




(*
(* umstaendliche version *)
zgoal SysArchSec.thy "(%theta AbsState'', %theta AbsState) :   \
\  AtransR                                                     \
\ =+=>                                                         \
\ (%theta AbsState'') : InitAbsState                           \
\ =+=>                                                         \
\   ((%theta AbsState, %theta AbsState') :                     \
\    {.AService @ (%theta AbsState, %theta AbsState').} )      \
\ =+=>                                                         \
\  abs_ciR                                                     \
\               =+=>                                           \
\ (wc, rep, rep_permtab)                                       \
\  : AReadProp_                                                \
\               =+=>                                           \
\  (wc', rep', rep_permtab')                                   \
\  : AReadProp_   ";

by(stripS_tac 1);
(* open the goal *)
(* exchange AReadProp in the goal *)
zbr replace_AReadProp 1;
zbd (abs_ciR_valid_AbsStateS
     ZRS
     AbsState_implies_ClientState
     ZRS
     type_wc) 1;
ba 1;
zbd (abs_ciR_valid_AbsStateS
     ZRS
     AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_rep) 1;
ba 1;
zbd (abs_ciR_valid_AbsStateS
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
zbd (abs_ciR_valid_AbsState
     ZRS
     AbsState_implies_ClientState
     ZRS
     type_wc) 1;
ba 1;
zbd (abs_ciR_valid_AbsState
     ZRS
     AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_rep) 1;
ba 1;
zbd (abs_ciR_valid_AbsState
     ZRS
     AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_repPtb) 1;
ba 1;
br impI 1;
(* - replaced both occurences of     *)
(* AProp   ----                      *)
br ballI 1;
by(case_tac "n : dom rep'" 1);
(* first, remove case 4 : ---------  *)

by(asm_full_simp_tac (HOL_ss addsimps [AtransR_def]) 2);

bd zrtrancl_into_zrtrancl 2;
ba 2;
br disjI1 2;

zbr (removeTheta wc_Ainvents) 2;
by(convert2hol_tac [AtransR_def] 2);
by(convert2hol_tac [theta_def] 2);
ba 2;
ba 2;
(* Now, cases 1-3:  --------------- *)
(* by(filterPrems_drop ["AService"] 1); *)
(* needed for auth_invariant         *)

(* *)
by(case_tac "n : dom rep" 1);
(* case 1: new file --------------- *)

zbd rep_domDiff_implies_perm 2;
ba 2;
ba 2;
ba 2;
ba 2;
ba 2;
br disjI2 2;
ba 2;

by(case_tac "rep %^ n = rep' %^ n" 1);
(* case 2: modified file ---------- *)
zbd rep_fNeq_implies_perm 2;
(* uses: abs_ci_fNeq_permOrder *)
ba 2;
ba 2;
ba 2;
ba 2;
ba 2;
ba 2;
br disjI2 2;
ba 2;

(* case 3: invariant file --------- *)
(* use IV.                          *)
(* needed equalities:               *)
(* -------------------------------- *)
(*  a- wc = wc'                     *)
(*  b- rep_permtab %^ n =           *)
(*     rep_permtab' %^ n            *)
(*  c- rep %^ n = rep' %^ n         *)
(*  d- authtab %^ rep' =            *)
(*       authtab %^ rep             *)
(*                                  *)
(* a from Xi ClientState, b from    *)
(* abs_ci_repPtab_invariant         *)
(* c from assumption.               *)
br mp 1;
by(guidedAssumption ["n : dom wc'"] 2);
by(res_inst_tac [("t", "wc'"), 
		 ("s", "wc")] subst 1);
zbd (abs_ciR_implies_abs_ci 
	 ZRS 
	 abs_ci_invariant_wc) 1;
ba 1;
br impI 1;
by(res_inst_tac [("t", "rep_permtab' %^ n"), 
		 ("s", "rep_permtab %^ n")] subst 1);
zbd abs_ciR_implies_abs_ci 1;
zbr abs_ci_repPtab_invariant 1;
ba 2;
ba 1;

by(res_inst_tac [("t", "rep' %^ n"), 
		 ("s", "rep %^ n")] subst 1);
ba 1;
by(res_inst_tac [("t", "authtab %^ rep'"), 
		 ("s", "authtab %^ rep")] subst 1);
by(res_inst_tac [("x", "n"), ("A", "dom wc")] bspec 2);
ba 2;
ba 2;


(* ----------------  admin - equality ---- *)
(* br constAuthtab 1;*)
(* fst of four subgoals. *)

zbd auth_invariant 1;
ba 1;
ba 1;
ba 1;

(* Old version using the constraint in abs_ciR
by(duplPrem "abs_ciR" 1);
zbd abs_ciR_implies_abs_ci 1;
zbr unch_abs_cvsauth_implies_auth_invariant 1;
zbd (abs_ci_valid_AbsState
     ZRS
     AbsState_implies_RepositoryState
     ) 1;
ba 1;
zbr (abs_ci_valid_AbsStateS
     ZRS
     AbsState_implies_RepositoryState
     ) 1;
ba 1;

zbr abs_ciR_implies_repAuth_invariant 1;
ba 1;
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(convert2hol_tac [theta_def] 1);
*)
(* ----------------  admin - equality ---- *)

qed"abs_ciR_AReadProp";
*)
