(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * owner_inRep_implies_perm.ML --- 
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
(* $Id: owner_inRep_implies_perm.ML 6746 2007-08-03 07:25:55Z brucker $ *)


zgoal thy "                                                     \
\ (? aid : dom abs_passwd .                                     \
\  (rep_permtab, rep, abs_passwd, file, aid  ) : has_access_ )  \
\ =+=>                                                          \
\ (%theta AbsState'', %theta AbsState) : AtransR                \
\ =+=> (%theta AbsState'') : InitAbsState                       \
\ =+=> file:Abs_Name                                            \
\ =+=>                                                          \
\ (? m : Aknows .                           \
\   (rep_permtab %^ file,                   \
\     authtab %^ rep %^ m )                 \
\              : cvs_perm_order)            ";
by(stripS_tac 1);
by(atomizePrem_ex 1);
br mp 1;
(* get AbsState from AtransR*)
zbr (removeTheta AbsStateAfterInitAtransR) 2;
by(removeTheta_tac 2);
by(removeTheta_tac 2);
br impI 1;
(* /get AbsState from AtransR*)
zbd has_access_implies_inPermOrder 1;
ba 4;

zbr (AbsState_implies_RepositoryState
	 ZRS 
	 RepState_implies_type_repPtb) 1;
by(convert2hol_tac [] 1);
zbr (AbsState_implies_RepositoryState
	 ZRS 
	 RepState_implies_type_rep) 1;
by(convert2hol_tac [] 1);
zbr (removeSNAME(AbsState_implies_ClientState
	 ZRS
	 type_absPwd)) 1;
by(convert2hol_tac [] 1);
(* get type abs_passwd for id: cvsUid *)
br mp 1;
zbr (removeSNAME(AbsState_implies_ClientState
	 ZRS
	 type_absPwd)) 2;
by(convert2hol_tac [] 2);
br impI 1;
br Rel_Dom_Elem 1;
by(convert2hol_tac [PASSWD_TAB_def, partial_func_def] 1);
ba 1;
(* /id: cvsUid/ *)

by(res_inst_tac [("x", "(aid, (abs_passwd %^ aid))")] 
		bexI 1);
ba 1;
zbr loginAknows 1;
by(rewtac theta_def);
ba 1;ba 1;ba 1;
qed"has_access_implies_permission";

(* inductive proof *)




zgoal SysArchSec.thy "                   \
\ (%theta AbsState, %theta AbsState') :  \
\  AtransR                               \
\              =+=>                      \
\ InitAbsState                           \
\              =+=>                      \
\ n : dom wc_uidtab'                     \
\              =+=>                      \
\ n : dom rep'                           \
\              =+=>                      \
\ (n, (wc' %^ n)): Ainvents  \\/         \
\ (? m : Aknows .                        \
\   (rep_permtab' %^ n,                  \
\     authtab %^ rep' %^ m )             \
\              : cvs_perm_order)         ";
by(stripS_tac 1);
by(rewtac AtransR_def);
br mp 1;
by(guidedAssumption ["dom wc_uidtab"] 2);
br mp 1;
by(guidedAssumption ["dom rep"] 2);
br mp 1;
by(guidedAssumption ["Init"] 2);
by(filterPrems_keep ["AService"] 1);
br mp 1;

by(eres_inst_tac [("P","%(abs_passwd0, rep0, rep_permtab0,   \
		       \wc0, wc_uidtab0, wfiles0) .          \
		       \%(abs_passwd1,rep1,rep_permtab1,     \
		       \wc1,wc_uidtab1,wfiles1).             \
		       \                                     \
                       \  ((abs_passwd0, rep0, rep_permtab0, \ 
		       \ wc0, wc_uidtab0, wfiles0)           \
                       \  : (asSet InitAbsState)) =+=>       \
                       \   n : dom rep1           =+=>       \
                       \   n : dom wc_uidtab1     =+=>       \
                       \  (n, (wc1 %^ n)) : Ainvents \\/     \
		       \  ( ? m:Aknows.                      \
                       \  (rep_permtab1 %^ n,                \
                       \    authtab %^ rep1 %^ m): cvs_perm_order)")] 
                 zrtrancl_full_induct2 2);

by(convert2hol_tac [theta_def] 1);

(* lemmata for the base cases:      *)
(*                                  *)
(* domExEmpty_any                   *)
(* InitAbsState_implies_wcUtb_empty *)

(* first base case : *)
by(simp_tac (HOL_ss addsimps [split_def] )1);
by(stripS_tac 1);
by(res_inst_tac [("f", "(fst (snd (snd (snd (snd x)))))")] domExEmpty_any 1);
ba 1;
zbr InitAbsState_implies_wcUtb_empty 1;
by(convert2hol_tac [] 1);

(* second base case : *)
by(simp_tac (HOL_ss addsimps [split_def] )1);
by(stripS_tac 1);
by(res_inst_tac [("f", "(fst (snd (snd (snd (snd y)))))")] domExEmpty_any 1);
ba 1;
zbr InitAbsState_implies_wcUtb_empty 1;
by(convert2hol_tac [] 1);

(* -prepare induction step- *)
by(split_all_tac 1);
by(convert2hol_tac [] 1);
by(stripS_tac 1);

by(rename_tac "  \
              \n abs_passwdx abs_passwdy abs_passwdz repx repy repz \
              \ rep_permtabx rep_permtaby rep_permtabz \
              \ wcx wcy wcz wc_uidtabx wc_filesx wc_uidtaby \
              \ wfilesy wc_uidtabz wfilesz \
\ " 1);

br mp 1;
zbr (removeTheta AService_imp_Ops) 2;
by(convert2hol_tac [] 2);
br impI 1;
(* -/prepare induction step/- *)
(* L  32 *)
(* proof-specific preparations. *)
be impE 1;
ba 1;

be disjE 1;

(* abs_loginR *)
by(atomizePrem_ex 1);
by(duplPrem "abs_login" 1);
by(duplPrem "abs_login" 1);
zbd abs_loginR_implies_repPtab_invariant 1;
zbd abs_loginR_invariant_wcUidtb 1;
zbd abs_loginR_invariant_wc 1;
by(atomizePrem 1);
by(hyp_subst_tac 1);
be impE 1;
ba 1;
be impE 1;
ba 1;
ba 1;

be disjE 1;
by(defer_tac 1);
(* abs_addR delayed *)
be disjE 1;
by(defer_tac 1);
(* abs_ciR delayed *)
be disjE 1;
by(defer_tac 1);
(* abs_up delayed *)
be disjE 1;

(* abs_cd *)
by(atomizePrem_ex 1);
by(duplPrem "abs_cd" 1);
by(duplPrem "abs_cd" 1);
zbd abs_cd_implies_repPtab_invariant 1;
zbd abs_cd_invariant_wcUidtb 1;
zbd abs_cd_invariant_wc 1;
by(atomizePrem 1);
by(hyp_subst_tac 1);
be impE 1;
ba 1;
be impE 1;
ba 1;
ba 1;

(* modifyR *)
by(case_tac "wcy %^ n = wcz %^ n" 1);
(* wc partial inv *)
by(res_inst_tac [("s", "wcy %^ n"), ("t", "wcz %^ n")] subst 1);
ba 1;
by(atomizePrem_ex 1);
by(duplPrem "modify" 1);
zbd modifyR_implies_repPtab_invariant 1;
zbd modifyR_invariant_wcUidtb 1;
by(atomizePrem 1);
by(hyp_subst_tac 1);
be impE 1;
ba 1;
be impE 1;
ba 1;
ba 1;
(* wc modified *)
br disjI1 1;
by(atomizePrem_ex 1);
zbd modifyR_wcDiff_Ainvents 1;
ba 1;
ba 1;


(* abs_addR *)
(* case wc invariant *)
by(case_tac "wcy %^ n = wcz %^ n" 1);
by(res_inst_tac [("s", "wcy %^ n"), ("t", "wcz %^ n")] subst 1);
ba 1;
by(atomizePrem_ex 1);
be impE 1;
zbd abs_addR_implies_rep_invariant 1;
by(hyp_subst_tac 1);
ba 1;
by(case_tac "n : dom wc_uidtaby" 1);
(* 2case n : dom wc_uidtaby  *)
be impE 1;
ba 1;
zbd abs_addR_implies_repPtab_invariant 1;
be conjE 1;
by(hyp_subst_tac 1);
ba 1;
(* 2case n ~: dom wc_uidtaby *)
by(duplPrem "abs_add" 1);
zbd abs_addR_implies_abs_add 1;
zbd abs_add_domDiff_utb_newfiles 1;
ba 1;
ba 1;
zbd abs_addR_newfiles_Ainvents 1;
ba 1;
br disjI1 1;
by(res_inst_tac [("s", "wcz %^ n"), ("t", "wcy %^ n")] subst 1);
br sym 1;
ba 1;
ba 1;

(* case wc changed*)
zbd zrtrancl_into_zrtrancl 1;
ba 1;
br mp 1;
zbr domWcUtb_implies_domWc 2;
(* remove set-cons *)
by(convert2hol_tac [AtransR_def, theta_def] 2);
by(convert2hol_tac [] 2);
ba 2;
(* *)
br impI 1;
by(atomizePrem_ex 1);
zbd abs_addR_fNeq_Ainvents 1;
ba 1;
ba 1;
br disjI1 1;
ba 1;

(* abs_ciR    *)
by(atomizePrem_ex 1);
by(case_tac "n : dom repy" 1);
(* 1. case n: dom repy *)
be impE 1;
ba 1;
zbd abs_ciR_implies_abs_ci 1;
by(duplPrem "abs_ci" 1);
by(duplPrem "abs_ci" 1);
by(duplPrem "abs_ci" 1);
zbd abs_ci_invariant_wcUidtb 1;
zbd abs_ci_invariant_wc 1;
by(hyp_subst_tac 1);
be impE 1;
ba 1;
(* still need to replace rep, rep_permtab. *)
(* - rep_permtab - *)
by(res_inst_tac [("s", "rep_permtaby %^ n"), 
		 ("t", "rep_permtabz %^ n")] subst 1);
zbr abs_ci_repPtab_invariant 1;
ba 2;
ba 1;
(* - rep -         *)
by(res_inst_tac [("s", "authtab %^ repy"), 
		 ("t", "authtab %^ repz")] subst 1);
ba 2;
zbr auth_invariant 1;
(* get the constrs. *)
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(convert2hol_tac [theta_def] 1);
by(convert2hol_tac [theta_def] 1);
(* =done= *)
(* 2. case n ~: dom repy *)
br disjI2 1;
zbr rep_domDiff_implies_perm 1;
ba 3;
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(convert2hol_tac [theta_def] 1);
by(convert2hol_tac [theta_def] 1);
ba 1;
ba 1;

(* L  159  *)
(* abs_up  *)
by(atomizePrem_ex 1);
by(case_tac "wcy %^ n = wcz %^ n" 1);
(* 1. first prove wcy %^ n ~= wcz %^ n *)
br mp 2;
zbr abs_up_fNeq_wc_has_access 3;
ba 5;
ba 5;
by(convert2hol_tac [] 4);
by(convert2hol_tac [AtransR_def] 3);
br impI 2;
br disjI2 2;
by(duplPrem "abs_up" 2);
zbd abs_up_implies_repPtab_invariant 2;
by(atomizePrem 2);
by(res_inst_tac [("s", "repy"), 
		 ("t", "repz")] subst 2);
ba 2;
by(res_inst_tac [("s", "rep_permtaby"), 
		 ("t", "rep_permtabz")] subst 2);
ba 2;

zbr (removeTheta has_access_implies_perm) 2;
(* remove the constraints. *)
by(convert2hol_tac [AtransR_def] 2);
(**)
by(res_inst_tac [("s", "repy"), 
		 ("t", "repz")] subst 2);
ba 2;
by(res_inst_tac [("s", "rep_permtaby"), 
		 ("t", "rep_permtabz")] subst 2);
ba 2;
ba 2;
(**)
by(convert2hol_tac [] 2);
ba 3;
(* remove: n : Abs_Name *)
zbd (abs_up_valid_AbsStateS
	 ZRS
	 AbsState_implies_RepositoryState
	 ZRS
	 RepState_implies_type_rep) 2;
by(rewtac ABS_DATATAB_def);
br dom_pfun 2;
ba 2;
ba 2;
(* now n: dom wcz*)
bd zrtrancl_into_zrtrancl 2;
ba 2;
zbr domWcUtb_implies_domWc 2;
by(convert2hol_tac [AtransR_def] 2);
by(convert2hol_tac [] 2);
ba 2;
(* finished case wcy %^ n ~= wcz %^ n *)
by(case_tac "n : dom wc_uidtaby" 1);
(* 1. case n : dom wc_uidtaby *)
zbd abs_up_implies_repPtab_invariant 1;
by(atomizePrem 1);
by(hyp_subst_tac 1);
be impE 1;
ba 1;
be impE 1;
ba 1;
by(res_inst_tac [("s", "wcy %^ n"), 
		 ("t", "wcz %^ n")] subst 1);
ba 1;
ba 1;
(* L  207  *)
(* 2. case n ~: dom wc_uidtaby *)
by(duplPrem "abs_up" 1);
zbd abs_up_domDiff_wcUtb_implies_hasAccess 1;
ba 1;
ba 1;

br disjI2 1;
by(duplPrem "abs_up" 1);
zbd abs_up_implies_repPtab_invariant 1;
by(atomizePrem 1);
by(res_inst_tac [("s", "repy"), 
		 ("t", "repz")] subst 1);
ba 1;
by(res_inst_tac [("s", "rep_permtaby"), 
		 ("t", "rep_permtabz")] subst 1);
ba 1;
(* old frag *)

zbr (removeTheta has_access_implies_perm) 1;
(* remove the constraints. *)
by(convert2hol_tac [AtransR_def] 1);
(**)
by(res_inst_tac [("s", "repy"), 
		 ("t", "repz")] subst 1);
ba 1;
by(res_inst_tac [("s", "rep_permtaby"), 
		 ("t", "rep_permtabz")] subst 1);
ba 1;
ba 1;
(**)
by(convert2hol_tac [] 1);
by(hyp_subst_tac 2);
ba 2;
(* remove: n : Abs_Name *)
zbd (abs_up_valid_AbsStateS
	 ZRS
	 AbsState_implies_RepositoryState
	 ZRS
	 RepState_implies_type_rep) 1;
by(rewtac ABS_DATATAB_def);
br dom_pfun 1;
ba 1;
ba 1;
qed"owner_inRep_AinvOrPerm";




