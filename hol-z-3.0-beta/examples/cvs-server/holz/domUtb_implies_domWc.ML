(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * domUtb_implies_domWc.ML --- 
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
(* $Id: domUtb_implies_domWc.ML 6746 2007-08-03 07:25:55Z brucker $ *)

zgoal SysArchSec.thy "                   \
\ (%theta AbsState, %theta AbsState') :  \
\  AtransR                               \
\              =+=>                      \
\ InitAbsState                           \
\              =+=>                      \
\ n : dom wc_uidtab'                     \
\              =+=>                      \
\ n : dom wc'                            ";
by(stripS_tac 1);

by(rewtac AtransR_def);
br mp 1;
by(guidedAssumption ["dom wc_uidtab"] 2);
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
                       \   n : dom wc_uidtab1     =+=>       \
                       \   n : dom wc1                  ")] 
                 zrtrancl_full_induct2 2);

by(convert2hol_tac [theta_def] 1);

(* fst base case*)
by(simp_tac (HOL_ss addsimps [split_def] )1);
by(stripS_tac 1);
by(res_inst_tac [("f", "(fst (snd (snd (snd (snd x)))))")] domExEmpty_any 1);
ba 1;
zbr InitAbsState_implies_wcUtb_empty 1;
by(convert2hol_tac [] 1);

(* snd base case*)
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
be impE 1;
ba 1;

be disjE 1;

(* abs_login *)

by(atomizePrem_ex 1);
by(duplPrem "abs_login" 1);
zbd abs_loginR_invariant_wc 1;
zbd abs_loginR_invariant_wcUidtb 1;
by(hyp_subst_tac 1);
br impE 1;
ba 1;
ba 1;ba 1;

be disjE 1;

(* abs_add *)

by(case_tac "n : dom wc_uidtaby" 1);
(* fst case*)
be impE 1;
ba 1;
by(atomizePrem_ex 1);
zbd abs_addR_implies_abs_add 1;
zbd abs_add_domWc_mono 1;
ba 1;
ba 1;

(* snd case*)
by(atomizePrem_ex 1);
zbd abs_addR_implies_abs_add 1;
zbd abs_add_domDiff_wcUtb_inDom_wc 1;
ba 1;
ba 1;
ba 1;


be disjE 1;

(* abs_ciR *)
by(atomizePrem_ex 1);
zbd abs_ciR_implies_abs_ci 1;
by(duplPrem "abs_ci" 1);
zbd abs_ci_invariant_wc 1;
zbd abs_ci_invariant_wcUidtb 1;

by(hyp_subst_tac 1);
be impE 1;
ba 1; 
ba 1;

be disjE 1;

(* abs_up *)
by(atomizePrem_ex 1);
by(case_tac "n : dom wc_uidtaby" 1 );
(* n : dom wc_uidtaby *)
be impE 1;
ba 1;
zbd abs_up_domWc_mono 1;
ba 1;
 ba 1;
(* n ~: dom wc_uidtaby *)
zbd abs_up_domDiff_wcUtb_inDom_wc 1;
ba 1;
ba 1;
ba 1;
(* abs_up_domDiff_wcUtb_inDom_wc *)

be disjE 1;

(* abs_cd*)

by(atomizePrem_ex 1);
by(duplPrem "abs_cd" 1);
zbd abs_cd_invariant_wc 1;
zbd abs_cd_invariant_wcUidtb 1;
by(hyp_subst_tac 1);
br impE 1;
ba 1;
ba 1;ba 1;

(* modifyR *)

by(atomizePrem_ex 1);
by(duplPrem "modify" 1);
zbd modifyR_invariant_wcUidtb 1;
zbd modifyR_implies_modify 1;
zbd modify_domWc_invariant 1;
by(hyp_subst_tac 1);
by(res_inst_tac [("t", "dom wcz"), ("s", "dom wcy")] subst 1);
ba 1;
be impE 1;
ba 1;
ba 1;
qed"domWcUtb_implies_domWc";
