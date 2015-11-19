(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * owner_Or_invented.ML --- 
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
(* $Id: owner_Or_invented.ML 6746 2007-08-03 07:25:55Z brucker $ *)

zgoal SysArchSec.thy "                   \
\ (%theta AbsState, %theta AbsState') :  \
\  AtransR                               \
\              =+=>                      \
\ InitAbsState                           \
\              =+=>                      \
\ n : dom wc'                            \
\              =+=>                      \
\ (n : dom wc_uidtab' \\/                \
\          (n, wc'%^ n) : Ainvents)      \
\ ";
by(stripS_tac 1);
by(rewtac AtransR_def);
br mp 1;
by(guidedAssumption ["n : "] 2);
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
                       \   n : dom wc1 =+=>                  \
		       \  (n : dom wc_uidtab1  \\/           \
                       \    (n, wc1%^ n) : Ainvents)         ")] 
                 zrtrancl_full_induct2 2);

by(convert2hol_tac [theta_def] 1);

(* lemmata for the base cases:   *)
(*                               *)
(* domExEmpty_any                *)
(* InitAbsState_implies_wc_empty *)

(* first base case : *)
by(simp_tac (HOL_ss addsimps [split_def] )1);
by(stripS_tac 1);
by(res_inst_tac [("f", "(fst (snd (snd (snd x))))")] domExEmpty_any 1);
ba 1;
zbr InitAbsState_implies_wc_empty 1;
by(convert2hol_tac [] 1);

(* second base case : *)
by(simp_tac (HOL_ss addsimps [split_def] )1);
by(stripS_tac 1);
by(res_inst_tac [("f", "(fst (snd (snd (snd y))))")] domExEmpty_any 1);
ba 1;
zbr InitAbsState_implies_wc_empty 1;
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


(* proof-specific preparations. *)
be impE 1;
ba 1;

(* not all assumptions are needed. *)
by(filterPrems_drop ["AService",
		     "InitAbsState"] 1);
(* solve abs_ci, abs_login and abs_cd *)
(* trivially by induction hypothesis. *)
be disjE 1;

(* abs_loginR *)
by(atomizePrem_ex 1);
by(duplPrem "abs_login" 1);
zbd abs_loginR_invariant_wc 1;
zbd abs_loginR_invariant_wcUidtb 1;
by(hyp_subst_tac 1);
be impE 1;
ba 1;
ba 1;

be disjE 1;
(* abs_addR - delayed. *)
by(defer_tac 1);

be disjE 1;
(* abs_ciR *)
by(atomizePrem_ex 1);
zbd abs_ciR_implies_abs_ci 1;
by(duplPrem "abs_ci" 1);
zbd abs_ci_invariant_wcUidtb 1;
zbd abs_ci_invariant_wc 1;

by(hyp_subst_tac 1);
be impE 1;
ba 1;
ba 1;

be disjE 1;
(* abs_up - delayed. *)
by(defer_tac 1);

be disjE 1;
(* abs_cd  *)
by(atomizePrem_ex 1);
by(duplPrem "abs_cd" 1);
zbd abs_cd_invariant_wc 1;
zbd abs_cd_invariant_wcUidtb 1;

by(hyp_subst_tac 1);
be impE 1;
ba 1;
ba 1;
(* defer modify R*)
by(defer_tac 1);
(* abs_add- lemmata           *)
(*                            *)
(* abs_add_domWcUtb_mono      *)
(* abs_addR_domDiff_Ainvents  *)
(* abs_addR_fNeq_Ainvents     *)
by(atomizePrem_ex 1);
by(case_tac "n : dom wcy" 1);
(* case 1 : n ~: dom wcy *)
zbd abs_addR_domDiff_Ainvents 2;
ba 2;
ba 2;
br disjI2 2;
ba 2;
(* case 1b : n : dom wcy *)
by(case_tac "wcy %^n = wcz %^ n " 1);
(* case 2 : wcy %^n ~= wcz %^ n *)
zbd abs_addR_fNeq_Ainvents 2;
ba 2;
ba 2;
br disjI2 2;
ba 2;
(* case 3 : wcy %^n = wcz %^ n *)
be impE 1;
ba 1;
by(res_inst_tac [("P", "n : dom wc_uidtaby"), 
		 ("Q", "(n, wcy %^ n) : Ainvents")] 
		disjE 1);
ba 1;
(* with IV - n : dom wc_uidtaby *)
br disjI1 1;
zbd abs_addR_implies_abs_add 1;
zbd abs_add_domWcUtb_mono 1;
ba 1;
ba 1;
(* with IV - (n, wcy %^ n) : Ainvents *)
br disjI2 1;
by(res_inst_tac [("t", "wcz %^ n"), 
		 ("s", "wcy %^ n")] subst 1);
ba 1;
ba 1;

(* abs_up - lemmata           *)
(*                            *)
(* abs_up_domWcUtb_mono       *)
(* abs_up_domDiff_wcUtb     *)
(* abs_up_fNeq_wcUtb        *)
by(atomizePrem_ex 1);
by(case_tac "n : dom wcy" 1);
(* case 1 : n ~: dom wcy *)
zbd abs_up_domDiff_wcUtb 2;
ba 2;
ba 2;
br disjI1 2;
ba 2;
(* case 1b : n : dom wcy *)
by(case_tac "wcy %^n = wcz %^ n " 1);
(* case 2 : wcy %^n ~= wcz %^ n *)
zbd abs_up_fNeq_wcUtb 2;
ba 2;
ba 2;
br disjI1 2;
ba 2;
(* case 3 : wcy %^n = wcz %^ n *)
be impE 1;
ba 1;
be disjE 1;
(* with IV - n : dom wc_uidtaby *)
zbd abs_up_domWcUtb_mono 1;
ba 1;
br disjI1 1;
ba 1;
(* with IV - (n, wcy %^ n) : Ainvents *)
br disjI2 1;
by(res_inst_tac [("t", "wcz %^ n"), 
		 ("s", "wcy %^ n")] subst 1);
ba 1;
ba 1;
(* modify - lemmata           *)
(*                            *)
(* modifyR_invariant_wcUidtb  *)
(* modify_domWc_invariant     *)
(* modifyR_wcDiff_Ainvents      *)

by(atomizePrem_ex 1);
by(case_tac "wcy %^n = wcz %^ n " 1);
(* case 1 : wcy %^n ~= wcz %^ n *)
zbd modifyR_wcDiff_Ainvents 2;
ba 2;
br disjI2 2;
ba 2;
(* case 2 : wcy %^n = wcz %^ n *)
by(duplPrem "modify" 1);
zbd modifyR_implies_modify 1;
zbd modify_domWc_invariant 1;
be impE 1;
by(res_inst_tac [("t", "dom wcy"), 
		 ("s", "dom wcz")] subst 1);
br sym 1;
ba 1;
ba 1;
be disjE 1;
(* IV : n : dom wc_uidtaby*)
zbd modifyR_invariant_wcUidtb 1;
by(hyp_subst_tac 1);
br disjI1 1;
ba 1;
(* IV : (n, wcy %^ n) : Ainvents *)
br disjI2 1;
by(res_inst_tac [("t", "wcz %^ n"), 
		 ("s", "wcy %^ n")] 
		subst 1);
ba 1;
ba 1;
qed"user_or_invented";
