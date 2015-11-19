(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * wc_Ainvents.ML --- 
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
(* $Id: wc_Ainvents.ML 6746 2007-08-03 07:25:55Z brucker $ *)


zgoal SysArchSec.thy "        \
\ ((%theta AbsState),(%theta AbsState')): AtransR  =+=> \
\ InitAbsState  =+=>          \
\ n ~: dom rep' =+=>          \
\ n : dom wc'   =+=>          \
\ (n, (wc' %^ n)) : Ainvents    ";
by(stripS_tac 1);
by(rewtac AtransR_def);
br mp 1;
by(guidedAssumption ["n ~:"] 2);
br mp 1;
by(guidedAssumption ["n :"] 2);
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
                       \   n : dom wc1 =+=> n ~: dom rep1    \
		       \ =+=> (n, (wc1 %^ n)) : Ainvents     ")] 
                 zrtrancl_full_induct2 2);

by(convert2hol_tac [theta_def] 1);

(* first Base case *)
by(simp_tac (HOL_ss addsimps [split_def] )1);
by(stripS_tac 1);
by(res_inst_tac [("f", "(fst (snd (snd (snd x))))")] domExEmpty_any 1);
ba 1;
zbr InitAbsState_implies_wc_empty 1;
by(convert2hol_tac [] 1);

(* second Base case *)
by(simp_tac (HOL_ss addsimps [split_def] )1);
by(stripS_tac 1);
by(res_inst_tac [("f", "(fst (snd (snd (snd y))))")] domExEmpty_any 1);
ba 1;
zbr InitAbsState_implies_wc_empty 1;
by(convert2hol_tac [] 1);

(* -prepare induction step- *)
by(split_all_tac 1);
by(rewtac theta_def);
zbd (removeTheta AService_imp_Ops) 1;
 by(convert2hol_tac [] 1);
(*by(Asm_full_simp_tac 1);*)
by(stripS_tac 1);
by(rename_tac "  \
              \n abs_passwdx abs_passwdy abs_passwdz repx repy repz \
              \ rep_permtabx rep_permtaby rep_permtabz \
              \ wcx wcy wcz wc_uidtabx wc_filesx wc_uidtaby \
              \ wfilesy wc_uidtabz wfilesz \
\ " 1);
(* Induction step *)
be impE 1;
ba 1;
by(filterPrems_drop ["InitAbsState", "*"] 1);
be disjE 1;
(* abs_loginR  ----------------------- *)
(* mainly use IV (substitute)          *)
by(atomizePrem_ex 1);
by(duplPrem "abs_login" 1);
zbd (removeSNAME 
	 (removeTheta(abs_loginR_implies_repPtab_invariant))) 1;
zbd (removeSNAME 
     (removeTheta(abs_loginR_invariant_wc))) 1;
by(atomizePrem 1);
br mp 1;
by(guidedAssumption ["n ~: dom repz"] 2);
br mp 1;
by(guidedAssumption ["n : dom wcz"] 2);

by(res_inst_tac [("t", "wcz"), ("s", "wcy")] subst 1);
ba 1;
by(res_inst_tac [("t", "repz"), ("s", "repy")] subst 1);
ba 1;
ba 1;

be disjE 1;
by(defer_tac 1);(*defer add*)
be disjE 1;
by(defer_tac 1);(*defer ci*)
be disjE 1;
by(defer_tac 1);(*defer up*)
be disjE 1;

(* abs_cd  ----------------------- *)
(* mainly use IV (substitute)          *)
by(atomizePrem_ex 1);
by(duplPrem "abs_cd" 1);
zbd (removeSNAME 
	 (removeTheta(abs_cd_implies_repPtab_invariant))) 1;
zbd (removeSNAME 
     (removeTheta(abs_cd_invariant_wc))) 1;
by(atomizePrem 1);
br mp 1;
by(guidedAssumption ["n ~: dom repz"] 2);
br mp 1;
by(guidedAssumption ["n : dom wcz"] 2);

by(res_inst_tac [("t", "wcz"), ("s", "wcy")] subst 1);
ba 1;
by(res_inst_tac [("t", "repz"), ("s", "repy")] subst 1);
ba 1;
ba 1;

(* modifyR ----------------------- *)
(* mainly use IV (substitute)      *)

by(atomizePrem_ex 1);
by(case_tac "wcy %^ n = wcz %^ n" 1);

zbd (removeSNAME modifyR_wcDiff_Ainvents) 2;
ba 2;
ba 2;
by(res_inst_tac [("t", "wcz %^ n"), 
		 ("s", "wcy %^ n")] subst 1);
ba 1;

by(duplPrem "modify" 1);
zbd (removeSNAME modifyR_implies_rep_invariant) 1;
zbd (removeSNAME modifyR_implies_modify) 1; 
zbd (removeSNAME modify_domWc_invariant) 1;
br mp 1;
by(guidedAssumption ["n ~: dom repz"] 2);
br mp 1;
by(guidedAssumption ["n : dom wcz"] 2);
by(res_inst_tac [("t", "dom wcz"),
		 ("s", "dom wcy")] subst 1);
ba 1;
by(res_inst_tac [("t", "repz"),
		 ("s", "repy")] subst 1);
ba 1;
ba 1;

(* abs_addR ---------------------- *)
(*                                 *)


by(atomizePrem_ex 1);
by(case_tac "n : dom wcy" 1);
(* 1. Fall : n ~: dom wcy *)
zbd (removeSNAME abs_addR_domDiff_Ainvents) 2;
by(guidedAssumption ["n ~: dom wcy"] 2);
ba 2;
ba 2;
(* 2. Fall : n  : dom wcy *)
be impE 1;
ba 1;
by(case_tac "wcy %^ n = wcz %^ n" 1);
(* 2.a. : wcy %^ n = wcz %^ n   *)
(* verwende IV                  *)
br mp 1;
by(guidedAssumption ["n ~: dom repz"] 2);
zbd (removeSNAME abs_addR_implies_rep_invariant) 1;
by(res_inst_tac [("s","wcy %^ n"), ("t","wcz %^ n")] subst 1);
ba 1;
by(res_inst_tac [("s","repy"), ("t","repz")] subst 1);
ba 1;
ba 1;
(* 2.b. : wcy %^ n ~= wcz %^ n   *)
(* setze lemma ein               *)
zbd (removeSNAME abs_addR_fNeq_Ainvents) 1;
ba 1;
ba 1;
ba 1;
(* abs_ciR --------------------- *)
by(atomizePrem_ex 1);
br mp 1;
zbd ((removeSNAME abs_ciR_implies_abs_ci )
	 ZRS
	 (removeSNAME abs_ci_domRep_mono)) 2;
br elem_contrapos 2;
ba 2;
ba 2;
br mp 1;
by(guidedAssumption ["n : dom wcz"] 2);
by(res_inst_tac [("t", "wcz"), 
		 ("s", "wcy")] subst 1);
zbd ((removeSNAME abs_ciR_implies_abs_ci)
	 ZRS
	 (removeSNAME abs_ci_invariant_wc)) 1;
ba 1;
ba 1;
(* abs_up  --------------------- *)
by(atomizePrem_ex 1);
by(case_tac "n : dom wcy" 1);
(* 2nd case: n ~: dom wcy *)
(* contradict on n : dom repz *)
zbd (removeSNAME abs_up_wcDomDiff_fromRep) 2;
ba 2;
ba 2;
by(res_inst_tac [("P", "n : dom repz")] notE 2);
ba 2;
ba 2;
(* 1 st case: n : dom wcy  *)
by(case_tac "wcy %^ n = wcz %^ n" 1);
(* 1a : wcy n ~= wcz n     *)
(* contradict on n : dom repz *)
zbd (removeSNAME abs_up_wcfNeq_fromRep) 2;
ba 2;
ba 2;
by(res_inst_tac [("P", "n : dom repz")] notE 2);
ba 2;
ba 2;
(* 1b : wcy n  = wcz n     *)
(* match on IH             *)
be impE 1;
ba 1;
zbd (removeSNAME abs_up_implies_rep_invariant) 1;
by(hyp_subst_tac 1);
be impE 1;
ba 1;
by(res_inst_tac [("s", "wcy %^ n"), 
		 ("t", "wcz %^ n")] subst 1);
by(AtomizePremSolveAll);
qed"wc_Ainvents";
