(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_Passwd_zrtrancl.ML --- 
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
(* $Id: abs_Passwd_zrtrancl.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* conclude false from initial state and *)
(* having an element in dom wc_uidtab.   *)

(* (essential lemma for base case.)      *)
zgoal SysArchSec.thy "(f : dom wc_uidtab)  \
\ =+=> InitAbsState                       \
\ =+=> False ";
by(stripS_tac 1);
by(convert2hol_tac [InitAbsState_def] 1);
auto();
qed"false_from_notEmpty_Init_wcUidtab";
(* ----  *)



(* -- *)

zgoal SysArchSec.thy "((%theta AbsState, %theta AbsState') :   \
\  {.AService @ (%theta AbsState, %theta AbsState').} %* )     \
\ =+=>                                                         \
\ (%theta AbsState) : InitAbsState                            \
\ =+=>                                                         \
\ (f : dom wc_uidtab')                                         \
\ =+=>                                                         \
\ ((wc_uidtab' %^ f) : dom abs_passwd')                        \
\   ";
by(stripS_tac 1);

br mp 1;
by(guidedAssumption ["f : dom wc_uidtab'"] 2);
br mp 1;
by(guidedAssumption ["InitAbsState"] 2);
br mp 1;
by(eres_inst_tac [("P","%(abs_passwd0, rep0, rep_permtab0, wc0, wc_uidtab0, wfiles0) .  \
                       \%(abs_passwd1,rep1,rep_permtab1,wcS,wc_uidtab1,wfiles1).        \
                       \  ((abs_passwd0, rep0, rep_permtab0, wc0, wc_uidtab0, wfiles0)  \
                       \              : (asSet InitAbsState)) =+=>                     \
                       \  (f : dom wc_uidtab1)                                          \
                       \  =+=>  ((wc_uidtab1 %^ f) : dom abs_passwd1)  ")] 
                 zrtrancl_full_induct2 2);
by(convert2hol_tac [theta_def] 1);

(* fst base case *)
by(filterPrems_drop ["InitAbsState (abs_passwd", "f : dom wc_uidtab'"] 1);
(* drop old assumptions. *)
by(split_all_tac 1);
by(convert2hol_tac [] 1);
br impI 1;
br impI 1;
br FalseE 1;
zbe false_from_notEmpty_Init_wcUidtab 1;
by(convert2hol_tac [] 1);

(* snd base case *)
(* [same proof as for the first one] *)
by(filterPrems_drop ["InitAbsState (abs_passwd", "f : dom wc_uidtab'"] 1);
(* drop old assumptions. *)
by(split_all_tac 1);
by(convert2hol_tac [] 1);
br impI 1;
br impI 1;
br FalseE 1;
zbe false_from_notEmpty_Init_wcUidtab 1;
by(convert2hol_tac [] 1);
(* -------------- *)
(* induction step *)
(* -------------- *)
by(filterPrems_drop ["(%theta AbsState) : InitAbsState", "f : dom wc_uidtab'"] 1);
by(split_all_tac 1);
by(convert2hol_tac [] 1);
br impI 1;
br impI 1;


by(rename_tac "  \
              \f abs_passwdx abs_passwdy abs_passwdz repx repy repz \
              \ rep_permtabx rep_permtaby rep_permtabz \
              \ wcx wcy wcz wc_uidtabx wc_filesx wc_uidtaby \
              \ wfilesy wc_uidtabz wfilesz \
\ " 1);
(* convert command step to *)
(* union of commands       *)
br mp 1;
br(asm_full_simplify(HOL_ss addsimps[theta_def])(stripS AService_imp_Ops)) 2; 
by(convert2hol_tac [] 2);
br impI 1;
(* get IV-implication. *)
be impE 1;
ba 1;
(* now watch each command: *)

be disjE 1;
(* ------------------- *)
(* 1. Case: abs_loginR *)
(* ------------------- *)
by(atomizePrem_ex 1);

by(case_tac "f : dom wc_uidtaby" 1);
(* contradict subcase f ~: dom wc_uidtaby *)
bd chDom_implies_chFunc 2;
ba 2;
by(res_inst_tac [("P", "wc_uidtabz = wc_uidtaby")] notE 2);
ba 2;
zbd abs_loginR_invariant_wcUidtb 2;
br sym 2;
ba 2;
(* use IV on subcase f ~: dom wc_uidtaby *)
be impE 1;
ba 1;
by(res_inst_tac [("t", "wc_uidtabz"), ("s", "wc_uidtaby")] subst 1);
zbd abs_loginR_invariant_wcUidtb 1;
ba 1;
br subsetD 1;
ba 2;
zbd abs_loginR_implies_abs_login 1;
zbd abs_login_domAbsPwd_mono 1;
ba 1;

(* cases abs_cd, abs_ci, modifyR *)
(* are nearly the same - but     *)
(* generation of a separate lemma*)
(* would probably decrease       *)
(* portability because of goal   *)
(* formulation.                  *)

(* ------------------- *)
(* 2. Case: abs_addR   (delayed) *)
(* ------------------- *)
be disjE 1;
by(defer_tac 1);
be disjE 1;

(* ------------------- *)
(* 3. Case: abs_ci     *)
(* ------------------- *)

by(atomizePrem_ex 1);
zbd abs_ciR_implies_abs_ci 1;
by(case_tac "f : dom wc_uidtaby" 1);
(* contradict subcase f ~: dom wc_uidtaby *)
bd chDom_implies_chFunc 2;
ba 2;
by(res_inst_tac [("P", "wc_uidtabz = wc_uidtaby")] notE 2);
ba 2;
zbd abs_ci_invariant_wcUidtb 2;
br sym 2;
ba 2;
(* get implication from IV *)
be impE 1;
ba 1;
by(res_inst_tac [("t", "wc_uidtabz"), ("s", "wc_uidtaby")] subst 1);
zbd abs_ci_invariant_wcUidtb 1;
ba 1;
by(res_inst_tac [("t", "abs_passwdz"), ("s", "abs_passwdy")] subst 1);
zbr abs_ci_invariant_absPwd 1;
ba 1;
ba 1;

(* ------------------- *)
(* 4. Case: abs_up   (delayed) *)
(* ------------------- *)
be disjE 1;
by(defer_tac 1);
be disjE 1;
(* ------------------- *)
(* 5. Case: abs_ci     *)
(* ------------------- *)
by(atomizePrem_ex 1);

by(case_tac "f : dom wc_uidtaby" 1);
(* contradict subcase f ~: dom wc_uidtaby *)
bd chDom_implies_chFunc 2;
ba 2;
by(res_inst_tac [("P", "wc_uidtabz = wc_uidtaby")] notE 2);
ba 2;
zbd abs_cd_invariant_wcUidtb 2;
br sym 2;
ba 2;
(* get implication from IV *)
be impE 1;
ba 1;
by(res_inst_tac [("t", "wc_uidtabz"), ("s", "wc_uidtaby")] subst 1);
zbd abs_cd_invariant_wcUidtb 1;
ba 1;
by(res_inst_tac [("t", "abs_passwdz"), ("s", "abs_passwdy")] subst 1);
zbd abs_cd_invariant_absPwd 1;
ba 1;
ba 1;

(* ------------------- *)
(* 6. Case: modifyR    *)
(* ------------------- *)
by(atomizePrem_ex 1);

by(case_tac "f : dom wc_uidtaby" 1);
(* contradict subcase f ~: dom wc_uidtaby *)
bd chDom_implies_chFunc 2;
ba 2;
by(res_inst_tac [("P", "wc_uidtabz = wc_uidtaby")] notE 2);
ba 2;
zbd modifyR_invariant_wcUidtb 2;
br sym 2;
ba 2;
(* get implication from IV *)
be impE 1;
ba 1;
by(res_inst_tac [("t", "wc_uidtabz"), ("s", "wc_uidtaby")] subst 1);
zbd modifyR_invariant_wcUidtb 1;
ba 1;
by(res_inst_tac [("t", "abs_passwdz"), ("s", "abs_passwdy")] subst 1);
zbd modifyR_invariant_absPwd 1;
ba 1;
ba 1;

(* --- leaves the 2 deferred cases: *)
(* abs_up and abs_addR.             *)

(* ------------------- *)
(* 2. Case: abs_addR   *)
(* ------------------- *)


by(atomizePrem_ex 1);
by(case_tac "f : dom wc_uidtaby" 1);
(* first subcase : f : dom wc_uidtaby *)
be impE 1;
ba 1;
zbd abs_addR_implies_abs_add 1;
br mp 1;
zbd abs_add_invariant_absPwd 2;
by(guidedAssumption ["abs_passwdy ="] 2);
br impI 1;
zbd abs_add_partInv_wcUtb 1;
ba 1;
by(res_inst_tac [("s", "wc_uidtaby %^ f"), ("t", "wc_uidtabz %^ f")] subst 1);
ba 1;
by(res_inst_tac [("s", "abs_passwdy"), ("t", "abs_passwdz")] subst 1);
ba 1;
ba 1;
(* second subcase : f~: dom wc_uidtaby *)

zbd abs_addR_implies_abs_add 1; 
zbd abs_add_defined_absPwd 1;
ba 2;
ba 1;
ba 1;

(* ------------------- *)
(* 4. Case: abs_up     *)
(* ------------------- *)

by(atomizePrem_ex 1);
by(case_tac "f : dom wc_uidtaby" 1);
(* first subcase : f : dom wc_uidtaby *)
be impE 1;
ba 1;
br mp 1;
zbd abs_up_invariant_absPwd 2;
by(guidedAssumption ["abs_passwdy ="] 2);
br impI 1;
zbd abs_up_partialInv_wcUidtb 1;
ba 1;
by(res_inst_tac [("s", "wc_uidtaby %^ f"), ("t", "wc_uidtabz %^ f")] subst 1);
ba 1;
by(res_inst_tac [("s", "abs_passwdy"), ("t", "abs_passwdz")] subst 1);
ba 1;
ba 1;
(* second subcase : f~: dom wc_uidtaby *)

zbd abs_up_defined_absPwd 1;
ba 2;
ba 1;
ba 1;
qed"definedAbsPwd";



