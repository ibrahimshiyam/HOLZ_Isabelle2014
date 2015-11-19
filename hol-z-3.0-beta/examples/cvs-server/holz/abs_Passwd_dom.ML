(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_Passwd_dom.ML --- 
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
(* $Id: abs_Passwd_dom.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* Some lemmata which use the fact that *)
(* the initial abs_passwd table is not  *)
(* empty.                               *)


(* --- *)

goal thy " (? a. ? b. (a, b): abs_passwd ) =+=> (mu id:dom abs_passwd. True) : dom abs_passwd";
by(stripS_tac 1);
by(convert2hol_tac [Mu_def] 1);
zbr eps_from_exists_example 1;
ba 1;
qed"domAbsPasswd_from_example";

(* more common version *)
(* for abs_up.         *)

goal thy " (? a. ? b. (a, b): abs_passwd /\\ P a) =+=> (mu id:dom abs_passwd. P id) : dom abs_passwd";
by(stripS_tac 1);
by(convert2hol_tac [Mu_def] 1);
zbr eps_from_exists_example_pred 1;
auto();
qed"domAbsPasswd_from_example_pred";

(* equivalent formulation *)
goal thy " (? a : dom abs_passwd.  P a) =+=> (mu id:dom abs_passwd. P id) : dom abs_passwd";
by(stripS_tac 1);
by(convert2hol_tac [Mu_def] 1);
zbr eps_from_exists_example_pred 1;
auto();
qed"domAbsPasswd_from_example_pred1";



goal thy " (? a. ? b. (a, b): abs_passwd ) =+=> (mu id:dom abs_passwd. P) : dom abs_passwd";
by(stripS_tac 1);
by(convert2hol_tac [Mu_def] 1);


goal thy "(? a : A. ? b : B. (a, b): abs_passwd ) \
\ =+=> (? a. ? b. (a, b): abs_passwd )";
auto();
qed"bex_convert";

goal thy " (? a : A. ? b : B. (a, b): abs_passwd ) =+=> (mu id:dom abs_passwd. True) : dom abs_passwd";
by(stripS_tac 1);
zbd bex_convert 1;
zbr domAbsPasswd_from_example 1;
ba 1;
qed"domAbsPasswd_from_Zexample";

(* This is the central lemma *)
(* for the inductive proof   *)
(* for dom abs_passwd lateron*)

goal thy "abs_passwd ~= {} \
\ =+=> (mu id:dom abs_passwd. True) : dom abs_passwd";
by(stripS_tac 1);
zbd notEmpty_implies_examplePair 1;
zbd domAbsPasswd_from_example 1;
ba 1;
qed"notEmpty_implies_domAbsPasswd";

(* Argument for the base cases: *)
(* InitAbsState implies that    *)
(* abs_passwd is empty:         *)
(* lemma:                       *)
(* InitAbsState_implies_nemptyAbsPwd *)

(* helpful though not needed yet: *)


(* show for reachable valid    *)
(* abs_passwd, that it isnt    *)
(* empty.                      *)

zgoal SysArchSec.thy "   \
\ (%theta AbsState) : InitAbsState             \
\ =+=>                                          \
\ (%theta AbsState, %theta AbsState') : AtransR \
\  =+=>                  \
\ abs_passwd' ~= {}      \
\  ";
by(stripS_tac 1);
by(rewrite_goals_tac [AtransR_def]);
br mp 1;
by(guidedAssumption ["InitAbsState"] 2);
br mp 1;
by(eres_inst_tac [("P","%(abs_passwd0, rep0, rep_permtab0, wc0, wc_uidtab0, wfiles0) .  \
                       \%(abs_passwd1,rep1,rep_permtab1,wcS,wc_uidtab1,wfiles1).        \
                       \  ((abs_passwd0, rep0, rep_permtab0, wc0, wc_uidtab0, wfiles0)  \
                       \              : (asSet InitAbsState)) =+=>                     \
                       \   (abs_passwd1 ~= {})   ")] 
                 zrtrancl_full_induct2 2);
by(convert2hol_tac [] 1);

(* first base case. *)
by(filterPrems_drop ["InitAbsState (abs_passwd"] 1);
by(split_all_tac 1);
by(convert2hol_tac [] 1);
br impI 1;
zbr InitAbsState_implies_nemptyAbsPwd 1;
by(convert2hol_tac [] 1);

(* second base case. *)
by(filterPrems_drop ["InitAbsState (abs_passwd"] 1);
by(split_all_tac 1);
by(convert2hol_tac [] 1);
br impI 1;
zbr InitAbsState_implies_nemptyAbsPwd 1;
by(convert2hol_tac [] 1);

(* induction step *)
by(filterPrems_drop ["(%theta AbsState) : InitAbsState"] 1);
by(split_all_tac 1);
by(convert2hol_tac [] 1);

by(rename_tac "  \
              \ abs_passwdx abs_passwdy abs_passwdz repx repy repz \
              \ rep_permtabx rep_permtaby rep_permtabz \
              \ wcx wcy wcz wc_uidtabx wfilesx wc_uidtaby \
              \ wfilesy wc_uidtabz wfilesz \
\ " 1);
(* get IV-implikation in the assumptions. *)
br impI 1;
be impE 1;
ba 1;

(* change command step against  *)
(* union of commands            *)

br mp 1;
br(asm_full_simplify(HOL_ss addsimps[theta_def])(stripS AService_imp_Ops)) 2; 
by(convert2hol_tac [] 2);
br impI 1;

(* now: split off cases and show them *)
(* using simple lemmata.              *)

(* abs_loginR *)
be disjE 1;
by(atomizePrem_ex 1);
zbr abs_loginR_notShrink_absPwd 1;
ba 1;
ba 1;

(* abs_addR *)
be disjE 1;
by(atomizePrem_ex 1);
zbr abs_addR_notShrink_absPwd 1;
ba 1;
ba 1;

(* abs_ci *)
be disjE 1;
by(atomizePrem_ex 1);
zbr abs_ciR_notShrink_absPwd 1;
ba 1;
ba 1;

(* abs_up  *)
be disjE 1;
by(atomizePrem_ex 1);
zbr abs_up_notShrink_absPwd 1;
ba 1;
ba 1;

(* abs_cd  *)
be disjE 1;
by(atomizePrem_ex 1);
zbr abs_cd_notShrink_absPwd 1;
ba 1;
ba 1;

(* abs_cd  *)
by(atomizePrem_ex 1);
zbr modifyR_notShrink_absPwd 1;
ba 1;
ba 1;
(* Done. *)

qed"domAbsPasswd_notEmpty";


