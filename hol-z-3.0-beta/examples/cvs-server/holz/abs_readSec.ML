(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_readSec.ML --- 
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
(* $Id: abs_readSec.ML 6746 2007-08-03 07:25:55Z brucker $ *)


(********************************************************************** 
 * Any sequence of CVS operations starting from an empty working copy 
 * does not lead to a working copy with data from the repository that 
 * the user has no permission to access in the repository (except if he 
 * was able to "invent" it).
 **********************************************************************)

(* This file contains 3 proofs for AReadsec -       *)
(* the last one is the simplest, without induction. *)
(* This shows the incremental proof construction    *)
(* way I used to find the proof.                    *)


(* ============================= *)

(* Inductive Proof for AReadSec  *)
(*                               *)
(* umstaendliche Version mit Fallunterscheidung.
zgoalw SysArchSec.thy [AReadSec_def, Areachable_def] "AReadSec";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [] 1);
by(removeTheta_tac 1);
by(rewtac AtransR_def);
be dom_restrE 1;
(* by( safe_tac ((claset()) addSss (simpset()))); *)
(* ... is useful to substitute the pairs.         *)
by(safe_step_tac (claset()) 1);
by(safe_step_tac (claset()) 1);
by(safe_step_tac (claset()) 1);

by(filterPrems_drop ["%Delta"] 1);
br mp 1;
by(guidedAssumption ["InitAbsState"] 2);
br mp 1;
by(eres_inst_tac [("P","%(abs_passwd0, rep0, rep_permtab0, wc0, wc_uidtab0, wfiles0) .  \
                       \%(abs_passwd1,rep1,rep_permtab1,wc1,wc_uidtab1,wfiles1).        \
                       \  ((abs_passwd0, rep0, rep_permtab0, wc0, wc_uidtab0, wfiles0)  \
                       \              : (asSet InitAbsState)) =+=>                     \
                       \  (wc1, rep1, rep_permtab1) : AReadProp_ ")] 
                 zrtrancl_full_induct2 2);
by(Asm_full_simp_tac 1);

(* This leaves the induction to show. *)

by(prune_params_tac);

(* first Base Case *)

by(split_all_tac 1);
by(asm_full_simp_tac ((simpset() addsimps [split_def])) 1);
br impI 1;
zbr InitAbsState_implies_AReadProp 1;
by(convert2hol_tac [] 1);

(* second Base Case *)

by(split_all_tac 1);
by(asm_full_simp_tac ((simpset() addsimps [split_def])) 1);
br impI 1;
zbr InitAbsState_implies_AReadProp 1;
by(convert2hol_tac [] 1);

(* Induction Step *)

by(filterPrems_drop ["AbsState (abs_passwd",
		     "AbsState (abs_passwd'",
		     "wfiles) : InitAbsState"] 1);

by(prune_params_tac);

by(split_all_tac 1);
by(asm_full_simp_tac ((simpset() addsimps [split_def])) 1);
by(duplPrem "(x, xd, xg," 1);(* duplicate the command step. *)
by(rewtac theta_def);
bd(asm_full_simplify
       (HOL_ss addsimps[theta_def])
       (stripS AService_imp_Ops)) 1; 
by(rename_tac "  \
              \ abs_passwdx abs_passwdy abs_passwdz repx repy repz \
              \ rep_permtabx rep_permtaby rep_permtabz             \
              \ wcx wcy wcz wc_uidtabx wfilesx wc_uidtaby          \
              \ wfilesy wc_uidtabz wfilesz                         \
              \ " 1);
br impI 1;
be impE 1;
ba 1;

be disjE 1;

(* abs_loginR*)

by(atomizePrem_ex 1);
zbd abs_loginR_AReadProp 1;
ba 1;
ba 1;

be disjE 1;
(* abs_addR*)

by(atomizePrem_ex 1);
zbd abs_addR_AReadProp 1;
ba 1;
ba 1;

be disjE 1;
(* abs_ci - later.*)
by(defer_tac 1);

be disjE 1;
(* abs_up - later.*)
by(defer_tac 1);
be disjE 1;

(* abs_cd *)
by(atomizePrem_ex 1);
zbd abs_cd_AReadProp 1;
ba 1;
ba 1;

(* modifyR *)
by(atomizePrem_ex 1);
zbd modifyR_AReadProp 1;
ba 1;
ba 1;
(*------------------*)
(* leaves: up, ci.  *)
(*------------------*)

(* 1. abs_ci:    lemmata:             *)
(*                                    *)
(* abs_ci_domDiff_permOrder   *)
(* abs_ci_fNeq_permOrder *)
by(atomizePrem_ex 1);
zbr abs_ciR_AReadProp 1;
ba 4;
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(convert2hol_tac [theta_def] 1);
by(convert2hol_tac [theta_def] 1);
ba 1;
(* abs_ciR_AReadProp *)

(* 2. abs_up:    lemmata:             *)
(*                                    *)
(*                                    *)
by(atomizePrem_ex 1);

zbr abs_up_AReadProp 1;
ba 4;
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(convert2hol_tac [theta_def] 1);
by(convert2hol_tac [theta_def] 1);
ba 1;
qed"AReadSec";
*)



(* ============================= *)

(* simplified AReadSec - Proof?  *)


(* ============================= *)




zgoalw SysArchSec.thy [AReadSec_def, Areachable_def] "AReadSec";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [] 1);
by(removeTheta_tac 1);
by(rewtac AtransR_def);
be dom_restrE 1;
(* by( safe_tac ((claset()) addSss (simpset()))); *)
(* ... is useful to substitute the pairs.         *)
by(safe_step_tac (claset()) 1);
by(safe_step_tac (claset()) 1);
by(safe_step_tac (claset()) 1);

by(filterPrems_drop ["%Delta"] 1);
br mp 1;
by(guidedAssumption ["InitAbsState"] 2);
br mp 1;
by(eres_inst_tac [("P","%(abs_passwd0, rep0, rep_permtab0, wc0, wc_uidtab0, wfiles0) .  \
                       \%(abs_passwd1,rep1,rep_permtab1,wc1,wc_uidtab1,wfiles1).        \
                       \  ((abs_passwd0, rep0, rep_permtab0, wc0, wc_uidtab0, wfiles0)  \
                       \              : (asSet InitAbsState)) =+=>                     \
                       \  (wc1, rep1, rep_permtab1) : AReadProp_ ")] 
                 zrtrancl_full_induct2 2);
by(Asm_full_simp_tac 1);

(* This leaves the induction to show. *)

by(prune_params_tac);

(* first Base Case *)

by(split_all_tac 1);
by(asm_full_simp_tac ((simpset() addsimps [split_def])) 1);
br impI 1;
zbr InitAbsState_implies_AReadProp 1;
by(convert2hol_tac [] 1);

(* second Base Case *)

by(split_all_tac 1);
by(asm_full_simp_tac ((simpset() addsimps [split_def])) 1);
br impI 1;
zbr InitAbsState_implies_AReadProp 1;
by(convert2hol_tac [] 1);

(* Induction Step *)

by(filterPrems_drop ["AbsState (abs_passwd",
		     "AbsState (abs_passwd'",
		     "wfiles) : InitAbsState"] 1);

by(prune_params_tac);

by(split_all_tac 1);
by(asm_full_simp_tac ((simpset() addsimps [split_def])) 1);
(*by(rewtac theta_def);*)
by(rename_tac "  \
              \ abs_passwdx abs_passwdy abs_passwdz repx repy repz \
              \ rep_permtabx rep_permtaby rep_permtabz             \
              \ wcx wcy wcz wc_uidtabx wfilesx wc_uidtaby          \
              \ wfilesy wc_uidtabz wfilesz                         \
              \ " 1);
br impI 1;
be impE 1;
ba 1;
(* -- use the main-lemma *)
zbr ref_AReadProp 1;
ba 4;
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(convert2hol_tac [theta_def] 1);
by(convert2hol_tac [theta_def] 1);

qed"AReadSec";






(* ============================= *)

(* simplify AReadSec - Proof?    *)
(* - next Iteration. -           *)

(* ============================= *)




zgoalw SysArchSec.thy [AReadSec_def, Areachable_def] "AReadSec";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [] 1);

br impI 1;
by(duplPrem "<:" 1);
zbd Init_drestr_AtransR_implies_AtransR 1;
zbd Init_drestr_AtransR_implies_Init 1;

by(filterPrems_drop ["%Delta"] 1);

zbd next_ref_AReadProp 1;
ba 1;
ba 1;
qed"AReadSec";
