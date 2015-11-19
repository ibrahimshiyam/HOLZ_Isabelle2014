(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * SimpleAbsOpsImpls.ML --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 2000-2003, University Freiburg, Germany
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
(* $Id: SimpleAbsOpsImpls.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* This file contains lemmas which *)
(* are simple implications of the  *)
(* abstract operations as used in  *)
(* the SysArchSec section:         *)
(*                                 *)
(* - Invariance lemmata:           *)
(*   some operations imply rep=rep'*)
(*                                 *)
(* - valid-start lemmata:          *)
(*   all operations imply AbsState *)
(*   at the beginning.             *)
(*                                 *)
(* - valid-end lemmata:            *)
(*   all operations imply AbsState'*)
(*   at the end.                   *)


(* some simple translation lemmata *)
(* which allow to switch between   *)
(* r-schemata and the corresponding*)
(* standard schemata.              *)

zgoalw SysArchSec.thy [abs_ciR_def] "abs_ciR =+=> abs_ci";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_ciR_implies_abs_ci";


zgoalw SysArchSec.thy [modifyR_def] "modifyR =+=> modify";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"modifyR_implies_modify";


(* Invariance lemmas:              *)
(* all operations (except abs_ci)  *)
(* leave the repository unchanged. *)

(* abs_loginR *)

zgoalw SysArchSec.thy [abs_loginR_def,abs_login_def,theta_def] 
"abs_loginR =+=> rep = rep'";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_loginR_implies_rep_invariant";

(* stronger version *)
zgoalw SysArchSec.thy [abs_loginR_def,abs_login_def,theta_def] 
"abs_loginR =+=> (rep_permtab = rep_permtab' /\\ rep = rep')";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_loginR_implies_repPtab_invariant";

(* abs_addR *)

zgoalw SysArchSec.thy [abs_addR_def,abs_add_def,theta_def] 
"abs_addR =+=> rep = rep'";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_addR_implies_rep_invariant";

(* stronger version *)
zgoalw SysArchSec.thy [abs_addR_def,abs_add_def,theta_def] 
"abs_addR =+=> (rep_permtab = rep_permtab' /\\ rep = rep')";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_addR_implies_repPtab_invariant";


(* abs_modifyR *)

zgoalw SysArchSec.thy [modifyR_def,modify_def,theta_def] 
"modifyR =+=> rep = rep'";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"modifyR_implies_rep_invariant";

(* stronger version *)
zgoalw SysArchSec.thy [modifyR_def,modify_def,theta_def] 
"modifyR =+=> (rep_permtab = rep_permtab' /\\ rep = rep')";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"modifyR_implies_repPtab_invariant";

(* abs_up *)

zgoalw SysArchSec.thy [abs_up_def,theta_def] 
"abs_up =+=> rep = rep'";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_up_implies_rep_invariant";

(* stronger version *)
zgoalw SysArchSec.thy [abs_up_def,theta_def] 
"abs_up =+=> (rep_permtab = rep_permtab' /\\ rep = rep')";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_up_implies_repPtab_invariant";

(* abs_cd *)

zgoalw SysArchSec.thy [abs_cd_def,theta_def] 
"abs_cd =+=> rep = rep'";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_cd_implies_rep_invariant";

(* stronger version *)
zgoalw SysArchSec.thy [abs_cd_def,theta_def] 
"abs_cd =+=> (rep_permtab = rep_permtab' /\\ rep = rep')";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_cd_implies_repPtab_invariant";

(* AbsState implies Client/Rep - State *)

zgoalw SysArchSec.thy [AbsState_def] "AbsState =+=> ClientState";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"AbsState_implies_ClientState";

zgoalw SysArchSec.thy [AbsState_def] "AbsState =+=> RepositoryState";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"AbsState_implies_RepositoryState";


(* valid-start lemmas:             *)
(* all operations imply AbsState.  *)

(* abs_loginR *)

zgoalw SysArchSec.thy [abs_loginR_def,abs_login_def,
		        AbsState_def]
"abs_loginR =+=> AbsState";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_loginR_valid_AbsState";

(* abs_addR *)

zgoalw SysArchSec.thy [abs_addR_def,abs_add_def,
		        AbsState_def]
"abs_addR =+=> AbsState";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_addR_valid_AbsState";

(* modifyR *)

zgoalw SysArchSec.thy [modifyR_def,modify_def,
		        AbsState_def]
"modifyR =+=> AbsState";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"modifyR_valid_AbsState";

(* abs_up *)

zgoalw SysArchSec.thy [abs_up_def,
		        AbsState_def]
"abs_up =+=> AbsState";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_up_valid_AbsState";

(* abs_cd *)

zgoalw SysArchSec.thy [abs_cd_def,
		        AbsState_def]
"abs_cd =+=> AbsState";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_cd_valid_AbsState";

(* abs_ci *)

zgoalw SysArchSec.thy [abs_ci_def,
		        AbsState_def]
"abs_ci =+=> AbsState";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_ci_valid_AbsState";

zgoalw SysArchSec.thy [abs_ciR_def,
		       abs_ci_def,
		        AbsState_def]
"abs_ciR =+=> AbsState";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_ciR_valid_AbsState";



(* valid-end lemmas:               *)
(* all operations imply AbsState'.  *)

(* abs_loginR *)

zgoalw SysArchSec.thy [abs_loginR_def,abs_login_def,
		        AbsState_def]
"abs_loginR =+=> AbsState'";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
qed"abs_loginR_valid_AbsStateS";

(* abs_addR *)

zgoalw SysArchSec.thy [abs_addR_def,abs_add_def,
		        AbsState_def]
"abs_addR =+=> AbsState'";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
qed"abs_addR_valid_AbsStateS";

(* modifyR *)

zgoalw SysArchSec.thy [modifyR_def,modify_def,
		        AbsState_def]
"modifyR =+=> AbsState'";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
qed"modifyR_valid_AbsStateS";

(* abs_up *)

zgoalw SysArchSec.thy [abs_up_def,
		        AbsState_def]
"abs_up =+=> AbsState'";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
qed"abs_up_valid_AbsStateS";

(* abs_cd *)

zgoalw SysArchSec.thy [abs_cd_def,
		        AbsState_def]
"abs_cd =+=> AbsState'";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
qed"abs_cd_valid_AbsStateS";

(* abs_ci *)

zgoalw SysArchSec.thy [abs_ci_def,
		        AbsState_def]
"abs_ci =+=> AbsState'";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
qed"abs_ci_valid_AbsStateS";

zgoalw SysArchSec.thy [abs_ci_def,abs_ciR_def,
		        AbsState_def]
"abs_ciR =+=> AbsState'";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
qed"abs_ciR_valid_AbsStateS";

(* also: InitAbsState implies AbsState *)

zgoalw SysArchSec.thy [InitAbsState_def]
"InitAbsState =+=> AbsState";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
qed"InitAbsState_implies_AbsState";

(* some simple lemmas              *)
(* on set constraints implications *)
(* from AbsState.                  *)

zgoalw SysArchSec.thy [AbsState_def, 
		       RepositoryState_def]
"AbsState =+=> rep : ABS_DATATAB";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"AbsState_implies_repSC";


zgoalw SysArchSec.thy [AbsState_def, 
		       RepositoryState_def]
"AbsState =+=> rep_permtab : ABS_PERMTAB";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"AbsState_implies_repPtabSC";



(* the following lemmata say *)
(* that each operation does  *)
(* not shrink the abs_passwd *)
(* table to {}(assuming ~=   *)
(* {} before)                *)

(* abs_loginR *)

zgoal SysArchSec.thy "  \
\  abs_passwd ~= {}     \
\ =+=>                  \
\ abs_loginR             \
\ =+=> abs_passwd' ~= {}\ 
\  ";
by(stripS_tac 1);
by(convert2hol_tac [abs_loginR_def, abs_login_def] 1);
br elem_notEmpty 1;
qed"abs_loginR_notShrink_absPwd";


(* abs_addR *)

zgoal SysArchSec.thy "  \
\  abs_passwd ~= {}     \
\ =+=>                  \
\ abs_addR               \
\ =+=> abs_passwd' ~= {}\ 
\  ";
by(stripS_tac 1);
by(convert2hol_tac [abs_addR_def, abs_add_def] 1);
qed"abs_addR_notShrink_absPwd";

(* modifyR *)

zgoal SysArchSec.thy "  \
\  abs_passwd ~= {}     \
\ =+=>                  \
\ modifyR               \
\ =+=> abs_passwd' ~= {}\ 
\  ";
by(stripS_tac 1);
by(convert2hol_tac [modifyR_def, modify_def] 1);
qed"modifyR_notShrink_absPwd";

(* abs_up *)

zgoal SysArchSec.thy "  \
\  abs_passwd ~= {}     \
\ =+=>                  \
\ abs_up                \
\ =+=> abs_passwd' ~= {}\ 
\  ";
by(stripS_tac 1);
by(convert2hol_tac [abs_up_def] 1);
qed"abs_up_notShrink_absPwd";

(* abs_cd *)

zgoal SysArchSec.thy "  \
\  abs_passwd ~= {}     \
\ =+=>                  \
\ abs_cd                \
\ =+=> abs_passwd' ~= {}\ 
\  ";
by(stripS_tac 1);
by(convert2hol_tac [abs_cd_def] 1);
qed"abs_cd_notShrink_absPwd";

(* abs_ci *)

zgoal SysArchSec.thy "  \
\  abs_passwd ~= {}     \
\ =+=>                  \
\ abs_ci                \
\ =+=> abs_passwd' ~= {}\ 
\  ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_ci_def 1);
bd DECL_D1 1;
by(convert2hol_tac [XI_def] 1);
auto();
qed"abs_ci_notShrink_absPwd";

zgoal SysArchSec.thy "  \
\  abs_passwd ~= {}     \
\ =+=>                  \
\ abs_ciR                \
\ =+=> abs_passwd' ~= {}\ 
\  ";
by(stripS_tac 1);
zbd abs_ciR_implies_abs_ci 1;
zbd abs_ci_notShrink_absPwd 1;
by(AtomizePremSolveAll);
qed"abs_ciR_notShrink_absPwd";


(* this is a simple implication *)
(* lemma for abs_loginR.        *)

zgoal SysArchSec.thy "abs_loginR =+=> (%Xi RepositoryState)";
by(stripS_tac 1);
by(convert2hol_tac [abs_loginR_def, abs_login_def] 1);
qed"abs_loginR_Imp_thetaRepState";

bind_thm ("abs_loginR_I_thetaRepState", (stripS abs_loginR_Imp_thetaRepState));

zgoal SysArchSec.thy "abs_loginR =+=> wc = wc'";
by(stripS_tac 1);
by(convert2hol_tac [abs_loginR_def, abs_login_def] 1);
qed"abs_loginR_invariant_wc";

(* a variant for abs_cd *)

zgoal SysArchSec.thy "abs_cd =+=> (%Xi RepositoryState)";
by(stripS_tac 1);
by(convert2hol_tac [ abs_cd_def] 1);
qed"abs_cd_implies_XiRepState";

zgoal SysArchSec.thy "abs_cd =+=> wc = wc'";
by(stripS_tac 1);
by(convert2hol_tac [abs_cd_def] 1);
qed"abs_cd_invariant_wc";

(* a variant for abs_ci *)

zgoal SysArchSec.thy "abs_ci =+=> wc = wc'";
by(stripS_tac 1);
by(convert2hol_tac [abs_ci_def] 1);
qed"abs_ci_invariant_wc";



(* these lemmata are simple     *)
(* implications for invariance  *)
(* of abs_passwd.               *)

zgoal SysArchSec.thy "abs_add =+=> (abs_passwd = abs_passwd')";
by(stripS_tac 1);
by(convert2hol_tac [abs_add_def] 1);
qed"abs_add_invariant_absPwd";


zgoal SysArchSec.thy "abs_up  =+=> (abs_passwd = abs_passwd')";
by(stripS_tac 1);
by(convert2hol_tac [abs_up_def] 1);
qed"abs_up_invariant_absPwd";

zgoal SysArchSec.thy "modifyR  =+=> (abs_passwd = abs_passwd')";
by(stripS_tac 1);
by(convert2hol_tac [modifyR_def, modify_def] 1);
qed"modifyR_invariant_absPwd";

zgoal SysArchSec.thy "abs_ci  =+=> (abs_passwd = abs_passwd')";
by(stripS_tac 1);
by(convert2hol_tac [abs_ci_def] 1);
qed"abs_ci_invariant_absPwd";

zgoal SysArchSec.thy "abs_ciR  =+=> (abs_passwd = abs_passwd')";
by(stripS_tac 1);
by(convert2hol_tac [abs_ci_def, abs_ciR_def] 1);
qed"abs_ciR_invariant_absPwd";

zgoal SysArchSec.thy "abs_cd  =+=> (abs_passwd = abs_passwd')";
by(stripS_tac 1);
by(convert2hol_tac [abs_cd_def] 1);
qed"abs_cd_invariant_absPwd";


(* these lemmata are simple     *)
(* implications for invariance  *)
(* of wc_uidtab                 *)


zgoal SysArchSec.thy "abs_loginR  =+=> (wc_uidtab = wc_uidtab')";
by(stripS_tac 1);
by(convert2hol_tac [abs_loginR_def, abs_login_def] 1);
qed"abs_loginR_invariant_wcUidtb";

zgoal SysArchSec.thy "modifyR  =+=> (wc_uidtab = wc_uidtab')";
by(stripS_tac 1);
by(convert2hol_tac [modifyR_def, modify_def] 1);
qed"modifyR_invariant_wcUidtb";

zgoal SysArchSec.thy "abs_ci  =+=> (wc_uidtab = wc_uidtab')";
by(stripS_tac 1);
by(convert2hol_tac [abs_ci_def] 1);
qed"abs_ci_invariant_wcUidtb";

zgoal SysArchSec.thy "abs_cd  =+=> (wc_uidtab = wc_uidtab')";
by(stripS_tac 1);
by(convert2hol_tac [abs_cd_def] 1);
qed"abs_cd_invariant_wcUidtb";
