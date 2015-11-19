(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * BasicAbsServiceStateImpls.ML --- 
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
(* $Id: BasicAbsServiceStateImpls.ML 6746 2007-08-03 07:25:55Z brucker $ *)


(* this file contains basic implications which *)
(* concern AbsState and AService.              *)
(*                                             *)
(* EG. lemma AService_imp_Ops allows the user  *)
(* to exchange a command step by the           *)
(* disjunction of the commands.                *)


(* lemma AbsStateAfterInitAbsState*)

val [prem] = goalw SysArchSec.thy []
"InitAbsState(abs_passwd, rep, rep_permtab, wc, wc_uidtab, wfiles) ==> \
\ AbsState(abs_passwd, rep, rep_permtab, wc, wc_uidtab, wfiles)";
br mp 1;
br prem 2;
br impI 1;
by(full_expand_schema_tac InitAbsState_def 1);
be conjE 1;
by(rewtac SNAME_def);
ba 1;
qed"AbsStateAfterInitAbsState";

(* derive Areachable from hull and initAbsState *)

zgoal SysArchSec.thy "  \
\ (%theta AbsState, %theta AbsState') : AtransR  \
\ =+=>                  \
\ (%theta AbsState) : InitAbsState  \
\ =+=>                  \
\ (%theta AbsState, %theta AbsState') : Areachable  \
\ ";
by(stripS_tac 1);
by(convert2hol_tac [Areachable_def, dom_restr_def] 1);
qed"hullInit_implies_Areachable";


(*                        *)
(* lemma AService_imp_Ops *)
(*                        *)

(* A valid transition means *)
(* one op was carried out.  *)

zgoal SysArchSec.thy "((%theta AbsState, %theta AbsState') : \
\    {.AService @ (%theta AbsState, %theta AbsState').} )\
\ =+=>     \
\     ((? passwd?. ( ? uid? . abs_loginR))\
\     \\/                                         \
\       ( ? newfiles? : ABS_DATATAB .abs_addR)    \
\     \\/                                         \
\       ( ? files? : (%P Abs_Name) .abs_ciR)       \
\     \\/                                         \
\       ( ? files? : (%P Abs_Name) .abs_up)       \
\     \\/                                         \
\       ( ? wfiles? : (%P Abs_Name) .abs_cd)      \
\     \\/                                         \
\       ( ? newData? : Abs_Data . ( ? filename? : Abs_Name . modifyR))\
\ )";
by(stripS_tac 1);

(* by(safe_tac (claset() addss simpset()) ); *)
(* by(asm_full_simp_tac (simpset() addsimps [SSet_def, theta_def, image_def]) 1); *)
by(convert2hol_tac [AService_def, SSet_def,image_def] 1);
by(Asm_full_simp_tac 1);


(* eliminate : abs_loginR  *)
by(etac disjE 1);
br disjI1 1;
ba 1;

(* eliminate : abs_addR    *)
by(etac disjE 1);
br disjI2 1;
br disjI1 1;
by(convert2hol_tac [abs_addR_def] 1);
by(Blast_tac 1);

(* other 4 op`s eliminated automatically *)
auto();

qed"AService_imp_Ops";


bind_thm("AService_imp_Ops_nTh",
	 (asm_full_simplify
	      (HOL_ss addsimps[theta_def])
	      (stripS AService_imp_Ops)));

(* same as before but now       *)
(* avoid the theta formulation. *)
(* I still keep it for legacy   *)
(* reasons - better use         *)
(* AService_imp_Ops_nTh instead *)

zgoal SysArchSec.thy " (x, y) : {.AService @ (%theta AbsState, %theta AbsState').}     \
\ =+=>                                                                                 \
\  ((%(abs_passwd,rep,rep_permtab,wc,wc_uidtab,wfiles) (abs_passwdS,                   \
\              repS,rep_permtabS,wcS,wc_uidtabS,wfilesS).                              \
\     ((? passwdq. ( ? uidq . (abs_passwd, abs_passwdS, passwdq, rep, repS, rep_permtab, \
\         rep_permtabS, uidq, wc, wcS, wc_uidtab, wc_uidtabS, wfiles,                  \
\         wfilesS) : abs_loginR))                                                      \
\     \\/                                                                              \
\       ( ? newfilesq : ABS_DATATAB . (abs_passwd, abs_passwdS, newfilesq, rep, repS, rep_permtab, \
\         rep_permtabS, wc, wcS, wc_uidtab, wc_uidtabS, wfiles, wfilesS) : abs_addR)   \
\     \\/                                                                              \
\       ( ? filesq : (%P Abs_Name) . (abs_passwd, abs_passwdS, filesq, rep, repS, rep_permtab, \
\        rep_permtabS, wc, wcS, wc_uidtab, wc_uidtabS, wfiles, wfilesS) : abs_ciR)      \
\     \\/                                                                              \
\       ( ? filesq : (%P Abs_Name) . (abs_passwd, abs_passwdS, filesq, rep, repS, rep_permtab, \
\         rep_permtabS, wc, wcS, wc_uidtab, wc_uidtabS, wfiles, wfilesS) : abs_up)     \
\     \\/                                                                              \
\       ( ? wfilesq : (%P Abs_Name) . (abs_passwd, abs_passwdS, rep, repS, rep_permtab, rep_permtabS, wc, \
\         wcS, wc_uidtab, wc_uidtabS, wfiles, wfilesS, wfilesq) : abs_cd)              \
\     \\/                                                                              \
\       ( ? newDataq : Abs_Data . ( ? filenameq : Abs_Name . (abs_passwd, abs_passwdS, \
\        filenameq, newDataq, rep, repS,                                               \
\         rep_permtab, rep_permtabS, wc, wcS, wc_uidtab, wc_uidtabS, wfiles,           \
\         wfilesS) : modifyR)) ))                                                      \
\     x y) \
\ ";
by(stripS_tac 1);
br mp 1;
br (stripS AService_imp_Ops) 2;
by(convert2hol_tac [split_def] 1);
by(Blast_tac 1);

by(pair_tac "x" 1);
by(pair_tac "ya" 1);
by(pair_tac "yaa" 1);
by(pair_tac "yb" 1);
by(pair_tac "yc" 1);

by(pair_tac "y" 1);
by(pair_tac "ye" 1);
by(pair_tac "yf" 1);
by(pair_tac "yg" 1);
by(pair_tac "yh" 1);

by(convert2hol_tac [split_def] 1);
qed"AService_imp_Ops_nTh1";


(* lemma which proves that       *)
(* an arbitrary command step     *)
(* implies a valid initial state *)

zgoalw SysArchSec.thy [theta_def]
"(x,y) : {. AService @(%theta AbsState, %theta AbsState').} =+=> x : AbsState";
by(stripS_tac 1);

by(split_all_tac 1);
by(pair_tac "y" 1);
by(pair_tac "ya" 1);
by(pair_tac "yb" 1);
by(pair_tac "yc" 1);
by(pair_tac "yd" 1);

bd AService_imp_Ops_nTh 1;

by(prune_params_tac);

by(rename_tac "abs_passwd rep rep_permtab wc wc_uidtab wfiles \
\        abs_passwdS repS rep_permtabS wcS wc_uidtabS wfilesS" 1);
auto();
(* Now handle 6 cases: one *)
(* for each operation.     *)

(* abs_loginR *)
bd (stripS abs_loginR_valid_AbsState) 1;
by(convert2hol_tac [] 1);

(* abs_addR *)
bd (stripS abs_addR_valid_AbsState) 1;
by(convert2hol_tac [] 1);(*--*)

(* abs_ci *)
bd (stripS abs_ciR_valid_AbsState) 1;
by(convert2hol_tac [] 1);

(* abs_up *)
bd (stripS abs_up_valid_AbsState) 1;
by(convert2hol_tac [] 1);

(* abs_cd *)
bd (stripS abs_cd_valid_AbsState) 1;
by(convert2hol_tac [] 1);

(* modifyR *)
bd (stripS modifyR_valid_AbsState) 1;
by(convert2hol_tac [] 1);

qed"AbsStateBeforeAService";



(* no-theta-version: *)

bind_thm ("AbsStateBeforeAService_nTh", 
	  (asm_full_simplify
	       (HOL_ss addsimps[theta_def]) 
	       (stripS AbsStateBeforeAService)));



(* lemma AbsStateAfterAService *)
(* one command step preserves  *)
(* System Invariant.           *)

zgoalw SysArchSec.thy [theta_def]
"(x,y) : {. AService @(%theta AbsState, %theta AbsState').} =+=> y : AbsState'";
by(stripS_tac 1);

by(split_all_tac 1);
by(pair_tac "x" 1);
by(pair_tac "y" 1);
by(pair_tac "yb" 1);
by(pair_tac "yc" 1);
by(pair_tac "yd" 1);

bd AService_imp_Ops_nTh 1;

by(prune_params_tac);

by(rename_tac "abs_passwd rep rep_permtab wc wc_uidtab wfiles \
\        abs_passwdS repS rep_permtabS wcS wc_uidtabS wfilesS" 1);
auto();
(* Now handle 6 cases: one *)
(* for each operation.     *)

(* abs_loginR *)
bd (stripS abs_loginR_valid_AbsStateS) 1;
by(convert2hol_tac [] 1);

(* abs_addR *)
bd (stripS abs_addR_valid_AbsStateS) 1;
by(convert2hol_tac [] 1);

(* abs_ci *)
bd (stripS abs_ciR_valid_AbsStateS) 1;
by(convert2hol_tac [] 1);

(* abs_up *)
bd (stripS abs_up_valid_AbsStateS) 1;
by(convert2hol_tac [] 1);

(* abs_cd *)
bd (stripS abs_cd_valid_AbsStateS) 1;
by(convert2hol_tac [] 1);

(* modifyR *)
bd (stripS modifyR_valid_AbsStateS) 1;
by(convert2hol_tac [] 1);

qed"AbsStateAfterAService";



(* no-theta-version: *)

bind_thm ("AbsStateAfterAService_nTh", 
	  (asm_full_simplify
	       (HOL_ss addsimps[theta_def]) 
	       (stripS AbsStateAfterAService)));



(* lemma AbsStateInAreachable1    *)
(* This lemma goes via lemma      *)
(* AbsStateAfterAService over the *) 
(* rtrancl.                       *)

(* this is a relict:                       *)
(* Areachable1 was AtransR(|InitAbsState|) *)
(*
val [prem] = goalw SysArchSec.thy []
"Areachable1(abs_passwd, rep, rep_permtab, wc, wc_uidtab, wfiles) \
\       ==> AbsState                                               \
\            (abs_passwd, rep, rep_permtab, wc, wc_uidtab, wfiles)";
br mp 1;
br prem 2;
*)
(* This is a workaround which *)
(* shall afterwards allow     *)
(* using findI to find this   *)
(* lemma.                     *)
(*
br impI 1;
by(rewrite_goals_tac[Areachable1_def, AtransR_def]);
by(res_inst_tac[("q","(abs_passwd, rep, rep_permtab, wc, wc_uidtab, wfiles)")] reach_induct 1);
by(rewrite_goals_tac[asPred_def]);(* *)
ba 1;

bd (stripS AbsStateAfterAService) 2;
by (convert2hol_tac [] 2);

by(convert2hol_tac [InitAbsState_def, AbsState_def] 1); 
auto();

qed"AbsStateInAreachable1";
*)


(* show AbsState after InitAbsState & AtransR *)

zgoal SysArchSec.thy "  \ 
\ (%theta AbsState): InitAbsState   \
\ =+=> (%theta AbsState, %theta AbsState'):  AtransR  \
\ =+=> (%theta AbsState'):AbsState'";
by(stripS_tac 1);
br mp 1;
ba 2;
br mp 1;
by(rewtac AtransR_def);

by(eres_inst_tac [("P","%(abs_passwd0, rep0, rep_permtab0, wc0, wc_uidtab0, wfiles0) .  \
                       \%(abs_passwd1,rep1,rep_permtab1,wc1,wc_uidtab1,wfiles1).        \
                       \  ((abs_passwd0, rep0, rep_permtab0, wc0, wc_uidtab0, wfiles0)  \
                       \              : (asSet InitAbsState)) =+=>                      \
                       \  ((abs_passwd1, rep1, rep_permtab1, wc1, wc_uidtab1, wfiles1)  \
                       \              : (asSet AbsState))  ")] 
                 zrtrancl_full_induct2 2);
by(contractVec 1);

(*                 *)
(* first Base Case *)
(* by(contractVec 1); *)

by(pair_tac "x" 1);
by(pair_tac "y" 1);
by(pair_tac "ya" 1);
by(pair_tac "yb" 1);
by(pair_tac "yc" 1);
(* candidate for similar contraction *)
by((asm_full_simp_tac 
	(HOL_ss addsimps 
		[split_def, fst_conv, 
		 snd_conv, Pair_eq]))1);
br impI 1;
br mp 1;
zbr InitAbsState_implies_AbsState 2;
by(filterPrems_drop ["%theta AbsState"] 2);
by(convert2hol_tac [] 2);
by(convert2hol_tac [] 1);
(* *)
(* second base case *)

by(pair_tac "y" 1);
by(pair_tac "ya" 1);
by(pair_tac "yb" 1);
by(pair_tac "yc" 1);
by(pair_tac "yd" 1);
by((asm_full_simp_tac 
	(HOL_ss addsimps 
		[split_def, fst_conv, 
		 snd_conv, Pair_eq]))1);
br impI 1;
br mp 1;
zbr InitAbsState_implies_AbsState 2;
by(filterPrems_drop ["%theta AbsState"] 2);
by(convert2hol_tac [] 2);
by(convert2hol_tac [] 1);

(* induction step ---------------*)
zbd AbsStateAfterAService 1;

by(pair_tac "z" 1);
by(pair_tac "ya" 1);
by(pair_tac "yb" 1);
by(pair_tac "yc" 1);
by(pair_tac "yd" 1);

by((asm_full_simp_tac 
	(HOL_ss addsimps 
		[split_def, fst_conv, 
		 snd_conv, Pair_eq]))1);
qed"AbsStateAfterInitAtransR";
 


(* These Lemmata are not used, but maybe still interesting.

zgoal SysArchSec.thy "                                  \
\ AService =+=>                                         \
\  (%theta AbsState, %theta AbsState')                  \
\  : {.AService @ (%theta AbsState, %theta AbsState').} ";
by(stripS_tac 1);
by(rewtac SSet_def);
by(rewtac image_def);
auto();
br bexI 1;
by(convert2hol_tac [SNAME_def] 2);
br conjI 1;
by(convert2hol_tac [] 1);
by(convert2hol_tac [] 1);
qed"AService_imp_SSetAService";



zgoal SysArchSec.thy "                            \
\     ((? passwd?. ( ? uid? . abs_loginR))        \
\     \\/                                         \
\       ( ? newfiles? : ABS_DATATAB .abs_addR)    \
\     \\/                                         \
\       ( ? files? : (%P Abs_Name) .abs_ciR)      \
\     \\/                                         \
\       ( ? files? : (%P Abs_Name) .abs_up)       \
\     \\/                                         \
\       ( ? wfiles? : (%P Abs_Name) .abs_cd)      \
\     \\/                                         \
\       ( ? newData? : Abs_Data . ( ? filename? : Abs_Name . modifyR)) \
\ )                                               \
\  =+=>                                           \
\  ((%theta AbsState, %theta AbsState') :         \
\    {.AService @ (%theta AbsState, %theta AbsState').} ) ";
by(stripS_tac 1);

by(convert2hol_tac [SSet_def, image_def, 
		    AService_def, theta_def] 1);
by(depth_tac ((claset()) addss (simpset())) 2 1);
qed"ops_imp_AService";


zgoal SysArchSec.thy "                                  \
\      abs_ciR        =+=>                              \
\ (%theta AbsState, %theta AbsState')                   \
\  : {.AService @ (%theta AbsState, %theta AbsState').} ";
by(stripS_tac 1);
zbr ops_imp_AService 1;
auto();
qed"abs_ciR_implies_AService";

*)


zgoal SysArchSec.thy "  \ 
\ (%theta AbsState, %theta AbsState'):  InitAbsState <: AtransR  \
\ =+=> (%theta AbsState): InitAbsState  ";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
qed"Init_drestr_AtransR_implies_Init";



zgoal SysArchSec.thy "  \ 
\ (%theta AbsState, %theta AbsState'):  InitAbsState <: AtransR  \
\ =+=> (%theta AbsState, %theta AbsState'): AtransR  ";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
qed"Init_drestr_AtransR_implies_AtransR";

