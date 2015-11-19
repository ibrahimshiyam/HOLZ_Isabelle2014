(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_read_up_lemmata.ML --- 
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
(* $Id: abs_read_up_lemmata.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* Main Lemmata for this proof: *)
(* ---------------------------- *)
(* user_or_invented          *)
(* wc_Ainvents       *)
(* owner_inRep_implies_perm     *)

(* old version, using abs_up *)
zgoal SysArchSec.thy "(%theta AbsState'', %theta AbsState) :   \
\  AtransR                                                     \
\ =+=>                                                         \
\ (%theta AbsState'') : InitAbsState                           \
\ =+=>                                                         \
\   ((%theta AbsState, %theta AbsState') :                     \
\    {.AService @ (%theta AbsState, %theta AbsState').} )      \
\ =+=>                                                         \
\  abs_up                                                      \
\               =+=>                                           \
\ (wc, rep, rep_permtab)                                       \
\  : AReadProp_                                                \
\               =+=>                                           \
\  (wc', rep', rep_permtab')                                   \
\  : AReadProp_   ";

by(stripS_tac 1);

(* exchange AReadProp in goal *)
zbr replace_AReadProp 1;

zbd (abs_up_valid_AbsStateS
     ZRS
     AbsState_implies_ClientState
     ZRS
     type_wc) 1;
ba 1;
zbd (abs_up_valid_AbsStateS
	 ZRS
	 AbsState_implies_repSC) 1;
ba 1;
zbd (abs_up_valid_AbsStateS
	 ZRS
	 AbsState_implies_repPtabSC) 1;
ba 1;
(* /exchange AReadProp in goal *)
(* exchange AReadProp in the assumptions *)
br mp 1;
by(guidedAssumption ["AReadProp"] 2);
by(res_inst_tac [("t",
		  "(wc, rep, rep_permtab) : AReadProp_")] 
		subst 1);
br sym 1;
br instantiateARead_def 1;
(* set constraints from unfolding the prop *)
zbd (abs_up_valid_AbsState
     ZRS
     AbsState_implies_ClientState
     ZRS
     type_wc) 1;
ba 1;
zbd (abs_up_valid_AbsState
     ZRS
     AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_rep) 1;
ba 1;
zbd (abs_up_valid_AbsState
     ZRS
     AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_repPtb) 1;
ba 1;
br impI 1;
(* - replaced both occurences of   *)
(* AProp   ----                    *)
br ballI 1;

(* need lengthened hull *)
by(rewtac AtransR_def);
bd zrtrancl_into_zrtrancl 1;
ba 1;
by(res_inst_tac [("P", "n : dom wc_uidtab'"), 
		 ("Q", "(n, wc' %^ n) : Ainvents")] 
		disjE 1);
(* user_or_invented *)
zbr user_or_invented 1;
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(convert2hol_tac [] 1);
ba 1;
(* Now 2 cases:                      *)
(* case 2 : (n, wc' %^ n) : Ainvents *)
br disjI1 2;
ba 2;
(* case 1 : n : dom wc_uidtab'       *)
by(case_tac "n : dom rep'" 1);
(* case 1a : n : dom rep'            *)

(* br disjI2 1; *)
(* zbr owner_inRep_implies_perm 1; *)
zbr owner_inRep_AinvOrPerm 1;

by(convert2hol_tac [AtransR_def] 1);
by(convert2hol_tac [] 1);
ba 1;
ba 1;
(* case 1b : n ~: dom rep'           *)
br disjI1 1;
zbr (removeTheta wc_Ainvents) 1;
by(convert2hol_tac [AtransR_def] 1);
by(convert2hol_tac [] 1);
ba 1;
ba 1;
qed"abs_up_AReadProp";


(* test to simplify proof: *)
(* drop abs_up.            *)
(* AbsStateAfterAService   *)
(* AbsStateBeforeAService  *)
(* for the setCons.        *)
(* ... worked!!!!!         *)

zgoal SysArchSec.thy "(%theta AbsState'', %theta AbsState) :   \
\  AtransR                                                     \
\ =+=>                                                         \
\ (%theta AbsState'') : InitAbsState                           \
\ =+=>                                                         \
\   ((%theta AbsState, %theta AbsState') :                     \
\    {.AService @ (%theta AbsState, %theta AbsState').} )      \
\ =+=>                                                         \
\ (wc, rep, rep_permtab)                                       \
\  : AReadProp_                                                \
\               =+=>                                           \
\  (wc', rep', rep_permtab')                                   \
\  : AReadProp_   ";

by(stripS_tac 1);

(* exchange AReadProp in goal *)
zbr replace_AReadProp 1;
(* by(duplPrem "AService" 1);*)
zbd (AbsStateAfterAService) 1;

zbr (removeSNAME(AbsState_implies_ClientState
     ZRS
     type_wc)) 1;
by(convert2hol_tac [] 1);

zbd (AbsStateAfterAService) 1;
zbr AbsState_implies_repSC 1;
by(convert2hol_tac [] 1);

zbd (AbsStateAfterAService) 1;
zbr  AbsState_implies_repPtabSC 1;
by(convert2hol_tac [] 1);

(* /exchange AReadProp in goal *)
(* exchange AReadProp in the assumptions *)
br mp 1;
by(guidedAssumption ["AReadProp"] 2);
by(res_inst_tac [("t",
		  "(wc, rep, rep_permtab) : AReadProp_")] 
		subst 1);
br sym 1;
br instantiateARead_def 1;
(* set constraints from unfolding the prop *)
zbd AbsStateBeforeAService 1;
zbr (AbsState_implies_ClientState
     ZRS
     type_wc) 1;
by(convert2hol_tac [] 1);

zbd AbsStateBeforeAService 1;
zbr (AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_rep) 1;
by(convert2hol_tac [] 1);

zbd AbsStateBeforeAService 1;
zbr (AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_repPtb) 1;
by(convert2hol_tac [] 1);

br impI 1;
(* - replaced both occurences of   *)
(* AProp   ----                    *)
br ballI 1;

(* need lengthened hull *)
by(rewtac AtransR_def);
bd zrtrancl_into_zrtrancl 1;
ba 1;
by(res_inst_tac [("P", "n : dom wc_uidtab'"), 
		 ("Q", "(n, wc' %^ n) : Ainvents")] 
		disjE 1);
(* user_or_invented *)
zbr user_or_invented 1;
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(convert2hol_tac [] 1);
ba 1;
(* Now 2 cases:                      *)
(* case 2 : (n, wc' %^ n) : Ainvents *)
br disjI1 2;
ba 2;
(* case 1 : n : dom wc_uidtab'       *)
by(case_tac "n : dom rep'" 1);
(* case 1a : n : dom rep'            *)
(* br disjI2 1;                      *)
(* zbr owner_inRep_implies_perm 1;   *)

zbr owner_inRep_AinvOrPerm 1;

by(convert2hol_tac [AtransR_def] 1);
by(convert2hol_tac [] 1);
ba 1;
ba 1;
(* case 1b : n ~: dom rep'           *)
br disjI1 1;
zbr (removeTheta wc_Ainvents) 1;
by(convert2hol_tac [AtransR_def] 1);
by(convert2hol_tac [] 1);
ba 1;
ba 1;
qed"ref_AReadProp";



(* test for a further simplification:     *)
(* is IV really needed? Is the induction  *)
(* superfluous?                           *)

zgoal SysArchSec.thy "(%theta AbsState, %theta AbsState') :   \
\  AtransR                                                     \
\ =+=>                                                         \
\ (%theta AbsState) : InitAbsState                           \
\               =+=>                                           \
\  (wc', rep', rep_permtab')                                   \
\  : AReadProp_   ";

by(stripS_tac 1);

(* AbsStateAfterInitAtransR *)

(* exchange AReadProp in goal *)
zbr replace_AReadProp 1;
(* by(duplPrem "AService" 1);*)
(* wc' *)
zbd (AbsStateAfterInitAtransR) 1;
ba 1;
zbr (AbsState_implies_ClientState ZRS type_wc) 1;
by(convert2hol_tac [] 1);
(* rep' *)
zbd (AbsStateAfterInitAtransR) 1;
ba 1;
zbr AbsState_implies_repSC 1;
by(convert2hol_tac [] 1);
(* rep_permtab' *)
zbd (AbsStateAfterInitAtransR) 1;
ba 1;
zbr  AbsState_implies_repPtabSC 1;
by(convert2hol_tac [] 1);

(* /exchange AReadProp in goal *)

(* - replaced occurence of         *)
(* AProp   ----                    *)


br ballI 1;

(* need lengthened hull *)
(* not anymore ?
by(rewtac AtransR_def);
bd zrtrancl_into_zrtrancl 1;
ba 1;
*)

by(res_inst_tac [("P", "n : dom wc_uidtab'"), 
		 ("Q", "(n, wc' %^ n) : Ainvents")] 
		disjE 1);
(* user_or_invented *)
zbr user_or_invented 1;
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(convert2hol_tac [] 1);
ba 1;
(* Now 2 cases:                      *)
(* case 2 : (n, wc' %^ n) : Ainvents *)
br disjI1 2;
ba 2;
(* case 1 : n : dom wc_uidtab'       *)
by(case_tac "n : dom rep'" 1);
(* case 1a : n : dom rep'            *)
(* br disjI2 1;                      *)
(* zbr owner_inRep_implies_perm 1;   *)


zbr owner_inRep_AinvOrPerm 1;


by(convert2hol_tac [AtransR_def] 1);
by(convert2hol_tac [] 1);
ba 1;
ba 1;
(* case 1b : n ~: dom rep'           *)
br disjI1 1;
zbr (removeTheta wc_Ainvents) 1;
by(convert2hol_tac [AtransR_def] 1);
by(convert2hol_tac [] 1);
ba 1;
ba 1;

qed"next_ref_AReadProp";

