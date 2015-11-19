(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * permAdmin_abs_ci_impls.ML --- 
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
(* $Id: permAdmin_abs_ci_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)


(* This file contains consequences of      *)
(* interactions with the system and commit,*)
(* especcialy concerning admin permission. *)


(* The following lemmata were initially    *)
(* tailored for proving                    *)
(* authtab rep (role, absPwd role):CvsPerm *)

(* this is a variant of an existing lemma. *)
(* show: abs_cvsauth : dom wc_uidtab       *)

(*
Like this, avoid using metavariables:
%%%%%%%zgoal AbsOperations.thy "      \
\ abs_ci =+=>   \
\ rep %^ abs_cvsauth ~= rep' %^ abs_cvsauth \
\ =+=> ((% x. x : dom wc_uidtab)abs_cvsauth)";
*)

zgoal thy "      \
\  abs_ci =+=>   \
\ rep %^ ?X ~= rep' %^ ?X \
\ =+=> ?X : dom wc_uidtab";
by(stripS_tac 1);
zbr abs_ci_fNeq_defined_wcUtb 1;
ba 1;
ba 2;
by(full_expand_schema_tac abs_ci_def 1);
bd DECL_D1 1;
zbr abs_cvsauth_inDom_rep 1;
by(rewtac DELTA_def);
by(atomizePremSolve 1);
qed"auth_inDom_wcUtb";


zgoal thy "                    \
\  abs_ci                      \
\ =+=>                         \
\ rep %^ ?X ~= rep' %^ ?X      \
\ =+=>                         \
\ (wc_uidtab %^ ?X) : Cvs_Uid ";
by(stripS_tac 1);
br pfun_appl 1;
zbd abs_ci_valid_AbsState 1;
zbd AbsState_implies_ClientState 1;
by(full_expand_schema_tac ClientState_def 1);
bd DECL_D1 1;
by(atomizePrem 1);
by(rewrite_goals_tac [ABS_UIDTAB_def]);
ba 1;
zbr auth_inDom_wcUtb 1;
ba 1;
ba 1;
qed"wcUidtb_abscvsauth_in_CvsUid";


zgoal thy "                    \
\  abs_ci                      \
\ =+=>                         \
\ rep %^ ?X ~= rep' %^ ?X      \
\ =+=>                         \
\  ((wc_uidtab %^ ?X),         \
\ (abs_passwd %^ (wc_uidtab %^ ?X) )) \
\ : dom (authtab %^ rep)  ";
by(stripS_tac 1);
br mp 1;
ba 2;
by(expand_schema_tac abs_ci_def 1);
br impI 1;
be DECL_E 1;
by(atomizePrem 1);
by(filterPrems_drop ["rep_permtab' ="] 1);
(* from other proof in abs_ci *)
bd trans 1;
zbr (Overrid_Compose RS sym) 1; (* HH *)
br mp 1;
br  neqAppl_domTrace_overrid 2;
ba 3;
br nsym 3;
ba 3;
zbr abs_cvsauth_inDom_rep 2;
by(convert2hol_tac [DELTA_def] 2);
by(atomizePremSolve 2);
by(hyp_subst_tac 2);
ba 2;
by(filterPrems_drop ["rep' ="] 1);
br impI 1;

bd domTrace_Overrid_short 1;

(* show that abs_cvsauth ~: rep_new *)
(* (contradict via abs_cvsauth_inDom_rep *)
br ccontr 1;
bd notNotinD 1;
zbd inDom_restrProp 1;
by(res_inst_tac [("P","abs_cvsauth : dom rep")] notE 1);
by(atomizePremSolve 1);
zbr abs_cvsauth_inDom_rep 1;
by(convert2hol_tac [DELTA_def] 1);
by(atomizePremSolve 1);
(* L33 *)

zbd inDom_restrProp 1;
by(atomizePrem 1);

zbr has_access_implies_up_inDom_auth 1;
ba 1;
by(convert2hol_tac [DELTA_def] 1); 
zbr RepState_implies_type_repPtb 1;
by(atomizePrem 1);
by(convert2hol_tac [] 1);

by(convert2hol_tac [DELTA_def] 1); 
zbr RepState_implies_type_rep 1;
by(atomizePrem 1);
by(convert2hol_tac [] 1);
(* halted here.*)
zbr type_absPwd 1;
by(convert2hol_tac [XI_def] 1);
by(atomizePremSolve 1);
zbr type_abs_cvsauth 1;
br pfun_appl 1;
ba 2;
by(convert2hol_tac [XI_def] 1);
by(atomizePrem 1);
br mp 1;
zbr type_wcUidtab 2;
by(rewrite_goals_tac [ABS_UIDTAB_def]);
br impI 1;
ba 1;
by(convert2hol_tac [] 1);
qed"abs_ci_authNeq_defined";

(*
This used a temporary predicate inside abs_ciR
zgoal thy "                     \
\  abs_ciR                      \
\  =+=>                         \
\ (%theta AbsState'', %theta AbsState) : AtransR \
\  =+=>                         \
\ (%theta AbsState'') : InitAbsState \
\  =+=>                         \
\ ?X : dom wc_uidtab            \
\  =+=>                         \
\ authtab %^ rep %^             \
\ ((wc_uidtab %^ abs_cvsauth),  \
\ abs_passwd %^ (wc_uidtab %^ abs_cvsauth)) \
\ ~= cvs_admin ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_ciR_def 1);
be conjE 1;
bd DECL_D2 1;
by(res_inst_tac [("x", "wc_uidtab %^ abs_cvsauth"), 
		 ("A", "dom abs_passwd")] bspec 1);
zbr definedAbsPwd 2;
by(convert2hol_tac [AtransR_def] 2);
by(convert2hol_tac [] 2);
ba 2;
ba 1;
qed"perm_neq_admin";
*)


(*
This used a temporary predicate inside abs_ciR
zgoal thy "                                 \
\  abs_ciR                                  \
\  =+=>                                     \
\ (%theta AbsState'', %theta AbsState) : AtransR \
\  =+=>                                     \
\ (%theta AbsState'') : InitAbsState       \
\  =+=>                                     \
\ rep %^ abs_cvsauth  = rep' %^ abs_cvsauth ";
by(stripS_tac 1);
br ccontr 1;
by(res_inst_tac [("P", " authtab %^ rep %^                    \
                  \ ((wc_uidtab %^ abs_cvsauth),              \
                  \ abs_passwd %^ (wc_uidtab %^ abs_cvsauth)) \
                  \  = cvs_admin ")] 
		notE 1);
(* 1. show: ... ~= cvs_admin *)
zbr perm_neq_admin 1;
ba 1;
ba 1;
ba 1;
zbr auth_inDom_wcUtb 1;
zbd abs_ciR_implies_abs_ci 1;
ba 1;
ba 1;
(* 2. show: ... = cvs_admin *)
by(duplPrem "abs_ciR" 1);
zbd abs_ciR_implies_abs_ci 1;
zbd abs_ci_changedRep_implies_hasAccess 1;
ba 1;
zbd abs_ciR_implies_abs_ci 1;
zbd (abs_ci_valid_AbsState 
	 ZRS 
	 AbsState_implies_RepositoryState) 1;
zbd abs_cvsauth_inDom_rep 1;
ba 1;
(* achieved has_access in Assumptions. *)
zbd has_access_implies_inPermOrder 1;
(* set-constrs. from has_access - lemma: *)
(* rep_permtab *)
zbd abs_ciR_implies_abs_ci 1;
zbd (abs_ci_valid_AbsState 
	 ZRS 
	 AbsState_implies_RepositoryState) 1;
zbd RepState_implies_type_repPtb 1;
ba 1;
(* rep *)
zbd abs_ciR_implies_abs_ci 1;
zbd (abs_ci_valid_AbsState 
	 ZRS 
	 AbsState_implies_RepositoryState) 1;
zbd RepState_implies_type_rep 1;
ba 1;
(* abs_passwd *)
zbd abs_ciR_implies_abs_ci 1;
zbd (abs_ci_valid_AbsState 
	 ZRS 
	 AbsState_implies_ClientState) 1;
zbd type_absPwd 1;
ba 1;
(* abs_cvsauth *)
zbr type_abs_cvsauth 1;
(* wc_uidtab %^ abs_cvsauth : Cvs_Uid *)
br pfun_appl 1;
(* wc_uidtab *)
zbd abs_ciR_implies_abs_ci 1;
zbd (abs_ci_valid_AbsState 
	 ZRS 
	 AbsState_implies_ClientState) 1;
zbd type_wcUidtab 1;
by(convert2hol_tac [ABS_UIDTAB_def] 1);
(* abs_cvsauth : dom wc_uidtab *)
zbd abs_ciR_implies_abs_ci 1;
zbd auth_inDom_wcUtb 1;
ba 1;
ba 1;
(**)
br mp 1;
by(guidedAssumption ["(rep_permtab %^ abs_cvsauth"] 2);
by(res_inst_tac [("t","rep_permtab %^ abs_cvsauth")] subst 1);
br sym 1;
zbr RepState_implies_permCvsauth 1;
zbd (abs_ciR_implies_abs_ci 
	 ZRS 
	 abs_ci_valid_AbsState
	 ZRS
	 AbsState_implies_RepositoryState)1;
by(convert2hol_tac [] 1);
br impI 1;

zbd admin_perm_only 1;
ba 2;
(* now still show authtab rep ... : cvsPerm. *)
br pfun_appl 1;
zbd (abs_ciR_implies_abs_ci
	 ZRS
	 abs_ci_valid_AbsState
	 ZRS 
	 AbsState_implies_RepositoryState
	 ZRS
	 validAuth )1;
by(convert2hol_tac [AUTH_TAB_def] 1);
zbd abs_ciR_implies_abs_ci 1;
zbd abs_ci_authNeq_defined 1;
ba 1;
ba 1;
qed"abs_ciR_implies_repAuth_invariant";
*)
