(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * owner_inRep_Lemmas.ML --- 
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
(* $Id: owner_inRep_Lemmas.ML 6746 2007-08-03 07:25:55Z brucker $ *)


zgoal SysArchSec.thy "                     \
\ (%theta AbsState'', %theta AbsState) :   \
\  AtransR                                 \
\  =+=>                                    \
\ (%theta AbsState'') : InitAbsState       \
\  =+=> abs_up    =+=>                     \
\ n ~: dom wc     =+=>                     \
\ n  : dom wc'    =+=>                     \
\ (? id : dom abs_passwd.                  \
\ (rep_permtab, rep,                       \
\ abs_passwd, n, id): has_access_)         ";
by(stripS_tac 1);
(* ---- *)
(* maybe also automate this one. *)
br mp 1;
by(guidedAssumption ["abs_up"] 2);
by(expand_schema_tac abs_up_def 1);
br impI 1;
(* ---- *)
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["abs_passwd' =", 
		     "wfiles' =",
		     "wc_uidtab' ="] 1);
bd Overrid_Compose_D1 1;
bd domDiff_trace_overrid 1;
ba 1;
ba 1;
bd domDistr 1;
be UnE 1;
(* snd case contradicts on n: dom wc *)
bd dom_id_img_prop 2;
by(atomizePrem 2);
br notE 2;
ba 2;
ba 2;
(* fst case *)
bd inRestrDom 1;
bd id_img_prop 1;
by(atomizePrem 1);
br bexI 1;
ba 1;
(* noch offen *)
zbd abs_up_defined_absPwd 1;
ba 2;
by(res_inst_tac [("Q", "n : dom wc"), 
		 ("P", "n : dom wc_uidtab")] contrapos 1);
ba 1;
zbr domWcUtb_implies_domWc 1;
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(convert2hol_tac [theta_def] 1);
ba 1;
zbd abs_up_invariant_absPwd 1;
by(hyp_subst_tac 1);
ba 1;
qed"abs_up_domDiff_has_access";



zgoal SysArchSec.thy "                     \
\ (%theta AbsState'', %theta AbsState) :   \
\  AtransR                                 \
\  =+=>                                    \
\ (%theta AbsState'') : InitAbsState       \
\  =+=> abs_up    =+=>                     \
\ (wc %^ n ~= wc' %^ n)     =+=>           \
\ n  : dom wc'    =+=>                     \
\ (? id : dom abs_passwd.                  \
\ (rep_permtab, rep,                       \
\ abs_passwd, n, id): has_access_)         ";
by(stripS_tac 1);
(* ---- *)
(* maybe also automate this one. *)
br mp 1;
by(guidedAssumption ["abs_up"] 2);
by(expand_schema_tac abs_up_def 1);
br impI 1;
(* ---- *)
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["abs_passwd' =", 
		     "wfiles' =",
		     "wc_uidtab' ="] 1);
by(case_tac "n : dom wc" 1);
(* second case already proven above ! *)
zbr abs_up_domDiff_has_access 2;
ba 4;
ba 4;
ba 3;
ba 2;
ba 2;
(* fst case: n : dom wc *)
zbd Overrid_Compose_D1 1;
zbd fneq_domTrace_overrid 1;
ba 1;
br nsym 1;
ba 1;
(* *)
bd domDistr 1;
be UnE 1;
by(res_inst_tac [("P", "n : dom wc")] notE 1);
ba 2;
zbd inRestrDom 1;
zbd id_img_prop 1;
by(atomizePremSolve 1);
(* Now selected the right set.  *)
bd dom_id_img_prop 1;
by(atomizePrem 1);
br bexI 1;
ba 1;
zbr definedAbsPwd 1;
by(convert2hol_tac [AtransR_def] 1);
by(convert2hol_tac [theta_def] 1);
ba 1;
qed"abs_up_fNeq_wc_has_access";



zgoal SysArchSec.thy "                     \
\ (%theta AbsState'', %theta AbsState) :   \
\  AtransR                                 \
\  =+=>                                    \
\ (%theta AbsState'') : InitAbsState       \
\  =+=>                                    \
\ n : Abs_Name                             \
\  =+=>                                    \
\ (? id : dom abs_passwd.                  \
\ (rep_permtab, rep,                       \
\ abs_passwd, n, id): has_access_)         \
\  =+=>                                    \
\ (? m:Aknows.                                     \
\        (rep_permtab %^ n, authtab %^ rep %^ m)   \
\          : cvs_perm_order)                       \
\ ";
by(stripS_tac 1);
by(atomizePrem_ex 1);
br mp 1;
zbr AbsStateAfterInitAtransR 2;
by(removeTheta_tac 2);
by(removeTheta_tac 2);
br impI 1;
zbd has_access_implies_inPermOrder 1;
(* get the types *)
(* - for RepositoryState *)
zbr (AbsState_implies_RepositoryState 
	 ZRS
	 RepState_implies_type_repPtb) 1;
by(convert2hol_tac [] 1);
zbr (AbsState_implies_RepositoryState 
	 ZRS
	 RepState_implies_type_rep) 1;
by(convert2hol_tac [] 1);
(* - for ClientState *)
zbr (AbsState_implies_ClientState 
	 ZRS
	 type_absPwd) 1;
by(convert2hol_tac [] 1);
ba 1;
br mp 1;
zbr (AbsState_implies_ClientState 
	 ZRS
	 type_absPwd_unfold) 2;
by(convert2hol_tac [] 2);
br impI 1;
zbd Type_inDom_Rel 1;
ba 1;
ba 1;
(* now proven all set constrs. *)
br bexI 1;
ba 1;
zbr loginAknows 1;
by(removeTheta_tac 1);
by(removeTheta_tac 1);
ba 1;
qed"has_access_implies_perm";
