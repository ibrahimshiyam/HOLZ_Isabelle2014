(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_ci_impls.ML --- 
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
(* $Id: abs_ci_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* specific implications of abs_ci *)

zgoalw SysArchSec.thy [abs_ciR_def] "abs_ciR =+=> abs_ci";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
qed"abs_ciR_implies_abs_ci";

bind_thm("abs_ci_implies_RepState", ((stripS abs_ci_valid_AbsState) 
		  RS 
		  (stripS AbsState_implies_RepositoryState)));

(* - siehe paper & pencil erst!!!*)

zgoal thy "abs_ci           \
\                 =+=>      \
\ f:dom rep'                \
\                 =+=>      \
\ f~:dom rep                \
\                 =+=>      \
\ ((wc_uidtab %^ f), (abs_passwd %^ (wc_uidtab %^ f))) \
\   :dom (authtab %^ rep )  \
\          ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_ci_def 1);
bd DECL_D2 1;
by(projectPrems ["rep' =", "f : dom rep'"
		 , "f ~: dom rep"] 1);
bd trans 1;
br (Overrid_Compose RS sym) 1;
bd domTrace_Overrid 1;
ba 1;
ba 1;
by(filterPrems_drop ["rep' ="] 1);
bd domDistr 1;
be UnE 1;
(*second case is contr.       *)
(* .. only locating right set *)
by(res_inst_tac [("P","f : dom rep")] notE 2);
ba 2;
bd inRestrDom 2;
bd id_img_prop 2;
by(atomizePremSolve 2);
(* first case: main proof. *)
bd inRestrDom 1;
bd id_img_prop 1;
by(atomizePremSolve 1);
qed"mf_inDomAuthtabRep";

zgoal thy "abs_ci           \
\ =+=> dom rep <= dom rep' ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_ci_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["rep_permtab' ="] 1);

bd trans 1;
zbr (Overrid_Compose RS sym) 1;
bd oplDomSubset 1;
ba 1;
qed"abs_ci_domRep_mono";

(* --- *)

zgoal thy "abs_ci           \
\                 =+=>      \
\ f :dom rep'               \
\                 =+=>      \
\ (rep %^ f ~= rep' %^ f)   \
\                 =+=>      \
\ f:dom wc_uidtab           ";
by(stripS_tac 1);
(* f must be in dom rep_new or *)
(* in dom rep_changed          *)
by(full_expand_schema_tac abs_ci_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["rep_permtab' ="] 1);
bd trans 1;
br (Overrid_Compose RS sym) 1;

zbd neqAppl_domTrace_overrid 1;
ba 1;
br nsym 1;
ba 1;
by(filterPrems_keep ["f : dom ((%n"] 1);
bd domDistr 1;
be UnE 1;
(* case f : dom rep_new     *)
bd inRestrDom 1;
bd id_img_prop 1;
by(atomizePremSolve 1);
(* case f : dom rep_changed *)
bd inRestrDom 1;
bd id_img_prop 1;
by(atomizePremSolve 1);
qed"abs_ci_fNeq_defined_wcUtb";


zgoal thy "abs_ci           \
\                 =+=>      \
\ f:dom rep'                \
\                 =+=>      \
\ f~:dom rep                \
\                 =+=>      \
\ f:dom wc_uidtab           ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_ci_def 1);
bd DECL_D2 1;
by(projectPrems ["rep' =", "f : dom rep'"
		 , "f ~: dom rep"] 1);
bd trans 1;
br (Overrid_Compose RS sym) 1;
bd domTrace_Overrid 1;
ba 1;
ba 1;
by(filterPrems_drop ["rep' ="] 1);
bd domDistr 1;
be UnE 1;
(* simply match property for *)

(* case f: dom rep_new       *)
be DomainE 1;
be dom_restrE 1;
bd rev_pairEq 1;
be conjE 1;
bd sym 1;
be subst 1;
be subst 1;
be imageE 1;
by(convert2hol_tac [] 1);
(* case f: dom rep_old       *)
be DomainE 1;
be dom_restrE 1;
bd rev_pairEq 1;
be conjE 1;
bd sym 1;
be subst 1;
be subst 1;
be imageE 1;
by(convert2hol_tac [] 1);
qed"abs_ci_domDiff_defined_wcUtb";


(* Task: repair a given proof part. *)
(*                                  *)
(* (szenario: make a proof and see, *)
(* one assumption was missing. Now  *)
(* insert it in the goal formulation*)
(* and reuse the proof part. If the *)
(* commands etac/dtac where used    *)
(* frequently, one has to modify the*)
(* existing proof part.             *)
(*                                  *)
(* critical points:                 *)
(*                                  *)
(* - usage of e_tac, d_tac          *) 
(* solution: move fresh assumption  *)
(* to the back of the assumption    *)
(* list, so it will not be chosen   *)
(* prior to the desired assumption. *)
(*                                  *)
(* - usage of ba on metavariables.  *)
(* solution: use guidedAssumption   *)
(* (which requires knowledge of the *)
(* name of the required assumption) *)
(* or better again sort fresh       *)
(* assumption to the back.          *)
(*                                  *)
(* Problems: automatic repairation  *)
(* of proof script would have either*)
(* trouble with REPEAT( d_tac..)    *)
(* or it would have a large overhead*)
(*                                  *)
(* I think that an interaktive      *)
(* problem handling can be handled  *)
(* also well, though in near future *)
(* a semi automatic repairing script*)
(* which heuristically inserts      *)
(* "move2End" can be written.       *)

(* For interactive proof repairing  *)
(* a mechanism which allows         *)
(* labelling certain proof states   *)
(* and jumping back to the desired  *)
(* label would be desirable.        *)


(* An instance of this lemma, with  *)
(* abs_cvsauth as a modified file,  *)
(* is used in the text.             *)
(* text-name:abs_ci_authNeq_perm    *)

zgoal thy "abs_ci           \
\                 =+=>      \
\ f:dom rep'                \
\                 =+=>      \
\ (rep %^ f ~= rep' %^ f)   \
\                 =+=>      \
\ (rep_permtab' %^ f, (authtab %^ rep )%^ (            \
\ (wc_uidtab %^ f), (abs_passwd %^ (wc_uidtab %^ f))))  \
\ : cvs_perm_order                                \
\ ";
by(stripS_tac 1);
br mp 1;
by(full_expand_schema_tac abs_ci_def 1);
by(guidedAssumption ["abs_ci"] 2);
br impI 1;
bd DECL_D2 1;
by(atomizePrem 1);
bd trans 1;
br (Overrid_Compose RS sym) 1;
(* do a substitution on the *)
(* assumptions!             *)
br mp 1;
by(guidedAssumption ["f : dom rep'"] 2);
by(res_inst_tac [("t", "rep'")] subst 1);
br sym 1;
ba 1;
br impI 1;
(* -- *)
by(duplPrem "f : dom rep'" 1);
(* by(move2End ["f : dom rep'"] 1); *)
(*HH - back*)
bd neqAppl_domTrace_overrid 1;
ba 1;
br nsym 1;
ba 1;
(* some pruning *)
by(filterPrems_drop ["rep' =", "f : dom (rep (+)"] 1);
bd domDistr 1;
by(move2End ["f : dom rep'"] 1);
be UnE 1;
(* this gives the 2 cases: *)
(* 1. f:dom rep_new defered. *)
by(defer_tac 1);(* L25 *)
(* ======================================= *)
(* 2. f:dom rep_changes    *)
by(move2End ["f : dom rep'"] 1);
be DomainE 1;
by(move2End ["f : dom rep'"] 1);
bd dom_restrD2 1;
by(move2End ["f : dom rep'"] 1);
be (make_elim id_img_prop) 1;
by(move2End ["f : dom rep'"] 1);
by(atomizePrem 1);
by(res_inst_tac [("P", "f : dom rep")] mp 1);
by(convert2hol_tac [split_def] 2);
br impI 1;
(* exchange rep_permtab (') *)
by(move2End ["f : dom rep'"] 1);
by(res_inst_tac [("s", "rep_permtab %^ f"), 
		 ("t", "rep_permtab' %^ f")] subst 1);
zbr abs_ci_repPtab_invariant 1;
by(move2End ["f : dom rep'"] 1);
ba 1;
ba 1;
(* substitute assumption has_access *)
by(REPEAT (dtac fst_PairIn 1));
by(move2End ["f : dom rep'"] 1);
zbr has_access_implies_inPermOrder 1;
(* this lemma finishes the second case    *)
(* , but leaves bunch of set constraints. *)
by(convert2hol_tac [split_def] 1);
(* match set constraints*)
(* rep_permtab *)
by(full_expand_schema_tac abs_ci_def 1);
bd DECL_D1 1;
by(convert2hol_tac [RepositoryState_def] 1);
(* rep *)
by(full_expand_schema_tac abs_ci_def 1);
bd DECL_D1 1;
by(convert2hol_tac [RepositoryState_def] 1);
(* abs_passwd *)
by(full_expand_schema_tac abs_ci_def 1);
bd DECL_D1 1;
by(convert2hol_tac [ClientState_def] 1);
(* f *)
by(full_expand_schema_tac abs_ci_def 1);
bd DECL_D1 1;
by(convert2hol_tac [ClientState_def] 1);
by(projectPrems ["wfiles : %P Abs_Name", 
		 "f : wfiles"] 1);
bd PowD 1;
bd subsetD 1;
ba 1;
ba 1;
(* wc_uidtab f *)
by(res_inst_tac [("X", "Abs_Name")]  Rel_Apply_in_Partial_Ran2 1);
ba 2;
by(full_expand_schema_tac abs_ci_def 1);
bd DECL_D1 1;
by(projectPrems ["%Xi"] 1);
by(convert2hol_tac [XI_def, ClientState_def, ABS_UIDTAB_def] 1);
(* Level 69 *)
(* ======================================= *)
(* 2nd, deferred case: *)
by(move2End ["f : dom rep'"] 1);
be DomainE 1;
by(move2End ["f : dom rep'"] 1);
bd dom_restrD2 1;
bd fst_PairIn 1;
by(move2End ["f : dom rep'"] 1);
by(res_inst_tac [("s","(authtab %^ rep %^ (wc_uidtab %^ f, \
                      \ (abs_passwd %^ (wc_uidtab %^ f))))"), 
		 ("t","rep_permtab' %^ f")] 
		subst 1);


by(res_inst_tac [("t", "rep_permtab' %^ f")] subst 1);
br sym 1;
br overriden_relAppl 1;
ba 2;(**)
br rev_dom_id_img_prop 1;
bd id_img_prop 1;
ba 1;(**)
br trans 1;
br sym 2;
br yields_prop 2;
br refl 1;
bd id_img_prop 1;
ba 1;
(* ------------------------- *)
(* this only leaves to show: *)
(* (x,x):cvs_perm_order      *)
(* ------------------------- *)
br cvsPerm_in_refl 1;
br pfun_appl 1;
zbd abs_ci_implies_RepState 1;
zbd validAuth 1;
by(convert2hol_tac [AUTH_TAB_def] 1);
zbr mf_inDomAuthtabRep 1;
(* at this point I recoginzed that *)
(* an assumption was missing.      *)
ba 1;
ba 1;
bd id_img_prop 1;
by(atomizePremSolve 1);
qed"abs_ci_fNeq_permOrder";



zgoal thy "abs_ci           \
\                 =+=>      \
\ f:dom rep'                \
\                 =+=>      \
\ f~:dom rep                \
\                 =+=>      \
\ (rep_permtab' %^ f =      \
\ (authtab %^ rep )%^       \
\ ((wc_uidtab %^ f), (abs_passwd %^ (wc_uidtab %^ f)))) ";
by(stripS_tac 1);
br mp 1;
br (abs_ci_valid_AbsState
    ZRS
    AbsState_implies_RepositoryState
    ZRS
    RepState_implies_eqDomRepRepPtb) 2;
ba 2;
br mp 1;
br (abs_ci_valid_AbsStateS
    ZRS
    AbsState_implies_RepositoryState
    ZRS
    RepState_implies_eqDomRepRepPtb) 2;
ba 2;
by(full_expand_schema_tac abs_ci_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(stripS_tac 1);
(* get f: dom rep_permtab' *)
br mp 1;
by(guidedAssumption ["f : dom rep'"] 2);
by(res_inst_tac [("t","dom rep'"),("s","dom rep_permtab'")] subst 1);
br sym 1;
ba 1;
br impI 1;
(* get f~: dom rep_permtab *)
br mp 1;
by(guidedAssumption ["f ~: dom rep"] 2);
by(res_inst_tac [("t","dom rep"),("s","dom rep_permtab")] subst 1);
br sym 1;
ba 1;
br impI 1;
(* trace rep_permtab' back to rep_permtab_new *)
by(move2Head ["rep_permtab' ="] 1);
(* rep_permtab f = { ..|..@ ..|--> ..} f}*)
bd domTrace_Overrid_comb 1;
ba 1;
ba 1;
(* speedup with some minor pruning. *)
by(filterPrems_drop ["rep' ="] 1);
by(atomizePrem 1);
by(move2Head ["rep_permtab' %^ f ="] 1);
by(move2Head ["f : dom ((%n"] 1);
bd dom_id_img_prop 1;
by(res_inst_tac [("t","rep_permtab' %^ f")] subst 1);
br sym 1;
ba 1;
by(res_inst_tac [("P","% x . x = ?Y")] subst 1);
br sym 1;
br yields_prop 1;
ba 1;
br refl 1;
qed"domDiff_compute_repPtab";



zgoal thy "abs_ci           \
\                 =+=>      \
\ f:dom rep'                \
\                 =+=>      \
\ f~:dom rep                \
\                 =+=>      \
\ (rep_permtab' %^ f, (authtab %^ rep )%^ (            \
\ (wc_uidtab %^ f), (abs_passwd %^ (wc_uidtab %^ f))))  \
\ : cvs_perm_order                                \
\ ";
by(stripS_tac 1);
by(res_inst_tac [("t","rep_permtab' %^ f")] subst 1);
zbd domDiff_compute_repPtab 1;
ba 1;
ba 1;
br sym 1;
ba 1;
(* ------------------------- *)
(* this only leaves to show: *)
(* (x,x):cvs_perm_order      *)
(* ------------------------- *)
br cvsPerm_in_refl 1;
br pfun_appl 1;
zbd abs_ci_implies_RepState 1;
zbd validAuth 1;
by(convert2hol_tac [AUTH_TAB_def] 1);
zbr mf_inDomAuthtabRep 1;
by(AtomizePremSolveAll);
qed"abs_ci_domDiff_permOrder";

(* *)

zgoal thy "abs_ci              \
\ =+=> rep %^ f ~= rep' %^ f   \
\ =+=> f : dom rep             \
\ =+=>                         \
\ (rep_permtab, rep,           \
\ abs_passwd, f, wc_uidtab %^ f) : has_access_";
by(stripS_tac 1);
br mp 1;
ba 2;
by(expand_schema_tac abs_ci_def 1);
br impI 1;
be DECL_E 1;
by(atomizePrem 1);
by(filterPrems_drop ["rep_permtab' ="] 1);
(* use associativity of (+) *)
(* on rep'=...              *)
bd trans 1;
zbr (Overrid_Compose RS sym) 1; (* HH *)
br mp 1;
br  neqAppl_domTrace_overrid 2;
ba 3;
br nsym 3;
ba 3;(* HH *)
br subsetD 2;
zbr abs_ci_domRep_mono 2;
ba 2;
ba 2;
by(filterPrems_drop ["rep' ="] 1);
br impI 1;
bd domTrace_Overrid_short 1;
zbd inDom_restrProp 2;
by(atomizePremSolve 2);
(* show that f ~: rep_new *)
(* (contradict on f: dom rep) *)
br ccontr 1;
bd notNotinD 1;
by(res_inst_tac [("P","f : dom rep")] notE 1);
by(atomizePremSolve 2);

zbd inDom_restrProp 1;
by(atomizePremSolve 1);

qed"abs_ci_changedRep_implies_hasAccess";


