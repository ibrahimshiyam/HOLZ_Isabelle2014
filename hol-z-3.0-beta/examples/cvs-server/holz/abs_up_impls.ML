(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_up_impls.ML --- 
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
(* $Id: abs_up_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* specific implications of abs_up *)



zgoal thy "abs_up =+=>    \
\ f : dom wc_uidtab =+=>  \
\ f : dom wc_uidtab'      ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_up_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["wc' ="] 1);
by(hyp_subst_tac 1);
br oplDomLeft 1;
ba 1;
qed"abs_up_domWcUtb_mono";


(* Version is already combined with *)
(* subsetD :                        *)

zgoal thy "abs_up =+=>            \
\  f: dom wc =+=>  f : dom wc'    ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_up_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["wc_uidtab' ="] 1);
by(hyp_subst_tac 1);
br oplDomLeft 1;
br oplDomLeft 1;
ba 1;
qed"abs_up_domWc_mono";



zgoal thy "abs_up         =+=>     \
\  f ~: dom wc_uidtab     =+=>     \
\  f : dom wc_uidtab'     =+=>     \
\  wc_uidtab' %^ f =               \
\   (mu id:dom abs_passwd.         \
\  (rep_permtab, rep, abs_passwd,  \
\  f, id) : AbstractState.has_access_)    ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_up_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["wc' ="] 1);
(* bd domTrace_Overrid 1; *)

bd domTrace_Overrid_comb 1;
ba 1;
ba 1;
be conjE 1;
bd dom_id_img_prop 1;
by(res_inst_tac [("t", "wc_uidtab' %^ f")] subst 1);
br sym 1;
ba 1;

br yields_prop 1;
ba 1;
qed"abs_up_domDiff_computeWcUtb_f";


zgoal thy "abs_up         =+=>     \
\  f ~: dom wc_uidtab     =+=>     \
\  f : dom wc_uidtab'     =+=>     \
\  f : dom wc'                     ";
by(stripS_tac 1);
(* ---- *)
br mp 1;
ba 2;
by(expand_schema_tac abs_up_def 1);
br impI 1;
(* ---- *)
bd DECL_D2 1;
by(atomizePrem 1);
by(duplPrem "f : dom wc_uidtab'" 1);
bd domTrace_Overrid 1;
ba 1;
ba 1;
bd dom_id_img_prop 1;
by(atomizePrem 1);
(*by(filterPrems_drop ["wc_uidtab' ="] 1);*)
by(res_inst_tac [("t", "wc'")] subst 1);
br sym 1;
ba 1;
(* by(hyp_subst_tac 1);*)
br oplDomLeft 1;
by(case_tac "f : dom wc" 1);
(* case f:dom wc  *)
br oplDomLeft 1;
ba 1;
(* case f~:dom wc *)
br oplDomRight 1;
br revRestrDom 1;
ba 1;
by(filterPrems_drop ["wc' ="] 1);
(* prove all single properties *)
(* except for has_access_      *)
by(REPEAT ((rtac singleProps 1)THEN(atac 1))); 
(* now still have to show has_access_ *)
br simpleGetProp 1;
by(res_inst_tac [("t", "wc_uidtab' %^ f")] subst 1);
br sym 1;
zbd abs_up_domDiff_computeWcUtb_f 1;
ba 1;
ba 1;
ba 1;
by(filterPrems_keep ["? id:dom abs_passwd"] 1);
by(convert2hol_tac [Domain_def, Mu_def] 1);
 auto();
br conjunct2 1;
br selectI 1;
br conjI 1;
(*auto also does from here.*)
ba 2;
br exI 1;
ba 1;
qed"abs_up_domDiff_wcUtb_inDom_wc";



zgoal thy "abs_up        =+=>  \
\ f ~: dom wc            =+=>  \
\ f  : dom wc'           =+=>  \
\ f : dom wc_uidtab'           ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_up_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["wc_uidtab' ="] 1);
zbd trans 1;
br (Overrid_Compose RS sym) 1;
bd domDiff_trace_overrid 1;
ba 1;
ba 1;
bd domDistr 1;
be UnE 1;
(* first case: right set *)
bd inRestrDom 1;
bd id_img_prop 1;
by(atomizePremSolve 1);
(* second case: not possible. *)
bd dom_id_img_prop 1;
auto();
(* contradict on f: dom wc *)
qed"abs_up_domDiff_wcUtb";



zgoal thy "abs_up        =+=>  \
\ wc %^ f ~= wc' %^ f    =+=>  \
\ f  : dom wc'           =+=>  \
\ f : dom wc_uidtab'           ";
by(stripS_tac 1);
br mp 1;
by(guidedAssumption ["abs_up"] 2);
(* by(full_expand_schema_tac abs_up_def 1); *)
by(expand_schema_tac abs_up_def 1);
br impI 1;
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["wc_uidtab' ="] 1);
zbd trans 1;
br (Overrid_Compose RS sym) 1;

bd fneq_domTrace_overrid 1;
ba 1;
br nsym 1;
ba 1;
bd domDistr 1;
be UnE 1;
(* first case: by the set prop. *)
bd inRestrDom 1;
bd id_img_prop 1;
by(atomizePremSolve 1);
(* second case: *)
bd dom_id_img_prop 1;
by(atomizePrem 1);
zbd abs_up_domWcUtb_mono 1;
ba 1;
ba 1;
qed"abs_up_fNeq_wcUtb";

(* cand. for t *)

zgoal thy "abs_up =+=>   \
\ f : dom wc_uidtab =+=>  \
\ (wc_uidtab %^ f = wc_uidtab' %^f) \
\ ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_up_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(hyp_subst_tac 1);
br sym 1;
br rev_overrid_choose_rel_apply 1;
ba 1;
(* contradict on:    *)
(* f : dom wc_uidtab *)
br ccontr 1;
by(rewrite_goals_tac [not_def]);
be impE 1;
ba 2;
br impI 1;
zbd inDom_implies_setProp 1;
auto();
qed"abs_up_partialInv_wcUidtb";


zgoal SysArchSec.thy "   \
\  abs_up  =+=>          \
\ n ~: dom wc     =+=>   \
\ n  : dom wc'    =+=>   \
\ n : dom rep'           ";
by(stripS_tac 1);
by(rewtac SNAME_def);
by(duplPrem "abs_up" 1);
zbd (removeSNAME abs_up_implies_rep_invariant) 1;
by(full_expand_schema_tac abs_up_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["wc_uidtab' =", 
		     "abs_passwd' =", 
		     "wfiles' ="] 1);
by(move2Head ["wc' ="] 1);
zbd trans 1;
br (Overrid_Compose RS sym) 1;
br mp 1;
by(eres_inst_tac [("x", "n"), 
		  ("B", "wc'"), 
		  ("A", "wc")] domTrace_Overrid 2);
ba 2;
ba 2;
br impI 1;
bd domDistr 1;
by(hyp_subst_tac 1);
by(filterPrems_drop ["(+)"] 1);
be UnE 1;
(* 1. case:  wc_new *)
bd inDomRestr 1;
ba 1;
(* 2. case: wc_mod  *)
bd dom_id_img_prop 1;
by(atomizePremSolve 1);
qed"abs_up_wcDomDiff_fromRep";

(*  *)

zgoal thy "abs_up =+=>   \
\ n : dom wc'     =+=>   \
\ wc %^ n ~= wc' %^ n    \
\ =+=> n : dom rep'      ";
by(stripS_tac 1);
by(rewtac SNAME_def);
by(duplPrem "abs_up" 1);
zbd (removeSNAME abs_up_implies_rep_invariant) 1;
by(full_expand_schema_tac abs_up_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["wc_uidtab' =", 
		     "abs_passwd' =", 
		     "wfiles' ="] 1);
(*by(hyp_subst_tac 1);*)
by(move2Head ["wc' ="] 1);
zbd trans 1;
br (Overrid_Compose RS sym) 1;
(*br mp 1;*)
bd domTrace_overrid_comb 1;
(*neqAppl_trace_overrid 1;*)
br nsym 2;
ba 2;
ba 1;
by(atomizePrem 1);
by(filterPrems_drop ["wc' %^ n"] 1);
bd domDistr 1;
by(hyp_subst_tac 1);
be UnE 1;
(* 2. case n : dom wc_mod *)
bd dom_id_img_prop 2;
by(atomizePremSolve 2);
(* 1. case n : dom wc_new *)
bd inDomRestr 1;
ba 1;
qed"abs_up_wcfNeq_fromRep";


zgoal SysArchSec.thy "             \
\  abs_up  =+=>                    \
\ n ~: dom wc_uidtab     =+=>      \
\ n  : dom wc_uidtab'    =+=>      \
\ (? id : dom abs_passwd.          \
\ (rep_permtab, rep,               \
\ abs_passwd, n, id): has_access_) ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_up_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["abs_passwd' =", 
		     "wfiles' =",
		     "wc' ="] 1);
bd domDiff_trace_overrid 1;
ba 1;
ba 1;
bd dom_id_img_prop 1;
by(atomizePremSolve 1);
qed"abs_up_domDiff_wcUtb_implies_hasAccess";


