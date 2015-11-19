(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_add_impls.ML --- 
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
(* $Id: abs_add_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* $Source: /local/softech-cvs/migrate/src/HOL-Z/examples/zeta/cvs-server/holz/abs_add_impls.ML,v $                                   *)

(* specific implications of abs_add *)

(* This is a implication of    *)
(* the abs_add   - Operation : *)
(*                             *)
(*  f : dom newfiles?          *)


(* uses metavariable to catch *)
(* newfiles?                  *)

zgoal SysArchSec.thy "  \
\ abs_add     =+=>      \
\ f : dom wc  =+=>      \
\ f : dom wc'";
by(stripS_tac 1);
by(full_expand_schema_tac abs_add_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(hyp_subst_tac 1);
br oplDomLeft 1;
ba 1;
qed"abs_add_domWc_mono";


zgoal SysArchSec.thy "  \
\ f : dom wc_uidtab'    \
\ =+=>                  \
\ f ~: dom wc_uidtab    \
\ =+=>                  \
\ abs_add               \
\ =+=>                  \
\ (f : (dom (?newfiles::((Abs_Name * Abs_Data) set)))) ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_add_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["dom rep", "wc (+)"] 1);
bd domTrace_Overrid 1;
ba 1;
ba 1;
zbr inDom_implies_setConstr 1;
ba 1;
qed"abs_add_domDiff_utb_newfiles";


zgoal SysArchSec.thy "  \
\ abs_add               \
\ =+=>                  \
\ f ~: dom wc_uidtab    \
\ =+=>                  \
\ f  : dom wc_uidtab'   \
\ =+=>                  \
\ f : dom wc' ";
by(stripS_tac 1);
(* by(duplPrem "abs_add" 1); *)
zbd abs_add_domDiff_utb_newfiles 1;
ba 1;
ba 1;
by(full_expand_schema_tac abs_add_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
zbd overriden_relApplDom 1;
by(AtomizePremSolveAll);
qed"abs_add_domDiff_wcUtb_inDom_wc";



zgoal SysArchSec.thy"abs_addR =+=> abs_add";
by(stripS_tac 1);
by(convert2hol_tac [abs_addR_def] 1);
qed"abs_addR_implies_abs_add";

bind_thm("abs_addR_invariant_absPwd",
	 (stripS abs_addR_implies_abs_add)
	     RS
	     (stripS abs_add_invariant_absPwd));


zgoal thy "abs_add =+=>   \
\ f : dom wc_uidtab =+=>  \
\ f : dom wc_uidtab'      \
\ ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_add_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(hyp_subst_tac 1);
br oplDomLeft 1;
ba 1;
qed"abs_add_domWcUtb_mono";


zgoal thy "abs_add =+=>   \
\ f : dom wc_uidtab =+=>  \
\ (wc_uidtab %^ f = wc_uidtab' %^f) \
\ ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_add_def 1);
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
qed"abs_add_partInv_wcUtb";


(* old files are not changed *)

zgoal thy "abs_add         =+=>                             \
\ n : dom wc'              =+=>                             \
\ n ~: dom (?newfiles::((Abs_Name * Abs_Data) set))  =+=>   \
\ wc %^ n = wc' %^ n ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_add_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["wc_uidtab' =", "wfiles' =", "abs_passwd' ="] 1);
br ccontr 1;
by(res_inst_tac [("P", "n : dom newfiles_63")] notE 1);
ba 1;
by(res_inst_tac [("f", "n"),
		 ("C", "wc'"),
		 ("A", "wc"),
		 ("B", "newfiles_63")] 
		neqAppl_domTrace_overrid 1);
ba 1;
ba 1;
br nsym 1;
ba 1;
qed"abs_add_invariant_wc";



zgoal thy "abs_addR  =+=>                            \
\  n : dom (?newfiles::((Abs_Name * Abs_Data) set))  \
\    =+=> (n, wc' %^ n) : Ainvents";
by(stripS_tac 1);
by(full_expand_schema_tac abs_addR_def 1);
by(atomizePrem 1);
be DECL_E 1;
by(full_expand_schema_tac abs_add_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["wfiles' =", 
		     "abs_passwd' =", 
		     "wc_uidtab' ="] 1);
by(res_inst_tac [("A", "newfiles_63")] subsetD 1);
ba 1;
by(res_inst_tac [("t", "wc' %^ n"), 
		 ("s", "newfiles_63 %^ n")] subst 1);
br sym 1;
br overriden_relAppl 1;
ba 1;
ba 1;
br relAppl_refl_example 1;
ba 1;
qed"abs_addR_newfiles_Ainvents";

(* *)

zgoal thy "abs_add         =+=>                             \
\ n : dom wc'              =+=>                             \
\ n ~: dom (?newfiles::((Abs_Name * Abs_Data) set))  =+=>   \
\ n : dom wc ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_add_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["wc_uidtab' =", 
		     "wfiles' =", 
		     "abs_passwd' ="] 1);
bd dom_simple_trace_left 1;
by(AtomizePremSolveAll);
qed"abs_add_domWc";



zgoal SysArchSec.thy "abs_addR  =+=>                       \
\ n ~: dom wc =+=> n : dom wc'                             \
\  =+=> (n : dom (?newfiles::((Abs_Name * Abs_Data) set))) ";
by(stripS_tac 1);
br mp 1;
by(guidedAssumption ["add"] 2);
by(expand_schema_tac abs_addR_def 1);
br impI 1;
by(atomizePrem 1);
bd DECL_D2 1;
br mp 1;
by(rotate_tac 1 2);
by(guidedAssumption ["add"] 2);
by(expand_schema_tac abs_add_def 1);
br impI 1;
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["wc_uidtab' =", 
		     "wfiles' =", 
		     "abs_passwd' ="] 1);
br domTrace_Overrid 1;
ba 1;
ba 1;
ba 1;
qed"abs_add_domDiff_newFiles";


zgoal thy "abs_addR  =+=>           \
\ n ~: dom wc =+=> n : dom wc'      \
\    =+=> (n, wc' %^ n) : Ainvents ";
by(stripS_tac 1);
by(duplPrem "add" 1);
zbd abs_add_domDiff_newFiles 1;
ba 1;
ba 1;
zbd abs_addR_newfiles_Ainvents 1;
by(AtomizePremSolveAll);
qed"abs_addR_domDiff_Ainvents";



zgoal SysArchSec.thy "abs_addR  =+=>                       \
\ (wc %^ n ~= wc' %^ n) =+=> n : dom wc'                   \
\  =+=> (n : dom (?newfiles::((Abs_Name * Abs_Data) set))) ";
by(stripS_tac 1);
br mp 1;
by(guidedAssumption ["add"] 2);
by(expand_schema_tac abs_addR_def 1);
br impI 1;
by(atomizePrem 1);
bd DECL_D2 1;
br mp 1;
by(rotate_tac 1 2);
by(guidedAssumption ["add"] 2);
by(expand_schema_tac abs_add_def 1);
br impI 1;
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["wc_uidtab' =", 
		     "wfiles' =", 
		     "abs_passwd' ="] 1);
br neqAppl_domTrace_overrid 1;
ba 1;
ba 1;
br nsym 1;
ba 1;
qed"abs_add_fNeq_newFiles";


zgoal thy "abs_addR  =+=>           \
\ n : dom wc'                       \
\ =+=> (wc %^ n ~= wc' %^ n) =+=>   \
\   (n, (wc' %^ n)) : Ainvents ";
by(stripS_tac 1);
by(duplPrem "add" 1);
zbd abs_add_fNeq_newFiles 1;
ba 1;
ba 1;
zbd abs_addR_newfiles_Ainvents 1;
by(AtomizePremSolveAll);
qed"abs_addR_fNeq_Ainvents";


zgoal thy "abs_add                  \
\ =+=> (wc %^ n ~= wc' %^ n) =+=>   \
\   n : dom wc'                     ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_add_def 1);
bd DECL_D2 1;
by(atomizePrem 1);

(*
zgoal thy "abs_addR  =+=>           \
\ n : dom wc'                       \
\ =+=> (wc_uidtab %^ n ~= wc_uidtab' %^ n) =+=>   \
\   (n, (wc' %^ n)) : Ainvents ";
by(stripS_tac 1);
by(duplPrem "add" 1);
zbd abs_add_fNeq_newFiles 1;
ba 1;
ba 1;
zbd abs_addR_newfiles_Ainvents 1;
by(AtomizePremSolveAll);
qed"abs_addR_fNeq_Ainvents";
*)



zgoal SysArchSec.thy "             \
\  abs_add  =+=>                   \
\ n ~: dom wc_uidtab     =+=>      \
\ n  : dom wc_uidtab'    =+=>      \
\ (? id : dom abs_passwd.          \
\ (id, abs_passwd %^ id) :         \
\  dom (authtab %^ rep))           ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_add_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["abs_passwd' =", 
		     "dom newfiles", 
		     "wfiles' =",
		     "wc' ="] 1);
bd domDiff_trace_overrid 1;
ba 1;
ba 1;
bd dom_id_img_prop 1;
by(atomizePremSolve 1);
qed"abs_add_domDiff_wcUtb_implies_hasAuth";

(*
zgoal SysArchSec.thy "             \
\  abs_add  =+=>                   \
\ n ~: dom wc_uidtab     =+=>      \
\ n  : dom wc_uidtab'    =+=>      \
\ (? id : dom abs_passwd.          \
\ (rep_permtab, rep,               \
\ abs_passwd, n, id): has_access_) ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_add_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_drop ["abs_passwd' =", 
		     "dom newfiles", 
		     "wfiles' =",
		     "wc' ="] 1);
bd domDiff_trace_overrid 1;
ba 1;
ba 1;
bd dom_id_img_prop 1;
by(atomizePremSolve 1);
qed"abs_add_domDiff_wcUtb_implies_hasAccess";

*)
