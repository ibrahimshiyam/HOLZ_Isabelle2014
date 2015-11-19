(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * modify_impls.ML --- 
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
(* $Id: modify_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)

zgoal thy "modify =+=> ?fname : Abs_Name";
by(stripS_tac 1);
by(full_expand_schema_tac modify_def 1);
bd (DECL_D1 RS conjunct2 RS conjunct2 RS conjunct1) 1;
ba 1;
qed"type_fq";

zgoal thy "modify =+=> ?nData : Abs_Data";
by(stripS_tac 1);
by(full_expand_schema_tac modify_def 1);
bd (DECL_D1 RS conjunct2 RS conjunct2 RS conjunct2 ) 1;
ba 1;
qed"type_newData";


zgoal thy "modify =+=> ?fname : dom wc";
by(stripS_tac 1);
by(full_expand_schema_tac modify_def 1);
bd (DECL_D2 RS conjunct1) 1;
ba 1;
qed"fq_inDom_wc";


(* the version used in the text is a *)
(* is a forward combination of       *)
(* modifyR_implies_modify and the    *)
(* following lemma.                  *)
(* text-name:modifyR_domWc_invariant *)

zgoal thy "modify =+=> dom wc = dom wc'";
by(stripS_tac 1);
by(full_expand_schema_tac modify_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
br (dom_inv_singleton RS sym) 1;
by(AtomizePremSolveAll);
qed"modify_domWc_invariant";


zgoal SysArchSec.thy "        \
\ modify  =+=>                \
\ ((wc %^ n)~=(wc' %^ n))     \
\ =+=> n = ?X";
by(stripS_tac 1);
br mp 1;
ba 2;
by(expand_schema_tac modify_def 1);
br impI 1;
bd DECL_D2 1;
by(atomizePrem 1);

by(hyp_subst_tac 1);
bd changeOverrid 1;
ba 1;
qed"modify_chWc_implies_fileq";


zgoal SysArchSec.thy "        \
\ modify  =+=>                \
\ ((wc %^ n)~=(wc' %^ n))     \
\ =+=> (wc' %^ n) = ?X";
by(stripS_tac 1);
br mp 1;
ba 2;
by(expand_schema_tac modify_def 1);
br impI 1;
bd DECL_D2 1;
by(atomizePrem 1);
bd neqAppl_trace_overrid 1;
bd nsym 1;
ba 1;
by(filterPrems_drop ["wfiles' =",
		     "wc_uidtab' =", 
		     "abs_passwd' ="] 1);
br mp 1;
by(guidedAssumption ["filename_63 |-->"] 2);
by(res_inst_tac [("t","n"),
		 ("s","filename_63")] subst 1);
br sym 1;
zbd modify_chWc_implies_fileq 1;
ba 1;
ba 1;
br impI 1;
by(filterPrems_drop ["} %^ n"] 1);
bd trans 1;

br singleMaplet_appl 1;
by(res_inst_tac [("P", "% x . x = ?Y")] subst 1);
br sym 1;
ba 1;
br refl 1;
qed"modify_chWc_implies_newDataq";

(* ============ (modifyR) ======== *)

(* filename?, newData? in Ainvents.*)

zgoal SysArchSec.thy "    \
\  modifyR    =+=>        \
\ (?X, ?Y) : Ainvents";
by(stripS_tac 1);
by(full_expand_schema_tac modifyR_def 1);
be conjE 1;
bd DECL_D2 1;
by(rewtac maplet_def);
ba 1;
qed"modifyR_implies_Ainvents";



zgoal SysArchSec.thy "    \
\ modifyR     =+=>        \
\ ((wc %^ n)~=(wc' %^ n)) \
\ =+=>                    \
\  (n, (wc' %^ n)): Ainvents  ";
by(stripS_tac 1);
by(res_inst_tac [("t","(n, wc' %^ n)"),
		 ("s", "(filename_63, merge %^ ((wc %^ filename_63),  newData_63))")] 
		subst 1);
(*zbd modifyR_implies_Ainvents 2;*)
(*ba 2;*)
br sym 1;
br pairEq 1;
(* filename?*)
zbd modifyR_implies_modify 1;
zbd modify_chWc_implies_fileq 1;
ba 1;
ba 1;
(* newData? *)
by(duplPrem "modifyR" 1);
zbd modifyR_implies_modify 1;
zbd modify_chWc_implies_newDataq 1;
ba 1;
by(subgoals_tac ["n = filename_63"] 1);
by(hyp_subst_tac 1);
ba 1;
(* filename?*)
zbd modifyR_implies_modify 1;
zbd modify_chWc_implies_fileq 1;
ba 1;
ba 1;

(* *)
zbr Ainv_implies_rMergeAinv 1;
zbd modifyR_implies_Ainvents 4;
ba 4;
(* get the set constraints *)
zbd (modifyR_implies_modify ZRS type_fq) 3;
ba 3;
zbd (modifyR_implies_modify ZRS type_newData) 2;
ba 2;
br pfun_appl 1;
zbd (modifyR_valid_AbsState
	 ZRS 
	 AbsState_implies_ClientState
	 ZRS type_wc) 1;
by(convert2hol_tac [ABS_DATATAB_def] 1);
zbd (modifyR_implies_modify
	 ZRS
	 fq_inDom_wc) 1;
ba 1;
qed"modifyR_wcDiff_Ainvents";
