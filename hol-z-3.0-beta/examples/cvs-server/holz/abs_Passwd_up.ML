(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_Passwd_up.ML --- 
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
(* $Id: abs_Passwd_up.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* Proofs concerning abs_passwd   *)
(* after an update operation.     *)

(* These proofs use lemmata which *)
(* stem from the files:           *)
(* - simpleRules.ML               *)
(* - SimpleAbsOpsImpls.ML         *)
(* - abs_Passwd_add.ML            *)


zgoal thy "              \
\ abs_up                 \
\ =+=>                   \
\ f ~: dom wc_uidtab     \ 
\ =+=>                   \
\ f  : dom wc_uidtab'    \ 
\ =+=> wc_uidtab' %^ f = \ 
\ (mu id:dom abs_passwd. \
\ ((rep_permtab, rep, abs_passwd, f, id) : has_access_))";
by(stripS_tac 1);

by(full_expand_schema_tac abs_up_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_keep ["dom wc_uidtab", "wc_uidtab' ="] 1);
by(hyp_subst_tac 1);

(* get assumption:          *)
(* f: dom wc_uidtab_changes *)
bd domTrace_Overrid 1;
ba 1;
br refl 1;

br trans 1;
br overrid_choose_rel_apply 1;
ba 1;
ba 1;
(**)
zbr appl_of_restricted_maplet_ext 1;

zbd inDom_implies_setConstr 1;
ba 1;

zbd inDom_implies_setProp 1;
auto();(* 4 times ba 1 plus conjI*)
qed"compute_wcuidtab_f";


zgoal SysArchSec.thy "  \
\ f : dom wc_uidtab'    \
\ =+=>                  \
\ f ~: dom wc_uidtab    \
\ =+=>                  \
\ abs_up                \
\ =+=>                  \
\ (wc_uidtab' %^f) : dom abs_passwd'   \
\ ";
by(stripS_tac 1);
(* by(full_expand_schema_tac abs_add_def 1); *)
by(res_inst_tac [("t","(wc_uidtab' %^f)")]  subst 1);
br sym 1;
zbr compute_wcuidtab_f 1;
ba 1;
ba 1;
ba 1;
by(res_inst_tac [("t", "abs_passwd'")] subst 1);
zbr abs_up_invariant_absPwd 1;
ba 1;
zbr domAbsPasswd_from_example_pred 1;
by(full_expand_schema_tac abs_up_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
bd domTrace_Overrid 1;
ba 1;
ba 1;
zbd inDom_implies_setProp 1;
auto();
(**)
qed"abs_up_defined_absPwd";


