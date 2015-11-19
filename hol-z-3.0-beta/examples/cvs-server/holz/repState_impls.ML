(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * repState_impls.ML --- 
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
(* $Id: repState_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* specific implications of RepositoryState *)

zgoal thy "RepositoryState =+=> (authtab %^ rep) : AUTH_TAB";
by(stripS_tac 1);
by(cut_facts_tac [def_authtab] 1);
by(res_inst_tac [("t", "authtab %^ rep")] subst 1);
br sym 1;
br mp 1;
by(res_inst_tac [("x", "rep")] bspec 1);
ba 1;
by(convert2hol_tac [RepositoryState_def] 1);
by(full_expand_schema_tac RepositoryState_def 1);
bd DECL_D2 1;
by(atomizePremSolve 1);
br pfun_appl 1;
br type_abs_auth_of 1;
by(convert2hol_tac [RepositoryState_def] 1);
qed"validAuth";


(*
zgoal thy "RepositoryState =+=> (rep : dom authtab)";
by(stripS_tac 1);
br DomainI 1;
*)

zgoal thy "RepositoryState =+=> rep_permtab : ABS_PERMTAB";
by(stripS_tac 1);
by(full_expand_schema_tac RepositoryState_def 1);
bd DECL_D1 1;
by(atomizePremSolve 1);
qed"RepState_implies_type_repPtb";

zgoal thy "RepositoryState =+=> rep : ABS_DATATAB";
by(stripS_tac 1);
by(full_expand_schema_tac RepositoryState_def 1);
bd DECL_D1 1;
by(atomizePremSolve 1);
qed"RepState_implies_type_rep";


zgoal thy "RepositoryState =+=> dom rep = dom rep_permtab";
by(stripS_tac 1);
by(full_expand_schema_tac RepositoryState_def 1);
bd DECL_D2 1;
by(atomizePremSolve 1);
qed"RepState_implies_eqDomRepRepPtb";

zgoal thy "RepositoryState =+=> ?X : dom rep";
by(stripS_tac 1);
by(full_expand_schema_tac RepositoryState_def 1);
bd DECL_D2 1;
by(atomizePremSolve 1);
qed"abs_cvsauth_inDom_rep";

goal SysArchSec.thy "!! rep. RepositoryState(rep, rep_permtab) \
\ ==> rep_permtab %^ abs_cvsauth = cvs_admin";
by(stripS_tac 1);
by(full_expand_schema_tac RepositoryState_def 1);
bd DECL_D2 1;
by(atomizePremSolve 1);
qed"RepState_implies_permCvsauth";


(* verbessern.*)




zgoal thy " \
\ RepositoryState =+=>                        \
\ RepositoryState' =+=>                       \
\ rep %^ abs_cvsauth = rep' %^ abs_cvsauth    \
\ =+=>                                        \
\ authtab %^ rep = authtab %^ rep'";
by(stripS_tac 1);
(* substitute left side *)
by(res_inst_tac [("t",
		  "authtab %^ rep"),
		 ("s","abs_auth_of %^ (rep %^ abs_cvsauth)")] 
		subst 1);
br sym 1;
zbr def_authtab 1;
zbr RepState_implies_type_rep 1;
ba 1;
zbr abs_cvsauth_inDom_rep 1;
ba 1;
(* substitute right side *)
by(res_inst_tac [("t",
		  "authtab %^ rep'"),
		 ("s","abs_auth_of %^ (rep' %^ abs_cvsauth)")] 
		subst 1);
br sym 1;
zbr def_authtab 1;zbr RepState_implies_type_rep 1;
ba 1;
zbr abs_cvsauth_inDom_rep 1;
ba 1;
(* substitute main assumption *)
by(res_inst_tac [("t", 
		  "rep %^ abs_cvsauth"),
		 ("s", 
		  "rep' %^ abs_cvsauth")] subst 1);
br sym 1;
ba 1;
br refl 1;
qed"unch_abs_cvsauth_implies_auth_invariant";


(* This lemma is combined in the text directly *)
(* with operation abs_ci.                      *)
(* text-name:neqAuth *)
zgoal thy " \
\ RepositoryState =+=>                        \
\ RepositoryState' =+=>                       \
\ authtab %^ rep ~= authtab %^ rep'            \
\                   =+=>                      \
\ rep %^ abs_cvsauth ~= rep' %^ abs_cvsauth   ";
by(stripS_tac 1);
br ccontr 1;
zbd unch_abs_cvsauth_implies_auth_invariant 1;
ba 1;
bd notnotD 1;
ba 1;
by(res_inst_tac [("P", "authtab %^ rep = authtab %^ rep'")] notE 1);
ba 1;
ba 1;
qed"ch_authtab_implies_ch_abs_cvsauth";
