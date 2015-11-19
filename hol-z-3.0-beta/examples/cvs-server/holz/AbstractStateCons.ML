(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * AbstractStateCons.ML --- 
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
(* $Id: AbstractStateCons.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* ******************************************************************** *)
(*  									*)
(* 	Project		: The CVS-Server Case Study			*)
(*  	Author 		: B. Wolff, F.Rittinger, A. Brucker     	*)
(*  	Affiliation 	: Albert-Ludwigs-University of Freiburg		*)
(*   	This file	: Consistency Conditions for the AbstractState  *)
(*                        ZSection by Harald Hiss                       *)
(*  	Release  	: 1.0						*)
(*  									*)
(*  ******************************************************************* *)

(* General setup of AbstractState *)
(* open AbstractState; 	 	  *)
(* 				  *)
(* toToplevel axdefs;  	 	  *)
(* toToplevel schemes; 	 	  *)
(* 				  *)


(* ******************************************************************** *)
(*  									*)
(* 	Definedness     						*)
(*  									*)
(* by Harald Hiss	        					*)
(*  									*)
(* ******************************************************************** *)

(* use_holz"SysArchConsistency";         *)
(* open SysArchConsistency;   evtl:      *)
(* toToplevel SysArchConsistency.axdefs; *)
(* toToplevel SysArchConsistency.schemes;*)



(* RepositoryState ~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* ABS_PERMTAB *)
(* RepositoryState_cc1 *)

goalw SysArchConsistency.thy [RepositoryState_cc1_def] "RepositoryState_cc1";
by(full_expand_schema_tac RepositoryState_def 1);
by (convert2hol_tac [] 1);
(*--by (rewrite_goals_tac[Ball_def]);               *)
br ballI 1;
auto();
qed("RepositoryState_cc1");

(*@proofstatistic:endProof*)


(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* RepositoryState_cc2 *)
(*ABS_PERMTAB*)
goalw SysArchConsistency.thy [RepositoryState_cc2_def] "RepositoryState_cc2";
by(full_expand_schema_tac RepositoryState_def 1);
by (convert2hol_tac [] 1);
auto();
by(rewrite_goals_tac[ABS_DATATAB_def]);
by(rewrite_goals_tac[ABS_PERMTAB_def]);
by (res_inst_tac [("t","dom b"), ("s","dom a")] subst 1);
ba 1;
by (res_inst_tac [("t","abs_cvsauth : dom a"), ("s","(? y. y:ran(a) & (abs_cvsauth,y):a)")] subst 1);
br sym 1;
br Dom_In 1;
auto();
qed("RepositoryState_cc2");
(*@proofstatistic:endProof*)





(* abs_cvsauth ~~~~~~~~~~~~~~~~~~~~~~~~~~*)


(*@proofstatistic:beginProof*)
(* abs_cvsauth_cc1 *)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* abs_data_of   *)

goalw SysArchConsistency.thy [] "abs_cvsauth_cc1_ = %N";
by(cut_facts_tac [abs_auth_of_axdef] 1);
by (convert2hol_tac [] 1);
be conjE 1;
by (thin_tac "?a" 1);
be conjE 1;
by(rotate_tac 1 1);
be conjE 1;
by(rotate_tac 2 1);
by (thin_tac "?a" 1);
by(cut_facts_tac [abs_cvsauth_cc1__axdef] 1);
by(rewrite_goals_tac[total_func_def,partial_func_def,rel_def]);
auto();
qed("abs_cvsauth_cc1");

(*@proofstatistic:endProof*)


(*@proofstatistic:beginProof*)
(* abs_cvsauth_cc2 *)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* abs_auth_of   *)
goalw SysArchConsistency.thy [] "abs_cvsauth_cc2_ = %N";
by(cut_facts_tac [abs_cvsauth_cc2__axdef] 1);
by (convert2hol_tac [] 1);
auto();
qed("abs_cvsauth_cc2");
(*@proofstatistic:endProof*)




(* abs_cvsauth_cc3*)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* abs_auth_of   *)
goalw SysArchConsistency.thy [] "abs_cvsauth_cc3_ = %N";
by(cut_facts_tac [abs_cvsauth_cc3__axdef] 1);
by(cut_facts_tac [abs_auth_of_axdef] 1);
by (convert2hol_tac [] 1);
auto();
qed("abs_cvsauth_cc3");
(*@proofstatistic:endProof*)


(* abs_cvsauth_cc4*)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* abs_data_of   *)
goalw SysArchConsistency.thy [] "abs_cvsauth_cc4_ = %N";
by(cut_facts_tac [abs_cvsauth_cc4__axdef] 1);
by(cut_facts_tac [abs_auth_of_axdef] 1);
by (convert2hol_tac [] 1);

by (rewrite_goals_tac[total_func_def]);
by (rewrite_goals_tac[partial_func_def]);
by(rewrite_goals_tac[rel_def]);
auto();
qed("abs_cvsauth_cc4");
(*@proofstatistic:endProof*)


(* abs_cvsauth_cc5*)

goalw SysArchConsistency.thy [] "abs_cvsauth_cc5_ = %N";

(* [missing]                                                   *)
(* appl : AbstractState.authtab %^ r                           *)
(*                                                             *)
(* Maybe it is useful to change the following line             *)
(* all r:ABS_DATATAB. r : (dom authtab --> original predicate) *)
(* , provided that there exists a workaround for CVS.          *)

(*qed("abs_cvsauth_cc5");*)




(* abs_cvsauth_cc6*)

goalw SysArchConsistency.thy [] "abs_cvsauth_cc6_ = %N";

(* [missing]                                                     *)
(*  appl :                                                       *)
(* AbstractState.abs_auth_of %^ (r %^ AbstractState.abs_cvsauth) *)
(*                                                               *)
(* ... has to be                                                 *)
(* defined to satisfy the definedness consistency condition.     *)
(* If this can be granted (e.g. using a workaround), then a local*)
(* implication may be used as the central argument for the proof.*)
(*qed("abs_cvsauth_cc6");*)



(* abs_cvsauth_cc7*)

goalw SysArchConsistency.thy [] "abs_cvsauth_cc7_ = %N";

(* [missing]                                                     *)
(* appl :    r %^ AbstractState.abs_cvsauth                      *)
(*                                                               *)
(* For all r:ABS_DATATAB, r abs_cvsauth has to be                *)
(* defined to satisfy the definedness consistency condition.     *)
(* If this can be granted (e.g. using a workaround), then a local*)
(* implication may be used as the central argument for the proof.*)
(*                                                               *)
(*qed("abs_cvsauth_cc7");                                        *)
