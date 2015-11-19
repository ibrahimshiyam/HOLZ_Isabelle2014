(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * AbsOperationsCons.ML --- 
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
(* $Id: AbsOperationsCons.ML 6746 2007-08-03 07:25:55Z brucker $ *)


(* abs_login ~~~~~~~~~~~~~~~~~~~~~~~~~~*)

goalw SysArchConsistency.thy [abs_login_cc1_def] "abs_login_cc1";

(* [missing]                                                   *)
(*                                                             *)
(* appl :  authtab %^ rep                                      *)


(* abs_ci ~~~~~~~~~~~~~~~~~~~~~~~~~~*) 

(* abs_ci_cc1 *)

goalw SysArchConsistency.thy [abs_ci_cc1_def] "abs_ci_cc1";

by(full_expand_schema_tac abs_ci_def 1);
by(stripS_tac 1);
by(convert2hol_tac [] 1); 
auto();
qed("abs_ci_cc1");



(* abs_ci_cc2 *)

goalw SysArchConsistency.thy [abs_ci_cc2_def] "abs_ci_cc2";

(* [missing]                                                   *)
(*  /see Security Section for inductive proof/                 *)
(* appl :   abs_passwd %^ (wc_uidtab %^ n)                     *)


(* abs_ci_cc3 *)

goalw SysArchConsistency.thy [abs_ci_cc3_def] "abs_ci_cc3";

(* [missing]                                                   *)
(* /doesn't hold                                               *)
(* appl :   authtab %^ rep                                     *)


(* abs_ci_cc4 *)

goalw SysArchConsistency.thy [abs_ci_cc4_def] "abs_ci_cc4";

by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
by(full_expand_schema_tac abs_ci_def 1);
by(convert2hol_tac [] 1);

by(full_expand_schema_tac abs_ci_def 2);
bd DECL_D1 2;
by(convert2hol_tac [] 2);

by(full_expand_schema_tac abs_ci_def 2);
bd DECL_D1 2;
by(convert2hol_tac [] 2);

by(full_expand_schema_tac ClientState_def 1);
by(full_expand_schema_tac abs_ci_def 1);
bd DECL_D1 1;
by(convert2hol_tac [] 1);
by(full_expand_schema_tac ClientState_def 1);
by(convert2hol_tac [] 1);
auto();
by(res_inst_tac[("t","dom rep_permtab"), ("s","dom rep")] subst 1);
by(full_expand_schema_tac abs_ci_def 1);
by(full_expand_schema_tac RepositoryState_def 1);
by(convert2hol_tac [] 1);
auto();

qed("abs_ci_cc4");


(* abs_ci_cc5 *)

goalw SysArchConsistency.thy [abs_ci_cc5_def] "abs_ci_cc5";
(* auto(); *)
by(stripS_tac 1);
br DECL_I 1;
br ballI 2;
br impI 2;
ba 2;
(* *)
by(full_expand_schema_tac abs_ci_def 1);
bd DECL_D1 1;
auto();
by(convert2hol_tac [XI_def, DELTA_def] 1);
qed("abs_ci_cc5");


(* abs_up ~~~~~~~~~~~~~~~~~~~~~~~~~~*)


(* abs_up_cc1 *)


goalw SysArchConsistency.thy [abs_up_cc1_def] "abs_up_cc1";
by(stripS_tac 1);
br DECL_I 1;
by(full_expand_schema_tac abs_up_def 1);
bd DECL_D1 1;
by(convert2hol_tac [DELTA_def, XI_def, Pow_def] 1);
br ballI 1;
br impI 1;
ba 1;
qed("abs_up_cc1");

(* abs_up_cc2 *)


goalw SysArchConsistency.thy [abs_up_cc2_def] "abs_up_cc2";

(* [missing]                                                   *)
(* /see inductive proof in security section/                   *)
(* appl :   abs_passwd %^ (wc_uidtab %^ n)                     *)

(* abs_up_cc3 *)


goalw SysArchConsistency.thy [abs_up_cc3_def] "abs_up_cc3";

(* [missing]                                                   *)
(* /not valid                                                  *)
(* appl :    authtab %^ rep                                    *)

(* abs_up_cc4 *)


goalw SysArchConsistency.thy [abs_up_cc4_def] "abs_up_cc4";

by(stripS_tac 1);
by(full_expand_schema_tac abs_up_def 1);
bd DECL_D1 1;
br DECL_I 1;
by(convert2hol_tac [DELTA_def, XI_def, Pow_def] 1);
by(res_inst_tac[("t","dom rep_permtab"), 
		("s","dom rep")] subst 1);
by(convert2hol_tac [RepositoryState_def] 1);
auto();

qed("abs_up_cc4");




(* ******************************************************************** *)
(*  									*)
(* 	Deadlockfreeness						*)
(*  									*)
(* by Harald Hiss	         					*)
(*  									*)
(* ******************************************************************** *)



(* *)


(* abs_login_df                      *)

goalw SysArchConsistency.thy [abs_login_df_def] "|- abs_login_df";
by(openDFobligation abs_login_def);
by(rewrAtomSubgoals);
by(do_improve []);
by(eraseTrivialsRiscy);
(* tryall laesst scheinbar kleinigkeit uebrig!  *)
(* mit metavariablen ist es zu sensibel.        *)
(* (vermutlich nach refl/ba von metavars werden *)
(* schwerere ziele leichter, und uebersehen.    *)
by(convert2hol_tac [ClientState_def] 1);
br oplMemSubstSingleton 1;

by(do_improve [PASSWD_TAB_def]);

qed"abs_login_df";

(* *)



(* abs_cd_df                      *)

goalw SysArchConsistency.thy [abs_cd_df_def] "|- abs_cd_df";
by(openDFobligation abs_cd_def);
by(rewrAtomSubgoals);
by(do_improve []);
by(eraseTrivialsRiscy);
by(convert2hol_tac [ClientState_def] 1);
auto();
qed"abs_cd_df";

(* *)


(* abs_add_df                      *)

goalw SysArchConsistency.thy [abs_add_df_def] "|- abs_add_df";
by(openDFobligation abs_add_def);
by(rewrAtomSubgoals);
by(do_improve []);
br refl 2;(* doesnt look nice here *)
by(convert2hol_tac [ClientState_def] 1);
auto();
br pfunOplDomSubst 1;
by(do_improve [ABS_DATATAB_def]);
by(rewrite_goals_tac [image_def]);
br pfunOplDomSubst 1;
by(do_improve [ABS_UIDTAB_def]);
by(convert2hol_tac [ABS_UIDTAB_def] 1);

br pfunI 1;
by(convert2hol_tac [rel_def, maplet_def, Mu_def] 1);
auto();
by(convert2hol_tac [rel_def, maplet_def, Mu_def] 1);
auto();
qed"abs_add_df";

(* *)


(* abs_ci_df                      *)

(* migrated proof to seperate file *)


use"abs_ci_df";


(* 

(* abs_up_df                      *)

goalw SysArchConsistency.thy [abs_up_df_def] "|- abs_up_df";
by(openDFobligation abs_up_def);
by(rewrAtomSubgoals);
by(do_improve []);
br refl 2;
br PowD 2;
ba 2;
by(convert2hol_tac [ClientState_def] 1);
(* show ClientState after abs_up. *)
by(rewrAtomSubgoals);

br pfunOplDomSubst 1;
by(convert2hol_tac [ClientState_def] 1);
by(convert2hol_tac [ABS_DATATAB_def] 2);

br  domRestrDistrS 1;
by(convert2hol_tac [RepositoryState_def, ABS_DATATAB_def] 1);
by(rewrite_goals_tac[ABS_UIDTAB_def]);
br pfunI 1;
br unMem 1;
br refl 3;
by(convert2hol_tac [partial_func_def] 1);







by(eraseTrivialsRiscy);
(* tryall laesst scheinbar kleinigkeit uebrig!  *)
(* mit metavariablen ist es zu sensibel.        *)
(* (vermutlich nach refl/ba von metavars werden *)
(* schwerere ziele leichter, und uebersehen.    *)
by(convert2hol_tac [ClientState_def] 1);
br oplMemSubstSingleton 1;

by(do_improve [PASSWD_TAB_def]);

qed"abs_up_df";

(* lemmas *)


goal thy 
"!! A B. [| A : T; B : T; T = X -|-> Y; \
\ (a : dom B)==> (a ~: dom A);  (a : dom A)==> (a ~: dom B)|] \
\   ==> (A Un B) : T";
auto();

br pfunI 1;
br unMem 1;

by(convert2hol_tac [partial_func_def] 1);
by(convert2hol_tac [partial_func_def] 1);
br refl 1;

qed"unMemPfun";
*)
