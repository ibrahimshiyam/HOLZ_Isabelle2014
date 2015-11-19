(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * Definedness_Conditions.ML --- 
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
(* $Id: Definedness_Conditions.ML 6746 2007-08-03 07:25:55Z brucker $ *)


use_holz"SysArchConsistency";

(* \Zsection{sectionname}                   *)
    (*                                      *)
    (* constructs the following             *)
    (*                                      *)
    (* struct sectionname                   *)
    (* begin                                *)
    (* val axdefs                           *)
    (* val schemes                          *)
    (* val thy                              *)
    (* end                                  *)
    (*                                      *)
    (* ...access to the values can be       *)
    (* achieved via:                        *)
    (*                                      *)
    (* open_schemes sectionname.schemes;    *)
    (*                                      *)
    (* Sticking to this schema, the         *)
    (* schemes corresponding to the sections*)
    (* won't overwrite each other.          *)

open_schemes(SysArchConsistency.schemes);
open_schemes(SysArchConsistency.axdefs);
open_schemes AbstractState.schemes;
open_schemes AbstractState.axdefs;
open_schemes FileSystem.schemes;
open_schemes FileSystem.axdefs;

(* --------------------------------------------------------- *)
(*                                                           *)
(* Definedness - Consistency - Conditions                    *)
(*                                                           *)
(* --------------------------------------------------------- *)


(* AbstractState - Zsection -------------------------------- *)


(* RepositoryState ~~~~~~~~~~~~~~~~~~~~~~~~~~*)


(* RepositoryState_cc_1 *)

goalw SysArchConsistency.thy [RepositoryState_cc_1_def] "RepositoryState_cc_1";
by(full_expand_schema_tac RepositoryState_def 1);
by (convert2hol_tac [] 1);
(*--by (rewrite_goals_tac[Ball_def]);               *)
br ballI 1;
auto();
by(rewrite_goals_tac[ABS_DATATAB_def]);
by(rewrite_goals_tac[ABS_PERMTAB_def]);
by (res_inst_tac [("t","dom y"), ("s","dom xa")] subst 1);
ba 1;
by (res_inst_tac [("t","abs_cvsauth : dom xa"), ("s","(? y. y:ran(xa) & (abs_cvsauth,y):xa)")] subst 1); 
br sym 1;
br Dom_In 1;
auto();
qed("RepositoryState_cc_1");

(* RepositoryState_cc_2 *)

goalw SysArchConsistency.thy [RepositoryState_cc_2_def] "RepositoryState_cc_2";
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
qed("RepositoryState_cc_2");




(* abs_cvsauth ~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* abs_cvsauth_cc1 *)

goalw SysArchConsistency.thy [] "abs_cvsauth_cc1_ = %N";
by(cut_facts_tac [abs_cvsauth_cc1__axdef] 1);
by (convert2hol_tac [] 1);
auto();
qed("abs_cvsauth_cc1");


(* abs_cvsauth_cc2 *)

goalw SysArchConsistency.thy [] "abs_cvsauth_cc2_ = %N";
by(cut_facts_tac [abs_auth_of_axdef] 1);
by (convert2hol_tac [] 1);
be conjE 1;
by (thin_tac "?a" 1);
be conjE 1;
by(rotate_tac 1 1);
be conjE 1;
by(rotate_tac 2 1);
by (thin_tac "?a" 1);

by(cut_facts_tac [abs_cvsauth_cc2__axdef] 1);
by (convert2hol_tac [] 1);

by (rewrite_goals_tac[total_func_def]);
by (rewrite_goals_tac[partial_func_def]);
by(rewrite_goals_tac[rel_def]);
auto();

qed("abs_cvsauth_cc2");

(* abs_cvsauth_cc3*)

goalw SysArchConsistency.thy [] "abs_cvsauth_cc3_ = %N";
by(cut_facts_tac [abs_cvsauth_cc3__axdef] 1);
by(cut_facts_tac [abs_auth_of_axdef] 1);
by (convert2hol_tac [] 1);

by (rewrite_goals_tac[total_func_def]);
by (rewrite_goals_tac[partial_func_def]);
by(rewrite_goals_tac[rel_def]);
auto();
qed("abs_cvsauth_cc3");

(* abs_cvsauth_cc4*)

goalw SysArchConsistency.thy [] "abs_cvsauth_cc4_ = %N";
by(cut_facts_tac [abs_cvsauth_cc4__axdef] 1);
by(cut_facts_tac [abs_auth_of_axdef] 1);
by (convert2hol_tac [] 1);
auto();
qed("abs_cvsauth_cc4");

(* abs_cvsauth_cc5*)

goalw SysArchConsistency.thy [] "abs_cvsauth_cc5_ = %N";

(* [missing]                                                   *)
(* this one probably needs to be fixed in the specification.   *)
(* Maybe it is useful to change the following line             *)
(* all r:ABS_DATATAB. r : (dom authtab --> original predicate) *)
(*qed("abs_cvsauth_cc5");*)

(* abs_cvsauth_cc6*)

goalw SysArchConsistency.thy [] "abs_cvsauth_cc6_ = %N";

(* [missing]                                                   *)
(* This one was locally fixed in the specification.            *)
(* So this CC has to be weakened.                              *)
(* An implication is used to state a local precondition.       *)
(*qed("abs_cvsauth_cc6");*)

(* abs_cvsauth_cc7*)

goalw SysArchConsistency.thy [] "abs_cvsauth_cc7_ = %N";

(* [missing]                                                   *)
(* This one was locally fixed in the specification.            *)
(* So this CC has to be weakened.                              *)
(* An implication is used to state a local precondition.       *)
(* Here, for all r:ABS_DATATAB only r abs_cvsauth has to be    *)
(* defined.                                                    *)
(*qed("abs_cvsauth_cc7");*)

(* AbsOperations - Zsection -------------------------------- *)


(* abs_login ~~~~~~~~~~~~~~~~~~~~~~~~~~*)

goalw SysArchConsistency.thy [abs_login_cc1_def] "abs_login_cc1";

(* [missing]                                                   *)
(* This one needs to be locally fixed in the specification.    *)
(* There is no statement yet which allows to conclude that     *)
(*                                                             *)
(* An implication is used to state a local precondition.       *)
(* Here, for all r:ABS_DATATAB only r abs_cvsauth needs to be  *)
(* defined.                                                    *)

(* abs_ci ~~~~~~~~~~~~~~~~~~~~~~~~~~*) 

(* abs_ci_cc1 *)

goalw SysArchConsistency.thy [abs_ci_cc1_def] "abs_ci_cc1";

(* [missing]                                                   *)
(* This one was locally fixed in the specification.            *)
(* So this CC has to be weakened.                              *)
(* Within a conjunction, here is stated a local precondition.  *)
(* n \in dom wc_roletab                                        *)

(*qed("abs_ci_cc1");*)

(* abs_ci_cc2 *)

goalw SysArchConsistency.thy [abs_ci_cc2_def] "abs_ci_cc2";

(* [missing]                                                   *)
(* This one needs to be locally fixed in the specification.    *)
(* So this CC has to be weakened.                              *)
(*                                                             *)
(* rep \in dom auth_tab is missing.                            *)

(*qed("abs_ci_cc2");*)

(* abs_ci_cc3 *)

goalw SysArchConsistency.thy [abs_ci_cc3_def] "abs_ci_cc3";


(* [missing]                                                   *)
(* This one is locally fixed in the specification.             *)
(* So this CC has to be weakened.                              *)
(* Within a conjunction, here is stated a local precondition.  *)
(* with dom rep = dom rep_permtab in RepositoryState           *)
(* and the conjunct n \in dom rep this can be solved.          *)

(*qed("abs_ci_cc3");*)


(* abs_ci_cc4 *)

goalw SysArchConsistency.thy [abs_ci_cc4_def] "abs_ci_cc4";


(* [missing]                                                   *)
(* This one is locally fixed in the specification.             *)
(* So this CC has to be weakened.                              *)
(* Within a conjunction, here is stated a local precondition.  *)
(* with dom rep = dom rep_permtab in RepositoryState           *)
(* and the conjunct n \in dom rep this can be solved.          *)
(* Here, we know wc_roletab n \in dom authtab rep              *)

(*qed("abs_ci_cc4");*)


(* abs_up ~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* [missing]                                   *)
(* with abs_up it is the same as  with abs_ci. *)

goalw SysArchConsistency.thy [abs_up_cc1_def] "abs_up_cc1";
(*qed("abs_up_cc4");*)


goalw SysArchConsistency.thy [abs_up_cc2_def] "abs_up_cc2";
(*qed("abs_up_cc4");*)


goalw SysArchConsistency.thy [abs_up_cc3_def] "abs_up_cc3";
(*qed("abs_up_cc4");*)


goalw SysArchConsistency.thy [abs_up_cc4_def] "abs_up_cc4";
(*qed("abs_up_cc4");*)


(* FileSystem - Zsection ----------------------------------- *)


(* is_in ~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* is_in_cc1*)

goalw SysArchConsistency.thy [] "is_in_cc1_ = %N";
by(cut_facts_tac [X_isdirin__axdef] 1);
by (convert2hol_tac [] 1);
be conjE 1;
by (thin_tac "?a" 1);
be conjE 1;
by (thin_tac "?a" 1);
be conjE 1;
by (thin_tac "?a" 1);
be conjE 1;
by(rotate_tac 1 1);
by (thin_tac "?a" 1);
by(cut_facts_tac [is_in_cc1__axdef] 1);
by (convert2hol_tac [] 1);
auto();
qed("is_in_cc1");

(* is_in_cc2*)

goalw SysArchConsistency.thy [] "is_in_cc2_ = %N";
by(cut_facts_tac [is_in_cc2__axdef] 1);
by (convert2hol_tac [] 1);
auto();
qed("is_in_cc2");

(* has_attrib_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* has_attrib_cc1         *)

goalw SysArchConsistency.thy [] "has_attrib_cc1_ = %N";
by(cut_facts_tac [groups_axdef] 1);
by (convert2hol_tac [] 1);
be conjE 1;
by (thin_tac "?a" 1);
by(cut_facts_tac [has_attrib_cc1__axdef] 1);
by (convert2hol_tac [] 1);
auto();
qed("has_attrib_cc1");

(* has_attrib_cc2         *)

goalw SysArchConsistency.thy [] "has_attrib_cc2_ = %N";

(* [missing]                                                   *)
(* This one is locally fixed in the specification.             *)
(* So this CC has to be weakened. (p31: \all p: dom (fa))      *)
(* and fa FileAttrtab, p path.                                 *)
(*qed("has_attrib_cc2");*)

(* has_w_access_cc1 ~~~~~~~~~~~~~~~~~~~~~~~~~~*)

goalw SysArchConsistency.thy [] "has_w_access_cc1_ = %N";

by(cut_facts_tac [has_w_access_cc1__axdef] 1);
by (convert2hol_tac [] 1);
auto();
by (rewrite_goals_tac[frontseq_def]);
auto();
qed("has_w_access_cc1");

(* mkdir_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* mkdir_cc1              *)

goalw SysArchConsistency.thy [mkdir_cc1_def] "mkdir_cc1";
by(full_expand_schema_tac mkdir_def 1);
by (convert2hol_tac [] 1);
auto();
qed("mkdir_cc1");

(* mkdir_cc2              *)

goalw SysArchConsistency.thy [mkdir_cc2_def] "mkdir_cc2";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
(*Get rid of trivial subgoals.*)
by(full_expand_schema_tac mkdir_def 1);
by(convert2hol_tac [] 1);
by(REPEAT_DETERM_N 9((full_expand_schema_tac mkdir_def 2)THEN(convert2hol_tac [] 2)));

by(full_expand_schema_tac mkdir_def 1);
bd DECL_D1 1;
by(convert2hol_tac [] 1);

(* Now, the subgoal which is left to us is: *)
(* ... ==> wdir : dom attributes            *)

(*by(full_expand_schema_tac mkdir_def 1);*)
(*by(convert2hol_tac [] 1);*)
by(REPEAT (etac conjE 1));
by(res_inst_tac [("s","wdir"),("t","wdir'")] subst 1);
ba 1;
by (rotate_tac 1 1);
by (thin_tac "?a" 1);
by (rotate_tac 1 1);
by(REPEAT_DETERM_N 6(thin_tac "?a" 1));
by (rotate_tac 1 1);
by(REPEAT_DETERM_N 4(thin_tac "?a" 1));
(* The following Assumptions carry enough information    *)
(* for the proof:                                        *)
(* FileSystem (attributes, files);                       *)
(* ProcessState (gid, uid, umask, wdir);                 *)
(* (wdir, files) : _isdirin_                             *)
(* Only some Definitions have to be added.               *)
(*                                                       *)
by(cut_facts_tac [X_isdirin__axdef] 1);
by (convert2hol_tac [] 1);
by(REPEAT(etac conjE 1));
by (rotate_tac 3 1);
by(REPEAT_DETERM_N 3(thin_tac "?a" 1));
by (rotate_tac 2 1);
by (thin_tac "?a" 1);
(* Now both isin and isdirin - Definitions      *)
(* are available in our assumptions.            *)
by(res_inst_tac [("s","dom files"),("t","dom attributes")] subst 1);
by(full_expand_schema_tac FileSystem_def 1);
by(convert2hol_tac [] 1);

by(res_inst_tac [("Q","?a")] rev_iffD2 1);
br sym 2;
by(rewrite_goals_tac[Ball_def]);
by(res_inst_tac [("Q","?b")] mp 2);
by(res_inst_tac [("x","wdir")] spec 2);
by(res_inst_tac [("Q","?c")] mp 2);
by(res_inst_tac [("x","files")] spec 2);
ba 2;
by(full_expand_schema_tac FileSystem_def 2);
by(rewrite_goals_tac[FILESYS_TAB_def]);
by(convert2hol_tac [] 2);
by(full_expand_schema_tac ProcessState_def 2);
by(convert2hol_tac [] 2);

br conjunct1 1;
by(res_inst_tac [("Q","?a")] rev_iffD2 1);
br sym 2;(**)
by(res_inst_tac [("Q","?b")] mp 2);
by(res_inst_tac [("x","wdir")] spec 2);
by(res_inst_tac [("Q","?c")] mp 2);
by(res_inst_tac [("x","files")] spec 2);
ba 2;
by(full_expand_schema_tac ProcessState_def 3);
by(convert2hol_tac [] 3);
by(full_expand_schema_tac FileSystem_def 2);
by(rewrite_goals_tac[FILESYS_TAB_def]);
by(convert2hol_tac [] 2);
ba 1;
qed("mkdir_cc2");


(* mkdir_cc3              *)

goalw SysArchConsistency.thy [mkdir_cc3_def] "mkdir_cc3";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();

by(full_expand_schema_tac mkdir_def 1);
by(convert2hol_tac [] 1);

by(REPEAT_DETERM_N 9 ((full_expand_schema_tac mkdir_def 2)THEN(convert2hol_tac [] 2)));
by(full_expand_schema_tac mkdir_def 1);

bd DECL_D1 1;
be conjE 1;
by(rotate_tac 1 1);
by(thin_tac "?a" 1);
by(convert2hol_tac [] 1);

qed("mkdir_cc3");


(* mkfile_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* mkfile_cc1             *)

goalw SysArchConsistency.thy [mkfile_cc1_def] "mkfile_cc1";
by(full_expand_schema_tac mkfile_def 1);
by (convert2hol_tac [] 1);
auto();
(* done.*)
qed("mkfile_cc1");

(* mkfile_cc2             *)

goalw SysArchConsistency.thy [mkfile_cc2_def] "mkfile_cc2";
by(cut_facts_tac [X_isdirin__axdef] 1);
by (convert2hol_tac [] 1);
be conjE 1;
by (thin_tac "?a" 1);
be conjE 1;
by (thin_tac "?a" 1);
be conjE 1;
by (thin_tac "?a" 1);
be conjE 1;
by (rotate_tac 1 1);
be conjE 1;
by (rotate_tac 2 1);
by (thin_tac "?a" 1);
(* with copy & paste from above      *)
(*                                   *)
(* Trying to finish with auto() here *)
(* is useless, the goal needs some   *)
(* pruning...                        *)
by(full_expand_schema_tac mkfile_def 1);
by(REPEAT (rtac allI 1));
br impI 1;
by (thin_tac "?a" 1);
br conjI 1;
by (thin_tac "?a" 1);
by (convert2hol_tac [] 1);
(* splitting off easier subgoals... *)
br conjI 1;
by (thin_tac "?a" 1);
by (convert2hol_tac [] 1);
by (Blast_tac 1);

br conjI 1;
by (thin_tac "?a" 1);
by (convert2hol_tac [] 1);

br conjI 1;
by (thin_tac "?a" 1);
by (convert2hol_tac [] 1);
(* from here : 6 Times the same. *)
(*1*)
br conjI 1;
by (thin_tac "?a" 1);
by (convert2hol_tac [] 1);
(*2*)
br conjI 1;
by (thin_tac "?a" 1);
by (convert2hol_tac [] 1);
(*3*)
br conjI 1;
by (thin_tac "?a" 1);
by (convert2hol_tac [] 1);
(*4*)
br conjI 1;
by (thin_tac "?a" 1);
by (convert2hol_tac [] 1);
(*5*)
br conjI 1;
by (thin_tac "?a" 1);
by (convert2hol_tac [] 1);
(*6*)
br conjI 1;
by (thin_tac "?a" 1);
by (convert2hol_tac [] 1);

(* Ok., maybe here at least a  tactical *)
(* could be of help.                    *)
(* ...leaves the last conjunct upto us: *)
(* need to show: al : dom a             *)

by(full_expand_schema_tac FileSystem_def 1);
by(rewrite_goals_tac[FILESYS_TAB_def]);
by(full_expand_schema_tac ProcessState_def 1);
by (convert2hol_tac [] 1);
by (rewrite_goals_tac[rel_apply_def]);
by (rewrite_goals_tac[ran_restr_def]);
auto();
qed("mkfile_cc2");


(* access_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* access_cc1             *)

goalw SysArchConsistency.thy [access_cc1_def] "access_cc1";
by(cut_facts_tac [X_isdirin__axdef] 1);
by (convert2hol_tac [] 1);
be conjE 1;
by (thin_tac "?a" 1);
be conjE 1;
by (thin_tac "?a" 1);
be conjE 1;
by (thin_tac "?a" 1);
be conjE 1;
by (rotate_tac 1 1);
be conjE 1;
by (rotate_tac 2 1);
by (thin_tac "?a" 1);
(* with copy & paste from above       *)
(*                                    *)
(* Trying to finish with auto() here  *)
(* is probably also useless, I do not *)
(* even try it. the goal needs some   *)
(* additional pruning...              *)
by(full_expand_schema_tac access_def 1);
by(REPEAT (rtac allI 1));
br impI 1;
by (thin_tac "?a" 1);

(* start here *)
(*by(REPEAT ((rtac conjI 1)THEN((thin_tac "?a" 1) THEN(convert2hol_tac [] 1))));*)
(*...this one went one step to far.   *)

br conjI 1;
by(REPEAT ((thin_tac "?a" 1) THEN ((convert2hol_tac [] 1) THEN(rtac conjI 1)) ));

by(Blast_tac 1);
(* so last but not least there is only one goal left... *)

by (convert2hol_tac [] 1);
by(rotate_tac 1 1);
(* also looks like some pruning needs to be done. *)
by(REPEAT (etac conjE 1));

by (res_inst_tac [("t","b"), ("s","al")] subst 1);
by (convert2hol_tac [] 1);
(* prune a little ... *)
by(rotate_tac 1 1);
by (thin_tac "?a" 1);
by(rotate_tac 4 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by(rotate_tac 4 1);
by (thin_tac "?a" 1);
by(full_expand_schema_tac ProcessState_def 1);
by(convert2hol_tac [] 1);
(* fetch facts from ProcessState, *)
(* al : Path for example          *)
(* now try also from FileSystem   *)
by(full_expand_schema_tac FileSystem_def 1);
by(convert2hol_tac [] 1);
by (thin_tac "?a" 1);
by(rotate_tac 1 1);
be conjE 1;
by(rotate_tac 2 1);
by(REPEAT (etac conjE 1));
by(rotate_tac 2 1);
by (thin_tac "?a" 1);
by(rotate_tac 3 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);(*aa : FILEATTR_TAB*)
(*by(rotate_tac 1 1);*)
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by(rotate_tac 1 1);
(*by (thin_tac "?a" 1);*)
by (thin_tac "?a" 1);
by(rewrite_goals_tac[FILESYS_TAB_def]);
by(rewrite_goals_tac[Ball_def]);

(*-- if there is no way for automation, *)
(* I will start using hands...          *)
(* I already see a solution...          *)

by (res_inst_tac [("t","dom aa"), ("s","dom ad")] subst 1); 
ba 1;
by(rotate_tac 6 1);
by (thin_tac "?a" 1);
(*                                        *)
(*by(rewrite_goals_tac[rel_apply_def]);   *)
(*auto();   nice:                         *)
(* throws out one unnecessary variable... *)
(* , plus one needed assumption...        *)
br conjunct1 1;
by(res_inst_tac [("P","?a")] rev_iffD2 1);
br sym 2;
by(res_inst_tac [("P","?a")] mp 2);
by (rewrite_goals_tac[insertseq_def]);
by (rewrite_goals_tac[emptyseq_def]);
by (rewrite_goals_tac[rel_apply_def]);
by(res_inst_tac [("x","(@ y. ((b, insert (#1, ag){p. ? n:dom {}. p = (zsuc n, @ y. (n, y) : {})}),y): concatseq)")] spec 2);
(* by(res_inst_tac [("x","((@ y. ((b, %< ag %>), y) : concatseq)")] spec 2);  *)
(* ... % - expressions cannot be parsed yet.                                  *)
by(res_inst_tac [("P","?a")] mp 2);
by(res_inst_tac [("x","ad")] spec 2);
ba 2;
(* forget about auto() here... *)
by (fold_goals_tac[rel_apply_def]);
by (fold_goals_tac[insertseq_def]);
by (fold_goals_tac[emptyseq_def]);
ba 1;
ba 1;
by(rewrite_goals_tac[Path_def]);
auto();
(* This time, I actually used tacticals.            *)
qed("access_cc1");


(* write_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* write_cc1                  *)

goalw SysArchConsistency.thy [write_cc1_def] "write_cc1";
by(full_expand_schema_tac write_def 1);
by (convert2hol_tac [] 1);
auto();
qed("write_cc1");


(* mv_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* mv_cc1                     *)

goalw SysArchConsistency.thy [mv_cc1_def] "mv_cc1"; 
by(stripS_tac 1);
by(convert2hol_tac [] 1);
by(full_expand_schema_tac mv_def 1); 
by(convert2hol_tac [] 1);
by(REPEAT ((rtac conjI 1)THEN(convert2hol_tac [] 1)));
by(Blast_tac 1);
by(res_inst_tac [("t","wdir'"), ("s","wdir")] subst 1);
by(Blast_tac 1);
by(REPEAT (etac conjE 1));
(* Now I start Pruning off unneeded literals from the assumptions. *)
by(rotate_tac 1 1);
by (thin_tac "?a" 1);
by(rotate_tac 1 1);
by (thin_tac "?a" 1);
(* a lot of useless assumptions...*)
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);

by(rotate_tac 1 1);
by (thin_tac "?a" 1);

by(rotate_tac 1 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);

(* now, we have to fetch the definition of      *)
(* the isin - Relation from the X_isdirin_axdef *)
by(cut_facts_tac [X_isdirin__axdef] 1);
by (convert2hol_tac [] 1);
by(rotate_tac 4 1);
by(REPEAT (etac conjE 1));
by(rotate_tac 4 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by(rotate_tac 1 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
(* now lets see how automatical this works... *)
by(rewrite_goals_tac[Ball_def]);
by(res_inst_tac [("Q","?a")] rev_iffD2 1);
br sym 2;
by(res_inst_tac [("Q","?b")] mp 2);
by(res_inst_tac [("x","wdir %&^ %< u1_63 %>")] spec 2);
by(res_inst_tac [("Q","?c")] mp 2);
by(res_inst_tac [("x","files")] spec 2);
ba 2;
ba 1;
by (rotate_tac 1 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by(full_expand_schema_tac FileSystem_def 1);
by(rewrite_goals_tac[FILESYS_TAB_def]);
by(convert2hol_tac [] 1);
(* only one subgoal left...                     *)
(* needs u1_63:Name and ProcessState(...,wdir)  *)
by (thin_tac "?a" 1);
by (rotate_tac 2 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by(full_expand_schema_tac ProcessState_def 1);
by(convert2hol_tac [] 1);
by(REPEAT (etac conjE 1));
by (rotate_tac 1 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
by (thin_tac "?a" 1);
(* ...need to somehow get rid of the %- Symbols... *)
by(rewrite_goals_tac[Path_def]);
auto();
qed("mv_cc1");



(* mv_cc2                     *)

goalw SysArchConsistency.thy [mv_cc2_def] "mv_cc2"; 
(*by(full_expand_schema_tac FileSystem_def 1);*)
by(stripS_tac 1);
by(convert2hol_tac [] 1);
by(REPEAT (SOMEGOAL(rtac conjI)));
(* avoid early expansion of the mv - schema *)
by(REPEAT_DETERM_N 10 ((full_expand_schema_tac mv_def 1)THEN(convert2hol_tac [] 1)));
by(Blast_tac 1);
by(REPEAT_DETERM_N 8 ((full_expand_schema_tac mv_def 1)THEN(convert2hol_tac [] 1)));
(* Here, I try for the first time to reuse *)
(* proofs in the schema-calculus in order  *)
(* to save time.                           *)
by(cut_facts_tac [mv_cc1] 1);
by(rewrite_goals_tac[mv_cc1_def]);
by(res_inst_tac [("t","dom attributes"), ("s","dom files")] subst 1);
by(full_expand_schema_tac mv_def 1);
by(full_expand_schema_tac FileSystem_def 1); 
by(convert2hol_tac [] 1);
(* upto here: ok. Maybe the schema insertion helps... *)
by(convert2hol_tac [] 1);
auto();
qed("mv_cc2");


(* chown_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* chown_cc1                     *)

goalw SysArchConsistency.thy [chown_cc1_def] "chown_cc1"; 
(*by(full_expand_schema_tac FileSystem_def 1);*)
by(stripS_tac 1);
by(res_inst_tac [("t","dom attributes"),("s","dom files")] subst 1);
by(full_expand_schema_tac chown_def 1);
by(full_expand_schema_tac FileSystem_def 1);
by(convert2hol_tac [] 1);
(* maybe achieve a higher degree of automation here...*)
by(full_expand_schema_tac chown_def 1);
by(convert2hol_tac [] 1);
auto();
qed("chown_cc1");

(* chown_cc2                     *)

(* By now, I think that the use of tacticals is *)
(* very appetising.                             *)

goalw SysArchConsistency.thy [chown_cc2_def] "chown_cc2"; 
by(stripS_tac 1);
by(full_expand_schema_tac chown_def 1);
by(convert2hol_tac [] 1);
br conjI 1;
by(Blast_tac 1);
by(res_inst_tac [("t","uid'"),("s","uid")] subst 1);
by(REPEAT (etac conjE 1));
ba 1;
by(REPEAT (etac conjE 1));
by(REPEAT_DETERM_N 2 (thin_tac "?a" 1));
by(rotate_tac 1 1);
by(REPEAT_DETERM_N 12 (thin_tac "?a" 1));
by(full_expand_schema_tac ProcessState_def 1);
by(convert2hol_tac [] 1);
by(REPEAT (etac conjE 1));
by(rotate_tac 1 1);
by(REPEAT_DETERM_N 3 (thin_tac "?a" 1));
(* now, I collected everything I need *)
(* from the Assumption. Its time to   *)
(* import the definition of groups    *)
(* in order to use the total-property.*)
by(cut_facts_tac [groups_axdef] 1);
by(rewrite_goals_tac[total_func_def]);
by(rewrite_goals_tac[partial_func_def]);
by(rewrite_goals_tac[rel_def]);
auto();

qed("chown_cc2");


(* chmod_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* chmod_cc1                     *)

goalw SysArchConsistency.thy [chmod_cc1_def] "chmod_cc1"; 
by(stripS_tac 1);
by(convert2hol_tac [] 1);
by(REPEAT (SOMEGOAL(rtac conjI)));

by(
REPEAT_DETERM_N 8(
(((full_expand_schema_tac chmod_def 1) THEN
(dtac DECL_D1 1))THEN
(convert2hol_tac [] 1))
));

by(full_expand_schema_tac chmod_def 1);
bd DECL_D1 1;
by(REPEAT (etac conjE 1));
by(REPEAT_DETERM_N 2(thin_tac "?a" 1));
by(rotate_tac 1 1);
by(thin_tac "?a" 1);
by(convert2hol_tac [] 1);
by(Blast_tac 1);

by(full_expand_schema_tac chmod_def 1);
bd DECL_D1 1;
by(REPEAT (etac conjE 1));
ba 1;
by(res_inst_tac[("t","dom attributes"),("s","dom files")]subst 1);
by(full_expand_schema_tac chmod_def 1);
by(full_expand_schema_tac FileSystem_def 1);
by(convert2hol_tac [] 1);
(*by(full_expand_schema_tac FileSystem_def 1);   *)
(* interesting : doesnt work here.               *)
by(full_expand_schema_tac chmod_def 1);
by(convert2hol_tac [] 1);
qed("chmod_cc1");


(* CVSServer - Zsection ----------------------------------- *)

open_schemes CVSServer.schemes;
open_schemes CVSServer.axdefs;

(* cvsperm2gid            *)

(* cvsperm2gid_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* cvsperm2gid_cc1                     *)

goalw SysArchConsistency.thy [] "cvsperm2gid_cc1_ = %N";
by(cut_facts_tac [cvsperm2gid_cc1__axdef] 1);
by(convert2hol_tac [] 1);
by(cut_facts_tac [groups_axdef] 1);
by(convert2hol_tac [] 1);
auto();
qed("cvsperm2gid_cc1");

(* cvsperm2uid_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* cvsperm2uid_cc1                     *)

goalw SysArchConsistency.thy [] "cvsperm2uid_cc1_ = %N";
by(cut_facts_tac [cvsperm2uid_cc1__axdef] 1);
by(convert2hol_tac [] 1);
by(cut_facts_tac [cvsperm2gid_axdef] 1);
by(convert2hol_tac [] 1);
by(REPEAT (etac conjE 1));
by(rotate_tac 3 1);
by(REPEAT_DETERM_N 6(thin_tac "?a" 1));
by(rewrite_goals_tac[total_inj_def]);
by(rewrite_goals_tac[total_func_def]);
auto();

qed("cvsperm2uid_cc1");


(* cvsperm2uid_cc2                     *)

goalw SysArchConsistency.thy [] "cvsperm2uid_cc2_ = %N";
by(cut_facts_tac [cvsperm2uid_cc2__axdef] 1);
by(convert2hol_tac [] 1);
by(cut_facts_tac [cvsperm2gid_axdef] 1);
by(convert2hol_tac [] 1);
by(REPEAT (etac conjE 1));
by(rotate_tac 2 1);
by(thin_tac "?a" 1);
by(rotate_tac 1 1);
by(REPEAT_DETERM_N 5(thin_tac "?a" 1));
by(rewrite_goals_tac[total_inj_def]);
by(rewrite_goals_tac[total_func_def]);
auto();

qed("cvsperm2uid_cc2");


(* cvs_rep_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* cvs_rep_cc1                     *)

goalw SysArchConsistency.thy [] "cvs_rep_cc1_ = %N";
by(cut_facts_tac [cvs_rep_cc1__axdef] 1);
by(cut_facts_tac [CVSROOT_axdef] 1);(* auto() should do then.. *)
(* [missing]                                                   *)
(* This one was locally fixed in the specification.            *)
(* So this CC has to be weakened.                              *)
(* An implication is used to state a local precondition.       *)
(*qed("cvs_rep_cc1");*)

(* cvs_rep_cc2                     *)

goalw SysArchConsistency.thy [] "cvs_rep_cc2_ = %N";
by(cut_facts_tac [cvs_rep_cc2__axdef] 1);
by(cut_facts_tac [CVSROOT_axdef] 1);
by(convert2hol_tac [] 1);
by(REPEAT (etac conjE 1));
by(rotate_tac 2 1);
by(REPEAT_DETERM_N 3(thin_tac "?a" 1));
by(rotate_tac 2 1);
by(REPEAT_DETERM_N 2(thin_tac "?a" 1));
by(rewrite_goals_tac[total_func_def]);
by(rewrite_goals_tac[partial_func_def]);
by(rewrite_goals_tac[rel_def]);
auto();
qed("cvs_rep_cc2");


(* cvs_rep_cc3                     *)

goalw SysArchConsistency.thy [] "cvs_rep_cc3_ = %N";
by(cut_facts_tac [cvs_rep_cc3__axdef] 1);
by(cut_facts_tac [CVSROOT_axdef] 1);
by(convert2hol_tac [] 1);
by(REPEAT (etac conjE 1));
by(rotate_tac 2 1);
by(REPEAT_DETERM_N 4(thin_tac "?a" 1));
by(rotate_tac 1 1);
by(REPEAT_DETERM_N 3(thin_tac "?a" 1));
by(rewrite_goals_tac[total_func_def]);
by(rewrite_goals_tac[partial_func_def]);
auto();

qed("cvs_rep_cc3");


(* cvs_rep_cc4                     *)

goalw SysArchConsistency.thy [] "cvs_rep_cc4_ = %N";
by(cut_facts_tac [cvs_rep_cc4__axdef] 1);
by(cut_facts_tac [CVSROOT_axdef] 1);
by(convert2hol_tac [] 1);
by(REPEAT (etac conjE 1));
by(rotate_tac 2 1);
by(REPEAT_DETERM_N 5(thin_tac "?a" 1));
by(rotate_tac 1 1);
by(REPEAT_DETERM_N 2(thin_tac "?a" 1));
auto();
qed("cvs_rep_cc4");



(* Cvs_FileSystem_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* Cvs_FileSystem_cc1                     *)


(* Maybe a small lemma helps out here : *)
(* traversing the first predicate of    *)
(* the FileSystem Schema seems to be too*)
(* complex...                           *)




(* <Lemmas>======================*)
(* first Lemma       ------------*)

goalw ZSeqtoList.thy [] 
"(x : seq Z & y : Z ) --> front(x %&^ %< y %>) = x ";
auto();
qed("CVS_FS_Lemma1");
qed_spec_mp("CVS_FS_Lemma1_rule");

(* Second Lemma      ------------*)

goalw ZSeqtoList.thy [] 
"(x : seq Z & y : Z)-->(x %&^ %< y %>) ~= %<%>";
auto();
by (seq_to_list_auto_tac 1);
by (seq_to_list_auto_tac 1);
auto();
qed("CVS_FS_Lemma2");
qed_spec_mp("CVS_FS_Lemma2_rule");

(* third Lemma      ------------*)

goalw ZSeqtoList.thy [] 
"(x : seq Z & a : Z & b : Z) --> (x %&^ %< a, b %>) : seq Z";
auto();
qed_spec_mp("CVS_FS_Lemma3_rule");

(* fifth Lemma     ------------*)

goalw ZSeqtoList.thy [] 
"(x : seq Z & a : Z & b : Z) --> (x %&^ %< a, b %>) = x %&^ %< a %> %&^ %< b %>";
by(seq_to_list_auto_tac 1);
by(seq_to_list_auto_tac 1);
qed_spec_mp("CVS_FS_Lemma5_rule");

(* fourth Lemma     ------------*)

goalw ZSeqtoList.thy [] 
"(x : seq Z & a : Z & b : Z) --> front(x %&^ %< a, b %>) = x %&^ %< a %>";
br impI 1;
by(res_inst_tac [("s","x %&^ %< a %> %&^ %< b %>"),("t","(x %&^ %< a, b %>)")] subst 1);
br sym 1;
br CVS_FS_Lemma5_rule 1;
ba 1;
br CVS_FS_Lemma1_rule 1;
auto();
qed_spec_mp("CVS_FS_Lemma4_rule");

(* </Lemmas>=====================*)

(*goalw SysArchConsistency.thy [Cvs_FileSystem_cc1_def] "(%A FileSystem @ (cvs_rep %&^ %< CVSROOT, cvsauth %> : dom files)) =+=> Cvs_FileSystem_cc1"; *)

goalw SysArchConsistency.thy [Cvs_FileSystem_cc1_def] "Cvs_FileSystem_cc1";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
by(full_expand_schema_tac Cvs_FileSystem_def 1);
by(convert2hol_tac [] 1);
by(full_expand_schema_tac Cvs_FileSystem_def 1);
by(convert2hol_tac [] 1);
(*by(res_inst_tac [("t","dom attributes"),("s","dom files")] subst 1);*)
(*by(full_expand_schema_tac Cvs_FileSystem_def 1);    *)
(*by(full_expand_schema_tac FileSystem_def 1);        *)
(*auto();...was a bit too early...                    *)
by(full_expand_schema_tac Cvs_FileSystem_def 1);
by(convert2hol_tac [] 1);
by(REPEAT (etac conjE 1));(*up to here: ok.*)
by(rotate_tac 1 1);
by(REPEAT_DETERM_N 4 (thin_tac "?a" 1));
by(rotate_tac 1 1);
by(REPEAT_DETERM_N 5 (thin_tac "?a" 1));
(* FileSystem (attributes, files);                            *)
(* ( cvs_rep %&^ %< CVSROOT, cvsauth %>, files) : _isfilein_  *)
(* ...are needed here.                                        *)
by(full_expand_schema_tac FileSystem_def 1);
by(convert2hol_tac [] 1);
by(REPEAT (etac conjE 1));
by(res_inst_tac [("t","dom attributes"),("s","dom files")] subst 1);
by(convert2hol_tac [] 1);
(* deleted superfluous assumptions from Cvs_FileSystem *)
by(rotate_tac 2 1);
by(thin_tac "?a" 1);
by(rotate_tac 1 1);
by(thin_tac "?a" 1);
(* gathered all facts from Cvs_FileSystem & FileSystem upto here. *)
by(cut_facts_tac [X_isdirin__axdef] 1);
by(convert2hol_tac [] 1);
by(REPEAT (etac conjE 1));
by(rotate_tac 3 1);
by(REPEAT_DETERM_N 3 (thin_tac "?a" 1));
(* added needed Axioms from the X_isdirin_axdefs ...*)
by(cut_facts_tac [CVSROOT_axdef] 1);
by(convert2hol_tac [] 1);
by(REPEAT (etac conjE 1));
by(rotate_tac 9 1);
by(REPEAT_DETERM_N 5 (thin_tac "?a" 1));
(* only carrying needed assumptions.              *)
(* maybe inserting a few milestones could help.   *)
(* auto() may be strengthened, and I will be able *)
(* to keep an overview of the proof.              *)
by(res_inst_tac [("P","(cvs_rep %&^ %< CVSROOT %> : dom files)")] mp 1);
br impI 1;
by(res_inst_tac [("P","(cvs_rep %&^ %< CVSROOT, cvsauth %> : dom files)")] mp 2);
br impI 2;
(* I will try to do the first subgoal first, *)
(* with defer_tac it is easier to read the   *)
(* subgoal...                                *)
by(defer_tac 1);
br conjunct1 3;
by(res_inst_tac [("Q","?a")] rev_iffD2 3);
br sym 4;
by(res_inst_tac [("Q","?b")] mp 4);
by(res_inst_tac [("x","cvs_rep")] spec 4);
by(res_inst_tac [("Q","?c")] mp 4);
by(res_inst_tac [("x","files")] spec 4);
by(rewrite_goals_tac[Ball_def]);
ba 4;
by(rewrite_goals_tac[FILESYS_TAB_def]);
ba 4;
ba 4;
br conjunct1 3;
by(res_inst_tac [("s", "front (cvs_rep %&^ %< CVSROOT %>)"),("t", "cvs_rep")] subst 3);
(*br mp 3;*)
br CVS_FS_Lemma1_rule 3;
br conjI 3;
ba 4;
by(rewrite_goals_tac[Path_def]);
ba 3;
(*                                                 *)
(* done with front(cvsrep^<CVSROOT>)= cvsrep.      *)
(*                                                 *)
by(res_inst_tac [("P","cvs_rep %&^ %< CVSROOT %> = %<%>"), ("Q","?a")] disjE 3);
ba 5;
br FalseE 4;
by(res_inst_tac [("P","cvs_rep %&^ %< CVSROOT %> = %<%>")] mp 4);
ba 5;
by(fold_goals_tac[not_def]);
br CVS_FS_Lemma2_rule 4;
br conjI 4;
ba 5;
ba 4;
by(res_inst_tac [("P","?a")] mp 3);
by(res_inst_tac [("x","cvs_rep %&^ %< CVSROOT %>")] spec 3);
ba 3;
ba 3;
(*                               *)
(* ... managed to get rid of the *)
(* 3rd subgoal.                  *)
br conjunct1 2;
by(res_inst_tac [("P","?a")] rev_iffD2 2);
br sym 3;
by(res_inst_tac [("P","?a")] mp 3);
by(res_inst_tac [("x","cvs_rep %&^ %< CVSROOT, cvsauth %>")] spec 3);
by(res_inst_tac [("P","?a")] mp 3);
by(res_inst_tac [("x","files")] spec 3);
by(REPEAT_DETERM_N 2 (thin_tac "?a" 3));
ba 3;
ba 3;
ba 2;
by(REPEAT_DETERM_N 6 (thin_tac "?a" 2));
(* mainly 1st subgoal left.         *)
(* maybe blow the 2nd away with an  *)
(* additional Lemma.                *)
by(res_inst_tac [("s", "front (cvs_rep %&^ %< CVSROOT, cvsauth %>)"),("t", "cvs_rep %&^ %< CVSROOT %>")] subst 1);
by(REPEAT_DETERM_N 6 (thin_tac "?a" 1));
by(thin_tac "?a" 2);
by(defer_tac 2);
(* first: match for isdirin         *)
br conjunct1 3;
by(res_inst_tac [("P","?a")] rev_iffD2 3);
br sym 4;
by(res_inst_tac [("P","?a")] mp 4);
by(res_inst_tac [("x","front (cvs_rep %&^ %< CVSROOT, cvsauth %>)")] spec 4);
by(res_inst_tac [("P","?a")] mp 4);
by(res_inst_tac [("x","files")] spec 4);
by(rotate_tac 1 4);
by(REPEAT_DETERM_N 8 (thin_tac "?a" 4));
ba 4;
ba 4;
by(REPEAT_DETERM_N 5 (thin_tac "?a" 4));
by(rotate_tac 3 4);
by(thin_tac "?a" 4);
by(defer_tac 3);
(* replaced :dom with isdirin. now:          *)
(* need to match with the first Predicate    *)
(* of the FileSystem Schema in order to      *)
(* get to                                    *)
(* cvs_rep %&^ %< CVSROOT, cvsauth %>        *)
(* from                                      *)
(* front  cvs_rep %&^ %< CVSROOT, cvsauth %> *)
br conjunct1 4;
by(res_inst_tac [("P","cvs_rep %&^ %< CVSROOT, cvsauth %> = %<%>"), ("Q","?a")] disjE 4);
ba 6;
br FalseE 5;
by(res_inst_tac [("P","cvs_rep %&^ %< CVSROOT, cvsauth %> = %<%>")] mp 5);
ba 6;
by(fold_goals_tac[not_def]);
by(REPEAT_DETERM_N 5 (thin_tac "?a" 5));
by(rotate_tac 3 5);
by(REPEAT_DETERM_N 2 (thin_tac "?a" 5));
by (seq_to_list_auto_tac 5);
by (seq_to_list_auto_tac 5);
by(res_inst_tac [("P","?a")] mp 4);
by(res_inst_tac [("x","cvs_rep %&^ %< CVSROOT, cvsauth %>")] spec 4);
by(rotate_tac 4 4);
ba 4;
ba 4;
(* now, quite trivial subgoals are left for *)
(* proving: concatenation of some Elem's    *)
(* is a Sequence and so on...               *)
br CVS_FS_Lemma4_rule 1;
br conjI 1;
br conjI 2;
by(REPEAT_DETERM_N 3 (assume_tac 1));
(*                                               *)
(* ok., now still 2 subgoals left at Level 123.  *)
(*                                               *)
by(res_inst_tac [("s","cvs_rep %&^ %< CVSROOT %>"),("t","front (cvs_rep %&^ %< CVSROOT, cvsauth %>)")] subst 2);
br sym 2;
br CVS_FS_Lemma4_rule 2;
br conjI 2;
br conjI 3;
ba 3;
ba 2;
ba 2;
auto();
(* QED *)
qed("Cvs_FileSystem_cc1");



(* Cvs_FileSystem_cc2                     *)

open_schemes Basics.axdefs;

goalw SysArchConsistency.thy [Cvs_FileSystem_cc2_def] "Cvs_FileSystem_cc2";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
by(full_expand_schema_tac Cvs_FileSystem_def 1);
by(convert2hol_tac [] 1);
by(thin_tac "?a" 1);
by(cut_facts_tac[cvs_admin_axdef] 1);
by(convert2hol_tac [] 1);
be conjE 1;
by(rotate_tac 1 1);
by(thin_tac "?a" 1);
by(cut_facts_tac[cvsperm2gid_axdef] 1);
by(convert2hol_tac [] 1);
be conjE 1;
by(rotate_tac 2 1);
by(thin_tac "?a" 1);
by(rewrite_goals_tac[total_inj_def]);
by(rewrite_goals_tac[total_func_def]);
auto();
qed("Cvs_FileSystem_cc2");

(* Cvs_FileSystem_cc3                     *)


goalw SysArchConsistency.thy [Cvs_FileSystem_cc3_def] "Cvs_FileSystem_cc3";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
by(full_expand_schema_tac Cvs_FileSystem_def 1);
by(convert2hol_tac [] 1);
by(thin_tac "?a" 1);
by(cut_facts_tac[cvsperm2gid_axdef] 1);
by(convert2hol_tac [] 1);
be conjE 1;be conjE 1;
by(thin_tac "?a" 1);
by(rotate_tac 1 1);
by(thin_tac "?a" 1);
by(cut_facts_tac[cvs_admin_axdef] 1);
by(convert2hol_tac [] 1);
be conjE 1;be conjE 1;
by(rotate_tac 1 1);
by(thin_tac "?a" 1);
by(rotate_tac 1 1);
by(thin_tac "?a" 1);
by(rewrite_goals_tac[total_inj_def]);
by(rewrite_goals_tac[total_func_def]);
auto();
qed("Cvs_FileSystem_cc3");

(* Cvs_FileSystem_cc4                     *)

goalw SysArchConsistency.thy [Cvs_FileSystem_cc4_def] "Cvs_FileSystem_cc4";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
by(full_expand_schema_tac Cvs_FileSystem_def 1);
by(convert2hol_tac [] 1);
by(etac conjE 1);
by(rotate_tac 1 1);
by(thin_tac "?a" 1);
by(full_expand_schema_tac FileSystem_def 1);
by(convert2hol_tac [] 1);
qed("Cvs_FileSystem_cc4");


(* Cvs_FileSystem_cc5                     *)

goalw SysArchConsistency.thy [Cvs_FileSystem_cc5_def] "Cvs_FileSystem_cc5";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
by(full_expand_schema_tac Cvs_FileSystem_def 1);
by(convert2hol_tac [] 1);
by(thin_tac "?a" 1);
by(cut_facts_tac[groups_axdef] 1);
by(convert2hol_tac [] 1);
be conjE 1;
by(thin_tac "?a" 1);
by(rewrite_goals_tac[total_func_def]);
auto();
qed("Cvs_FileSystem_cc5");



(* get_auth_tab_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* get_auth_tab_cc1                     *)


goalw SysArchConsistency.thy [] "get_auth_tab_cc1_ = %N";
by(cut_facts_tac [get_auth_tab_cc1__axdef] 1);
by(convert2hol_tac [] 1);
auto();
qed("get_auth_tab_cc1");

(* get_auth_tab_cc2                     *)

goalw SysArchConsistency.thy [] "get_auth_tab_cc2_ = %N";
(*by(cut_facts_tac [get_auth_tab_cc2__axdef] 1);*)
(*by(convert2hol_tac [] 1);*)

(* [missing]                                                   *)
(* I am not sure how to treat this one. The function           *)
(* application occurs within a Collect Part of a Mu-Op...      *)
(* The application may not be defined as FILESYS_TAB is a      *)
(* partial application.                                        *)
(*                                                             *)
(*qed("get_auth_tab_cc2");*)

(* get_auth_tab_cc3                     *)

goalw SysArchConsistency.thy [] "get_auth_tab_cc3_ = %N";
(*by(cut_facts_tac [get_auth_tab_cc3__axdef] 1);*)
(*by(convert2hol_tac [] 1);*)

(* [missing]                                                   *)
(* This one is locally fixed in the specification.             *)
(* So this CC has to be weakened.                              *)
(* With in the Mu-Operator, the function application of        *)
(* auth_of is secured.                                         *)
(* qed("get_auth_tab_cc3"); *)


(* Q_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* Q_cc1                     *)


goalw SysArchConsistency.thy [] "Q_cc1_ = %N";
by(cut_facts_tac [Q_cc1__axdef] 1);
by(convert2hol_tac [] 1);
by(cut_facts_tac [Q_axdef] 1);
by(convert2hol_tac [] 1);
by(rewrite_goals_tac[total_func_def]);
by(rewrite_goals_tac[partial_func_def]);
auto();
qed("Q_cc1");

(* Q_cc2                     *)

goalw SysArchConsistency.thy [] "Q_cc2_ = %N";
by(cut_facts_tac [Q_cc2__axdef] 1);
by(convert2hol_tac [] 1);
by(cut_facts_tac [Q_axdef] 1);
by(convert2hol_tac [] 1);
by(rewrite_goals_tac[total_func_def]);
by(rewrite_goals_tac[Ball_def]);
by(REPEAT (etac conjE 1));
by(rotate_tac 3 1);
by(thin_tac "?a" 1);
auto();
by(rewrite_goals_tac[partial_func_def]);
by(rewrite_goals_tac[rel_def]);
auto();
qed("Q_cc2");

(* Q_cc3                     *)

goalw SysArchConsistency.thy [] "Q_cc3_ = %N";
(*by(cut_facts_tac [Q_cc3__axdef] 1);*)
(*by(convert2hol_tac [] 1);*)
(*by(cut_facts_tac [Q_axdef] 1);*)
(*by(convert2hol_tac [] 1);*)


(* [missing]                                                   *)
(* This one is locally fixed in the specification.             *)
(* So this CC has to be weakened.                              *)
(* With in the Collect - Statement of a Set, this condition is *)
(* added as a conjunct to the predicate.                       *)
(*qed("Q_cc3");*)


(* cvs_co_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* cvs_co_cc1                     *)


goalw SysArchConsistency.thy [cvs_co_cc1_def] "cvs_co_cc1";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
by(full_expand_schema_tac cvs_co_def 1);
by(convert2hol_tac [] 1);
auto();
by(cut_facts_tac [Q_axdef] 1);
by(convert2hol_tac [] 1);
by(rewrite_goals_tac[total_func_def]);
by(rewrite_goals_tac[partial_func_def]);
auto();
qed("cvs_co_cc1");


(* cvs_co_cc2                     *)

goalw thy [total_func_def] " !!f. f : A ---> B ==> f : A -|-> B";
auto();
qed "total_func_implies_Pfun";



goalw SysArchConsistency.thy [cvs_co_cc2_def] "cvs_co_cc2";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
by(full_expand_schema_tac cvs_co_def 1);
by(convert2hol_tac [] 1);
br conjI 1;
by(convert2hol_tac [] 1);
by(Blast_tac 1);
by(res_inst_tac [("P","Q %^ (attributes, files, passwd, role, wcs_attributes) : Path ---> %P Path")] mp 1);
by(rewrite_goals_tac[Path_def]);
auto();

br Rel_Apply_in_Partial_Ran2 1;
br total_func_implies_Pfun 1;
(* This was the Lemma from above. *)
by(cut_facts_tac [Q_axdef] 1);
bd DECL_D1 1;
by(rewrite_goals_tac[Path_def]);
ba 1;
by(res_inst_tac [("t","dom Q"),("s","Collect Cvs_FileSystem")] subst 1);
by(REPEAT (thin_tac "?a" 1));
by(cut_facts_tac [Q_axdef] 1);
bd DECL_D1 1;
by(rewrite_goals_tac[total_func_def]);
by(rewrite_goals_tac[Path_def]);
by(convert2hol_tac [] 1);
by(convert2hol_tac [] 1);
qed("cvs_co_cc2");


(* cvs_update              *)


(* cvs_update_cc1                     *)

goalw SysArchConsistency.thy [cvs_update_cc1_def] "cvs_update_cc1";
by(stripS_tac 1);
by(convert2hol_tac [] 1);

by(REPEAT_DETERM_N 9(
((rtac conjI 1)THEN((full_expand_schema_tac cvs_update_def 1)THEN(dtac DECL_D1 1)))THEN(convert2hol_tac [] 1)
));
by(cut_facts_tac [Q_axdef] 1);
bd DECL_D1 1;
by(full_expand_schema_tac cvs_update_def 1);

by(res_inst_tac [("t","dom Q"),("s","Collect Cvs_FileSystem")] subst 1);
by(thin_tac "?a" 1);
by(rewrite_goals_tac[total_func_def]);
by(rewrite_goals_tac[partial_func_def]);
by(convert2hol_tac [] 1);
bd DECL_D1 1;
by(thin_tac "?a" 1);
be conjE 1;
by(rotate_tac 1 1);
by(thin_tac "?a" 1);
by(convert2hol_tac [] 1);

qed("cvs_update_cc1");



(* cvs_update_cc2                     *)


goalw SysArchConsistency.thy [cvs_update_cc2_def] "cvs_update_cc2";
by(stripS_tac 1);
by(convert2hol_tac [] 1);

by(REPEAT_DETERM_N 9(
((rtac conjI 1)THEN((full_expand_schema_tac cvs_update_def 1)THEN(dtac DECL_D1 1)))THEN(convert2hol_tac [] 1)
));

by(res_inst_tac [("P","Q %^ (attributes, files, passwd, role, wcs_attributes) : Path ---> %P Path")] mp 1);
by(rewrite_goals_tac[Path_def]);
auto();

by(cut_facts_tac [Q_axdef] 1);
bd DECL_D1 1;
by(full_expand_schema_tac cvs_update_def 1);
by(rewrite_goals_tac[Path_def]);

br Rel_Apply_in_Partial_Ran2 1;
br total_func_implies_Pfun 1;
by(convert2hol_tac [] 1);
by(res_inst_tac [("t","dom Q"),("s","Collect Cvs_FileSystem")] subst 1);

by(REPEAT (thin_tac "?a" 1));
by(cut_facts_tac [Q_axdef] 1);
bd DECL_D1 1;
by(rewrite_goals_tac[total_func_def]);
by(rewrite_goals_tac[Path_def]);
by(convert2hol_tac [] 1);
by(convert2hol_tac [] 1);
qed("cvs_update_cc2");




(*========================*)
(*                        *)
(* up to here: done.      *)
(* Rest will come soon.   *)
(*                        *)
(*========================*)


(* cvs_update_cc3                     *)

(* careful: goal not anymore up to date.         *)
(* cc's have to be reviewed for being up to date *)
(* and fitting to the spec.                      *)
goalw SysArchConsistency.thy [cvs_update_cc3_def] "cvs_update_cc3";
by(stripS_tac 1);
by(convert2hol_tac [] 1);


by(rtac conjI 1);
by(full_expand_schema_tac cvs_update_def 1);
by(dtac DECL_D1 1);
by(convert2hol_tac [] 1);

by(rtac conjI 1);
by(full_expand_schema_tac cvs_update_def 1);
by(dtac DECL_D1 1);
by(convert2hol_tac [] 1);

by(rtac conjI 1);
by(full_expand_schema_tac cvs_update_def 1);
by(dtac DECL_D1 1);
by(convert2hol_tac [] 1);

by(rtac conjI 1);
by(full_expand_schema_tac cvs_update_def 1);
by(dtac DECL_D1 1);
by(convert2hol_tac [] 1);

by(rtac conjI 1);
by(full_expand_schema_tac cvs_update_def 1);
by(dtac DECL_D1 1);
by(convert2hol_tac [] 1);

by(rtac conjI 1);
by(full_expand_schema_tac cvs_update_def 1);
by(dtac DECL_D1 1);
by(convert2hol_tac [] 1);

by(rtac conjI 1);
by(full_expand_schema_tac cvs_update_def 1);
by(dtac DECL_D1 1);
by(convert2hol_tac [] 1);

by(rtac conjI 1);
by(full_expand_schema_tac cvs_update_def 1);
by(dtac DECL_D1 1);
by(convert2hol_tac [] 1);

by(rtac conjI 1);
by(full_expand_schema_tac cvs_update_def 1);
by(dtac DECL_D1 1);
by(convert2hol_tac [] 1);




cvs_update_cc3_def;
qed("cvs_update_cc3");

(* cvs_ci                 *)

cvs_ci_cc1_def;
qed("cvs_ci_cc1");

cvs_ci_cc2_def;
qed("cvs_ci_cc2");

cvs_ci_cc3_def;
qed("cvs_ci_cc3");

cvs_ci_cc4_def;
qed("cvs_ci_cc4");

cvs_ci_cc5_def;
qed("cvs_ci_cc5");

cvs_ci_cc6_def;
qed("cvs_ci_cc6");

cvs_ci_cc7_def;
qed("cvs_ci_cc7");

cvs_ci_cc8_def;
qed("cvs_ci_cc8");
