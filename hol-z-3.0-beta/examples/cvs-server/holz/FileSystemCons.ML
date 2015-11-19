(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * FileSystemsCons.ML --- 
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
(* $Id: FileSystemCons.ML 6746 2007-08-03 07:25:55Z brucker $ *)

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



(* is_in ~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* is_in_cc1*)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* on_the_fly *)


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
(*@proofstatistic:endProof*)


(* has_attrib_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* has_attrib_cc1         *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* groups        *)
goalw SysArchConsistency.thy [] "has_attrib_cc1_ = %N";
by(cut_facts_tac [groups_axdef, has_attrib_cc1__axdef] 1);
by (convert2hol_tac [total_func_def,partial_func_def] 1);
auto();
qed("has_attrib_cc1");
(*@proofstatistic:endProof*)

(* has_attrib_cc2         *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* on the fly        *)
goalw SysArchConsistency.thy [] "has_attrib_cc2_ = %N";
by(cut_facts_tac [has_attrib_cc2__axdef] 1);
auto();
qed("has_attrib_cc2");
(*@proofstatistic:endProof*)


(* has_w_access_cc1 ~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* front         *)

goalw SysArchConsistency.thy [] "has_w_access_cc1_ = %N";

by(cut_facts_tac [has_w_access_cc1__axdef] 1);
by (convert2hol_tac [] 1);
auto();
by (rewrite_goals_tac[frontseq_def]);
auto();
qed("has_w_access_cc1");
(*@proofstatistic:endProof*)

(*=====================================*)
(* new version of mkdir_cc1 - Proof    *)
(*=====================================*)

(* mkdir_cc1              *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* FILEATTR_TAB  *)

goalw SysArchConsistency.thy [mkdir_cc1_def] "mkdir_cc1";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
(*Get rid of trivial subgoals.*)
by(convert2hol_tac [mkdir_def] 1);
by(REPEAT_DETERM_N 9((full_expand_schema_tac mkdir_def 2)THEN(convert2hol_tac [] 2)));

by(full_expand_schema_tac mkdir_def 1);
bd DECL_D1 1;
by(convert2hol_tac [] 1);

(* Now, the subgoal which is left to us is:     *)
(* ... ==> wdir : dom attributes                *)
(* Arguments are : dom files = dom attributtes  *)
(* and wdir isdirin files                       *)
by(res_inst_tac [("s","dom files"),("t","dom attributes")] subst 1);
by(full_expand_schema_tac FileSystem_def 1);
by(convert2hol_tac [mkdir_def, FileSystem_def] 1);
(* lemma for decreasing proofsize.*)
br in_dom_if_isdirin 1;

(* get rid of the set constraints: *)
by(convert2hol_tac [mkdir_def, FileSystem_def, FILESYS_TAB_def] 1);
by(convert2hol_tac [mkdir_def, ProcessState_def] 1);
by(convert2hol_tac [mkdir_def] 1);
auto();
qed("mkdir_cc1");
(*@proofstatistic:endProof*)

(*=====================================*)
(* old version of mkdir_cc1 - Proof    *)
(*=====================================*)

(* mkdir_cc1              *)
(* FILEATTR_TAB  *)
goalw SysArchConsistency.thy [mkdir_cc1_def] "mkdir_cc1";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
(*Get rid of trivial subgoals.*)
by(convert2hol_tac [mkdir_def] 1);
by(REPEAT_DETERM_N 9((full_expand_schema_tac mkdir_def 2)THEN(convert2hol_tac [] 2)));

by(full_expand_schema_tac mkdir_def 1);
bd DECL_D1 1;
by(convert2hol_tac [] 1);

(* Now, the subgoal which is left to us is:     *)
(* ... ==> wdir : dom attributes                *)
(* Arguments are : dom files = dom attributtes  *)
(* and wdir isdirin files                       *)
by(full_expand_schema_tac mkdir_def 1);       
by(convert2hol_tac [] 1);                     
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
qed("mkdir_cc1");
(*                   *)
(* end of old proof  *)
(*                   *)
(* Note, usage of lemmas decreases LOC          *)
(* on approximately one third of original proof *)
(* size.                                        *)



(* mkfile_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)


(* mkfile_cc1               *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* FILEATTR_TAB  *)

goalw SysArchConsistency.thy [mkfile_cc1_def] "mkfile_cc1";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
(*Get rid of trivial subgoals.*)
by(convert2hol_tac [mkfile_def] 1);
by(REPEAT_DETERM_N 9((full_expand_schema_tac mkfile_def 2)THEN(convert2hol_tac [] 2)));

by(full_expand_schema_tac mkfile_def 1);
bd DECL_D1 1;
by(convert2hol_tac [] 1);
by(convert2hol_tac [mkfile_def] 1);
(* Now, the subgoal which is left to us is:     *)
(* ... ==> wdir : dom attributes                *)
(* Arguments are : dom files = dom attributtes  *)
(* and wdir isdirin files                       *)
by(res_inst_tac [("s","dom files"),("t","dom attributes")] subst 1);
by(full_expand_schema_tac FileSystem_def 1);
by(convert2hol_tac [mkfile_def, FileSystem_def] 1);
(* lemma for decreasing proofsize.*)
br in_dom_if_isdirin 1;

(* get rid of the set constraints: *)
by(convert2hol_tac [mkfile_def, FileSystem_def, FILESYS_TAB_def] 1);
by(convert2hol_tac [mkfile_def, ProcessState_def] 1);
by(convert2hol_tac [mkfile_def] 1);
auto();
qed("mkfile_cc1");
(*@proofstatistic:endProof*)



(* access_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)


(* access_cc1               *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* FILESYS_TAB  *)
goalw SysArchConsistency.thy [access_cc1_def] "access_cc1";

by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
(*Get rid of trivial subgoals.*)
by(convert2hol_tac [access_def] 1);
by(REPEAT_DETERM_N 9((full_expand_schema_tac access_def 2)THEN(convert2hol_tac [] 2)));

by(full_expand_schema_tac access_def 1);
bd DECL_D1 1;
by(convert2hol_tac [] 1);

by(REPEAT_DETERM_N 4(convert2hol_tac [access_def, ProcessState_def] 1));

by(convert2hol_tac [access_def] 1);

br Rel_Apply_in_Partial_Ran2 1;
by(convert2hol_tac [FileSystem_def, FILESYS_TAB_def] 1);

be conjE 1;
by(res_inst_tac [("t","files'"), ("s","files")] subst 1);
by(convert2hol_tac [] 1);
ba 1;

(* removing the duplicate goals...*)

by(convert2hol_tac [access_def, ProcessState_def] 2);
by(distinct_subgoals_tac);
(* ... tidying the proof-state! *)
(* also see ref.pdf p. 35       *)

by(res_inst_tac [("t","files'"), ("s","files")] subst 1);
by(res_inst_tac [("t","wdir'"), ("s","wdir")] subst 2);
by( REPEAT_DETERM_N 2 (convert2hol_tac [] 1));

(* ... still need to show:                *)
(* ... ==>  wdir %&^ %<u_63%> : dom files *)

br in_dom_if_isfilein 1;

by(convert2hol_tac [FileSystem_def, FILESYS_TAB_def] 1);
by(convert2hol_tac [ProcessState_def, Path_def] 1);
auto();
qed("access_cc1");
(*@proofstatistic:endProof*)



(* mv_file_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)


(* mv_file_cc1               *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* FILESYS_TAB  *)
goalw SysArchConsistency.thy [mv_file_cc1_def] "mv_file_cc1";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();
(*Get rid of trivial subgoals.*)
by((full_expand_schema_tac mv_file_def 1)THEN (convert2hol_tac [mv_file_def] 1));

by(REPEAT_DETERM_N 8 ((full_expand_schema_tac mv_file_def 2)THEN (convert2hol_tac [mv_file_def] 2)));
by(full_expand_schema_tac mv_file_def 1);
(* need only constraint-part of schema. *)
bd DECL_D1 1;
by(convert2hol_tac [] 1);
(* use lemma from FileSystem.ML *)
br in_dom_if_isfilein 1;
(* get rid of set constraints   *)
by(convert2hol_tac [mv_file_def, FileSystem_def, FILESYS_TAB_def] 1);
by(full_expand_schema_tac mv_file_def 1);
bd DECL_D1 1;
br cat_path 1;

by(convert2hol_tac [ProcessState_def, Path_def] 1);
br elem_path 1;
by(convert2hol_tac [] 1);
by(convert2hol_tac [mv_file_def] 1);
auto();
qed"mv_file_cc1";
(*@proofstatistic:endProof*)


(* mv_file_cc2              *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* FILEATTR_TAB  *)
goalw SysArchConsistency.thy [mv_file_cc2_def] "mv_file_cc2";
by(stripS_tac 1);

by(res_inst_tac [("t","dom attributes"), ("s","dom files")] subst 1);
by(convert2hol_tac [mv_file_def, FileSystem_def] 1);
(* now try reuse of mv_file_cc1 *)
br mp 1;
br mv_file_cc1 2;
by(convert2hol_tac [mv_file_cc1_def] 1);
auto();
qed"mv_file_cc2";
(*@proofstatistic:endProof*)



(* mv_dir_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)


(* mv_dir_cc1              *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* FILESYS_TAB  / on the fly *)
goalw SysArchConsistency.thy [mv_dir_cc1_def] "mv_dir_cc1";
by(stripS_tac 1);
auto();
by(convert2hol_tac [mv_dir_def] 2);
by(full_expand_schema_tac mv_dir_def 1);
bd DECL_D1 1;
by(convert2hol_tac [] 1);
(* lemma from FileSystem.ML *)
br in_dom_if_isin 1;
ba 3;
by(convert2hol_tac [mv_dir_def, FileSystem_def, FILESYS_TAB_def] 1);
(* Get rid of set constraints *)
br cat_path 1;
br cat_path 1;
by(convert2hol_tac [mv_dir_def, ProcessState_def] 1);
ba 2;
br elem_path 1;
by(convert2hol_tac [mv_dir_def] 1);
qed"mv_dir_cc1";
(*@proofstatistic:endProof*)


(* mv_dir_cc2              *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* FILEATTR_TAB  *)
goalw SysArchConsistency.thy [mv_dir_cc2_def] "mv_dir_cc2";
by(stripS_tac 1);

by(res_inst_tac [("t","dom attributes"), ("s","dom files")] subst 1);
by(convert2hol_tac [mv_dir_def, FileSystem_def] 1);
(* now try reuse of mv_dir_cc1 *)
br mp 1;
br mv_dir_cc1 2;
by(convert2hol_tac [mv_dir_cc1_def] 1);
auto();
qed"mv_dir_cc2";
(*@proofstatistic:endProof*)



(* rename_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)


(* rename_dir_cc1              *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* FILESYS_TAB  / on the fly *)
goalw SysArchConsistency.thy [rename_dir_cc1_def] "rename_dir_cc1";
by(stripS_tac 1);
auto();
by(convert2hol_tac [rename_dir_def] 2);
by(full_expand_schema_tac rename_dir_def 1);
bd DECL_D1 1;
by(convert2hol_tac [] 1);
(* lemma from FileSystem.ML *)
br in_dom_if_isin 1;
ba 3;
by(convert2hol_tac [rename_dir_def, FileSystem_def, FILESYS_TAB_def] 1);
(* Get rid of set constraints *)
br cat_path 1;
br cat_path 1;
by(convert2hol_tac [rename_dir_def, ProcessState_def] 1);
ba 2;
br elem_path 1;
by(convert2hol_tac [rename_dir_def] 1);

qed"rename_dir_cc1";
(*@proofstatistic:endProof*)



(* rename_dir_cc2              *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* FILEATTR_TAB  *)
goalw SysArchConsistency.thy [rename_dir_cc2_def] "rename_dir_cc2";
by(stripS_tac 1);

by(res_inst_tac [("t","dom attributes"), ("s","dom files")] subst 1);
by(convert2hol_tac [rename_dir_def, FileSystem_def] 1);
(* now try reuse of rename_dir_cc1 *)
br mp 1;
br rename_dir_cc1 2;
by(convert2hol_tac [rename_dir_cc1_def] 1);
auto();
qed"rename_dir_cc2";
(*@proofstatistic:endProof*)


(* chown_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* chown_cc1                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* FILEATTR_TAB  *)
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
(*@proofstatistic:endProof*)


(* chown_cc2                     *)

(*                                              *)
(*                                              *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* groups        *)
goalw SysArchConsistency.thy [chown_cc2_def] "chown_cc2"; 
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [chown_def] 1);
auto();
by(cut_facts_tac [groups_axdef] 1);
by(res_inst_tac [("P","uid : Uid")] mp 1);
by(convert2hol_tac [ProcessState_def] 2);
by(convert2hol_tac [total_func_def] 1);
qed("chown_cc2");
(*@proofstatistic:endProof*)



(* chmod_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* chmod_cc1                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* FILEATTR_TAB  *)

goalw SysArchConsistency.thy [chmod_cc1_def] "chmod_cc1"; 
by(stripS_tac 1);
by(res_inst_tac [("t","dom attributes"),("s","dom files")] subst 1);
by(convert2hol_tac [chmod_def, FileSystem_def] 1);

by(convert2hol_tac [chmod_def] 1);
auto();
qed("chmod_cc1");

