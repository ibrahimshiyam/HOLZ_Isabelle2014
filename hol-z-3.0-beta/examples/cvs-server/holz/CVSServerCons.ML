(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * CVSServerCons.ML  --- 
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
(* $Id: CVSServerCons.ML 6746 2007-08-03 07:25:55Z brucker $ *)


(* cvsperm2gid            *)

(* cvsperm2gid_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* cvsperm2gid_cc1                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* groups        *)
goalw SysArchConsistency.thy [] "cvsperm2gid_cc1_ = %N";
by(cut_facts_tac [cvsperm2gid_cc1__axdef] 1);
by(convert2hol_tac [] 1);
by(cut_facts_tac [groups_axdef] 1);
by(convert2hol_tac [total_func_def] 1);
auto();
qed("cvsperm2gid_cc1");
(*@proofstatistic:endProof*)


(* cvsperm2uid_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* cvsperm2uid_cc1                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* cvsperm2uid   *)

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
(*@proofstatistic:endProof*)

(* cvsperm2uid_cc2                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* cvsperm2gid   *)

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
(*@proofstatistic:endProof*)


(* cvs_rep_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* cvs_rep_cc1                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* data_of       *)
goalw SysArchConsistency.thy [] "cvs_rep_cc1_ = %N";
by(cut_facts_tac [cvs_rep_cc1__axdef] 1);
auto();
by(cut_facts_tac [CVSROOT_axdef] 1);
by(convert2hol_tac [] 1);
by(REPEAT (etac conjE 1));
br tfun_dom 1;
by(convert2hol_tac [] 1);
br pfun_snd_expl 1;
ba 2;
ba 1;
qed("cvs_rep_cc1");
(*@proofstatistic:endProof*)

(* cvs_rep_cc2                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* auth_of       *)
goalw SysArchConsistency.thy [] "cvs_rep_cc2_ = %N";
by(cut_facts_tac [cvs_rep_cc2__axdef] 1);
auto();
qed("cvs_rep_cc2");
(*@proofstatistic:endProof*)


(* cvs_rep_cc3                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* auth_of       *)
goalw SysArchConsistency.thy [] "cvs_rep_cc3_ = %N";
by(cut_facts_tac [cvs_rep_cc3__axdef] 1);
by(cut_facts_tac [CVSROOT_axdef] 1);
auto();
qed("cvs_rep_cc3");
(*@proofstatistic:endProof*)


(* cvs_rep_cc4                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* data_of       *)
goalw SysArchConsistency.thy [] "cvs_rep_cc4_ = %N";
by(cut_facts_tac [cvs_rep_cc4__axdef] 1);
auto();
by(cut_facts_tac [CVSROOT_axdef] 1);

br tfun_dom 1;
ba 2;
bd DECL_D1 1;
by(REPEAT (etac conjE 1));
ba 1;
qed("cvs_rep_cc4");
(*@proofstatistic:endProof*)



(* repOf_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* repOf_cc1                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* data_of       *)
goalw SysArchConsistency.thy [] "repOf_cc1_ = %N";
by(cut_facts_tac [repOf_cc1__axdef] 1);
auto();
br tfun_dom 1;
by(cut_facts_tac [repOf_axdef] 1);
bd DECL_D1 1;
ba 1;
ba 1;
qed("repOf_cc1");
(*@proofstatistic:endProof*)


(* attributes_in_rep_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* attributes_in_rep_cc1                    *)
(*@proofstatistic:beginProof                *)
(*@proofstatistic:PartialFuncDefinednessProof *)
(* on the fly    *)
goalw SysArchConsistency.thy [] "attributes_in_rep_cc1_ = %N";
by(cut_facts_tac [attributes_in_rep_cc1__axdef] 1);
auto();by(thin_tac "?a" 1);by(thin_tac "?a" 1);

by(full_expand_schema_tac FileSystem_def 1 );
by(convert2hol_tac [] 1);
auto();
by(res_inst_tac [("s","dom ya"),("t","dom x")] subst 1);
ba 1;
br pair_rel_dom 1;ba 1;
qed"attributes_in_rep_cc1";
(*@proofstatistic:endProof*)


(* attributes_in_rep_cc2                    *)
(*@proofstatistic:beginProof                *)
(*@proofstatistic:TotalFuncDefinednessProof *)
(* groups        *)
goalw SysArchConsistency.thy [] "attributes_in_rep_cc2_ = %N";
by(cut_facts_tac [attributes_in_rep_cc2__axdef] 1);
auto();
br tfun_dom 1;
by(cut_facts_tac [groups_axdef] 1);
by(convert2hol_tac [] 1);
be conjE 1;
ba 1;
by(thin_tac "?a" 1);
by(thin_tac "?a" 1);
by(convert2hol_tac [FileSystem_def] 1);
auto();
qed"attributes_in_rep_cc2";
(*@proofstatistic:endProof*)


(* attributes_in_root_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* attributes_in_root_cc1                   *)
(*@proofstatistic:beginProof                *)
(*@proofstatistic:TotalFuncDefinednessProof *)
(* cvsperm2uid   *)
goalw SysArchConsistency.thy [] "attributes_in_root_cc1_ = %N";
by(cut_facts_tac [attributes_in_root_cc1__axdef] 1);
auto();
by(cut_facts_tac [cvsperm2gid_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1;

by(convert2hol_tac [total_inj_def] 1);
by(REPEAT (etac conjE 1));
ba 1;

by(cut_facts_tac [cvs_admin_axdef] 1);
bd DECL_D1 1;
auto();
qed"attributes_in_root_cc1";
(*@proofstatistic:endProof*)


(* attributes_in_root_cc2                   *)
(*@proofstatistic:beginProof                *)
(*@proofstatistic:TotalFuncDefinednessProof *)
(* cvsperm2gid   *)
goalw SysArchConsistency.thy [] "attributes_in_root_cc2_ = %N";
by(cut_facts_tac [attributes_in_root_cc2__axdef] 1);
auto();
by(cut_facts_tac [cvsperm2gid_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1;

by(convert2hol_tac [total_inj_def] 1);
by(REPEAT (etac conjE 1));
ba 1;

by(cut_facts_tac [cvs_admin_axdef] 1);
bd DECL_D1 1;
auto();
qed"attributes_in_root_cc2";
(*@proofstatistic:endProof*)



(* attributes_in_root_cc3                   *)
(*@proofstatistic:beginProof                *)
(*@proofstatistic:TotalFuncDefinednessProof *)
(* cvsperm2gid   *)
goalw SysArchConsistency.thy [] "attributes_in_root_cc3_ = %N";
by(cut_facts_tac [attributes_in_root_cc3__axdef] 1);
auto();
by(cut_facts_tac [cvsperm2gid_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1;

by(convert2hol_tac [total_inj_def] 1);
by(REPEAT (etac conjE 1));
ba 1;

by(cut_facts_tac [cvs_admin_axdef] 1);
bd DECL_D1 1;
auto();
qed"attributes_in_root_cc3";
(*@proofstatistic:endProof*)

(* attributes_in_root_cc4                     *)
(*@proofstatistic:beginProof                  *)
(*@proofstatistic:PartialFuncDefinednessProof *)
(* FILESYS_TAB   *)
goalw SysArchConsistency.thy [] "attributes_in_root_cc4_ = %N";
by(cut_facts_tac [attributes_in_root_cc4__axdef] 1);
auto();
by(thin_tac "?a" 1);by(thin_tac "?a" 1);

by(full_expand_schema_tac FileSystem_def 1 );
by(convert2hol_tac [] 1);
auto();
by(res_inst_tac [("s","dom ya"),("t","dom x")] subst 1);
ba 1;
br pair_rel_dom 1;ba 1;
qed"attributes_in_root_cc4";



(* get_auth_tab_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* get_auth_tab_cc1                     *)

(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* get_auth_tab  *)
goalw SysArchConsistency.thy [] "get_auth_tab_cc1_ = %N";
by(cut_facts_tac [get_auth_tab_cc1__axdef] 1);
auto();
by(cut_facts_tac [get_auth_tab_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1;
ba 1;
ba 1;
qed("get_auth_tab_cc1");
(*@proofstatistic:endProof*)


(* get_auth_tab_cc3                     *)

(*goalw SysArchConsistency.thy [] "get_auth_tab_cc3_ = %N"; *)
(*by(cut_facts_tac [get_auth_tab_cc3__axdef] 1); *)
(*by(cut_facts_tac [get_auth_tab_axdef] 1); *)
(* *)
(*by(thin_tac "?a" 1);by(thin_tac "?a" 1); *)

(* a lemma similar to set_ext *)
(* could be useful here?      *)



(* rep_access_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* rep_access_cc1                  *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* rep_access    *)
goalw SysArchConsistency.thy [] "rep_access_cc1_ = %N";
by(cut_facts_tac [rep_access_cc1__axdef] 1);
auto();
br tfun_dom 1;
by(cut_facts_tac [rep_access_axdef] 1);
bd DECL_D1 1;
ba 1; 
ba 1;
qed "rep_access_cc1";
(*@proofstatistic:endProof*)


(* rep_access_cc2                  *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* rep_access    *)
goalw SysArchConsistency.thy [] "rep_access_cc2_ = %N";
by(cut_facts_tac [rep_access_cc2__axdef] 1);
auto();
br tfun_dom 1;
by(cut_facts_tac [rep_access_axdef] 1);
bd DECL_D1 1;
br tfun_snd 1;
ba 1;
ba 1;
ba 1;
qed "rep_access_cc2";
(*@proofstatistic:endProof*)

(* rep_access_cc3                  *)
(*@proofstatistic:beginProof       *)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* on-the-fly    *)
goalw SysArchConsistency.thy [] "rep_access_cc3_ = %N";
by(cut_facts_tac [rep_access_cc3__axdef] 1);
auto();
qed "rep_access_cc3";
(* local fix *)


(* rep_access_cc4                  *)
(*@proofstatistic:beginProof       *)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* get_auth_tab  *)
goalw SysArchConsistency.thy [] "rep_access_cc4_ = %N";
by(cut_facts_tac [rep_access_cc4__axdef] 1);
auto();
by(cut_facts_tac [get_auth_tab_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1;
ba 1; ba 1;
qed "rep_access_cc4";
(*@proofstatistic:endProof*)


(* rep_access_cc5                  *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* cvsperm2uid   *)
goalw SysArchConsistency.thy [] "rep_access_cc5_ = %N";
by(cut_facts_tac [rep_access_cc5__axdef] 1);
auto();
by(cut_facts_tac [cvsperm2gid_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1; 
by(convert2hol_tac [total_inj_def] 1);
auto();
qed "rep_access_cc5";
(*@proofstatistic:endProof*)




(* choose_cc1                  *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* choose        *)
goalw SysArchConsistency.thy [] "choose_cc1_ = %N";
by(cut_facts_tac [choose_cc1__axdef] 1);
auto();
by(cut_facts_tac [choose_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1; 
ba 1;
auto();
qed "choose_cc1";
(*@proofstatistic:endProof*)



(* choose_cc3                  *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* choose        *)
goalw SysArchConsistency.thy [] "choose_cc3_ = %N";
by(cut_facts_tac [choose_cc3__axdef] 1);
auto();
by(cut_facts_tac [cvsperm2gid_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1; 
by(convert2hol_tac [total_inj_def] 1);
auto();
qed "choose_cc3";
(*@proofstatistic:endProof*)



(* choose_cc4                  *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* get_auth_tab  *)
goalw SysArchConsistency.thy [] "choose_cc4_ = %N";
by(cut_facts_tac [choose_cc4__axdef] 1);
auto();
by(cut_facts_tac [get_auth_tab_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1;
ba 1; 
by(convert2hol_tac [Cvs_FileSystem_def,FileSystem_def] 1);
auto();
qed "choose_cc4";
(*@proofstatistic:endProof*)


(* choose_cc5                  *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* on the fly  *)
goalw SysArchConsistency.thy [] "choose_cc5_ = %N";
by(cut_facts_tac [choose_cc5__axdef] 1);
auto();
qed "choose_cc5";
(*@proofstatistic:endProof*)



(* Cvs_FileSystem_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* Cvs_FileSystem_cc1                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* FILEATTR_TAB *)

goalw SysArchConsistency.thy [Cvs_FileSystem_cc1_def] "Cvs_FileSystem_cc1";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();

by(REPEAT_DETERM_N 3(convert2hol_tac [Cvs_FileSystem_def] 1));

br (stripS domAttr_domFiles) 1;
br conjI 1;
by(full_expand_schema_tac Cvs_FileSystem_def 1);
bd DECL_D1 1;
be conjE 1;
ba 1;
(* FileSystem_lemma with this proof *)
(* as a main purpose                *)
br (stripS FSminus2Path) 1;
br conjI 1;
by(full_expand_schema_tac Cvs_FileSystem_def 2);
(*bd DECL_D2 2;*)
br in_dom_if_isfilein 2;
bd DECL_D2 4;
be conjE 4;
be conjE 4;
ba 4;
(* Now only to show trivial *)
(* set constraints.         *)
by(convert2hol_tac [FileSystem_def, FILESYS_TAB_def] 2);
auto();
by(convert2hol_tac [Cvs_FileSystem_def] 1);
be conjE 1;
ba 1;(**)
br cat_path 1;

by(res_inst_tac [("t","%< ?X, ?Y %>")] subst 2);
br sym 2;
br twoElemPath 2;
by(rewrite_goals_tac[Path_def]);
br catName 3;
auto();
qed"Cvs_FileSystem_cc1";
(*@proofstatistic:endProof*)




(* Cvs_FileSystem_cc2                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* cvsperm2uid  *)

goalw SysArchConsistency.thy [Cvs_FileSystem_cc2_def] "Cvs_FileSystem_cc2";
by(stripS_tac 1);
by(convert2hol_tac [Cvs_FileSystem_def] 1);
by(cut_facts_tac [cvsperm2gid_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1; 
by(convert2hol_tac [total_inj_def] 1);
auto();

qed"Cvs_FileSystem_cc2";
(*@proofstatistic:endProof*)


(* Cvs_FileSystem_cc3                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* cvsperm2gid  *)

goalw SysArchConsistency.thy [Cvs_FileSystem_cc3_def] "Cvs_FileSystem_cc3";
by(stripS_tac 1);
by(convert2hol_tac [Cvs_FileSystem_def] 1);
by(cut_facts_tac [cvsperm2gid_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1; 
by(convert2hol_tac [total_inj_def] 1);
auto();

qed"Cvs_FileSystem_cc3";
(*@proofstatistic:endProof*)



(* Cvs_FileSystem_cc4                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* cvsperm2gid  *)

goalw SysArchConsistency.thy [Cvs_FileSystem_cc4_def] "Cvs_FileSystem_cc4";
by(stripS_tac 1);
by(convert2hol_tac [] 1);
auto();

by(REPEAT_DETERM_N 3(convert2hol_tac [Cvs_FileSystem_def] 1));

br (stripS domAttr_domFiles) 1;
br conjI 1;
by(full_expand_schema_tac Cvs_FileSystem_def 1);
bd DECL_D1 1;
be conjE 1;
ba 1; 
(* still show :                        *)
(* cvs_rep %&^ %<CVSROOT%> : dom files *)

br (stripS prefix_closedness) 1;
auto();
by(convert2hol_tac [Cvs_FileSystem_def] 1);
be conjE 1;
ba 1;
by(rewrite_goals_tac [Path_def]);
br catPathName 1;

by(res_inst_tac [("t","cvs_rep %&^ ?A %&^ ?B"),("s","cvs_rep %&^ (?A %&^ ?B)")] subst 2);
by(asm_simp_tac (simpset() addsimps [concatseq_assoc]) 2);

by(res_inst_tac [("t","%< CVSROOT %> %&^ %< ?X %>"), ("s","%< CVSROOT, ?X %>")] subst 2);
br twoElemPath 2;

br in_dom_if_isfilein 3;
by(convert2hol_tac [Cvs_FileSystem_def] 5);
by(REPEAT (etac conjE 5));
ba 5;
(* Now only to show trivial *)
(* set constraints.         *)
by(convert2hol_tac [Cvs_FileSystem_def, FileSystem_def, FILESYS_TAB_def] 3);
br cat_path 3;
by(rewrite_goals_tac[Path_def]);
br double_is_path 4;
auto();
qed"Cvs_FileSystem_cc4";
(*@proofstatistic:endProof*)





(* Cvs_FileSystem_cc5                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* cvsperm2gid  *)

goalw SysArchConsistency.thy [Cvs_FileSystem_cc5_def] "Cvs_FileSystem_cc5";
by(stripS_tac 1);
by(convert2hol_tac [Cvs_FileSystem_def] 1);
by(cut_facts_tac [cvsperm2gid_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1; 
by(convert2hol_tac [total_inj_def] 1);
auto();
qed"Cvs_FileSystem_cc5";
(*@proofstatistic:endProof*)



(* cvs_login_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* cvs_login_cc1                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* get_auth_tab *)

goalw SysArchConsistency.thy [cvs_login_cc1_def] "cvs_login_cc1";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvs_login_def] 1);
auto();


by(cut_facts_tac [get_auth_tab_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1;
ba 1; 
by(convert2hol_tac [Cvs_FileSystem_def,FileSystem_def] 1);
auto();
qed"cvs_login_cc1";
(*@proofstatistic:endProof*)





(* cvs_add_normal_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* cvs_add_normal_cc1                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* wcs_attributes*)

goalw SysArchConsistency.thy [cvs_add_normal_cc1_def] "cvs_add_normal_cc1";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvs_add_normal_def] 1);
by(convert2hol_tac [cvs_add_normal_def] 2);
auto();
qed"cvs_add_normal_cc1";
(*@proofstatistic:endProof*)



(* cvs_add_normal_cc2                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* get_auth_tab~files *)

(*goalw SysArchConsistency.thy [cvs_add_normal_cc2_def] "cvs_add_normal_cc2";*)
(*by(stripS_tac 1);*)
(*br DECL_I 1;*)
(*by(convert2hol_tac [cvs_add_normal_def] 1);*)
(*auto();*)
(*by(rewrite_goals_tac [Let_def]);*)
(*qed"cvs_add_normal_cc2";*)
(*@proofstatistic:endProof*)


(* cvs_add_normal_cc3                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* get_auth_tab *)

goalw SysArchConsistency.thy [cvs_add_normal_cc3_def] "cvs_add_normal_cc3";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvs_add_normal_def] 1);
auto();

by(cut_facts_tac [get_auth_tab_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1;
ba 1; 
by(convert2hol_tac [Cvs_FileSystem_def,FileSystem_def] 1);
auto();
qed"cvs_add_normal_cc3";
(*@proofstatistic:endProof*)



(* cvs_add_normal_cc5                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:TotalFuncDefinednessProof*)
(* cvsperm2uid *)

goalw SysArchConsistency.thy [cvs_add_normal_cc5_def] "cvs_add_normal_cc5";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvs_add_normal_def] 1);
auto();
by(rewrite_goals_tac [Let_def]);

by(cut_facts_tac [cvsperm2gid_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1; 
by(convert2hol_tac [total_inj_def] 1);
auto();
qed"cvs_add_normal_cc5";
(*@proofstatistic:endProof*)





(* cvs_add_error_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* cvs_add_error_cc2                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* get_auth_tab *)

goalw SysArchConsistency.thy [cvs_add_error_cc2_def] "cvs_add_error_cc2";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvs_add_error_def] 1);
auto();

by(cut_facts_tac [get_auth_tab_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1;
ba 1; 
by(convert2hol_tac [Cvs_FileSystem_def,FileSystem_def] 1);
auto();
qed"cvs_add_error_cc2";
(*@proofstatistic:endProof*)


(* cvs_add_error_cc5                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* cvsperm2uid  *)

goalw SysArchConsistency.thy [cvs_add_error_cc5_def] "cvs_add_error_cc5";

by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvs_add_error_def] 1);
auto();
by(rewrite_goals_tac [Let_def]);

by(cut_facts_tac [cvsperm2gid_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1; 
by(convert2hol_tac [total_inj_def] 1);
auto();

qed"cvs_add_error_cc5";
(*@proofstatistic:endProof*)



(* cvs_co_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* cvs_co_cc1                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* rep_access ..*)

goalw SysArchConsistency.thy [cvs_co_cc1_def] "cvs_co_cc1";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvs_co_def] 1);
auto();

br (stripS rep_accessPathInDomRepFiles) 1;
auto();
by(convert2hol_tac [] 1);
qed"cvs_co_cc1";
(*@proofstatistic:endProof*)


(* cvs_co_cc2                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* choose       *)

goalw SysArchConsistency.thy [cvs_co_cc2_def] "cvs_co_cc2";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvs_co_def] 1);
auto();

by(cut_facts_tac [choose_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1; 
by(convert2hol_tac [total_inj_def] 1);
auto();
by(convert2hol_tac [theta_def] 1);

by(cut_facts_tac [rep_access_axdef] 1);
bd DECL_D1 1;
(* halt here. *)
by(convert2hol_tac [theta_def] 1);
by(res_inst_tac [("A", "rep_access %^ (attributes, cvs_passwd, files, wcs_attributes) %^ p_63")] subsetD 1);
br PowTotalApplDom2Levels 1;
ba 4;
ba 3;
ba 1;
auto();
qed"cvs_co_cc2";
(*@proofstatistic:endProof*)




(* cvsUp_cc ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

(* cvsUp_cc1                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* rep_access ..*)

goalw SysArchConsistency.thy [cvsUp_cc1_def] "cvsUp_cc1";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvsUp_def] 1);
auto();
by(full_expand_schema_tac cvsUp_def 1);
bd DECL_D2 1;
auto();
qed"cvsUp_cc1";
(*@proofstatistic:endProof*)





(* cvsUp_cc2                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* rep_access ..*)

goalw SysArchConsistency.thy [cvsUp_cc2_def] "cvsUp_cc2";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvsUp_def] 1);
auto();
br tfun_dom 1;
by(cut_facts_tac [repOf_axdef] 1);
bd DECL_D1 1;
ba 1;

br Rel_Apply_in_Partial_Ran2 1;


by(full_expand_schema_tac cvsUp_def 2);
bd DECL_D2 2;
auto();(**)

by(full_expand_schema_tac Cvs_FileSystem_def 1);

by(convert2hol_tac [CVS_ATTR_TAB_def] 1);
auto();
qed"cvsUp_cc2";
(*@proofstatistic:endProof*)





(* cvsUp_cc5                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* rep_access ..*)

goalw SysArchConsistency.thy [cvsUp_cc5_def] "cvsUp_cc5";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvsUp_def] 1);
auto();
br tfun_dom 1;
by(cut_facts_tac [rep_access_axdef] 1);
bd DECL_D1 1;
ba 1; 
by(convert2hol_tac[] 1);
qed"cvsUp_cc5";
(*@proofstatistic:endProof*)



(* cvsUp_cc4                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* rep_access ..*)

goalw SysArchConsistency.thy [cvsUp_cc4_def] "cvsUp_cc4";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvsUp_def] 1);
auto();

br (stripS rep_accessPathInDomRepFiles) 1;
auto();
by(convert2hol_tac [] 1);

br cat_path 1;
ba 2;(**)
(* uebrig: *)
(* ...==> (wcs_attributes %^ wdir).rep : Path *)



(* cvsUp_cc6                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* rep_access ..*)

goalw SysArchConsistency.thy [cvsUp_cc6_def] "cvsUp_cc6";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvsUp_def] 1);
auto();
br tfun_ApplDom 1;
by(cut_facts_tac [rep_access_axdef] 1);
bd DECL_D1 1;
ba 1;
by(convert2hol_tac [] 1);
br cat_path 1;
by(convert2hol_tac [cvsUp_def] 2);
(* uebrig: *)
(* ... ==> (wcs_attributes %^ wdir).rep : Path*)



(* cvsUp_cc7                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* rep_access ..*)

goalw SysArchConsistency.thy [cvsUp_cc7_def] "cvsUp_cc7";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvsUp_def] 1);
auto();
by(cut_facts_tac [choose_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1;
ba 1;
auto();
by(convert2hol_tac [] 1);
(* uebrig: *)
(* ... ==> (wcs_attributes %^ wdir).rep : Path*)
(* "!! x y. [| f: A ---> B ---> C ; q: f %^ x %^ y|] ==> y: B" *)
(* ... vermischt es noch.*)


(* cvsUpNoAct_cc1                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* wcs_attributes *)

goalw SysArchConsistency.thy [cvsUpNoAct_cc1_def] "cvsUpNoAct_cc1";
by(stripS_tac 1);
by(convert2hol_tac [cvsUpNoAct_def] 1);
auto();
qed"cvsUpNoAct_cc1";
(*@proofstatistic:endProof*)


(* cvsUpNoAct_cc2                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* rep_of         *)

goalw SysArchConsistency.thy [cvsUpNoAct_cc2_def] "cvsUpNoAct_cc2";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvsUpNoAct_def] 1);
auto();

by(cut_facts_tac [repOf_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1;
ba 1;
br Rel_Apply_in_Partial_Ran2 1;

by(convert2hol_tac [cvsUpNoAct_def, Cvs_FileSystem_def, CVS_ATTR_TAB_def] 1);
by(REPEAT (etac conjE 1));
ba 1;
by(convert2hol_tac [cvsUpNoAct_def] 1);
auto();
qed"cvsUpNoAct_cc2";
(*@proofstatistic:endProof*)



(* cvs_ci_cc1                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* wcs_attributes *)

goalw SysArchConsistency.thy [cvs_ci_cc1_def] "cvs_ci_cc1";
by(stripS_tac 1);
by(convert2hol_tac [cvs_ci_def] 1);
auto();
qed"cvs_ci_cc1";
(*@proofstatistic:endProof*)



(* cvs_ci_cc4                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* rep_access     *)

goalw SysArchConsistency.thy [cvs_ci_cc4_def] "cvs_ci_cc4";
by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvs_ci_def] 1);
auto();
br tfun_dom 1;
by(cut_facts_tac [rep_access_axdef] 1);
bd DECL_D1 1;
ba 1; 
by(convert2hol_tac[] 1);
qed"cvs_ci_cc4";
(*@proofstatistic:endProof*)



(* cvs_ci_cc10                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* cvsperm2uid  *)

goalw SysArchConsistency.thy [cvs_ci_cc10_def] "cvs_ci_cc10";

by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvs_ci_def] 1);
auto();

by(cut_facts_tac [cvsperm2gid_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1; 
by(convert2hol_tac [total_inj_def] 1);
auto();

qed"cvs_ci_cc10";
(*@proofstatistic:endProof*)



(* cvs_ci_cc11                     *)
(*@proofstatistic:beginProof*)
(*@proofstatistic:PartialFuncDefinednessProof*)
(* cvsperm2uid  *)

goalw SysArchConsistency.thy [cvs_ci_cc11_def] "cvs_ci_cc11";

by(stripS_tac 1);
br DECL_I 1;
by(convert2hol_tac [cvs_ci_def] 1);
auto();

by(cut_facts_tac [cvsperm2gid_axdef] 1);
bd DECL_D1 1;
br tfun_dom 1; 
by(convert2hol_tac [total_inj_def] 1);
auto();

qed"cvs_ci_cc11";
(*@proofstatistic:endProof*)


