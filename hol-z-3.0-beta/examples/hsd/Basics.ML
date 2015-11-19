(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * Basics.ML --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 2003-2007 ETH Zurich, Switzerland
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
(* $Id: Basics.ML 6743 2007-08-03 06:39:08Z brucker $ *)

(* ISABELLE/HOL-Z START *)
(* toggle to sml-mode, start sml shell with start_holz *)
(*

cd "holz";
use_holz "Basics";

 *)


(* PORTED >>>>

use "Prelude.ML";

fun pprint_off() = (print_depth 0; goals_limit:=0);
fun pprint_on() = (print_depth 50; goals_limit:=10);

pprint_off();

toToplevel Basics.axdefs;
toToplevel Basics.schemes;


Add_axdefs_TC (map snd Basics.axdefs);


Add_Univrule_TC(map (get_thm Basics.thy)
                     ["LOGOUT_RESULT_def","APPEND_SIGNATURE_RESULT_def",
                      "ACCESS_TYPE_def","SIG_LOG_WRITE_ACCESS_def",
                      "PRI_KEY_READ_ACCESS_def","COMMAND_def",
                      "USER_NAME_def","VALID_SIGNATURE_def",
                      "VALID_PRI_KEY_def","VALID_SESSION_ID_def",
                      "VALID_USER_ID_def","UNIT_def","CHAR_def","String_def"]);




(* making datatype induced theorems accessible to proof engine *)
val COMMAND_induct =
    get_thm Basics.thy "Basics.COMMAND_induct";
val PRI_KEY_READ_ACCESS_induct =
    get_thm Basics.thy "Basics.PRI_KEY_READ_ACCESS_induct";
val SIG_LOG_WRITE_ACCESS_induct =
    get_thm Basics.thy "Basics.SIG_LOG_WRITE_ACCESS_induct";
val ACCESS_TYPE_induct =
    get_thm Basics.thy "Basics.ACCESS_TYPE_induct";
val APPEND_SIGNATURE_RESULT_induct =
    get_thm Basics.thy "Basics.APPEND_SIGNATURE_RESULT_induct";
val LOGOUT_RESULT_induct =
    get_thm Basics.thy "Basics.LOGOUT_RESULT_induct";
val SESSION_ERROR_induct =
    get_thm Basics.thy "Basics.SESSION_ERROR_induct";


val authenticate_user_not_generate_signature=
    get_thm Basics.thy "Basics.authenticate_user_not_generate_signature";
val authenticate_user_not_logout=
    get_thm Basics.thy "Basics.authenticate_user_not_logout";
val authenticate_user_not_empty =
    get_thm Basics.thy "Basics.authenticate_user_not_empty";
val generate_signature_not_logout=
    get_thm Basics.thy "Basics.generate_signature_not_logout";
val generate_signature_not_empty=
    get_thm Basics.thy "Basics.generate_signature_not_empty";
val logout_not_empty=
    get_thm Basics.thy "Basics.logout_not_empty";


val accept_read_prikey_not_refuse_read_prikey=
    get_thm Basics.thy "Basics.accept_read_prikey_not_refuse_read_prikey";


val accept_write_siglog_not_refuse_write_siglog =
    get_thm Basics.thy "Basics.accept_write_siglog_not_refuse_write_siglog";


val read_prikey_not_read_siglog =
    get_thm Basics.thy "Basics.read_prikey_not_read_siglog";
val read_prikey_not_write_siglog =
    get_thm Basics.thy "Basics.read_prikey_not_write_siglog";
val write_siglog_not_read_siglog =
    get_thm Basics.thy "Basics.write_siglog_not_read_siglog";

val access_denied_not_sig_log_updated=
    get_thm Basics.thy "Basics.access_denied_not_sig_log_updated";

val invalid_session_id_error_not_session_terminated=
    get_thm Basics.thy "Basics.invalid_session_id_err_not_session_terminated";



val distincts = [authenticate_user_not_generate_signature,
             authenticate_user_not_logout,
             authenticate_user_not_empty,generate_signature_not_logout,
             generate_signature_not_empty,logout_not_empty,
             accept_read_prikey_not_refuse_read_prikey,
             accept_write_siglog_not_refuse_write_siglog,
             read_prikey_not_read_siglog,read_prikey_not_write_siglog,
             write_siglog_not_read_siglog,
             access_denied_not_sig_log_updated,
             invalid_session_id_error_not_session_terminated];

Addsimps    (distincts @ (map (fn X => X RS not_sym) distincts));
(* setup the prover with all distincts and symmetric variants *)



goal Basics.thy "!!X. X : %F SESSION_ID ==> (new %^ X) ~: X";
by(cut_facts_tac [new_axdef] 1);auto();
qed"new_fresh";
Addsimps[new_fresh];

goal Basics.thy "NULL = Inr unit";
by(cut_facts_tac [NO_USER_axdef] 1);auto();
qed"NULL_def";

goal Basics.thy "NULL_KEY = Inr unit";
by(cut_facts_tac [NO_USER_axdef] 1);auto();
qed"NULL_KEY_def";

goal Basics.thy "NO_USER = Inr unit";
by(cut_facts_tac [NO_USER_axdef] 1);auto();
qed"NO_USER_def";


goal Basics.thy "NULL : SIGNATURE";
by(cut_facts_tac [NO_USER_axdef] 1);auto();
qed"NULL_is_SIGNATURE";

goal Basics.thy "NULL_KEY : PRI_KEY";
by(cut_facts_tac [NO_USER_axdef] 1);auto();
qed"NULL_KEY_is_PRI_KEY";

goal Basics.thy "NO_USER : USER_ID";
by(cut_facts_tac [NO_USER_axdef] 1);auto();
qed"NO_USER_is_USER_ID";

Addsimps[NULL_is_SIGNATURE,NULL_KEY_is_PRI_KEY,NO_USER_is_USER_ID];
Delsimps[NULL_def,NULL_KEY_def,NO_USER_def];
(* These definitions should not be automatically unfolded,
   as is HOL-Z default strategy. *)


goal Basics.thy "CRYPT_ERR = Inr crypt_err";auto();
qed"CRYPT_ERR_def";

goal Basics.thy "NO_USER_ERR = Inr no_user_err";auto();
qed"NO_USER_ERR_def";

goal Basics.thy "INVALID_PW_ERR = Inr invalid_pw_err";auto();
qed"INVALID_PW_ERR_def";

goal Basics.thy "SAME_USER_ERR = Inr same_user_err";auto();
qed"SAME_USER_ERR_def";

Delsimps[CRYPT_ERR_def,NO_USER_ERR_def,SAME_USER_ERR_def];
(* correcting default configuration *)

goal Basics.thy
"AUTH_ERRORS =                                           \
\ {CRYPT_ERR, NO_USER_ERR, INVALID_PW_ERR, SAME_USER_ERR}";
auto();
qed"AUTH_ERRORS_def";



goal Basics.thy "CRYPT_ERR : AUTH_ERRORS";auto();
qed"CRYPT_ERR_in_AUTH_ERRORS";

goal Basics.thy "SAME_USER_ERR : AUTH_ERRORS";auto();
qed"SAME_USER_ERR_in_AUTH_ERRORS";

goal Basics.thy "NO_USER_ERR : AUTH_ERRORS";auto();
qed"NO_USER_ERR_in_AUTH_ERRORS";

goal Basics.thy "INVALID_PW_ERR : AUTH_ERRORS";auto();
qed"INVALID_PW_ERR_in_AUTH_ERRORS";

Delsimps[NO_USER_ERR_def,INVALID_PW_ERR_def,
         SAME_USER_ERR_def,AUTH_ERRORS_def];
(* correcting default configuration *)
Addsimps[CRYPT_ERR_in_AUTH_ERRORS,SAME_USER_ERR_in_AUTH_ERRORS,
         NO_USER_ERR_in_AUTH_ERRORS,INVALID_PW_ERR_in_AUTH_ERRORS];


goalw Basics.thy [SIGNATURE_def,sum_def,image_def] "X : SIGNATURE";
auto();by(res_inst_tac [("s","X")] sumE 1);auto();
qed"X_in_SIGNATURE";

goalw Basics.thy [USER_ID_def,sum_def,image_def] "X : USER_ID";
auto();by(res_inst_tac [("s","X")] sumE 1);auto();
qed"X_in_USER_ID";

goalw Basics.thy [PRI_KEY_def,sum_def,image_def] "X : PRI_KEY";
auto();by(res_inst_tac [("s","X")] sumE 1);auto();
qed"X_in_PRI_KEY";

goalw Basics.thy [SESSION_ID_def,sum_def,image_def] "X : SESSION_ID";
auto();by(res_inst_tac [("s","X")] sumE 1);auto();
qed"X_in_SESSION_ID";

Addsimps[X_in_SIGNATURE,X_in_SIGNATURE,X_in_USER_ID,X_in_PRI_KEY,
         X_in_SESSION_ID];
(* Any X of sum type is in the corresponding sets.
   Use this fact automatically. *)


goalw Basics.thy [SESSION_TABLE_def]
"!!ssn_tbl. ssn_tbl : SESSION_TABLE ==> NO_USER ~: dom ssn_tbl";
br contra_subsetD 1;
br Rel_Dom_subset 1;
be Pfun_Rel 1;
auto();
qed"NO_USER_not_in_dom_SESSION_TABLE";

goalw Basics.thy []
"!!ssn_tbl. [| ssn_tbl : SESSION_TABLE; x : dom ssn_tbl |] ==> x ~= NO_USER";
be contrapos2 1;back();
by(asm_full_simp_tac (simpset() addsimps [NO_USER_not_in_dom_SESSION_TABLE])1);
qed"NO_USER_not_in_dom_SESSION_TABLE_rev";
Addsimps[NO_USER_not_in_dom_SESSION_TABLE_rev];


goalw Basics.thy [SESSION_TABLE_def]
"!!ssn_tbl. [| ssn_tbl : SESSION_TABLE; x : dom ssn_tbl|] ==> \
\ CRYPT_ERR ~: dom(ssn_tbl %^ x)";
br contra_subsetD 1;
br Rel_Dom_subset 1;
br Pfun_Rel 1;
br pfun_apply 1; ba 1; ba 1;
by(auto_tac (claset(),simpset() addsimps [AUTH_ERRORS_def]));
qed"CRYPT_ERR_not_in_dom_dom_SESSION_TABLE";

goalw Basics.thy [SESSION_TABLE_def]
"!!ssn_tbl. [| ssn_tbl : SESSION_TABLE; x : dom ssn_tbl|] ==> \
\ NO_USER_ERR ~: dom(ssn_tbl %^ x)";
br contra_subsetD 1;
br Rel_Dom_subset 1;
br Pfun_Rel 1;
br pfun_apply 1; ba 1; ba 1;
by(auto_tac (claset(),simpset() addsimps [AUTH_ERRORS_def]));
qed"NO_USER_ERR_not_in_dom_dom_SESSION_TABLE";

goalw Basics.thy [SESSION_TABLE_def]
"!!ssn_tbl. [| ssn_tbl : SESSION_TABLE; x : dom ssn_tbl|] ==> \
\ INVALID_PW_ERR ~: dom(ssn_tbl %^ x)";
br contra_subsetD 1;
br Rel_Dom_subset 1;
br Pfun_Rel 1;
br pfun_apply 1; ba 1; ba 1;
by(auto_tac (claset(),simpset() addsimps [AUTH_ERRORS_def]));
qed"INVALID_PW_ERR_not_in_dom_dom_SESSION_TABLE";

goalw Basics.thy [SESSION_TABLE_def]
"!!ssn_tbl. [| ssn_tbl : SESSION_TABLE; x : dom ssn_tbl|] ==> \
\ SAME_USER_ERR ~: dom(ssn_tbl %^ x)";
br contra_subsetD 1;
br Rel_Dom_subset 1;
br Pfun_Rel 1;
br pfun_apply 1; ba 1; ba 1;
by(auto_tac (claset(),simpset() addsimps [AUTH_ERRORS_def]));
qed"SAME_USER_ERR_not_in_dom_dom_SESSION_TABLE";




goalw Basics.thy [ACCESS_CONTROL_LIST_def]
"!!acl. acl : ACCESS_CONTROL_LIST ==> NO_USER ~: dom acl";
br contra_subsetD 1;
br Rel_Dom_subset 1;
be Pfun_Rel 1;
auto();
qed"NO_USER_not_in_dom_ACCESS_CONTROL_LIST";
Addsimps[NO_USER_not_in_dom_SESSION_TABLE,
         CRYPT_ERR_not_in_dom_dom_SESSION_TABLE,
         NO_USER_ERR_not_in_dom_dom_SESSION_TABLE,
         INVALID_PW_ERR_not_in_dom_dom_SESSION_TABLE,
         SAME_USER_ERR_not_in_dom_dom_SESSION_TABLE,
         NO_USER_not_in_dom_ACCESS_CONTROL_LIST];



goal Basics.thy "!!X. X : %F SESSION_ID ==> (new %^ X) ~= CRYPT_ERR";
by(cut_facts_tac [new_axdef,AUTH_ERRORS_def] 1);
bd DECL_D1 1;
bd tfun_apply 1; ba 1;
auto();
qed"new_neq_CRYPT_ERR";

goal Basics.thy "!!X. X : %F SESSION_ID ==> (new %^ X) ~= NO_USER_ERR";
by(cut_facts_tac [new_axdef,AUTH_ERRORS_def] 1);
bd DECL_D1 1;
bd tfun_apply 1; ba 1;
auto();
qed"new_neq_NO_USER_ERR";

goal Basics.thy "!!X. X : %F SESSION_ID ==> (new %^ X) ~= INVALID_PW_ERR";
by(cut_facts_tac [new_axdef,AUTH_ERRORS_def] 1);
bd DECL_D1 1;
bd tfun_apply 1; ba 1;
auto();
qed"new_neq_INVALID_PW_ERR";

goal Basics.thy "!!X. X : %F SESSION_ID ==> (new %^ X) ~= SAME_USER_ERR";
by(cut_facts_tac [new_axdef,AUTH_ERRORS_def] 1);
bd DECL_D1 1;
bd tfun_apply 1; ba 1;
auto();
qed"new_neq_SAME_USER_ERR";
Addsimps [new_neq_CRYPT_ERR,new_neq_NO_USER_ERR,
          new_neq_INVALID_PW_ERR,new_neq_SAME_USER_ERR];


val prems = goalw Basics.thy [PRI_KEY_LIST_def]
"!! uid. [| X : dom pri_key_lst;                         \
\           pri_key_lst: PRI_KEY_LIST |] ==>             \
\   pri_key_lst %^ X ~= NULL_KEY";
by (forward_tac [pfun_apply] 1);ba 1;
auto();
qed"pri_key_lst_apply_not_NULL_KEY";
Addsimps [pri_key_lst_apply_not_NULL_KEY];


val prems = goalw Basics.thy [SESSION_TABLE_def]
"!!sid. [| ssn_tbl : SESSION_TABLE |] ==>                        \
\       {uid. uid : dom ssn_tbl & P uid}  <= USER_ID - {NO_USER}";
be pfunE 1;bd Rel_Dom_subset 1;
br subset_trans 1; ba 2;
auto();
qed"aux1";


 val prems = goalw Basics.thy [SESSION_TABLE_def]
 "!!sid.[| ssn_tbl : SESSION_TABLE;                               \
 \         (sid, y) : X; (x, X) : ssn_tbl |]                      \
 \      ==>                                                       \
 \      { uid. uid : dom ssn_tbl & sid : dom (ssn_tbl %^          \
 \                                                      uid)} ~= {}";
 by(asm_full_simp_tac (HOL_ss addsimps [all_not_in_conv RS sym]) 1);
 auto();
 qed "aux2";
(* The weird indentation is due to zeta: it does not accept the line:

% \    { uid. uid : dom ssn_tbl & sid : dom (ssn_tbl  %^  uid)} ~= {}";

   without the leading % !!!
 *)

val prems = goalw Basics.thy [SESSION_TABLE_def]
"!!sid.[| ssn_tbl : SESSION_TABLE;                               \
\         sid : dom(ssn_tbl %^ x); x : dom ssn_tbl |]              \
\      ==>                                                       \
\      { uid. uid : dom ssn_tbl & sid : dom (ssn_tbl %^          \
\                                                      uid)} ~= {}";
by(asm_full_simp_tac (HOL_ss addsimps [all_not_in_conv RS sym]) 1);
by(res_inst_tac [("x","x")] exI 1);
auto();
qed "aux2'";


val prems = goalw Basics.thy [SESSION_TABLE_def]
"!!sid.[| ssn_tbl : SESSION_TABLE;                                \
\         (sid, y) : X; (x, X) : ssn_tbl |]                       \
\       ==> {uid. uid : dom ssn_tbl & sid : dom (ssn_tbl %^       \
\                                                           uid)} \
\          <= dom ssn_tbl";
auto();
qed"aux3";

Add_Univdef_TC[X_in_SIGNATURE,X_in_USER_ID,
               X_in_PRI_KEY,X_in_SESSION_ID];


 <<< PORTED *)


*)
