(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * HSD.ML --- 
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
(* $Id: HSD.ML 6743 2007-08-03 06:39:08Z brucker $ *)


(* cd "holz";
   use_holz "HSD";
 *)
(*
toToplevel HSD.axdefs;
toToplevel HSD.schemes;

Add_axdefs_TC (map snd HSD.axdefs);

(* Windows Side Operations - nothing to do wrt. state invariance lemmas,
   since windows side has no own state. *)

zgoal HSD.thy
"AuthenticateUserL =+=> (signature_log' =  signature_log &            \
\                        access_control_list' = access_control_list & \
\                        pri_key_list' = pri_key_list)";
by(stripS_tac 1);
by(forward_tac [stripS (get_decl HSD.thy "AuthenticateUserL" 2)] 1);
by(forward_tac [stripS (get_decl HSD.thy "AuthenticateUserL" 3)] 1);
by (convert2hol_tac [] 1);
qed"AuthenticateUserL_inv_state_components";


zgoal HSD.thy
"AuthenticateUserL                                                    \
\  =+=>  uid : dom session_table                                      \
\  =+=>  (session_table' %^ uid = session_table %^ uid)";
by(stripS_tac 1);
by(zftac (get_conj HSD.thy "AuthenticateUserL" 2) 1);
by(zftac (get_conj HSD.thy "AuthenticateUserL" 3) 1);
by(thin_tac "Authentication = ?X" 1);
by(thin_tac "session_table' = ?X" 1);
(* saturation of tc's *)
by(zftac (get_decl HSD.thy "AuthenticateUserL" 1) 1);
by(zftac (get_decl HSD.thy "AuthenticateUserL" 3) 1);
by(zftac (get_decl HSD.thy "AuthenticateUserL" 7) 1);
by(zdtac (get_decl HSD.thy "DARMA" 4) 1);
by(asm_full_simp_tac (HOL_ss addsimps [XI_def,DELTA_def]) 1);
by(REPEAT (etac conjE 1));
by(zftac (get_decl HSD.thy "SessionManager" 1) 1);
by(zdtac (get_decl HSD.thy "SessionManager" 2) 1);
by(zdtac (get_decl HSD.thy "AccessController" 1) 1);
(* <<< saturation *)
by(zstac (AuthenticateUser_axdef RS DECL_D2) 1);
by(zstac (RegistSessionInformation_axdef RS DECL_D2) 1);
by(case_tac "User_authentication_uid = uid" 1);
by(ALLGOALS(simp_tac (simpset() addsimps  [maplet_def]
                                addsplits [expand_if])));
bd (neq_sym RS iffD1) 2;
by(ALLGOALS(Asm_simp_tac));
qed"AuthenticateUserL_uid_auth_implies_session_table_inv";




zgoal HSD.thy
"GenerateSignatureL =+=> (access_control_list' = access_control_list & \
\                        session_IDs = session_IDs'  &                 \
\                        pri_key_list' = pri_key_list)";
by(stripS_tac 1);
by(forward_tac [stripS (get_decl HSD.thy "GenerateSignatureL" 3)] 1);
by(dtac (stripS(get_conj HSD.thy "GenerateSignatureL" 6)) 1);
by (convert2hol_tac [] 1);
qed"GenerateSignatureL_inv_state_components";


Delsimps[No_Dom_Restr];

(* <<<<<<<<<<<<<<<<<<<<<<< *)

zgoal HSD.thy
"GenerateSignatureL =+=> dom(signature_log) <= dom(signature_log')";
by(stripS_tac 1);
by(full_expand_schema_tac GenerateSignatureL_def 1);
auto();
by(asm_full_simp_tac (HOL_ss addsimps [XI_def,DELTA_def]) 1);
by(REPEAT (etac conjE 1));
by(forward_tac [stripS (get_decl HSD.thy "HysteresisSignature" 1)] 1);
by(forward_tac [stripS (get_decl HSD.thy "SessionManager" 1)] 1);
by(forward_tac [stripS (get_decl HSD.thy "AccessController" 1)] 1);
by(forward_tac [stripS (get_decl HSD.thy "AccessController" 2)] 1);
by(asm_full_simp_tac (HOL_ss addsimps [Let_def])1);
be if_eqL_E 1;

by(forw_inst_tac [("f","% x. fst(snd x)")] arg_cong 1);by(rotate_tac ~1 1);
by(forw_inst_tac [("f","% x. fst(snd x)")] arg_cong 2);by(rotate_tac ~1 2);
bd pair_rel_dom_fst 1;
by(ALLGOALS(asm_full_simp_tac (prod_ss addsimps [Let_def])));

by(REPEAT (etac conjE 1));
by(stac (stripS(AppendSignatureRecord_axdef RS DECL_D2)) 1);
by(ALLGOALS(Asm_simp_tac));
by(asm_simp_tac (simpset() addsimps [Let_def] addsplits [expand_if]) 1);
br impI 1;
br (CheckValidofSession_axdef RS DECL_D1 RS tfun_apply_snd) 1;
by(ALLGOALS(Asm_simp_tac));

by(asm_simp_tac (prod_ss addsimps [Let_def] addsplits [expand_if]) 1);
auto();
qed"GenerateSignatureL_siglog_mono";


zgoal HSD.thy
"GenerateSignatureL =+=>                                            \
\ Signature_generation_sid ~: dom (gen_un (ran session_table)) =+=> \
\ signature_log' = signature_log & session_table' = session_table";
by(stripS_tac 1);
by(full_expand_schema_tac GenerateSignatureL_def 1);
be DECL_E 1;
by(asm_full_simp_tac (HOL_ss addsimps [XI_def,DELTA_def]) 1);
by(REPEAT (etac conjE 1));
by(forward_tac [stripS (get_decl HSD.thy "HysteresisSignature" 1)] 1);
by(forward_tac [stripS (get_decl HSD.thy "SessionManager" 1)] 1);
by(forward_tac [stripS (get_decl HSD.thy "AccessController" 1)] 1);
by(forward_tac [stripS (get_decl HSD.thy "AccessController" 2)] 1);
by(asm_full_simp_tac (HOL_ss addsimps [Let_def])1);
be if_eqL_E 1;
by(Asm_full_simp_tac 1);
by(HINT "(Signature_generation_sid, session_table, \
        \ pri_key_list) : ReadPrivateKeyFailure_" (K all_tac) 1);
by(rotate_tac ~1 1);
by(asm_full_simp_tac HOL_ss 1);
br (isValidSessionVSReadPrivateKeyFailure1 RS mp) 1;
by(ALLGOALS(asm_full_simp_tac HOL_ss));
be isValidSession_1 1;ba 1;
qed"GenerateSignatureL_inv_if_invalid_session";


zgoal HSD.thy
"GenerateSignatureL =+=>                            \
\   (dom session_table <= dom pri_key_list &        \
\    dom signature_log <= dom pri_key_list) =+=>    \
\   (dom session_table' <= dom pri_key_list' &      \
\    dom signature_log' <= dom pri_key_list')";
by(stripS_tac 1);
by(forward_tac [stripS GenerateSignatureL_inv_state_components] 1);
by(forward_tac [stripS (get_decl HSD.thy "GenerateSignatureL" 1)] 1);
by(forward_tac [stripS (get_decl HSD.thy "GenerateSignatureL" 2)] 1);
by(forward_tac [stripS (get_decl HSD.thy "GenerateSignatureL" 3)] 1);
by(asm_full_simp_tac (HOL_ss addsimps [XI_def,DELTA_def]) 1);
by(case_tac "Signature_generation_sid : dom (gen_un (ran session_table))" 1);
bd(stripS GenerateSignatureL_inv_if_invalid_session) 2;
auto();
by(dtac (stripS(get_conj HSD.thy "GenerateSignatureL" 2)) 1);
be if_eqL_E 1;
by(forw_inst_tac [("f","% x. snd(snd x)")] arg_cong 1);by(rotate_tac ~1 1);
by(forw_inst_tac [("f","% x. snd(snd x)")] arg_cong 2);by(rotate_tac ~1 2);
by(ALLGOALS(asm_full_simp_tac (prod_ss addsimps [Let_def])));
auto();
by(thin_tac "?X" 1);
by(eres_inst_tac [("Q","(xa,ya) : ?Y")] contrapos2 1);
by(stac (stripS(AppendSignatureRecord_axdef RS DECL_D2)) 1);
by(ALLGOALS(Asm_simp_tac));
by(asm_simp_tac (simpset() addsimps [Let_def] addsplits [expand_if]) 1);
br(ReadPrivateKey_axdef RS DECL_D1 RS tfun_apply_snd) 1;
by(Asm_simp_tac 1);
by(dtac (stripS (get_decl HSD.thy "SessionManager" 1)) 1);
by(dtac (stripS (get_decl HSD.thy "AccessController" 2)) 1);
by(dtac (stripS (get_decl HSD.thy "HysteresisSignature" 1)) 2);
by(ALLGOALS Asm_full_simp_tac);
by(asm_simp_tac (simpset() addsimps [Let_def,maplet_def] addsplits [expand_if]) 1);
br conjI 1; by(strip_tac 1);by(strip_tac 2);
auto();

by(dres_inst_tac [("a","(xa, ya)")] pair_rel_dom_fst 1);
by(Asm_full_simp_tac 1);
by(dtac (stripS (get_decl HSD.thy "SessionManager" 1)) 1);
by(dtac (stripS (get_decl HSD.thy "AccessController" 2)) 1);
by(rotate_tac ~2 1);
by(asm_full_simp_tac (HOL_ss addsimps [ReadPrivateKey_dom_session_table_inv]) 1);
auto();

by(dres_inst_tac [("a","(xa, ya)")] pair_rel_dom_fst 1);
by(Asm_full_simp_tac 1);
by(dtac (stripS (get_decl HSD.thy "SessionManager" 1)) 1);
by(dtac (stripS (get_decl HSD.thy "AccessController" 2)) 1);
by(rotate_tac ~2 1);
by(eres_inst_tac [("Q","xa : ?X")] contrapos2 1);
by(stac CheckValidofSession_dom_session_table_inv 1);
br (ReadPrivateKey_axdef RS DECL_D1 RS tfun_apply_snd) 1;
by(Asm_simp_tac 1); ba 1;
by(stac ReadPrivateKey_dom_session_table_inv 1);
by(ALLGOALS(Asm_simp_tac));
auto();

by(dtac (stripS(get_conj HSD.thy "GenerateSignatureL" 2)) 1);
be if_eqL_E 1;
by(forw_inst_tac [("f","% x. snd(snd x)")] arg_cong 1);by(rotate_tac ~1 1);
by(forw_inst_tac [("f","% x. snd(snd x)")] arg_cong 2);by(rotate_tac ~1 2);
by(ALLGOALS(asm_full_simp_tac (prod_ss addsimps [Let_def])));
auto();

by(forw_inst_tac [("f","fst")] arg_cong 1);back();
by(rotate_tac ~1 1);
by(asm_full_simp_tac prod_ss 1);
by(thin_tac "(fst ?X,snd ?Y) = ?Z" 1);
by(dres_inst_tac [("a","(xa, ya)")] pair_rel_dom_fst 1);
by(Asm_full_simp_tac 1);
by(eres_inst_tac [("Q","xa : ?X")] contrapos2 1);
by(dtac (stripS (get_decl HSD.thy "SessionManager" 1)) 1);
by(dtac (stripS (get_decl HSD.thy "AccessController" 2)) 1);
by(dtac (stripS (get_decl HSD.thy "HysteresisSignature" 1)) 1);
by(stac (stripS(AppendSignatureRecord_axdef RS DECL_D2)) 1);
by(ALLGOALS(Asm_simp_tac));
by(asm_simp_tac (simpset() addsimps [Let_def] addsplits [expand_if]) 1);
br impI 1;
br (CheckValidofSession_axdef RS DECL_D1 RS tfun_apply_snd) 1;
by(ALLGOALS(Asm_simp_tac));
by(simp_tac (prod_ss addsimps [Let_def,maplet_def] addsplits [expand_if]) 1);
auto();

by(eres_inst_tac [("Pa","fst(?X) : dom pri_key_list")] swap 1);
bd CheckValidofSession_uid_in_dom_ssn_tbl2 1; ba 1;
auto();

by(eres_inst_tac [("Pa","fst(?X) : dom pri_key_list")] swap 1);
bd CheckValidofSession_uid_in_dom_ssn_tbl2 1;
br (CheckValidofSession_axdef RS DECL_D1 RS tfun_apply_snd) 1;
by(ALLGOALS(Asm_simp_tac));
be subsetD 1;

by(asm_full_simp_tac (simpset() ) 1);
qed"GenerateSignatureL_implies_pri_key_list_bounds";


zgoal HSD.thy
" GenerateSignatureL =+=> uid ~: dom session_table =+=>             \
\ ( uid : dom signature_log &                                       \
\   signature_log %^ uid = signature_log' %^ uid) |                 \
\ ( uid ~: dom signature_log & uid ~: dom signature_log')";
by(stripS_tac 1);
by(full_expand_schema_tac GenerateSignatureL_def 1);
be DECL_E 1;
by(asm_full_simp_tac (HOL_ss addsimps [XI_def,DELTA_def]) 1);
by(REPEAT (etac conjE 1));
by(forward_tac [stripS (get_decl HSD.thy "HysteresisSignature" 1)] 1);
(*by(forward_tac [stripS (get_decl HSD.thy "SessionManager" 1)] 1); *)
by(forward_tac [stripS (get_decl HSD.thy "AccessController" 1)] 1);
by(forward_tac [stripS (get_decl HSD.thy "AccessController" 2)] 1);
by(asm_full_simp_tac (HOL_ss addsimps [Let_def])1);
be if_eqL_E 1;
by(ALLGOALS(Asm_full_simp_tac));
by(REPEAT (etac conjE 1));
by(thin_tac "Signature = ?X" 1);
by(dres_inst_tac [("f","fst")]arg_cong 1);back();by(rotate_tac ~1 1);
by(ALLGOALS(Asm_full_simp_tac));
by(forward_tac [not_ReadPrivateKeyFailure1VSisValidSession] 1);
by(forward_tac [stripS (get_decl HSD.thy "SessionManager" 1)] 2);
by(ALLGOALS(Asm_full_simp_tac));
by(thin_tac "Command = ?X" 1);
by(thin_tac "SNAME AccessController ?X" 1);
by(thin_tac "SNAME HysteresisSignature ?X" 1);
by(forward_tac [CheckValidofSession_uid_in_dom_ssn_tbl1] 1); (* nec ? *)
be (stripS (get_decl HSD.thy "SessionManager" 1)) 1;

by(case_tac "uid : dom signature_log" 1);
by(ALLGOALS(Asm_simp_tac));
by(stac (stripS(AppendSignatureRecord_axdef RS DECL_D2)) 1);
by(ALLGOALS(Asm_simp_tac));

br(ReadPrivateKey_axdef RS DECL_D1 RS tfun_apply_snd) 1;
by(Asm_simp_tac 1);
be (stripS (get_decl HSD.thy "SessionManager" 1)) 1;
by(asm_simp_tac (simpset() addsimps [Let_def] addsplits [expand_if]) 1);
br impI 1;
by(stac oplus_apply2 1); br refl 2;
bd CheckValidofSession_uid_in_dom_ssn_tbl2 1;
br(ReadPrivateKey_axdef RS DECL_D1 RS tfun_apply_snd) 1;
by(Asm_simp_tac 1);
be (stripS (get_decl HSD.thy "SessionManager" 1)) 1;

by(forward_tac [stripS (get_decl HSD.thy "SessionManager" 1)] 1);
by(rotate_tac ~1 1);
by(asm_full_simp_tac (simpset() addsimps [Let_def,maplet_def]) 1);
by(Blast_tac 1);

by(stac (stripS(AppendSignatureRecord_axdef RS DECL_D2)) 1);
by(ALLGOALS(Asm_simp_tac));
br(ReadPrivateKey_axdef RS DECL_D1 RS tfun_apply_snd) 1;
by(Asm_simp_tac 1);
be (stripS (get_decl HSD.thy "SessionManager" 1)) 1;
by(asm_full_simp_tac (simpset() addsimps [Let_def,maplet_def]) 1);

by(asm_full_simp_tac (simpset() addsimps [Let_def,maplet_def]
                                addsplits [expand_if]) 1);
br impI 1;
bd CheckValidofSession_uid_in_dom_ssn_tbl2 1;
br(ReadPrivateKey_axdef RS DECL_D1 RS tfun_apply_snd) 1;
by(Asm_simp_tac 1);
be (stripS (get_decl HSD.thy "SessionManager" 1)) 1;
by(forward_tac [stripS (get_decl HSD.thy "SessionManager" 1)] 1);
by(rotate_tac ~1 1);
by(asm_full_simp_tac (simpset() addsimps [Let_def,maplet_def]) 1);
by(Blast_tac 1);
qed"GenerateSignatureL_implies_not_siglogChanges";
(* This theorem is hard !!! *)



(* version pre facto *)
zgoal HSD.thy
"GenerateSignatureL =+=>                                                        \
\ ((uid : dom signature_log' /\\ uid ~: dom signature_log) \\/                  \
\  (uid : dom signature_log  /\\ signature_log %^ uid ~= signature_log' %^ uid)) =+=> \
\  uid : dom session_table /\\ Signature_generation_sid : dom (session_table %^ uid)";
by(stripS_tac 1);
by(full_expand_schema_tac GenerateSignatureL_def 1);
be DECL_E 1;
by(asm_full_simp_tac (HOL_ss addsimps [XI_def,DELTA_def]) 1);
by(REPEAT (etac conjE 1));
(* sig saturation *)
by(zftac (get_decl HSD.thy "HysteresisSignature" 1) 1);
(*by(zftac (get_decl HSD.thy "SessionManager" 1) 1); *)
by(zftac (get_decl HSD.thy "AccessController" 1) 1);
by(zftac (get_decl HSD.thy "AccessController" 2) 1);
(* <<< sig saturation *)
by(asm_full_simp_tac (HOL_ss addsimps [Let_def])1);
be if_eqL_E 1;
by(ALLGOALS(Asm_full_simp_tac));
by(REPEAT (etac conjE 1));
by(Blast_tac 1);
by(asm_full_simp_tac (simpset() addsimps [Let_def])1);
by(REPEAT (etac conjE 1));
by (zftac (get_decl HSD.thy "SessionManager" 1) 1);
by(HINT "SESSION_ID = UNIV" (fn _ => (rtac set_ext 2) THEN (Asm_simp_tac 2)) 1);
by (zftac (not_ReadPrivateKeyFailure1VSisValidSession) 1);
by (zftac (AppendSignatureRecordFailure_VS_isValidSession RS mp) 1);
by(ALLGOALS(Asm_full_simp_tac));
(* exploit in invertibility of session_table *)
br ballI 1; br ballI 1; br impI 1;
be (stripS(get_conj HSD.thy "SessionManager" 1)) 1;
by(ALLGOALS(Asm_simp_tac));
(* <<< exploit ... *)
by(zftac AppendSignatureRecord_lemma2 1);
by(dres_inst_tac [("f","fst")] arg_cong 3);back();
by(Asm_full_simp_tac 3);
by(ALLGOALS tc_tac);
by(zstac (ReadPrivateKey_axdef RS DECL_D2) 1);
by(ALLGOALS(asm_simp_tac (simpset() addsimps [Let_def])));
(* exploit in invertibility of session_table *)
br ballI 1; br ballI 1; br impI 1;
be (stripS(get_conj HSD.thy "SessionManager" 1)) 1;
by(ALLGOALS(Asm_simp_tac));
(* <<< exploit ... *)
by(HINT "uid : dom session_table" (K all_tac) 1);
by(res_inst_tac [("t","uid")] subst 2); ba 2;
br CheckValidofSession_uid_in_dom_ssn_tbl1 2;
by(ALLGOALS(Asm_simp_tac));
by(zftac isValidSession_2' 1);
be conjE 1; be exE 1;by(REPEAT (etac conjE 1));
by(HINT "uid = x" (K all_tac) 1);
by(ALLGOALS(Asm_simp_tac));
(* <<< exploit ... *)
be (stripS(get_conj HSD.thy "SessionManager" 1)) 1;
by(ALLGOALS(Asm_simp_tac));
br exI 1; br conjI 1; ba 2;
by(eres_inst_tac [("Q","?X = uid")] contrapos2 1);
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(asm_simp_tac (simpset()
                 addsimps  [asSet_def,image_def,Let_def,maplet_def]
                 addsplits [expand_if] ) 1);
by(HINT "NO_USER ~= uid"  (fn _ => (dtac NO_USER_not_in_dom_SESSION_TABLE 2)
                              THEN (Blast_tac 2))   1);
by(Asm_simp_tac 1);
br impI 1;
br choose_neq_X 1;
by(Blast_tac 3);
by(ALLGOALS(asm_full_simp_tac (simpset() addsimps
                               [asSet_def,choose_in_subset,aux1,aux2,aux2',aux3])));
qed"GenerateSignatureL_siglogChanges_charn";



(* version post facto *)
(* proof style: experimental. without tc-saturation *)
zgoal HSD.thy
"GenerateSignatureL =+=>                                                        \
\ ((uid : dom signature_log' /\\ uid ~: dom signature_log) \\/                  \
\  (uid : dom signature_log  /\\ signature_log %^ uid ~= signature_log' %^ uid)) =+=> \
\  uid : dom session_table' /\\ Signature_generation_sid : dom (session_table' %^ uid)";
by(stripS_tac 1);
by(zftac (GenerateSignatureL_siglogChanges_charn) 1);
by(full_expand_schema_tac GenerateSignatureL_def 1);
be DECL_E 1;
by(asm_full_simp_tac (HOL_ss addsimps [XI_def,DELTA_def]) 1);
by(REPEAT (etac conjE 1));
by(asm_full_simp_tac (HOL_ss addsimps [Let_def])1);
be if_eqL_E 1;
by(ALLGOALS(Asm_full_simp_tac));
by(REPEAT (etac conjE 1));
by(thin_tac "Signature = ?X" 1);
by(dres_inst_tac [("f","snd")] arg_cong 1);back();
by(ALLGOALS(Asm_full_simp_tac));
by(zstac (AppendSignatureRecord_axdef RS DECL_D2) 1);
  by(zetac (get_decl HSD.thy "HysteresisSignature" 1) 2);
  by(zftac (get_decl HSD.thy "SessionManager" 1) 1);
  by(zftac (get_decl HSD.thy "AccessController" 2) 1);
  by(tc_tac 1);
by(ALLGOALS(asm_simp_tac (simpset() addsimps  [asSet_def,image_def,Let_def,maplet_def]
                                    addsplits [expand_if])));
by(zstac (stripS(ReadPrivateKey_axdef RS DECL_D2)) 1);
  by(zftac (get_decl HSD.thy "SessionManager" 1) 1);
  by(zftac (get_decl HSD.thy "AccessController" 2) 1);
  by (zftac (not_ReadPrivateKeyFailure1VSisValidSession) 1);
  by(zftac (get_decl HSD.thy "SessionManager" 1) 1);
  by(zftac (get_decl HSD.thy "AccessController" 2) 1);
by(ALLGOALS(asm_simp_tac (simpset() addsimps  [asSet_def,image_def,Let_def,maplet_def]
                                    addsplits [expand_if])));
by (zstac CheckValidofSession_dom_session_table_inv 1);
by (zstac CheckValidofSession_dom_session_table_inv 3);
by(Asm_simp_tac 5);
  by(zftac (get_decl HSD.thy "SessionManager" 1) 1);
  by(zftac (get_decl HSD.thy "AccessController" 2) 1);
  by(tc_tac 1);
  by(zftac (get_decl HSD.thy "SessionManager" 1) 1);
  by(zftac (get_decl HSD.thy "AccessController" 2) 1);

by(zftac (get_decl HSD.thy "SessionManager" 1) 1);
by(zdtac (AppendSignatureRecordFailure_VS_isValidSession RS mp) 1);
  by(zftac (get_decl HSD.thy "AccessController" 2) 1);
  by(zetac (get_decl HSD.thy "HysteresisSignature" 1) 2);

by(stripS_tac 1);
by(HINT "SESSION_ID = UNIV" (fn _ => (rtac set_ext 2) THEN (Asm_simp_tac 2)) 1);
be (stripS(get_conj HSD.thy "SessionManager" 1)) 1;
by(ALLGOALS(Asm_simp_tac));

by(zstac sid_ind_dom_CheckValidofSession_inv2 1);
by(zstac sid_ind_dom_CheckValidofSession_inv 4);
by(ALLGOALS(Asm_simp_tac));
by(stripS_tac 5);
by(HINT "SESSION_ID = UNIV" (fn _ => (rtac set_ext 6) THEN (Asm_simp_tac 6)) 5);
by(zetac (get_decl HSD.thy "SessionManager" 1) 4);
by(zrtac (get_conj HSD.thy "SessionManager" 1) 4);
by(ALLGOALS(Asm_simp_tac));

  by(zftac (get_decl HSD.thy "SessionManager" 1) 1);
  by(zftac (get_decl HSD.thy "AccessController" 2) 1);
by(ALLGOALS(Asm_simp_tac));


  by(zftac (get_decl HSD.thy "SessionManager" 1) 1);
  by(zftac (get_decl HSD.thy "AccessController" 2) 1);
by(ALLGOALS(Asm_simp_tac));

  by(zftac (get_decl HSD.thy "SessionManager" 1) 1);
  by(zftac (get_decl HSD.thy "AccessController" 2) 1);
by(stripS_tac 1);
br (stripS(get_conj HSD.thy "SessionManager" 1)) 1; ba 1;
by(HINT "SESSION_ID = UNIV" (fn _ => (rtac set_ext 4) THEN (Asm_simp_tac 4)) 3);
by(ALLGOALS(Asm_full_simp_tac));
by(thin_tac "session_table' = ?X" 1);
by(thin_tac "SNAME DARMA ?X" 1);
by(thin_tac "?X | ?Y" 1);
be exE 1;
by(REPEAT(etac conjE 1));
bd sid_in_Check_implies_sid_in_ssn_tbl 1;
bd sid_in_Check_implies_sid_in_ssn_tbl 5;
auto();
by(zrtac (get_conj HSD.thy "SessionManager" 1) 2);
by(zrtac (get_conj HSD.thy "SessionManager" 1) 1);
auto();
qed"GenerateSignatureL_siglogChanges_charn2";



zgoal HSD.thy
"GenerateSignatureL =+=>                                            \
\   (signature_log %^ uid ~= signature_log' %^ uid |                \
\    uid ~: dom signature_log & uid : dom signature_log') =+=>      \
\   (! uid':dom signature_log - {uid}.                              \
\                    signature_log %^ uid' = signature_log' %^ uid')";
by(stripS_tac 1);
by(full_expand_schema_tac GenerateSignatureL_def 1);
be DECL_E 1;
by(asm_full_simp_tac (HOL_ss addsimps [XI_def,DELTA_def]) 1);
by(REPEAT (etac conjE 1));
by(forward_tac [stripS (get_decl HSD.thy "HysteresisSignature" 1)] 1);
(*by(forward_tac [stripS (get_decl HSD.thy "SessionManager" 1)] 1); *)
by(forward_tac [stripS (get_decl HSD.thy "AccessController" 1)] 1);
by(forward_tac [stripS (get_decl HSD.thy "AccessController" 2)] 1);
by(asm_full_simp_tac (HOL_ss addsimps [Let_def])1);
be if_eqL_E 1;
by(ALLGOALS(Asm_full_simp_tac));
by(REPEAT (etac conjE 1));
by(dres_inst_tac [("f","fst")] arg_cong 1);back();by(rotate_tac ~1 1);
by(ALLGOALS(Asm_full_simp_tac));
by(forward_tac [not_ReadPrivateKeyFailure1VSisValidSession] 1);
by(forward_tac [stripS (get_decl HSD.thy "SessionManager" 1)] 2);
by(ALLGOALS(Asm_full_simp_tac));
by(stac (stripS (AppendSignatureRecord_axdef RS DECL_D2)) 1);
by(ALLGOALS(Asm_simp_tac));
br(ReadPrivateKey_axdef RS DECL_D1 RS tfun_apply_snd) 1;
by(Asm_simp_tac 1);
be (stripS (get_decl HSD.thy "SessionManager" 1)) 1;
by(asm_simp_tac (simpset() addsimps [Let_def] addsplits [expand_if]) 1);
br impI 1;
by(simp_tac (simpset() addsimps [maplet_def]) 1);
by(stac oplus_non_apply 1);
br refl 2;
by(thin_tac "?X" 1);
be disjE 1;
be swap 1;
by(Asm_full_simp_tac 1);
by(thin_tac "uid' = ?X" 1);
by(forward_tac [stripS (get_decl HSD.thy "SessionManager" 1)] 1);
auto();
by(ALLGOALS(asm_simp_tac (simpset() addsimps [Let_def])));
by(eres_inst_tac [("Pa","?X = ?Y")] swap 1);back();
by(stac (stripS (ReadPrivateKey_axdef RS DECL_D2)) 2);
by(stac (stripS (ReadPrivateKey_axdef RS DECL_D2)) 1);
by(ALLGOALS(asm_simp_tac (simpset() addsimps [Let_def])));
be (stripS (get_decl HSD.thy "SessionManager" 1)) 3;
be (stripS (get_decl HSD.thy "SessionManager" 1)) 1;
br AppendSignatureRecord_lemma1 1;
by(ALLGOALS(Asm_simp_tac));
be (stripS (get_decl HSD.thy "SessionManager" 1)) 2;
br disjI2 1;
auto();
by(eres_inst_tac [("Pa","?X = ?Y")] swap 1);
br AppendSignatureRecord_lemma1 1;
by(ALLGOALS(Asm_simp_tac));
be (stripS (get_decl HSD.thy "SessionManager" 1)) 2;
br disjI1 1;
by(dres_inst_tac [("a","(uid, ya)")] pair_rel_dom_fst 1);
by(ALLGOALS(Asm_full_simp_tac));
qed"GenerateSignatureL_and_siglogChanges_implies_inv_others";




zgoal HSD.thy
"GenerateSignatureL =+=>                                                        \
\ ((uid : dom signature_log' /\\ uid ~: dom signature_log) \\/                  \
\  (uid : dom signature_log  /\\ signature_log %^ uid ~= signature_log' %^ uid)) =+=> \
\     (? siglog:SIGNATURE.                                                                \
\        ? hmg:seq CHAR.                                                        \
\            signature_log' %^ uid = hys_sig_gen %^ (hmg, pri_key_list %^ uid, siglog))";
by(stripS_tac 1);
by(full_expand_schema_tac GenerateSignatureL_def 1);
be DECL_E 1;
by(asm_full_simp_tac (HOL_ss addsimps [XI_def,DELTA_def]) 1);
by(REPEAT (etac conjE 1));
by(forward_tac [stripS (get_decl HSD.thy "HysteresisSignature" 1)] 1);
(*by(forward_tac [stripS (get_decl HSD.thy "SessionManager" 1)] 1); *)
by(forward_tac [stripS (get_decl HSD.thy "AccessController" 1)] 1);
by(forward_tac [stripS (get_decl HSD.thy "AccessController" 2)] 1);
by(asm_full_simp_tac (HOL_ss addsimps [Let_def])1);
be if_eqL_E 1;
by(ALLGOALS(Asm_full_simp_tac));
by(REPEAT (etac conjE 1));
by(rotate_tac ~2 1);
by(Asm_full_simp_tac 1);
by(REPEAT (etac conjE 1));
by(dres_inst_tac [("f","fst")] arg_cong 1);back();
by(rotate_tac ~1 1);
by(ALLGOALS(Asm_full_simp_tac));
by (forward_tac [stripS (get_decl HSD.thy "SessionManager" 1)] 1);
by(forward_tac [not_ReadPrivateKeyFailure1VSisValidSession] 1);
by(forward_tac [AppendSignatureRecordFailure_VS_isValidSession RS mp] 4);
by(ALLGOALS(Asm_full_simp_tac));
(* exploit in invertibility of session_table *)
br ballI 1;
br ballI 1; br impI 1;
be (stripS(get_conj HSD.thy "SessionManager" 1)) 1;
by(HINT "SESSION_ID = UNIV" (K all_tac) 3);
br set_ext 4;
by(ALLGOALS(Asm_simp_tac));

(* unfold AppendSignatureRecord and side conditions *)
by(zstac (AppendSignatureRecord_axdef RS DECL_D2) 1);
by(ALLGOALS(asm_simp_tac (simpset() addsimps [Let_def,maplet_def])));
by(zrtac (CheckValidofSession_axdef RS DECL_D1 RS tfun_apply_snd) 1);

(* Now reduce the main goal to the basics ... *)
by(stac oplus_by_pair_apply1 1);
by(defer_tac 1); (* push away equality condition *)
br bexI 1; br bexI 1; ba 2;
by(res_inst_tac [("t","uid")] subst 1);
br refl 2; (* thats it ... *)
by(tc_tac 2);


(* Now cleanup: proof applicabilities,
   in particular

  fst (CheckValidofSession %^ (Signature_generation_sid,
                               read_prikey, session_table)) = uid

  and

  fst (CheckValidofSession %^ (Signature_generation_sid,
  write_siglog,
  snd (CheckValidofSession %^ (Signature_generation_sid, read_prikey,
                               session_table)))) = uid *)
br sym 2;
by (zrtac AppendSignatureRecord_lemma1 2);
by (zrtac AppendSignatureRecord_lemma2 1);
by(defer_tac 1);

br ballI 1;
br ballI 1;
br impI 1;
be exE 1;
by (zetac (get_conj HSD.thy "SessionManager" 1) 1);
by(res_inst_tac [("x","s")] bexI 1);
by(Blast_tac 1);
by(tc_tac 1);
by(zstac (ReadPrivateKey_axdef RS DECL_D2) 2);
by(zstac (ReadPrivateKey_axdef RS DECL_D2) 1);
by(ALLGOALS(asm_simp_tac (simpset() addsimps [Let_def])));
qed"GenerateSignatureL_and_siglogChanges_implies_prikey_use";




zgoal HSD.thy
"GenerateSignatureL =+=>                                                        \
\ ((uid : dom signature_log' /\\ uid ~: dom signature_log) \\/                  \
\  (uid : dom signature_log  /\\ signature_log %^ uid ~= signature_log' %^ uid)) =+=> \
\  accept_read_prikey ~= PROJ (session_table' %^ uid %^ Signature_generation_sid) fst ''pkra''";
by(stripS_tac 1);
by(zftac GenerateSignatureL_siglogChanges_charn 1);
by(HINT "SESSION_ID = UNIV" (fn _ => (rtac set_ext 2) THEN (Asm_simp_tac 2)) 1);
by(full_expand_schema_tac GenerateSignatureL_def 1);
be DECL_E 1;
by(asm_full_simp_tac (HOL_ss addsimps [XI_def,DELTA_def]) 1);
by(REPEAT (etac conjE 1));
by(forward_tac [stripS (get_decl HSD.thy "HysteresisSignature" 1)] 1);
(*by(forward_tac [stripS (get_decl HSD.thy "SessionManager" 1)] 1); *)
by(forward_tac [stripS (get_decl HSD.thy "AccessController" 1)] 1);
by(forward_tac [stripS (get_decl HSD.thy "AccessController" 2)] 1);
by(asm_full_simp_tac (HOL_ss addsimps [Let_def])1);
be if_eqL_E 1;
by(ALLGOALS(Asm_full_simp_tac));
by(REPEAT (etac conjE 1));
by(rotate_tac ~3 1);
by(ALLGOALS(Asm_full_simp_tac));

by(REPEAT (etac conjE 1));
by(dres_inst_tac [("f","snd")] arg_cong 1);back();
by(ALLGOALS(Asm_full_simp_tac));

by(zftac (not_ReadPrivateKeyFailure1VSisValidSession) 1);
by(zetac (get_decl HSD.thy "SessionManager" 1) 1);
by(thin_tac "session_table' = ?X" 1);
by(zftac (get_decl HSD.thy "SessionManager" 1) 1);
by(ALLGOALS(Asm_full_simp_tac));
by(zstac (AppendSignatureRecord_axdef RS DECL_D2) 1);
by(simp_tac (HOL_ss addsimps [Let_def]) 1);
by(tc_tac 1);
by(asm_simp_tac (simpset() addsimps [Let_def] addsplits [expand_if]) 1);
by(forward_tac [AppendSignatureRecordFailure_VS_isValidSession RS mp] 1);
by(ALLGOALS(Asm_full_simp_tac));
(* exploit in invertibility of session_table *)
br ballI 1; br ballI 1; br impI 1;
be (stripS(get_conj HSD.thy "SessionManager" 1)) 1;
by(ALLGOALS(Asm_simp_tac));
by(zftac isValidSession_2' 1);
by(zftac isValidSession_3' 1);
by(REPEAT(etac conjE 1 ORELSE etac exE 1));
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(simp_tac (simpset() addsimps [Let_def,asSet_def,image_def,maplet_def])1);
by(stac if_P 1);
by(Asm_full_simp_tac 1);
by(stac if_not_P 1);
by(Blast_tac 1);
by(dres_inst_tac [("s","accept_read_prikey")] sym 1);
by(ALLGOALS(Asm_simp_tac));
by(res_inst_tac [("s","uid"),("t","SessionManager.choose %^ ?X")] subst 1);
by(ALLGOALS(Asm_simp_tac));
by(defer_tac 1);
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(asm_simp_tac (simpset() addsimps [Let_def,asSet_def,image_def,maplet_def])1);
by(stac if_not_P 1);
by(Asm_simp_tac 1);
by(zetac (isValidSession_2' RS conjunct1) 1);
by(res_inst_tac [("s","uid"),("t","SessionManager.choose %^ ?X")] subst 1);
by(zrtac (choose_unique RS sym) 1);
br ballI 1; br ballI 1; br impI 1;
be (stripS(get_conj HSD.thy "SessionManager" 1)) 1;
by(ALLGOALS(Asm_simp_tac));
by(asm_simp_tac (simpset() addsimps [PROJ_def])1);
br(choose_unique' RS sym) 1;
br set_ext 1;
by(ALLGOALS(Asm_simp_tac));
by(stac (refl RS conj_cong) 1);
be sid_ind_dom_CheckValidofSession_inv 1;
by(ALLGOALS(Asm_simp_tac));
br iffI 2;
by(hyp_subst_tac 3);
by(Asm_simp_tac 3);
be (stripS(get_conj HSD.thy "SessionManager" 1)) 2;
by(ALLGOALS(Asm_simp_tac));
by(res_inst_tac [("x","Signature_generation_sid")] exI 2);
by(Asm_simp_tac 2);
by(stripS_tac 1);
be exE 1;
be (stripS(get_conj HSD.thy "SessionManager" 1)) 1;
by(ALLGOALS(Asm_simp_tac));
by(res_inst_tac [("x","s")] exI 1);
by(ALLGOALS(Asm_simp_tac));
qed"GenerateSignatureL_implies_no_accept_key";



(* The following crucial theorem establishes at the data model level,
   that the operation GenerateSignatureL will never change the
   session_table' and signature_log' *for an authenticated user*,
   if in the session table accept_read_prikey is not set.
   Note that this does not imply that session_table and
   signature_log are unchanged; GenerateSignatureL may process
   another user successfully.
   This is a core proof for HSD_3 on the data level.
 *)
zgoal HSD.thy
"GenerateSignatureL =+=>                                              \
\ (uid : dom session_table /\\                                        \
\  sid : dom (session_table %^ uid) /\\                               \
\  accept_read_prikey ~=                                              \
\   PROJ (session_table %^ uid %^ sid) fst ''pkra'')                  \
\ --> (session_table' %^ uid = session_table %^ uid  /\\              \
\      signature_log' %^ uid = signature_log %^ uid)";
by(stripS_tac 1);
by(full_expand_schema_tac GenerateSignatureL_def 1);
be DECL_E 1;
by(asm_full_simp_tac (HOL_ss addsimps [XI_def,DELTA_def]) 1);
by(REPEAT (etac conjE 1));
by(forward_tac [stripS (get_decl HSD.thy "HysteresisSignature" 1)] 1);
(*by(forward_tac [stripS (get_decl HSD.thy "SessionManager" 1)] 1); *)
by(forward_tac [stripS (get_decl HSD.thy "AccessController" 1)] 1);
by(forward_tac [stripS (get_decl HSD.thy "AccessController" 2)] 1);
by(asm_full_simp_tac (HOL_ss addsimps [Let_def])1);
be if_eqL_E 1;
by(ALLGOALS(Asm_full_simp_tac));
by(REPEAT (etac conjE 1));
by(zftac (not_ReadPrivateKeyFailure1VSisValidSession) 1);
by(zetac (get_decl HSD.thy "SessionManager" 1) 1);
by(zftac isValidSession_2' 1);
by(zetac (get_decl HSD.thy "SessionManager" 1) 1);
be conjE 1; be exE 1;
by(REPEAT (etac conjE 1));
by(case_tac "sid = Signature_generation_sid" 1);
   by(hyp_subst_tac 1);
   by(HINT "uid = x" (K all_tac) 1);
   by(rotate_tac ~3 1);
   by(Asm_full_simp_tac 1);
   by (zdtac (get_conj HSD.thy "SessionManager" 1) 1);
   br bexI 1;br X_in_SESSION_ID 2;
   br conjI 1; ba 2;
   by(rotate_tac ~1 1);
   by(Asm_full_simp_tac 1);

(* now the other case - essentially covered by lemma: *)
be AppendSignatureRecord_imp_nosid_nochange 1;
by(ALLGOALS Asm_simp_tac);
by(zetac (get_decl HSD.thy "SessionManager" 1) 1);
by(ALLGOALS stripS_tac);
be (stripS(get_conj HSD.thy "SessionManager" 1)) 2;
be (stripS(get_conj HSD.thy "SessionManager" 2)) 1;
by(HINT "SESSION_ID = UNIV" (fn _ => (rtac set_ext 6) THEN (Asm_simp_tac 6)) 5);
auto();
qed"GenerateSignatureL_not_accept_read_key_implies_inv";






zgoal HSD.thy
"LogoutL =+=> (signature_log' =  signature_log &            \
\              session_IDs' = session_IDs &                 \
\              access_control_list' = access_control_list & \
\              pri_key_list' = pri_key_list)";
by(stripS_tac 1);
by(forward_tac [stripS (get_decl HSD.thy "LogoutL" 2)] 1);
by(forward_tac [stripS (get_decl HSD.thy "LogoutL" 3)] 1);
by(dtac (stripS (get_conj HSD.thy "LogoutL" 4)) 1);
by (convert2hol_tac [] 1);
qed"LogoutL_inv_state_components";

zgoal HSD.thy
"LogoutL =+=>                                                  \
\ (uid : (dom session_table) /\\ Logout_ID : (dom (session_table %^ uid))) \
\ =+=>  uid ~: (dom session_table')";
by(stripS_tac 1);be conjE 1;
by(full_expand_schema_tac LogoutL_def 1);
by(res_inst_tac [("t","session_table'")] subst 1);
br FreeSessionInformation_deletes_sid2 2;
auto();
by(forw_inst_tac [("f","snd")] arg_cong 1);by(rotate_tac ~1 1);
by(forw_inst_tac [("f","snd")] arg_cong 2);by(rotate_tac ~1 2);
by(asm_full_simp_tac (HOL_ss addsimps [DELTA_def]) 3);
be conjE 3;
by(dtac (stripS (get_decl HSD.thy "SessionManager" 1)) 3);
by(ALLGOALS(asm_full_simp_tac (prod_ss)));
qed"LogoutL_delete_uid";


zgoal HSD.thy
"LogoutL =+=>                                                  \
\ (uid : (dom session_table) /\\ Logout_ID ~: (dom (session_table %^ uid))) \
\ =+=>  uid : (dom session_table')";
by(stripS_tac 1);be conjE 1;
by(full_expand_schema_tac LogoutL_def 1);
by(res_inst_tac [("t","session_table'")] subst 1);
br FreeSessionInformation_deletes_sid3 2;
auto();
by(forw_inst_tac [("f","snd")] arg_cong 1);by(rotate_tac ~1 1);
by(forw_inst_tac [("f","snd")] arg_cong 2);by(rotate_tac ~1 2);
by(asm_full_simp_tac (HOL_ss addsimps [DELTA_def]) 3);
be conjE 3;
by(dtac (stripS (get_decl HSD.thy "SessionManager" 1)) 3);
by(ALLGOALS(asm_full_simp_tac (prod_ss)));
qed"LogoutL_keep_uid";


zgoal HSD.thy
"LogoutL =+=>  (uid : (dom session_table'))   \
\ =+=>  (session_table' %^ uid = session_table %^ uid)";
by(stripS_tac 1);
by(forward_tac [stripS (get_conj HSD.thy "LogoutL" 2)] 1);
by(dres_inst_tac [("f","snd")]arg_cong 1);
by(eres_inst_tac [("P","uid : ?X")] rev_mp 1);
by(ALLGOALS(Asm_full_simp_tac));
by(zstac (FreeSessionInformation_axdef RS DECL_D2) 1);
  by(forward_tac [stripS (get_decl HSD.thy "LogoutL" 1)] 1);
  by(asm_full_simp_tac (HOL_ss addsimps [DELTA_def]) 1);
  be conjE 1;
  by(zetac (get_decl HSD.thy "SessionManager" 1) 1);
by(case_tac "Logout_ID : dom (gen_un (ran session_table))" 1);
by(ALLGOALS(Asm_simp_tac));
by(asm_simp_tac (simpset() addsimps [Let_def,maplet_def,asSet_def,image_def]) 1);
by(asm_simp_tac (simpset() addsimps [Domain_def,rel_apply_def]) 1);
qed"LogoutL_session_table_inv";



(* Nop is really a Nop and does not change any component
   if the state. *)
zgoal HSD.thy
"NopOperationL =+=> (session_table' = session_table &       \
\              session_IDs' = session_IDs &                 \
\              signature_log' =  signature_log &            \
\              access_control_list' = access_control_list & \
\              pri_key_list' = pri_key_list)";
by(stripS_tac 1);
by(forward_tac [stripS (get_decl HSD.thy "NopOperationL" 1)] 1);
by(forward_tac [stripS (get_decl HSD.thy "NopOperationL" 2)] 1);
by(forward_tac [stripS (get_decl HSD.thy "NopOperationL" 3)] 1);
by (convert2hol_tac [] 1);
qed"NopOperationL_inv_state_components";
*)
