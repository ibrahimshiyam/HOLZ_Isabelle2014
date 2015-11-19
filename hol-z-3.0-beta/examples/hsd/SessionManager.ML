(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * SessionManager.ML --- 
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
(* $Id: SessionManager.ML 6743 2007-08-03 06:39:08Z brucker $ *)


(* cd "holz";
   use_holz "SessionManager";
*)

(*
toToplevel SessionManager.axdefs;
toToplevel SessionManager.schemes;

Add_axdefs_TC (map snd SessionManager.axdefs);




(* ******************************************************************* *)
(* Basics on RegistSessionInformation                                  *)
(* ******************************************************************* *)

val prems = goal SessionManager.thy
"[| uid : dom ssn_tbl ; ssn_tbl : SESSION_TABLE ; ssn_IDs: %F SESSION_ID|] ==>  \
\ RegistSessionInformation %^ (uid,ssn_tbl,ssn_IDs) = SAME_USER_ERR";
by(cut_facts_tac ((RegistSessionInformation_axdef RS DECL_D2)::prems) 1);
auto();
qed "RegistSessionInformation_F";
Addsimps[RegistSessionInformation_F];


val prems = goal SessionManager.thy
"[| uid ~: dom ssn_tbl ; ssn_tbl : SESSION_TABLE; ssn_IDs: %F SESSION_ID |] ==>  \
\ RegistSessionInformation %^ (uid,ssn_tbl,ssn_IDs) = (new %^ ssn_IDs)";
by(cut_facts_tac ((RegistSessionInformation_axdef RS DECL_D2)::prems) 1);
auto();
qed "RegistSessionInformation_N";
Addsimps[RegistSessionInformation_N];
(* HERE *)


val prems = goal SessionManager.thy
"[| uid ~: dom ssn_tbl ; ssn_tbl : SESSION_TABLE; ssn_IDs: %F SESSION_ID |] ==>  \
\ RegistSessionInformation %^ (uid,ssn_tbl,ssn_IDs) ~: AUTH_ERRORS";
by(cut_facts_tac (prems) 1);
by(stac RegistSessionInformation_N 1);
auto();
bd((new_axdef RS DECL_D1) RS tfun_apply) 1;
auto();
qed "RegistSessionInformation_NOERROR_INV";
Addsimps[RegistSessionInformation_NOERROR_INV];



(* ******************************************************************* *)
(* Basics on FreeSession                                               *)
(* ******************************************************************* *)

goal SessionManager.thy
"!!X.  [| X : %P (USER_ID - {NO_USER}); X ~= {} |] ==> \
\         ((SessionManager.choose %^ X) : X)";
by(cut_facts_tac [choose_axdef RS DECL_D2] 1);
auto();
qed"choose_in_X";
Addsimps[choose_in_X];


goal SessionManager.thy
"!!X.  [| X : %P (USER_ID - {NO_USER}); X ~= {}; X <= Y |] ==> \
\         ((SessionManager.choose %^ X) : Y)";
bd choose_in_X 1;ba 1;auto();
qed"choose_in_subset";
Addsimps[choose_in_subset];



goal SessionManager.thy
"!!X. [| X : %P (USER_ID - {NO_USER}); X ~= {} |] ==> \
\((SessionManager.choose %^ X) ~= NO_USER)";
by(forward_tac [choose_in_X] 1); ba 1;
be swap 1;
by(rotate_tac ~1 1);
by(Asm_full_simp_tac 1);
auto();
qed"choose_neq_NO_USER";
Addsimps[choose_neq_NO_USER];

goal SessionManager.thy
"!!X. [| X : %P (USER_ID - {NO_USER}); X ~= {}; x ~:X |] ==> \
\((SessionManager.choose %^ X) ~= x)";
bd choose_in_X 1; ba 1;auto();
qed"choose_neq_X";



goal SessionManager.thy
"!!sid.                                                           \
\   [| s_tab : SESSION_TABLE;                                     \
\      ! x:dom s_tab.                                             \
\          ! y:dom s_tab.                                         \
\           (? s. s:dom (s_tab %^ x) & s:dom (s_tab %^ y))=+=>    \
\           x = y;                                                \
\      xa : dom s_tab;  sid : dom (s_tab %^ xa)|]                 \
\   ==> (SessionManager.choose %^                                 \
\         {y. y : dom s_tab &  sid : dom (s_tab %^ y)             \
\                                                     }) = xa ";
by(eres_inst_tac [("x","xa")] ballE 1);
by(Asm_full_simp_tac 2);
be ballE 1; be impE 1; be sym 2;
br exI 1; br conjI 1; ba 1;
by (HINT "{y. (y : dom s_tab) & sid : (dom (s_tab %^ y))          \
\         } :  %P(USER_ID - {NO_USER})"
         (K all_tac) 1);
bd choose_in_X 1;
by(asm_full_simp_tac (simpset() addsimps []) 2);
br PowI 2;
be aux1 2;
by(eres_inst_tac [("Pa"," ?X %^ ?Y: ?Z")] swap 2);
br choose_in_subset 2;
by(Blast_tac 4);
br PowI 2;
be aux1 2;
by(Step_tac 1);
by(eres_inst_tac [("Q","?X = {}")] contrapos2 1);
by(eres_inst_tac [("Q","?X = {}")] contrapos2 2);
be aux2' 1;
be aux2' 3;
auto();
qed"choose_unique";


goal SessionManager.thy
"!!X.  [| X = {x}; x ~= NO_USER |] ==> (SessionManager.choose %^ X) = x ";
by(cut_facts_tac [choose_axdef RS DECL_D2] 1);
by(eres_inst_tac [("x","{x}")] ballE 1);
auto();
qed"choose_unique'";



val prems = goal SessionManager.thy
"[| sid : dom (gen_un (ran ssn_tbl)); ssn_tbl : SESSION_TABLE |] ==>             \
\ FreeSessionInformation %^ (sid,ssn_tbl) = (session_terminated, ?X)";
by(cut_facts_tac ((FreeSessionInformation_axdef RS DECL_D2)::prems) 1);
by (REPEAT (etac ballE 1));
br trans 1;ba 1;auto();
qed "FreeSessionInformation_N";
Addsimps[FreeSessionInformation_N];


val prems = goal SessionManager.thy
"[| sid ~: dom (gen_un (ran ssn_tbl)); ssn_tbl : SESSION_TABLE |] ==>   \
\ FreeSessionInformation %^ (sid,ssn_tbl) = (invalid_session_id_err, ssn_tbl)";
by(cut_facts_tac ((FreeSessionInformation_axdef RS DECL_D2)::prems) 1);
by (REPEAT (etac ballE 1));
br trans 1;ba 1;auto();
qed "FreeSessionInformation_F";
Addsimps[FreeSessionInformation_F];



val prems = goal SessionManager.thy
"!!sid. [| sid : SESSION_ID; ssn_tbl : SESSION_TABLE |] ==>             \
\ sid ~: dom (gen_un (ran (snd(FreeSessionInformation %^ (sid,ssn_tbl)))))";
by(case_tac "sid : dom (gen_un (ran ssn_tbl))" 1);
by(ALLGOALS(asm_simp_tac (simpset() addsimps
                          [asSet_def,image_def,maplet_def])));
auto();
qed "FreeSessionInformation_deletes_sid1";
Addsimps[FreeSessionInformation_deletes_sid1];



val prems = goal SessionManager.thy
"!!sid. [| uid : dom ssn_tbl ; sid : dom (ssn_tbl %^ uid); ssn_tbl : SESSION_TABLE |] ==>  \
\   uid ~: dom(snd(FreeSessionInformation %^ (sid,ssn_tbl)))";
by(case_tac "sid : dom (gen_un (ran ssn_tbl))" 1);
by(ALLGOALS(asm_full_simp_tac (simpset() addsimps
                          [asSet_def,image_def,maplet_def,SESSION_TABLE_def])));
auto();
qed "FreeSessionInformation_deletes_sid2";
Addsimps[FreeSessionInformation_deletes_sid2];

val prems = goal SessionManager.thy
"!!sid. [| uid : dom ssn_tbl ; sid ~: dom (ssn_tbl %^ uid); ssn_tbl : SESSION_TABLE |] ==>  \
\   uid : dom(snd(FreeSessionInformation %^ (sid,ssn_tbl)))";
by(case_tac "sid : dom (gen_un (ran ssn_tbl))" 1);
by(ALLGOALS(asm_full_simp_tac (simpset() addsimps
                          [asSet_def,image_def,maplet_def,SESSION_TABLE_def])));
auto();
qed "FreeSessionInformation_deletes_sid3";
Addsimps[FreeSessionInformation_deletes_sid3];



(* remove automatic unfolding of CheckValidofSession_axdef. *)
Delsimps[stripS(CheckValidofSession_axdef RS DECL_D2)];

val prems = goal SessionManager.thy
"[| sid ~: dom (gen_un (ran ssn_tbl)); ssn_tbl : SESSION_TABLE |] ==>   \
\ CheckValidofSession %^ (sid,X,ssn_tbl) = (NO_USER, ssn_tbl)";
by(cut_facts_tac ((CheckValidofSession_axdef RS DECL_D2)::prems) 1);
by (REPEAT (etac ballE 1));
br trans 1;ba 1;auto();
qed "CheckValidofSession_F1";
Addsimps[CheckValidofSession_F1];


val prems = goal SessionManager.thy
"!!sid. \
\[| sid : dom (gen_un (ran ssn_tbl)); ! x. x ~: dom ssn_tbl | ?X sid x;\
\   ssn_tbl : SESSION_TABLE |] ==>                                     \
\ CheckValidofSession %^ (sid,read_prikey,ssn_tbl) = (NO_USER, ssn_tbl)";
by(cut_facts_tac ((CheckValidofSession_axdef RS DECL_D2)::prems) 1);
by (REPEAT (etac ballE 1));
br trans 1;ba 1;
(* by(res_inst_tac [("ACCESS_TYPE","X")] ACCESS_TYPE_induct 1); *)
by(ALLGOALS(asm_simp_tac (simpset() addsimps [image_def, Ball_def,asSet_def])));
by(stac if_P 1); ba 1;
auto();
qed "CheckValidofSession_F2";
(* trick proof synthesizing premise containing Z - projection:
   ! x. x ~: dom ssn_tbl \/
           (sid ~: dom (ssn_tbl %^ x) \/
            accept_read_prikey ~= (ssn_tbl %^ x %^ sid).pkra)
 *)
Addsimps[CheckValidofSession_F2]; (* probably not too useful ... *)


val prems = goal SessionManager.thy
"!!sid. \
\[| sid : dom (gen_un (ran ssn_tbl)); ! x. x ~: dom ssn_tbl | ?X sid x;\
\   ssn_tbl : SESSION_TABLE |] ==>                                     \
\ CheckValidofSession %^ (sid,write_siglog,ssn_tbl) = (NO_USER, ssn_tbl)";
by(cut_facts_tac ((CheckValidofSession_axdef RS DECL_D2)::prems) 1);
by (REPEAT (etac ballE 1));
br trans 1;ba 1;
(* by(res_inst_tac [("ACCESS_TYPE","X")] ACCESS_TYPE_induct 1); *)
by(ALLGOALS(asm_simp_tac (simpset() addsimps [image_def, Ball_def,asSet_def])));
by(stac if_P 1); ba 1;
auto();
qed "CheckValidofSession_F3";
Addsimps[CheckValidofSession_F3]; (* probably not too useful ... *)

val prems = goal SessionManager.thy
"!!sid. \
\[| sid : dom (gen_un (ran ssn_tbl)); ! x. x ~: dom ssn_tbl | ?X sid x;\
\   ssn_tbl : SESSION_TABLE |] ==>                                     \
\ CheckValidofSession %^ (sid,read_siglog,ssn_tbl) = (NO_USER, ssn_tbl)";
by(cut_facts_tac ((CheckValidofSession_axdef RS DECL_D2)::prems) 1);
by (REPEAT (etac ballE 1));
br trans 1;ba 1;
(* by(res_inst_tac [("ACCESS_TYPE","X")] ACCESS_TYPE_induct 1); *)
by(ALLGOALS(asm_simp_tac (simpset() addsimps [image_def, Ball_def,asSet_def])));
by(stac if_P 1); ba 1;
auto();
qed "CheckValidofSession_F4";
Addsimps[CheckValidofSession_F4]; (* probably not too useful ... *)




val prems = goal SessionManager.thy
"[| sid ~: dom (gen_un (ran ssn_tbl)); ssn_tbl : SESSION_TABLE |] ==>   \
\  (sid,acc_typ,ssn_tbl)~: isValidSession_";
by(cut_facts_tac ((isValidSession__axdef RS DECL_D2)::prems) 1);
by(REPEAT (etac ballE 1));
by(res_inst_tac[("P","Not")] ssubst 1); ba 1;
auto();
qed"isValidSession_1";
Addsimps[isValidSession_1];

val prems = goal SessionManager.thy
"!!sid. [|  (sid,acc_typ,ssn_tbl): isValidSession_;                     \
\           ssn_tbl : SESSION_TABLE |] ==>   \
\       sid : dom (gen_un (ran ssn_tbl))";
be contrapos2 1;
br isValidSession_1 1;
auto();
qed"isValidSession_1'";


val prems = goal SessionManager.thy
"!!sid.                                                                        \
\[| sid : dom (gen_un (ran ssn_tbl));                                          \
\   ! x. x ~: dom ssn_tbl | (sid ~: dom (ssn_tbl %^ x) |                       \
\            accept_read_prikey ~= PROJ (ssn_tbl %^ x %^ sid) fst ''pkra'');   \
\   ssn_tbl : SESSION_TABLE |]                                                 \
\  ==> (sid,read_prikey,ssn_tbl)~: isValidSession_";
by(cut_facts_tac ((isValidSession__axdef RS DECL_D2)::prems) 1);
by(REPEAT (etac ballE 1));
by(res_inst_tac[("P","Not")] ssubst 1); ba 1;
auto();
qed"isValidSession_2";
Addsimps[isValidSession_2];
(* abstracts CheckValidofSession_F2 *)


val prems = goal SessionManager.thy
"!!sid.                                                                        \
\[| (sid,read_prikey,ssn_tbl) : isValidSession_;                               \
\   ssn_tbl : SESSION_TABLE |]                                                 \
\  ==>  (? x. x : dom ssn_tbl & (sid : dom (ssn_tbl %^ x) &                    \
\            accept_read_prikey = PROJ (ssn_tbl %^ x %^ sid) fst ''pkra''))    \
\       & sid : dom (gen_un (ran ssn_tbl))";
by(forward_tac [isValidSession_1'] 1); ba 1;
br conjI 1;
be contrapos2 1;
br isValidSession_2 1;
auto();
qed"isValidSession_2'";


val prems = goal SessionManager.thy
"!!sid.                                                                        \
\[| sid : dom (gen_un (ran ssn_tbl));                                          \
\   ! x. x ~: dom ssn_tbl | (sid ~: dom (ssn_tbl %^ x) |                       \
\            accept_write_siglog ~= PROJ (ssn_tbl %^ x %^ sid) snd ''slwa'');  \
\   ssn_tbl : SESSION_TABLE |]                                                 \
\  ==> (sid,write_siglog,ssn_tbl)~: isValidSession_";
by(cut_facts_tac ((isValidSession__axdef RS DECL_D2)::prems) 1);
by(REPEAT (etac ballE 1));
by(res_inst_tac[("P","Not")] ssubst 1); ba 1;
auto();
qed"isValidSession_3";
Addsimps[isValidSession_3];
(* abstracts CheckValidofSession_F3 *)


val prems = goal SessionManager.thy
"!!sid.                                                                        \
\[| (sid,write_siglog ,ssn_tbl) : isValidSession_;                             \
\   ssn_tbl : SESSION_TABLE |]                                                 \
\  ==>  (? x. x : dom ssn_tbl & (sid : dom (ssn_tbl %^ x) &                    \
\             accept_write_siglog = PROJ (ssn_tbl %^ x %^ sid) snd ''slwa''))    \
\       & sid : dom (gen_un (ran ssn_tbl))";
by(forward_tac [isValidSession_1'] 1); ba 1;
br conjI 1;
be contrapos2 1;
br isValidSession_3 1;
auto();
qed"isValidSession_3'";


(* do not unfold any longer, just use derived rules *)
Delsimps[stripS(isValidSession__axdef RS DECL_D2)];



(* more special attempt *)
val prems = goal SessionManager.thy
"!!sid.                                                                    \
\[| (sid,read_prikey,ssn_tbl): isValidSession_ ; ssn_tbl : SESSION_TABLE   \
\|] ==>   fst(CheckValidofSession %^ (sid, read_prikey, ssn_tbl)) : dom ssn_tbl";
by(stac (stripS(CheckValidofSession_axdef RS DECL_D2)) 1);
by(ALLGOALS(asm_simp_tac (simpset() addsimps [image_def,Let_def])));
by(case_tac "sid : dom (gen_un (ran ssn_tbl))" 1);
bd isValidSession_1 2;
by(ALLGOALS(Asm_full_simp_tac));
by(Step_tac 2);
by(Step_tac 2);
by(ALLGOALS(asm_full_simp_tac (simpset() addsimps
                               [asSet_def, choose_in_subset,aux1,aux2,aux3])));
by(case_tac "?X" 1);
br if_general_I1 1;ba 1;
be if_general_I2 2;
by(ALLGOALS(asm_full_simp_tac (simpset() addsimps
                               [asSet_def, choose_in_subset,aux1,aux2,aux3])));
be contrapos2 1;
br isValidSession_2 1;
auto();
qed "CheckValidofSession_uid_in_dom_ssn_tbl1";

val prems = goal SessionManager.thy
"!!sid.                                                                    \
\[| (sid,write_siglog,ssn_tbl): isValidSession_ ; ssn_tbl : SESSION_TABLE  \
\|] ==>   fst(CheckValidofSession %^ (sid, write_siglog, ssn_tbl)) : dom ssn_tbl";
by(stac (stripS(CheckValidofSession_axdef RS DECL_D2)) 1);
by(ALLGOALS(asm_simp_tac (simpset() addsimps [image_def,Let_def])));
by(case_tac "sid : dom (gen_un (ran ssn_tbl))" 1);
bd isValidSession_1 2;
by(ALLGOALS(Asm_full_simp_tac));
by(Step_tac 2);
by(Step_tac 2);
by(ALLGOALS(asm_full_simp_tac (simpset() addsimps
                               [asSet_def, choose_in_subset,aux1,aux2,aux3])));
by(case_tac "?X" 1);
br if_general_I1 1;ba 1;
be if_general_I2 2;
by(ALLGOALS(asm_full_simp_tac (simpset() addsimps
                               [asSet_def, choose_in_subset,aux1,aux2,aux3])));
be contrapos2 1;
br isValidSession_3 1;
auto();
qed "CheckValidofSession_uid_in_dom_ssn_tbl2";


val prems = goal SessionManager.thy
"!!sid.                                                                    \
\[| (sid,read_siglog,ssn_tbl): isValidSession_ ; ssn_tbl : SESSION_TABLE   \
\|] ==>   fst(CheckValidofSession %^ (sid, read_siglog, ssn_tbl)) : dom ssn_tbl";
by(stac (stripS(CheckValidofSession_axdef RS DECL_D2)) 1);
by(ALLGOALS(asm_simp_tac (simpset() addsimps [image_def,Let_def])));
by(case_tac "sid : dom (gen_un (ran ssn_tbl))" 1);
bd isValidSession_1 2;
by(ALLGOALS(Asm_full_simp_tac));
by(Step_tac 2);
by(Step_tac 2);
by(ALLGOALS(asm_full_simp_tac (simpset() addsimps
                               [asSet_def, choose_in_subset,aux1,aux2,aux3])));
qed "CheckValidofSession_uid_in_dom_ssn_tbl3";


(* premise can be weakened to sid : dom (gen_un (ran ssn_tbl)) *)
(* a nice little tricky lemma ... and a vital invariant ... *)
val [valid_session,ssn_c, uid_c, invert] = goal SessionManager.thy
"[| (sid, read_prikey, ssn_tbl) : isValidSession_;                                \
\   ssn_tbl : SESSION_TABLE; uid : dom ssn_tbl;                                   \
\   ! x: dom ssn_tbl. ! y: dom ssn_tbl.                                           \
\        (? s. s:dom(ssn_tbl %^ x) & s:dom(ssn_tbl %^ y))  =+=> (x = y)|]         \
\ ==> (sid : dom(snd(CheckValidofSession %^ (sid,read_prikey,ssn_tbl)) %^ uid))   \
\     = (sid : dom (ssn_tbl %^ uid))";
by(cut_facts_tac [ssn_c,ssn_c RS (valid_session RS isValidSession_2')] 1);
be conjE 1; be exE 1;
by(REPEAT(etac conjE 1 ORELSE etac exE 1));
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(asm_simp_tac (simpset() addsimps [Let_def,asSet_def,image_def,maplet_def])1);
by(stac if_not_P 1);
by(Blast_tac 1);
by(res_inst_tac [("s","x"),("t","SessionManager.choose %^ ?X")] subst 1);
by(ALLGOALS(Asm_simp_tac));
br (invert RS (ssn_c RS (choose_unique RS sym))) 1; ba 1; ba 1;
by(case_tac "sid : dom (ssn_tbl %^ uid)" 1);
by(ALLGOALS(Asm_simp_tac));
by(HINT " x = uid" (K all_tac) 1);
by(HINT " uid ~= x" (K all_tac) 3);
by(ALLGOALS(Asm_simp_tac));
be (stripS invert) 1;
br uid_c 1;
by(Blast_tac 1);
be swap 1;
by(Asm_full_simp_tac 1);
qed "sid_ind_dom_CheckValidofSession_inv";



val [quod, valid_session,ssn, uid_c, invert] = goal SessionManager.thy
"[|  s : dom (snd (CheckValidofSession %^ (sid,read_prikey, ssn_tbl)) %^ x);      \
\    (sid, read_prikey, ssn_tbl) : isValidSession_;                               \
\    ssn_tbl : SESSION_TABLE;  x : dom ssn_tbl;                                   \
\    ! x: dom ssn_tbl. ! y: dom ssn_tbl.                                          \
\        (? s. s:dom(ssn_tbl %^ x) & s:dom(ssn_tbl %^ y))  =+=> (x = y)           \
\ |] ==> s : dom (ssn_tbl %^ x)";
by(cut_facts_tac [quod,ssn,ssn RS (valid_session RS isValidSession_2')] 1);
be conjE 1; be exE 1;
by(REPEAT(etac conjE 1 ORELSE etac exE 1));
be contrapos2 1;
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(asm_simp_tac (simpset() addsimps [Let_def,asSet_def,image_def,maplet_def])1);
by(stac if_not_P 1);
by(Blast_tac 1);
by(thin_tac "accept_read_prikey = ?X" 1);
by(res_inst_tac
   [("s","xa"),
    ("t","SessionManager.choose %^ {y. y:dom ssn_tbl & sid:dom(ssn_tbl %^ y)}")] ssubst 1);
be (invert RS (ssn RS choose_unique)) 1; ba 1;
by(case_tac "x =xa" 1);
by(ALLGOALS(Asm_simp_tac));
be swap 1;
by(ALLGOALS(Asm_full_simp_tac));
qed"sid_in_Check_implies_sid_in_ssn_tbl";



val [valid_session,ssn_c, uid_c, invert] = goal SessionManager.thy
"[| (sid, write_siglog, ssn_tbl) : isValidSession_;                                \
\   ssn_tbl : SESSION_TABLE; uid : dom ssn_tbl;                                   \
\   ! x: dom ssn_tbl. ! y: dom ssn_tbl.                                           \
\        (? s. s:dom(ssn_tbl %^ x) & s:dom(ssn_tbl %^ y))  =+=> (x = y)|]         \
\ ==> (sid : dom(snd(CheckValidofSession %^ (sid,write_siglog,ssn_tbl)) %^ uid))   \
\     = (sid : dom (ssn_tbl %^ uid))";
by(cut_facts_tac [ssn_c,ssn_c RS (valid_session RS isValidSession_3')] 1);
be conjE 1; be exE 1;
by(REPEAT(etac conjE 1 ORELSE etac exE 1));
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(asm_simp_tac (simpset() addsimps [Let_def,asSet_def,image_def,maplet_def])1);
by(stac if_not_P 1);
by(Blast_tac 1);
by(res_inst_tac [("s","x"),("t","SessionManager.choose %^ ?X")] subst 1);
by(ALLGOALS(Asm_simp_tac));
br (invert RS (ssn_c RS (choose_unique RS sym))) 1; ba 1; ba 1;
by(case_tac "sid : dom (ssn_tbl %^ uid)" 1);
by(ALLGOALS(Asm_simp_tac));
by(HINT " x = uid" (K all_tac) 1);
by(HINT " uid ~= x" (K all_tac) 3);
by(ALLGOALS(Asm_simp_tac));
be (stripS invert) 1;
br uid_c 1;
by(Blast_tac 1);
be swap 1;
by(Asm_full_simp_tac 1);
qed "sid_ind_dom_CheckValidofSession_inv2";



(* VERSCHOENERUNGSVERSUCH: why not "more intuitive" SessionManager invariant:

val [] = goal SessionManager.thy
"(! x:dom session_table.                                               \
\        ! s:dom (session_table %^ x). dom (session_table %^ x) = {s}) \
\ =                                                                    \
\ (! x:dom session_table. card(dom (session_table %^ x)) <= Suc 0)";
auto();
by(eres_inst_tac [("x","x")] ballE 1);
auto();
by(case_tac "dom (session_table %^ x) = {}" 1);
auto();
by(eres_inst_tac [("x","fst xa")] ballE 1);
auto();
by(eres_inst_tac [("x","x")] ballE 1);
auto();
by(asm_full_simp_tac (HOL_ss addsimps [le_eq_less_or_eq]) 1);
auto();

... because it does not hold !

*)

*)

