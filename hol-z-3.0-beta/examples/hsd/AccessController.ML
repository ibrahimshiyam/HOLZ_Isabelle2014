(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * AccessController.ML --- Access Controller and Hysteresis Signature Generator
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
(* $Id: AccessController.ML 6743 2007-08-03 06:39:08Z brucker $ *)


(* cd "holz";
   use_holz "AccessController";

 *)
(*
toToplevel AccessController.axdefs;
toToplevel AccessController.schemes;

Add_axdefs_TC (map snd AccessController.axdefs);



val prems = goal AccessController.thy
"[| uid ~: dom acc_cnt_lst ; ssn_tbl : SESSION_TABLE; ssn_IDs: %F SESSION_ID; \
\   hpw:seq CHAR; acc_cnt_lst : ACCESS_CONTROL_LIST |] ==>                    \
\ AuthenticateUser %^ (uid,hpw,acc_cnt_lst,ssn_tbl,ssn_IDs) = NO_USER_ERR";
by(cut_facts_tac ((AuthenticateUser_axdef RS DECL_D2)::prems) 1);
auto();
qed"AuthenticateUser_F1";
Addsimps[AuthenticateUser_F1];


val prems = goal AccessController.thy
"!! uid. [| uid : dom acl ; hpw ~= ?F(acl%^(uid));  sIDs: %F SESSION_ID;     \
\           hpw:seq CHAR; uid : dom ssn_tbl; ssn_tbl : SESSION_TABLE;        \
\           acl : ACCESS_CONTROL_LIST |] ==>  \
\ AuthenticateUser %^ (uid,hpw,acl,ssn_tbl,sIDs) = INVALID_PW_ERR";
by(cut_facts_tac [AuthenticateUser_axdef RS DECL_D2] 1);
by (REPEAT (etac ballE 1));
br trans 1;ba 1;
by(Asm_simp_tac 1);
by(stac if_P 1); ba 1;auto();
bind_thm("AuthenticateUser_F2",uresult());
(* trick proof that synthesizes projection condition that can
   not be parsed in this setting ... *)
Addsimps[AuthenticateUser_F2];


val prems = goal AccessController.thy
"!! uid. [| uid : dom acl ; hpw = ?F(acl%^(uid)); sIDs : %F SESSION_ID;     \
\   hpw:seq CHAR; ssn_tbl : SESSION_TABLE; acl : ACCESS_CONTROL_LIST |] ==> \
\ AuthenticateUser %^ (uid,hpw,acl,ssn_tbl,sIDs) =                          \
\ RegistSessionInformation %^ (uid,ssn_tbl,sIDs)";
by(cut_facts_tac [AuthenticateUser_axdef RS DECL_D2] 1);
by (REPEAT (etac ballE 1));
br trans 1;ba 1;
by(Asm_simp_tac 1);
by(stac if_not_P 1); back(); back();
auto();
bind_thm("AuthenticateUser_S1",uresult());
(* trick proof that synthesizes projection condition that can
   not be parsed in this setting ... *)
Addsimps[AuthenticateUser_S1];

(* we refine these rules further, i.e. we also unfold the
   RegistSessionInformation predicate up to the primitives ...
   And finally block the prover from automatically unfolding
   RegistSessionInformation such that no interference with
   the newly derived rules may occur. *)

val prems = goal AccessController.thy
"!! uid. [| uid : dom acl ; hpw = ?F(acl%^(uid)); ssn_IDs : %F SESSION_ID;  \
\           hpw:seq CHAR;  uid : dom ssn_tbl; ssn_tbl : SESSION_TABLE;      \
\           acl : ACCESS_CONTROL_LIST                          |] ==>       \
\ AuthenticateUser %^ (uid,hpw,acl,ssn_tbl,ssn_IDs) = SAME_USER_ERR";
auto();
by(stac if_not_P 1);
auto();
bind_thm("AuthenticateUser_F3",uresult());
Addsimps[AuthenticateUser_F3];

(* Enlists the conditions of success:
   - uid is defined in the access control list
   - the user is authenticated (the passwd phw matches the one
     stored in the acl)
   - uid is fresh (i.e. not already logged in)
 *)
val prems = goal AccessController.thy
"!! uid. [| uid : dom acl ; hpw = ?F(acl%^(uid));                       \
\           ssn_IDs : %F SESSION_ID; hpw:seq CHAR; uid ~: dom ssn_tbl;  \
\           ssn_tbl : SESSION_TABLE; acl : ACCESS_CONTROL_LIST |] ==>   \
\ AuthenticateUser %^ (uid,hpw,acl,ssn_tbl,ssn_IDs) = new %^ ssn_IDs";
auto();
by(stac if_not_P 1);
auto();
bind_thm("AuthenticateUser_Success",uresult());
Addsimps[AuthenticateUser_Success];

(* will no longer automatically unfold def of RegistSessionInformation *)
Delsimps[stripS(RegistSessionInformation_axdef RS DECL_D2)];




val prems = goal AccessController.thy
"!! uid. [| sid : SESSION_ID; ssn_tbl : SESSION_TABLE;       \
\           pri_key_lst: PRI_KEY_LIST |] ==>                 \
\   ((sid,read_prikey,ssn_tbl) ~: isValidSession_) -->       \
\   ((sid,ssn_tbl,pri_key_lst) : ReadPrivateKeyFailure_)";
auto();
qed"isValidSessionVSReadPrivateKeyFailure1";


val prems = goal AccessController.thy
"!! uid. [| (sid,ssn_tbl,pri_key_lst) ~: ReadPrivateKeyFailure_; \
\            sid : SESSION_ID; ssn_tbl : SESSION_TABLE;          \
\           pri_key_lst: PRI_KEY_LIST |] ==>                     \
\   ((sid,read_prikey,ssn_tbl) : isValidSession_)";
be swap 1;
br (isValidSessionVSReadPrivateKeyFailure1 RS mp) 1;
auto();
qed"not_ReadPrivateKeyFailure1VSisValidSession";



val [p1,p2,p3,p4] = goal AccessController.thy
"[| sid : SESSION_ID; ssn_tbl : SESSION_TABLE; pri_key_lst:      \
\   PRI_KEY_LIST;                                                \
\   fst (CheckValidofSession %^ (sid, read_prikey, ssn_tbl)) :   \
\           dom pri_key_lst |] ==>                               \
\                                                                \
\ ((sid,ssn_tbl,pri_key_lst) : ReadPrivateKeyFailure_) -->       \
\  ((sid,read_prikey,ssn_tbl) ~: isValidSession_) ";
by(cut_facts_tac [p1,p2,p3] 1);
auto();
by(rotate_tac ~3 1);
by(asm_full_simp_tac (simpset() addsimps [Let_def]) 1);
by(forward_tac [p4 RS pri_key_lst_apply_not_NULL_KEY] 1);
auto();
qed"isValidSessionVSReadPrivateKeyFailure2";



(* ReadSignatureRecord: Nothing to do.
   HOL-Z default setup will lead to automatic unfolds
   of ReadSignatureRecord and reduction to isValidSession,
   CheckValidofSession
   which will be treated by previously derived rules. *)
val prems = goal AccessController.thy
"!! uid. [| sid : SESSION_ID; ssn_tbl : SESSION_TABLE;                 \
\           sig_log: SIGNATURE_LOG; pri_key_lst: PRI_KEY_LIST;         \
\           (sid,read_siglog,ssn_tbl) ~: isValidSession_;              \
\           (sid,read_prikey,ssn_tbl) ~: isValidSession_ |] ==>        \
\   ((sid,ssn_tbl,pri_key_lst,sig_log) : ReadSignatureRecordFailure_)";
auto();
qed"isValidSessionVSReadSignatureRecordFailure1";




goalw Basics.thy [SESSION_TABLE_def]
" !!sid x.                                                             \
\      [| s_tab : SESSION_TABLE; sid : dom (gen_un (ran s_tab)) |]     \
\      ==> sid ~: AUTH_ERRORS";
by(asm_full_simp_tac (HOL_ss addsimps [partial_func_def,rel_def]) 1);
by(Blast_tac 1);
qed"aux4";


goalw Basics.thy [SESSION_TABLE_def]
"!!sid. [| s_tab : SESSION_TABLE; sid : dom (gen_un (ran s_tab)) |]    \
\       ==>  ? x. x : dom s_tab /\\  (sid : dom (s_tab %^ x))";
auto();
qed"aux0";



goalw AccessController.thy []
"!!sid.                                                                  \
\       [| s_tab : SESSION_TABLE;                                        \
\          sid : dom (gen_un (ran s_tab)) |]                             \
\      ==> s_tab (+) {(SessionManager.choose %^ {y. y : dom s_tab /\\    \
\                                    sid : dom (s_tab %^ y)},            \
\                      {(sid, refuse_read_prikey,                        \
\                        snd(s_tab %^ (SessionManager.choose %^          \
\                            {y. y : dom s_tab /\\ sid : dom (s_tab %^ y)\
\                            }) %^ sid))                                 \
\                      })}                                               \
\           : SESSION_TABLE";
by(simp_tac (HOL_ss addsimps [SESSION_TABLE_def]) 1);
br Partial_Func_overrid_Distr 1;
by (convert2hol_tac [SESSION_TABLE_def] 1);
by(Asm_simp_tac 1);
br conjI 1; br conjI 2;
by (convert2hol_tac [SESSION_TABLE_def] 3);
br choose_neq_NO_USER 1;
be aux4 3;
br PowI 1;
be aux1 1; ba 2;
by (forward_tac [aux0] 1); ba 1;
by(Step_tac 1);
by(eres_inst_tac [("Q","?X = {}")] contrapos2 1);
be aux2 1;
by(Blast_tac 1);
by(Blast_tac 1);
qed"aux5";



(* really ??? XXX *)
Delsimps[beta_apply_pfun,beta_apply_tfun, tfun_implies_pfun,tfun_apply,
         choose_in_X,choose_in_subset,choose_neq_NO_USER];

(* VERY TIME CONSUMING: TODO: optimize: Step 31 *)
goal AccessController.thy
"!!sid.[| s_tab : SESSION_TABLE; pkl : PRI_KEY_LIST;            \
\         ! x: dom s_tab. ! y: dom s_tab.                       \
\              (? s. s:dom(s_tab %^ x) & s:dom(s_tab %^ y))     \
\              =+=> (x = y);                                    \
\         sig_log : SIGNATURE_LOG; hms : seq CHAR |] ==>        \
\  (sid,s_tab,pkl,sig_log,hms)~:AppendSignatureRecordFailure_   \
\  =+=> ((sid, write_siglog,                                    \
\         snd(CheckValidofSession%^(sid,read_prikey,s_tab)))    \
\           : isValidSession_)";
by(stac (read_instantiate_sg (sign_of AccessController.thy)
         [("SignatureGeneration6","SignatureGeneration")]
         (stripS (AppendSignatureRecordFailure__axdef RS DECL_D2))) 1);
(* because of HOL-Z-Bug this is more complicated than necessary ... *)
by(stac (stripS(AppendSignatureRecord_axdef RS DECL_D2)) 6);
by(ALLGOALS(Asm_simp_tac));
by(ALLGOALS(asm_simp_tac (simpset() addsimps [Let_def,asSet_def,image_def,maplet_def]
                                    addsplits [expand_if])));

br impI 1;
by(case_tac "sid ~: dom (gen_un (ran s_tab))" 1);
by(Asm_simp_tac 1);
by(cut_facts_tac [excl_mid] 1);
be disjE 1;
by(stac CheckValidofSession_F2 1);ba 2;
by(ALLGOALS(Asm_full_simp_tac));
be exE 1;

by(stac (stripS(CheckValidofSession_axdef RS DECL_D2)) 1);
by(ALLGOALS(Asm_simp_tac));
by(simp_tac (simpset() addsimps  [Let_def,asSet_def,image_def,maplet_def]
                                addsplits [expand_if])1);
by(Asm_simp_tac 1);
br impI 1;
by (thin_tac "Ex ?X" 1); (* Cleanup *)

(* Unfold isValidSession, prove side-conditions. *)
by(stac (stripS (isValidSession__axdef RS DECL_D2)) 1);
by(res_inst_tac [("t","{?X}")] subst 3);
be aux5 4;
by(ALLGOALS(Asm_simp_tac));
by (convert2hol_tac [] 1);

(* Unfold CheckValidOfSession, prove side-conditions. *)
by(stac (stripS(CheckValidofSession_axdef RS DECL_D2)) 1);
by(res_inst_tac [("t","{?X}")] subst 3);
be aux5 4;
by(ALLGOALS(Asm_simp_tac));
by (convert2hol_tac [image_def] 1);

(* Unfold CheckValidOfSession, prove side-conditions. *)
by(stac if_P 1);
by(Blast_tac 1);
by(ALLGOALS(Asm_simp_tac));

(* now comes the main chunk: accept_write_siglog
   must be set in the updated table provided that
   accept_write_siglog was set in the original table. *)
by(simp_tac (simpset() addsimps  [Let_def,asSet_def,image_def, maplet_def]
                       addsplits [expand_if]) 1);
br conjI 1;
by(res_inst_tac [("x","SessionManager.choose %^ {y. y : dom s_tab & \
                      \ sid : dom (s_tab %^ y)}")] exI 1);
by(Asm_simp_tac 1);
by (convert2hol_tac [] 1);
by(eres_inst_tac [("Q","?X : isValidSession_")] contrapos2 1);
br isValidSession_3 1; ba 1;
by (convert2hol_tac [] 1);
by(ALLGOALS(Asm_full_simp_tac));
br allI 1;
br (disjCI RS (disj_commute RS iffD1)) 1;
br (disjCI RS (disj_commute RS iffD1)) 1;
by (Asm_full_simp_tac 1);
by(REPEAT (etac conjE 1));
by(eres_inst_tac [("Q","?X ~= ?Y")] contrapos2 1);
by (Asm_full_simp_tac 1);
by(stac choose_unique 1);
by(ALLGOALS(Asm_simp_tac));

br impI 1;
by(thin_tac "Ex ?X" 1);
br choose_neq_NO_USER 1;
by (Asm_full_simp_tac 1);

(* choose_neq_NO_USER has to preconditions that are proven in the
   following: A: proof of boundedness of choose-argument
              B: proof of non-emptiness of choose-argument *)
(* proof of boundedness *)
br pfunE 1;
by (asm_full_simp_tac (HOL_ss addsimps [SESSION_TABLE_def]) 1);
bd Rel_Dom_subset 1;
br subset_trans 1; ba 2;
auto();
br choose_in_subset 1;
br PowI 1;
br aux1 1;
br aux2' 2;
by (ALLGOALS Asm_simp_tac);
auto();

(* proof of ineptness *)
by(eres_inst_tac [("Q","?X = {}")] contrapos2 1);
by(asm_full_simp_tac (HOL_ss addsimps [all_not_in_conv RS sym]) 1);
by(res_inst_tac [("x","SessionManager.choose %^ {y. y : dom s_tab & \
                      \ sid : dom (s_tab %^ y)}")] exI 1);
by(Asm_simp_tac 1);
qed"AppendSignatureRecordFailure_VS_isValidSession";
(* a really cruel theorem !!! *)


goal AccessController.thy
"!!sid.[| s_tab : SESSION_TABLE; pkl : PRI_KEY_LIST |] ==>           \
\      dom (snd (CheckValidofSession %^ (sid,X,s_tab))) = dom s_tab";
by(stac (stripS(CheckValidofSession_axdef RS DECL_D2)) 1);
by(ALLGOALS(Asm_simp_tac));
by(case_tac "sid : dom (gen_un (ran s_tab))" 1);
by(ALLGOALS(Asm_simp_tac));
by(res_inst_tac [("ACCESS_TYPE","X")] ACCESS_TYPE_induct 1);
by(ALLGOALS(Asm_simp_tac));
by(ALLGOALS(asm_simp_tac (simpset() addsimps [Let_def,asSet_def,image_def,maplet_def]
                                    addsplits [expand_if])));
by(auto_tac (claset(), simpset() addsimps
                       [asSet_def, choose_in_subset,aux1,aux2,aux3]));
qed"CheckValidofSession_dom_session_table_inv";
Addsimps[CheckValidofSession_dom_session_table_inv];


goal AccessController.thy
"!! sid. [|s_tab : SESSION_TABLE; pkl : PRI_KEY_LIST |] ==>          \
\dom (snd (ReadPrivateKey %^(sid,s_tab, pkl)))  = dom s_tab";
by(stac (stripS(ReadPrivateKey_axdef RS DECL_D2)) 1);
by(ALLGOALS(Asm_simp_tac));
by(asm_simp_tac (simpset() addsimps [Let_def] addsplits [expand_if]) 1);
qed"ReadPrivateKey_dom_session_table_inv";
Addsimps[ReadPrivateKey_dom_session_table_inv];



val prems = goal AccessController.thy
"!!sid. [| ssn_tbl : SESSION_TABLE; pri_key_lst:PRI_KEY_LIST;                \
\          hms : seq CHAR; sig_log: SIGNATURE_LOG |] ==>                     \
\       ((sid, ssn_tbl, pri_key_lst, sig_log, hms)                            \
\                   ~: AppendSignatureRecordFailure_)  =+=>                   \
\       (sid, write_siglog, ssn_tbl) : isValidSession_";
by(stac (stripS(AppendSignatureRecordFailure__axdef RS DECL_D2)) 1);
by(ALLGOALS(Asm_simp_tac));
by(asm_simp_tac (simpset() addsimps [Let_def] addsplits [expand_if]) 1);
qed"notAppendSignatureRecordFailureVSisValidSession";


val [single_session, uid,x,sid,xsid,neq] = goal AccessController.thy
" [|  ! x:dom ssn_tbl.                                                    \
\             (! s. s : dom (ssn_tbl %^ x) --> dom(ssn_tbl %^  x) = {s}); \
\     uid : dom ssn_tbl;   x : dom ssn_tbl;                               \
\     sid : dom (ssn_tbl %^  uid);                                        \
\     xsid : dom (ssn_tbl %^  x);                                         \
\     sid ~= xsid |] ==>   uid ~= x";
by(cut_facts_tac [single_session, uid,sid,x,xsid,neq] 1);
be swap 1;
by(asm_full_simp_tac (simpset() addsimps [Ball_def]) 1);
by(eres_inst_tac [("x","uid")] all_dupE 1);
by(eres_inst_tac [("x","x")] allE 1);
by(hyp_subst_tac 1);
by(asm_full_simp_tac (simpset() addsimps []) 1);
by(eres_inst_tac [("x","sid")] all_dupE 1);
by(eres_inst_tac [("x","xsid")] allE 1);
be impE 1; ba 1;
be impE 1; ba 1;
by(Asm_full_simp_tac 1);
qed"single_session_implies_neqsids_implies_nequids";





goal AccessController.thy
"!! uid. \
\[| (uid : dom sig_log' & uid ~: dom sig_log) |                         \
\    (uid : dom signature_log & sig_log %^ uid ~= sig_log' %^ uid       \
\     );                                                                \
\     sig_log : SIGNATURE_LOG; acl : ACCESS_CONTROL_LIST;               \
\     pkl : PRI_KEY_LIST; ssn_tbl : SESSION_TABLE;                      \
\     (sid, read_prikey, ssn_tbl) : isValidSession_;                    \
\     (sid, write_siglog,  snd (ReadPrivateKey %^ (sid, ssn_tbl,pkl)    \
\      )):isValidSession_;                                              \
\     sig_log' = fst (snd (AppendSignatureRecord %^                     \
\                          (sid,                                        \
\                          snd (ReadPrivateKey %^ (sid, ssn_tbl, pkl)   \
\                              ),                                       \
\                          sig,                                         \
\                          sig_log)))                                   \
\  |] ==> fst (CheckValidofSession %^                                   \
\               (sid, write_siglog,                                     \
\                snd (CheckValidofSession %^ (sid,read_prikey,ssn_tbl)  \
\                    ))) = uid";
auto();
by(defer_tac 1);
by(eres_inst_tac [("Pa","?X = ?Y")] swap 1);
by(stac (stripS (AppendSignatureRecord_axdef RS DECL_D2)) 1);
by(ALLGOALS(Asm_simp_tac));
by(asm_simp_tac (simpset() addsimps [Let_def]) 1);
br (CheckValidofSession_axdef RS DECL_D1 RS tfun_apply_snd) 1;
by(ALLGOALS(Asm_simp_tac));
by(asm_simp_tac (simpset() addsimps [Let_def]) 1);
by(simp_tac (simpset() addsimps [maplet_def]) 1);
by(stac oplus_non_apply 1);
by(ALLGOALS(Asm_simp_tac));

br (neq_sym RS iffD1) 1; ba 1;
by(dres_inst_tac [("a","(uid, y)")] pair_rel_dom_fst 1);
by(eres_inst_tac [("Q","fst(uid,y) : ?X")] contrapos2 1);
by(ALLGOALS(Asm_full_simp_tac));
by(stac (stripS (AppendSignatureRecord_axdef RS DECL_D2)) 1);
by(ALLGOALS(Asm_simp_tac));
by(asm_simp_tac (simpset() addsimps [Let_def]) 1);
br (CheckValidofSession_axdef RS DECL_D1 RS tfun_apply_snd) 1;
by(ALLGOALS(Asm_simp_tac));
by(asm_full_simp_tac (simpset() addsimps [Let_def,maplet_def]) 1);
br (neq_sym RS iffD1) 1; ba 1;
qed"AppendSignatureRecord_lemma1";


(* This theorem covers the important case, that AppendSignatureRecord
   works without failure, but the user under consideration <uid>
   (having an active session) has a session identifier different to
   the one processed by AppendSignatureRecord. This means, it has to
   be shown that processing another user, say x with his session
   identifier xsid, does not change the session- and siglogtable for uid. *)

(* TIME CONSUMING: TODO: optimize *)
val [uidS,xS,sidUid,xsidx,neq,ssn_tbl,hmg,single_session,invert,sig_log,pkl,
     noReadPrivateKeyFailure,exec,noReadSignatureRecordFailure,
     noAppendSignatureRecordFailure] = goal AccessController.thy
"  [| uid : dom ssn_tbl;  x : dom ssn_tbl;                                \
\     sid : dom (ssn_tbl %^                                               \
\                uid);                                                    \
\     xsid : dom (ssn_tbl %^                                              \
\                 x);                                                     \
\     sid ~= xsid; ssn_tbl : SESSION_TABLE;hmg : seq CHAR;                \
\     ! x:dom ssn_tbl.(! s. s:dom(ssn_tbl %^ x                            \
\                                )-->dom(ssn_tbl %^ x                     \
\                                                    )={s});              \
\     ! x:dom ssn_tbl. ! y:dom ssn_tbl.                                   \
\        (? s. s : dom (ssn_tbl %^ x) & s : dom (ssn_tbl %^ y             \
\              ))=+=> x = y;                                              \
\     sig_log : SIGNATURE_LOG;pkl : PRI_KEY_LIST;                         \
\     (xsid, ssn_tbl, pkl) ~: ReadPrivateKeyFailure_;                     \
\     (sig_log', ssn_tbl') = snd (AppendSignatureRecord %^                \
\     (xsid, snd (ReadPrivateKey %^ (xsid, ssn_tbl, pkl)                  \
\                ),                                                       \
\      SignatureGeneration %^                                             \
\         (xsid, ssn_tbl, pkl, sig_log,  hmg), sig_log));                 \
\     (xsid, ssn_tbl, pkl, sig_log) ~: ReadSignatureRecordFailure_;       \
\     (xsid, ssn_tbl, pkl, sig_log, hmg) ~: AppendSignatureRecordFailure_ \
\  |]  \
\  ==> ssn_tbl' %^ uid = ssn_tbl %^ uid & sig_log' %^ uid = sig_log %^ uid";

by(cut_facts_tac [ssn_tbl,sig_log,pkl] 1);
by(forward_tac [AppendSignatureRecordFailure_VS_isValidSession RS mp] 1);
by(ALLGOALS(asm_simp_tac (simpset() addsimps
                          [invert,sig_log,hmg,noAppendSignatureRecordFailure])));
br noAppendSignatureRecordFailure 2;  br hmg 1;
by (zftac (X_in_SESSION_ID RS (noReadPrivateKeyFailure RS
                               not_ReadPrivateKeyFailure1VSisValidSession)) 1);
by(zftac isValidSession_2' 1);
by(zftac isValidSession_3' 1);
by(REPEAT(etac conjE 1 ORELSE etac exE 1));
by(cut_facts_tac [exec] 1);
by(eres_inst_tac [("Q","(sig_log', ?X) = ?Y")] contrapos2 1);
by(zstac (AppendSignatureRecord_axdef RS DECL_D2) 1);
by(zstac (ReadPrivateKey_axdef RS DECL_D2) 1);
by(simp_tac (simpset() addsimps  [asSet_def,image_def,Let_def,maplet_def]
                       addsplits [expand_if])1);
by(Asm_simp_tac 1);
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);back();
by(ALLGOALS(asm_simp_tac (simpset() addsimps  [asSet_def,image_def,Let_def,maplet_def])));
by(stac if_not_P 1);
  by(Asm_simp_tac 1);
  by(res_inst_tac [("x","xa")] exI 1);
  by(Asm_simp_tac 1);
  by(zstac (CheckValidofSession_dom_session_table_inv RS sym) 1); ba 1;

by(Asm_simp_tac 1);
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
  by(ALLGOALS(asm_simp_tac (simpset() addsimps  [asSet_def,image_def,Let_def,maplet_def])));
  by(stac if_not_P 1);
  by(Blast_tac 1);
  by(Asm_simp_tac 1);
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(ALLGOALS(asm_simp_tac (simpset() addsimps  [asSet_def,image_def,Let_def,maplet_def])));
  (* stupid type constraint reasoning: In
     ssn_tbl (+) {(choose ^ {y. y : dom ssn_tbl & xsid : dom (ssn_tbl ^ y)},
                         {(xsid, refuse_read_prikey,
                           (ssn_tbl ^ (choose ^ {y.
             y : dom ssn_tbl &
             xsid : dom (ssn_tbl ^ y)}) ^ xsid).slwa)})}
           : SESSION_TABLE
     nothing works automatic since non-determinism of choose must
     be checked against typ-constraint
  *)

  by(asm_full_simp_tac (HOL_ss addsimps [SESSION_TABLE_def,oplus_pfunI]) 1);
  br oplus_pfunI 1; ba 1;
  br pair_pfunI 1;
  br choose_in_subset 1; br PowI 1; br aux1 1;
  by(asm_full_simp_tac (HOL_ss addsimps [SESSION_TABLE_def]) 1);
  br aux2' 1;
  by(asm_full_simp_tac (HOL_ss addsimps [SESSION_TABLE_def]) 1);
  ba 1; ba 1; br aux1 1;
  by(asm_full_simp_tac (HOL_ss addsimps [SESSION_TABLE_def]) 1);
  br pair_pfunI 1;
  by(res_inst_tac [("f","ssn_tbl %^ x\
                                     \")] (Pfun_Rel RS Rel_Dom_Elem) 1);
  ba 2;
  be(pfun_apply) 1; ba 1;
  by(asm_simp_tac Z2HOL_ss 1);
  by(tc_tac 1);
(* <<<<<<<<<<<<<<<<<<<<<<<<<<< *)
by(stac if_P 1);
by(stac if_not_P 2);
by(ALLGOALS Asm_simp_tac);
(* Factoring out common subexpressions choose ^ {y. y : dom ssn_tbl & ... } *)
by(res_inst_tac [("s","x"),("t","SessionManager.choose %^ \
                                                          \ ?X")] subst 3);
back(); back();
by(res_inst_tac [("s","x"),("t","SessionManager.choose %^ \
                                                          \ ?X")] subst 4);
by(res_inst_tac [("s","x"),("t","SessionManager.choose %^ \
                                                          \ ?X")] subst 5);

by(eres_inst_tac [("Pa"," ?X & ?Y")] swap 6);
by(HINT "uid ~= x" (K ((rtac (single_session RS
                              single_session_implies_neqsids_implies_nequids) 7)
                        THEN (rtac neq 11)
                        THEN (ALLGOALS (simp_tac (HOL_ss addsimps
                             [uidS,sidUid,xS,xsidx,neq]))))) 6);
by(Asm_full_simp_tac 6); (* that's it: if uid is not x; then
                            all updates done matter only for x (but
                            not for uid). *)
(* the left-overs ... *)
by(res_inst_tac [("s","x"),("t","SessionManager.choose %^ \
                                                          \?X")] subst 1);
  br ([ssn_tbl,invert] MRS (choose_unique RS sym)) 1; ba 1; ba 1;
  by(Blast_tac 1);

br exI 1; br conjI 1; br disjI1 1; br refl 1;
  by(res_inst_tac [("s","x"),("t","SessionManager.choose %^ \
                                                            \?X")] subst 1);
  br ([ssn_tbl,invert] MRS (choose_unique RS sym)) 1; ba 1; ba 1;
  by(ALLGOALS Asm_simp_tac);
  by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
  by(asm_simp_tac (simpset() addsimps
                            [asSet_def,image_def,Let_def,maplet_def])1);
  by(stac if_not_P 1);
    by(Blast_tac 1);
    by(Asm_simp_tac 1);
      by(res_inst_tac [("s","x"),("t","SessionManager.choose %^ \
                                                                \?X")] subst 1);
      br ([ssn_tbl,invert] MRS (choose_unique RS sym)) 1; ba 1; ba 1;
      by(stac oplus_by_pair_apply1  1); by(Asm_simp_tac 2);
      by(thin_tac "~(?X & ?Y)" 1);
      br (((invert RS bspec) RS bspec) RS mp) 1;
      by(asm_full_simp_tac (HOL_ss addsimps [CheckValidofSession_dom_session_table_inv]) 1);
      ba 1;
      by(res_inst_tac [("x","xsid")] exI 1);
      by(Asm_full_simp_tac 1);
      bd(sid_ind_dom_CheckValidofSession_inv RS iffD1) 1;
      by(ALLGOALS Asm_simp_tac);
      br invert 1;

by(ALLGOALS(thin_tac "~(?X & ?Y)" ));
by(ALLGOALS(thin_tac "accept_write_siglog = ?X" ));
by(ALLGOALS(thin_tac "accept_read_prikey = ?X" ));
br ([ssn_tbl,invert] MRS (choose_unique RS sym)) 1; ba 1; ba 1;
by(ALLGOALS(rtac (choose_unique' RS sym)));
bd NO_USER_not_in_dom_SESSION_TABLE_rev 4; ba 4; ba 4;
bd NO_USER_not_in_dom_SESSION_TABLE_rev 2; ba 2; ba 2;
by(ALLGOALS(rtac (set_ext)));
by(ALLGOALS Asm_simp_tac);

by(ALLGOALS(rtac iffI));
by(ALLGOALS Asm_simp_tac);
by(REPEAT(etac conjE 1));
by(REPEAT(etac conjE 2));
be disjE 2;
by(ALLGOALS Asm_simp_tac);
by(ALLGOALS (eres_inst_tac [("P","xb : dom ssn_tbl")] rev_mp) ); (* to make subgoals equal *)
by(distinct_subgoals_tac);
br impI 1;
by(case_tac "xb = x" 1);
by(rotate_tac ~1 2);
by(ALLGOALS Asm_full_simp_tac);
be swap 1;
br (((invert RS bspec) RS bspec) RS mp) 1;
auto();
qed"AppendSignatureRecord_imp_nosid_nochange";


goal AccessController.thy
"!! uid. \
\[| (uid : dom sig_log' & uid ~: dom sig_log) |                         \
\    (uid : dom signature_log & sig_log %^ uid ~= sig_log' %^ uid);     \
\     sig_log : SIGNATURE_LOG; acl : ACCESS_CONTROL_LIST;               \
\     pkl : PRI_KEY_LIST; ssn_tbl : SESSION_TABLE;                      \
\     (sid, read_prikey, ssn_tbl) : isValidSession_;                    \
\     (sid, write_siglog,                                               \
\          snd (ReadPrivateKey %^ (sid, ssn_tbl,pkl))):isValidSession_; \
\     ! x:dom ssn_tbl. ! y:dom ssn_tbl.                                 \
\           (? s. s:dom (ssn_tbl %^ x) & s:dom (ssn_tbl %^ y))=+=> x=y; \
\     sig_log' = fst (snd (AppendSignatureRecord %^                     \
\                          (sid,                                        \
\                          snd (ReadPrivateKey %^ (sid, ssn_tbl, pkl)   \
\                              ),                                       \
\                          sig,                                         \
\                          sig_log)))                                   \
\  |] ==> fst(CheckValidofSession%^(sid,read_prikey,ssn_tbl)            \
\            ) = uid";
by(zftac isValidSession_2' 1);
by(zftac isValidSession_3' 1);
by(eres_inst_tac [("Q","sig_log' = ?Y")] contrapos2 1);
by(zstac (AppendSignatureRecord_axdef RS DECL_D2) 1);
by(zstac (ReadPrivateKey_axdef RS DECL_D2) 1);
by(ALLGOALS(asm_simp_tac (simpset() addsimps  [Let_def,maplet_def]
                                    addsplits [expand_if])));
be conjE 1;
by(eres_inst_tac [("Q","(sid,write_siglog,?X) : ?Y")] contrapos2 1);
by(zstac (ReadPrivateKey_axdef RS DECL_D2) 1);
by(ALLGOALS(asm_full_simp_tac (simpset() addsimps [Let_def])));
be swap 1;
by(rotate_tac ~1 1);
by(ALLGOALS(asm_full_simp_tac (simpset() addsimps [Let_def])));
by(REPEAT (etac conjE 1));
by(hyp_subst_tac 1);

be disjE 1;
by(REPEAT (etac conjE 1));
by(REPEAT (etac conjE 2));

by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(zstac (CheckValidofSession_axdef RS DECL_D2) 2);
by(ALLGOALS(asm_full_simp_tac
            (simpset() addsimps [Let_def,asSet_def,image_def,maplet_def])));

br choose_unique 1;
br choose_unique 5;
by(ALLGOALS(Asm_simp_tac));
be disjE 2;be disjE 1;
by(Blast_tac 4);
by(Blast_tac 2);
by(hyp_subst_tac 1);by(hyp_subst_tac 2);

(* one: fst (CheckValidofSession %^ (sid, write_siglog,
  snd (CheckValidofSession %^ (sid, read_prikey, ssn_tbl))))  : dom ssn_tbl *)
be exE 1;back();
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(asm_full_simp_tac
            (simpset() addsimps [Let_def,asSet_def,image_def,maplet_def])1);
by(stac if_not_P 1);
by(Asm_simp_tac 1);
by(Asm_simp_tac 2);
by(res_inst_tac [("x","x")] exI 1);
by(Asm_simp_tac 1);
br choose_in_subset 1;
br PowI 1;
be aux1 1;
by(Asm_simp_tac 1);
by(asm_full_simp_tac (HOL_ss addsimps [all_not_in_conv RS sym]) 1);
by(Blast_tac 1);
by(Blast_tac 1);

(* two:  sid : dom (ssn_tbl %^ fst (CheckValidofSession %^ (sid, write_siglog,
                    snd (CheckValidofSession %^ (sid, read_prikey,
           ssn_tbl))))) *)
be exE 1;
by(REPEAT (etac conjE 1));
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(asm_full_simp_tac
            (simpset() addsimps [Let_def,asSet_def,image_def,maplet_def])1);
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(asm_full_simp_tac
            (simpset() addsimps [Let_def,asSet_def,image_def,maplet_def])1);
by(stac if_not_P 1);
by(Blast_tac 1);
by(res_inst_tac[("s","x")] (choose_unique' RS ssubst) 1);
br set_ext 1;
br iffI 1;
by(ALLGOALS(Asm_full_simp_tac));
by(res_inst_tac[("s","x")] (choose_unique' RS ssubst) 2);
by(asm_simp_tac (simpset() addsimps [Overrid_Domain]) 4);
by(ALLGOALS(Asm_simp_tac));
be conjE 1;
by(eres_inst_tac [("Q","sid : dom ((ssn_tbl (+) ?X) %^ xa) ")] contrapos2 1);
by(res_inst_tac[("s","x")] (choose_unique' RS ssubst) 1);
by(Blast_tac 4);
by(Blast_tac 1);
by(Asm_simp_tac 1);
by(stac oplus_by_pair_apply2 1); ba 1;
by(eres_inst_tac [("x","x")] ballE 1);
by(eres_inst_tac [("x","xa")] ballE 1);
by(Blast_tac 2);
by(Blast_tac 2);
by(Blast_tac 1);

(* three:   uid : dom signature_log;uid ~: dom ssn_tbl ==>
          sig_log %^ uid =
          (sig_log (+) {(fst (CheckValidofSession %^ (sid, write_siglog,
                snd (CheckValidofSession %^ (sid, read_prikey, ssn_tbl)))),
                         sig)}) %^ uid   *)
by(eres_inst_tac [("Pa","sig_log %^ uid = ?X")] swap 1);
be exE 1;
by(REPEAT (etac conjE 1));
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(asm_full_simp_tac
            (simpset() addsimps [Let_def,asSet_def,image_def,maplet_def])1);
by(stac oplus_by_pair_apply2 1); br refl 2;
br (neq_sym RS iffD1) 1;
br choose_neq_X 1;
by(Blast_tac 3);
br PowI 1;
be aux1 1;
by(simp_tac (HOL_ss addsimps [all_not_in_conv RS sym]) 1);
by(res_inst_tac [("x","x")] exI 1);
by(Asm_simp_tac 1);
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(asm_simp_tac
            (simpset() addsplits [expand_if]
                       addsimps  [Let_def,asSet_def,image_def,maplet_def])1);
br impI 1;
by(stac oplus_by_pair_apply1 1);
br sym 1;
br choose_unique 1;
by(ALLGOALS(Asm_simp_tac));


(* four:   uid : dom signature_log;sid ~: dom (ssn_tbl %^ uid) ==>
          sig_log %^ uid =
          (sig_log (+) {(fst (CheckValidofSession %^ (sid, write_siglog,
                snd (CheckValidofSession %^ (sid, read_prikey, ssn_tbl)))),
                         sig)}) %^ uid  *)
by(eres_inst_tac [("Pa","sig_log %^ uid = ?X")] swap 1);
be exE 1;
by(REPEAT (etac conjE 1));
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(asm_full_simp_tac
            (simpset() addsimps [Let_def,asSet_def,image_def,maplet_def])1);

by(stac oplus_by_pair_apply2 1); br refl 2;
br (neq_sym RS iffD1) 1;
br choose_neq_X 1;
br PowI 1;
be aux1 1;
by(simp_tac (HOL_ss addsimps [all_not_in_conv RS sym]) 1);
by(res_inst_tac [("x","x")] exI 1);
by(Asm_simp_tac 1);
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(asm_simp_tac
            (simpset() addsplits [expand_if]
                       addsimps  [Let_def,asSet_def,image_def,maplet_def])1);
br impI 1;
by(stac oplus_by_pair_apply1 1);
br sym 1;
br choose_unique 1;
by(ALLGOALS(Asm_simp_tac));
br disjI2 1;
by(zstac (CheckValidofSession_axdef RS DECL_D2) 1);
by(asm_simp_tac
            (simpset() addsplits [expand_if]
                       addsimps  [Let_def,asSet_def,image_def,maplet_def])1);
br impI 1;
by(stac oplus_by_pair_apply2 1);
by(ALLGOALS(Asm_simp_tac));
br (neq_sym RS iffD1) 1;
br choose_neq_X 1;
br PowI 1;
be aux1 1;
by(Blast_tac 2);
by(simp_tac (HOL_ss addsimps [all_not_in_conv RS sym]) 1);
by(res_inst_tac [("x","x")] exI 1);
by(Asm_simp_tac 1);
qed"AppendSignatureRecord_lemma2";
(* a really cruel lemma. With all bells and whistles over CheckValidofSession.
   And what you never wanted to know about it ... ;-) *)
*)
