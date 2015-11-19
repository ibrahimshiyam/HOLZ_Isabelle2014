(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * Analysis.ML ---
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
(* $Id: Analysis.ML 6743 2007-08-03 06:39:08Z brucker $ *)


(* cd "holz";
   use_holz "Analysis";
 *)
(*

toToplevel Analysis.axdefs;
toToplevel Analysis.schemes;

Add_axdefs_TC (map snd Analysis.axdefs);

Delsimps[No_Dom_Restr]; (* seems to be unmovable ... *)



val prems = goalw Analysis.thy [Traces_def,Init_def]
"!!t. t : Traces ==>                                                 \
\     EX acces_control_list pri_key_list.                            \
\            acces_control_list : ACCESS_CONTROL_LIST &              \
\            pri_key_list : PRI_KEY_LIST &                           \
\            t %^ #0 = (acces_control_list, pri_key_list, {}, {}, {})";
by (convert2hol_tac [InitState_def,SessionManagerInit_def,AccessController_def,
                     HysteresisSignatureInit_def,AccessControllerInit_def] 1);
auto();
qed "traces_init_D1";
Addsimps[traces_init_D1];



zgoalw Analysis.thy [Traces_def]
"t : Traces =+=>   t : (%N ---> GlobalState)";
by(stripS_tac 1);
by (convert2hol_tac [] 1);
auto();
qed "traces_init_D2";
Addsimps[stripS traces_init_D2];


val prems = goalw Analysis.thy []
"!!t.[| t : Traces; i : %N |] ==>                                      \
\     EX acl_l pky_l sIDs s_tab sig_log. ((t %^ i) =                   \
\               (acl_l,pky_l,sIDs,s_tab,sig_log) &                     \
\                SessionManager (sIDs,s_tab) &                         \
\                (HysteresisSignature sig_log &                        \
\                 AccessController (acl_l,pky_l))) ";
bd (stripS traces_init_D2) 1;
bd tfun_apply 1; ba 1;
by (convert2hol_tac [GlobalState_def] 1);
by(res_inst_tac [("p","t %^ i")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","y")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","ya")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yb")] PairE 1);
by(rotate_tac ~1 1);
auto();
qed "trace_GlobalState";


val prems = goalw Analysis.thy []
"!!t.[| t : Traces; i : %N |] ==>                                      \
\     EX acl_l pky_l sIDs s_tab sig_log. ((t %^ (i + #1)) =            \
\               (acl_l,pky_l,sIDs,s_tab,sig_log) &                     \
\                SessionManager (sIDs,s_tab) &                         \
\                (HysteresisSignature sig_log &                        \
\                 AccessController (acl_l,pky_l))) ";
br trace_GlobalState 1;
auto();
qed "trace_GlobalStateSuc";

(* Destruction rule that performs projection. *)
val prems = goalw Analysis.thy [Traces_def,Next_def]
"!!x. [| System x |] ==>                                               \
\      EX  MsgHash_I SID_O SID_I                                       \
\          acl acl' mess_I pwd_I pkl                                   \
\          pkl' result_O sIDs sIDs'                                    \
\          ses_id_O ses_id_I s_tab s_tab'                              \
\          sig_O sig_log sig_log' uid_I uname_I.                       \
\     x =  (MsgHash_I, SID_O, SID_I,                                   \
\          acl, acl', mess_I, pwd_I, pkl,                              \
\          pkl', result_O, sIDs, sIDs',                                \
\          ses_id_O, ses_id_I, s_tab, s_tab',                          \
\          sig_O, sig_log, sig_log', uid_I, uname_I)";
by(res_inst_tac [("p","x")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","y")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","ya")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yb")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yc")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yd")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","ye")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yf")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yg")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yh")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yi")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yj")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yk")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yl")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","ym")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yn")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yo")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yp")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yq")] PairE 1);
by(rotate_tac ~1 1);
by(res_inst_tac [("p","yr")] PairE 1);
by(rotate_tac ~1 1);
auto();
qed "System_Project";



(* The following big chunk extends the System Decomposition Theorem
   to a theorem over subsequent trace points: Provided that a property
   holds for four system transition scenarios, it holds for all of them
   (the other are impossible). *)


val [p1,p2,p3,p4,p5,p6] = goalw Analysis.thy [Traces_def,Next_def]
"[|t : Traces; i : %N;                                          \
\  !! acl acl' mess_I pwd_I pkl pkl' sIDs sIDs' s_tab s_tab'    \
\     sig_log sig_log'  SID_O  ses_id_O sig_O uid_I uname_I     \
\     x xa xb xc xd xe xf xg y.                                 \
\     [| t %^ i = (acl, pkl, sIDs, s_tab, sig_log);             \
\        t %^ (i + #1) = (acl',pkl',sIDs',s_tab',sig_log');     \
\        SNAME DARMA (x,xa,xb,xc,xd,xe,xf,xg,y);                \
\        SNAME AuthenticateUserW                                \
\          (x,xa,xb,xc,xd,xe,xf,xg,y,pwd_I,ses_id_O,uid_I);     \
\        SNAME AuthenticateUserL                                \
\         (x,xa,xb,xc,SID_O,xd,xe,xf,xg,y,acl,acl',pwd_I,       \
\          pkl,pkl',sIDs,sIDs',s_tab,s_tab',sig_log,sig_log',   \
\          uname_I)|]                                           \
\     ==> P (acl, pkl, sIDs, s_tab, sig_log)                    \
\           (acl', pkl', sIDs', s_tab', sig_log');              \
\                                                               \
\  !! acl acl' mess_I pwd_I pkl pkl' sIDs sIDs' s_tab s_tab'    \
\     sig_log sig_log' ses_id_I sig_O                           \
\     x xa xb xc xd xe xf xg y.                                 \
\     [| t %^ i = (acl, pkl, sIDs, s_tab, sig_log);             \
\        t %^ (i + #1) = (acl',pkl',sIDs',s_tab',sig_log');     \
\        SNAME DARMA (x,xa,xb,xc,xd,xe,xf,xg,y);                \
\        SNAME GenerateSignatureW                               \
\           (x,xa,xb,xc,xd,xe,xf,xg,y,mess_I,ses_id_I,sig_O);   \
\        SNAME NopOperationL                                    \
\           (x,xa,xb,xc,xd,xe,xf,xg,y,acl,acl',pkl,pkl',sIDs,   \
\            sIDs', s_tab, s_tab', sig_log, sig_log') |]        \
\     ==> P (acl, pkl, sIDs, s_tab, sig_log)                    \
\           (acl', pkl', sIDs', s_tab', sig_log');              \
\                                                               \
\  !! acl acl' mess_I pwd_I pkl pkl' sIDs sIDs' s_tab s_tab'    \
\     sig_log sig_log' MsgHash_I SID_I  ses_id_I sig_O          \
\     x xa xb xc xd xe xf xg y.                                 \
\     [| t %^ i = (acl, pkl, sIDs, s_tab, sig_log);             \
\        t %^ (i + #1) = (acl',pkl',sIDs',s_tab',sig_log');     \
\        SNAME DARMA (x,xa,xb,xc,xd,xe,xf,xg,y);                \
\        SNAME GenerateSignatureW                               \
\           (x,xa,xb,xc,xd,xe,xf,xg,y,mess_I,ses_id_I,sig_O);   \
\        SNAME GenerateSignatureL                               \
\           (x,xa,xb,MsgHash_I,xc,SID_I,xd,xe,xf,xg,y,acl,      \
\            acl',pkl,pkl',sIDs,sIDs',s_tab,s_tab',sig_O,       \
\            sig_log, sig_log')                                 \
\     |]                                                        \
\     ==> P (acl, pkl, sIDs, s_tab, sig_log)                    \
\           (acl', pkl', sIDs', s_tab', sig_log');              \
\                                                               \
\  !! acl acl' mess_I pwd_I pkl pkl' sIDs sIDs' s_tab s_tab'    \
\     sig_log sig_log' SID_I  result_O ses_id_I                 \
\     x xa xb xc xd xe xf xg y.                                 \
\     [| t %^ i = (acl, pkl, sIDs, s_tab, sig_log);             \
\        t %^ (i + #1) = (acl',pkl',sIDs',s_tab',sig_log');     \
\        SNAME DARMA (x,xa,xb,xc,xd,xe,xf,xg,y);                \
\        SNAME LogoutW (x,xa,xb,xc,xd,xe,xf,xg,y,result_O,ses_id_I);  \
\        SNAME LogoutL                                                \
\             (x,xa,xb,xc,SID_I,xd,xe,xf,xg,y,acl,acl',pkl,     \
\              pkl',result_O,sIDs,sIDs',s_tab,s_tab',sig_log,   \
\              sig_log')    |]                                  \
\     ==> P (acl, pkl, sIDs, s_tab, sig_log)                    \
\           (acl', pkl', sIDs', s_tab', sig_log')               \
\                                                               \
\|] ==>                                                         \
\                                                               \
\    P (t %^ i) (t %^ (i + #1))";
by(cut_facts_tac [p1,p2] 1);
by (convert2hol_tac [SSet_def] 1);
auto();
by(eres_inst_tac [("x","i")]  ballE 1);
auto();
by (forward_tac [System_Project] 1);
auto();
by(dtac(asm_full_simplify Z2HOL_ss(stripS SysArch_decomposition_theorem))1);
auto();
by(rtac(asm_full_simplify Z2HOL_ss p3) 1);
auto();
by(rtac(asm_full_simplify Z2HOL_ss p4) 1);
auto();
by(rtac(asm_full_simplify Z2HOL_ss p5) 1);
auto();
by(rtac(asm_full_simplify Z2HOL_ss p6) 1);
auto();
qed"State_Transition_Cases";



(* ************************************************************************** *)
(*                                                                            *)
(* Global Invariants ...                                                      *)
(*                                                                            *)
(* ************************************************************************** *)


val prems = goalw Analysis.thy []
"!!t. [|t:Traces ; i : %N |] ==>  \
\ fst(t %^ #0) = fst(t %^ i) &\
\ fst(snd(t %^ #0)) = fst(snd(t %^ i))";
by(res_inst_tac [("x","i")] naturals_induct 1);
ba 1;
by(ALLGOALS(Asm_simp_tac));
be State_Transition_Cases 1;
by(ALLGOALS(Asm_simp_tac));
by(zdtac AuthenticateUserL_inv_state_components 1);
by(zdtac NopOperationL_inv_state_components 1);
by(zdtac GenerateSignatureL_inv_state_components 1);
by(zdtac LogoutL_inv_state_components 1);
qed"acl_and_pkl_inv0";


(* Now we bring this in a form that can be nicely
   printed:

 1. !!t. [| t : Traces; i : %N |]
         ==> (t %^ #0).access_control_list = (t %^ i).access_control_list /\
             (t %^ #0).private_key_list = (t %^ i).private_key_list
 *)
val prems = goalw Analysis.thy []
"!!t. [|t:Traces ; i : %N |] ==>                               \
\  PROJ(t %^ #0)(fst)(''access_control_list'') =               \
\  PROJ(t %^ i) (fst)(''access_control_list'') &               \
\  PROJ(t %^ #0)(% x. fst(snd(x)))(''private_key_list'') =     \
\  PROJ(t %^ i) (% x. fst(snd(x)))(''private_key_list'')";
by (convert2hol_tac [SSet_def] 1);
br  acl_and_pkl_inv0 1;
auto();
qed"acl_and_pkl_inv";



(* printed nicely, the following system invariant reads as follows:

    "[| ?t : Traces; ?i : %N |]
    ==> dom ((?t %^ ?i).signature_log) <=
        dom ((?t %^ (?i + #1)).signature_log)"

    This global system invariant motivates the precise definition for
    siglogChanges. Strictly speaking, the case

       uid : dom(s1.signature_log) & uid ~: dom(s2.signature_log)

    would represent a "change" of the log. Due to signature_log_mono,
    this case is inherently impossible.

 *)

val prems = goalw Analysis.thy []
"!!t. [|t:Traces ; i : %N |] ==>                                        \
\  dom(PROJ(t %^ i)       (% x. snd(snd(snd(snd(x)))))(''signature_log'')) <= \
\  dom(PROJ(t %^ (i + #1))(% x. snd(snd(snd(snd(x)))))(''signature_log''))";
by (convert2hol_tac [SSet_def] 1);
be State_Transition_Cases 1;
by(ALLGOALS(Asm_simp_tac));
(* 1. !!t acl acl' pwd_I pkl pkl' sIDs sIDs' s_tab s_tab' sig_log sig_log'
       SID_O ses_id_O uid_I uname_I x xa xb xc xd xe xf xg y.
       [| i : %N; t %^ i = (acl, pkl, sIDs, s_tab, sig_log);
          t %^ (i + #1) = (acl', pkl', sIDs', s_tab', sig_log');
          SNAME DARMA (x, xa, xb, xc, xd, xe, xf, xg, y);
          SNAME AuthenticateUserW
           (x, xa, xb, xc, xd, xe, xf, xg, y, pwd_I, ses_id_O, uid_I);
          SNAME AuthenticateUserL
           (x, xa, xb, xc, SID_O, xd, xe, xf, xg, y, acl, acl', pwd_I, pkl,
            pkl', sIDs, sIDs', s_tab, s_tab', sig_log, sig_log', uname_I) |]
       ==> dom sig_log <= dom sig_log'
 2. !!t acl acl' mess_I pkl pkl' sIDs sIDs' s_tab s_tab' sig_log sig_log'
       ses_id_I sig_O x xa xb xc xd xe xf xg y.
       [| i : %N; t %^ i = (acl, pkl, sIDs, s_tab, sig_log);
          t %^ (i + #1) = (acl', pkl', sIDs', s_tab', sig_log');
          SNAME DARMA (x, xa, xb, xc, xd, xe, xf, xg, y);
          SNAME GenerateSignatureW
           (x, xa, xb, xc, xd, xe, xf, xg, y, mess_I, ses_id_I, sig_O);
          SNAME NopOperationL
           (x, xa, xb, xc, xd, xe, xf, xg, y, acl, acl', pkl, pkl', sIDs,
            sIDs', s_tab, s_tab', sig_log, sig_log') |]
       ==> dom sig_log <= dom sig_log'
 3. !!t acl acl' mess_I pkl pkl' sIDs sIDs' s_tab s_tab' sig_log sig_log'
       MsgHash_I SID_I ses_id_I sig_O x xa xb xc xd xe xf xg y.
       [| i : %N; t %^ i = (acl, pkl, sIDs, s_tab, sig_log);
          t %^ (i + #1) = (acl', pkl', sIDs', s_tab', sig_log');
          SNAME DARMA (x, xa, xb, xc, xd, xe, xf, xg, y);
          SNAME GenerateSignatureW
           (x, xa, xb, xc, xd, xe, xf, xg, y, mess_I, ses_id_I, sig_O);
          SNAME GenerateSignatureL
           (x, xa, xb, MsgHash_I, xc, SID_I, xd, xe, xf, xg, y, acl, acl',
            pkl, pkl', sIDs, sIDs', s_tab, s_tab', sig_O, sig_log,
            sig_log') |]
       ==> dom sig_log <= dom sig_log'
 4. !!t acl acl' pkl pkl' sIDs sIDs' s_tab s_tab' sig_log sig_log' SID_I
       result_O ses_id_I x xa xb xc xd xe xf xg y.
       [| i : %N; t %^ i = (acl, pkl, sIDs, s_tab, sig_log);
          t %^ (i + #1) = (acl', pkl', sIDs', s_tab', sig_log');
          SNAME DARMA (x, xa, xb, xc, xd, xe, xf, xg, y);
          SNAME LogoutW
           (x, xa, xb, xc, xd, xe, xf, xg, y, result_O, ses_id_I);
          SNAME LogoutL
           (x, xa, xb, xc, SID_I, xd, xe, xf, xg, y, acl, acl', pkl, pkl',
            result_O, sIDs, sIDs', s_tab, s_tab', sig_log, sig_log') |]
       ==> dom sig_log <= dom sig_log'

 *)

by(zdtac AuthenticateUserL_inv_state_components 1);
by(zdtac NopOperationL_inv_state_components 1);
(* by(zftac GenerateSignatureL_inv_state_components 1); *)
by(zdtac GenerateSignatureL_siglog_mono 1);
by(zdtac LogoutL_inv_state_components 1);
(* No subgoals! *)
qed"signature_log_mono";


val prems = goalw Analysis.thy []
"!!t. [|t:Traces ; i : %N |] ==>                                        \
\  dom(PROJ(t %^ i)       (% x. snd(snd(snd(snd(x)))))(''signature_log'')) <= \
\  dom(PROJ(t %^ (i + $# z))(% x. snd(snd(snd(snd(x)))))(''signature_log''))";
by(induct_tac "z" 1);
by(ALLGOALS(Asm_simp_tac));
be subset_trans 1;
by(simp_tac (HOL_ss addsimps [zsuc_def]) 1);
by(res_inst_tac [("t"," $# 1")] subst 1);
be signature_log_mono 2;
by(ALLGOALS(Asm_simp_tac));
qed"signature_log_mono_trace";


(* nicely printed, the following theorem looks as:

!!t. [| t : Traces; i : %N |]
     ==> (t %^ i).session_IDs <= (t %^ (i + #1)).session_IDs

  i.e. the system is monotone in the session_IDs parameter. *)

val prems = goalw Analysis.thy []
"!!t. [|t:Traces ; i : %N |] ==>                                     \
\  PROJ(t %^ i)       (% x. fst(snd(snd(x))))(''session_IDs'') <=    \
\  PROJ(t %^ (i + #1))(% x. fst(snd(snd(x))))(''session_IDs'')";
by (convert2hol_tac [SSet_def] 1);
be State_Transition_Cases 1;
by(ALLGOALS(Asm_simp_tac));
by(zdtac (get_conj HSD.thy "AuthenticateUserL" 4) 1);
by(zdtac  NopOperationL_inv_state_components 2);
by(zdtac  GenerateSignatureL_inv_state_components 2);
by(zdtac  LogoutL_inv_state_components 2);
auto();
by(asm_simp_tac (simpset() addsimps [Let_def] addsplits [expand_if]) 1);
qed"session_IDs_mono";



(* More general than no_siglogChanges_at_init, in fact a
   semantic characterization of this event predicate :

   !!t n uid.
      [| t : Traces; n : %N; uid ~: dom ((t %^ n).session_table) |]
      ==> (t %^ n, t %^ (n + #1)) ~: siglogChanges %^ uid

  *)
val [] = goalw Analysis.thy []
"!!t n uid.                                                         \
\   [| t : Traces; n : %N;                                          \
\      uid ~: dom (PROJ (t %^ n)                                    \
\                 (% x. fst(snd(snd(snd(x)))))                      \
\                 ''session_table'')                                \
\   |] ==> (t %^ n, t %^ (n + #1)) ~: siglogChanges %^ uid";
by(zstac (siglogChanges_axdef RS DECL_D2) 1);
by(zftac traces_init_D2 1);
by(zftac traces_init_D2 2);
by(ALLGOALS(asm_simp_tac (simpset() addsimps[tfun_apply])));
br State_Transition_Cases 1;
ba 1;
by(Asm_full_simp_tac 1);
by(zdtac AuthenticateUserL_inv_state_components 1);
by(zdtac NopOperationL_inv_state_components 2);
by(zftac GenerateSignatureL_inv_state_components 2);
by(zdtac LogoutL_inv_state_components 3);
by (ALLGOALS(convert2hol_tac []));
auto(); (* exploit architectural contradictions ... *)
bd (asm_full_simplify Z2HOL_ss
           (stripS GenerateSignatureL_implies_not_siglogChanges)) 1;
bd (asm_full_simplify Z2HOL_ss
           (stripS GenerateSignatureL_implies_not_siglogChanges)) 3;
auto();
qed"uid_not_in_session_table_implies_no_siglogChanges";


(* Corollary: there will never be a siglogchange at the beginning
   of a trace *)
val prems = goalw Analysis.thy []
"[|t:Traces |] ==> (t %^ #0, t %^ #1) ~: siglogChanges %^ uid";
by(cut_facts_tac prems 1);
by(res_inst_tac [("t","#1")] subst 1);
br uid_not_in_session_table_implies_no_siglogChanges 2;
bd traces_init_D1 4;
auto();
by (convert2hol_tac [] 1);
qed"no_siglogChanges_at_init";



(* nicely printed:

   [| t:Traces;i:%N |] ==> dom ((t %^ i).signature_log) <= dom ((t %^ i).pri_key_list)
   [| t : Traces; i : %N |]
     ==> dom ((t %^ i).session_table) <= dom ((t %^ i).pri_key_list) /\
         dom ((t %^ i).signature_log) <= dom ((t %^ i).pri_key_list)
 *)

val prems = goalw Analysis.thy []
"!!t. [|t:Traces ; i : %N |] ==>                                        \
\  dom(PROJ(t %^ i)(% x. fst(snd(snd(snd(x)))))(''session_table'')) <=  \
\  dom(PROJ(t %^ i)(% x. fst(snd(x)))(''pri_key_list'')) &              \
\  dom(PROJ(t %^ i)(% x. snd(snd(snd(snd(x)))))(''signature_log'')) <=  \
\  dom(PROJ(t %^ i)(% x. fst(snd(x)))(''pri_key_list''))";
by(res_inst_tac [("x","i")] naturals_induct 1);
ba 1;
bd traces_init_D1 2;
by (ALLGOALS (convert2hol_tac [SSet_def]));
by(eres_inst_tac [("P","?X & ?Y")] rev_mp 1);
by(HINT "$# 1 = #1" (Asm_simp_tac) 1);
by(asm_simp_tac HOL_ss 1);
be State_Transition_Cases 1;
by(ALLGOALS(Asm_simp_tac));
be exE 5; be conjE 5; be exE 5;
by(Asm_full_simp_tac 5);
by(zftac AuthenticateUserL_inv_state_components 1);
by(zdtac NopOperationL_inv_state_components 2);
by(zftac GenerateSignatureL_inv_state_components 2);
by(zftac LogoutL_inv_state_components 3);
br impI 2;
by(zdtac GenerateSignatureL_implies_pri_key_list_bounds 2);
by(ALLGOALS Asm_full_simp_tac);

(* Consider LogoutL: use definition of session_table',
   unfold FreeSessionInformation, and prove that
   removing entries from s_tab does not conflict with the fact
   that s_tab is bound by pkl. *)
by(zftac (get_decl HSD.thy "LogoutL" 1) 2);
by(asm_full_simp_tac (HOL_ss addsimps[DELTA_def]) 2);
by(REPEAT (etac conjE 2));
by(zdtac (get_decl HSD.thy "SessionManager" 1) 2);
by(zdtac (get_conj HSD.thy "LogoutL" 2) 2);
by(dres_inst_tac [("f","snd"),("x","(xc,s_tab')")] arg_cong 2);
by(ALLGOALS Asm_full_simp_tac);
by(zstac (FreeSessionInformation_axdef RS DECL_D2) 2);
by(simp_tac (simpset() addsimps  [Let_def,maplet_def,asSet_def,image_def]
                       addsplits [expand_if]) 2);
by(thin_tac "s_tab' = ?X" 2);
by(Blast_tac 2);

(* Consider AuthenticateUser: an entry is made, but this results
   from fst(CheckValidOfSession) and thus is bound by  dom pkl. *)
(* Saturation >>> *)
by(zftac (get_decl HSD.thy "AuthenticateUserL" 1) 1);
by(zftac (get_decl HSD.thy "AuthenticateUserL" 2) 1);
by(zftac (get_decl HSD.thy "AuthenticateUserL" 3) 1);
by(asm_full_simp_tac (HOL_ss addsimps[XI_def,DELTA_def]) 1);
by(REPEAT (etac conjE 1));
by(zftac (get_decl HSD.thy "SessionManager" 2) 1);
by(zdtac (get_decl HSD.thy "SessionManager" 1) 1);
by(zdtac (get_decl HSD.thy "DARMA" 4) 1);
(* <<< Saturation  *)
(* now comes the sun *)
by(zftac (get_conj HSD.thy "AuthenticateUserL" 3) 1);
by(zdtac (get_conj HSD.thy "AuthenticateUserL" 2) 1);
by(hyp_subst_tac 1);
by(thin_tac "s_tab' = ?X" 1);
by(thin_tac "t %^ x = ?X" 1);
by(thin_tac "t %^ (x+ #1) = ?X" 1);
by(thin_tac "xa = ?X" 1);
by(forward_tac [hash_axdef RS DECL_D1 RS conjunct1 RS tfun_apply] 1);
by(zftac (get_decl HSD.thy "AccessController" 1) 1);
by(zftac (get_decl HSD.thy "AccessController" 2) 1);
by(zdtac (get_conj HSD.thy "AccessController" 1) 1);
by(zstac (AuthenticateUser_axdef RS DECL_D2) 1);
by(asm_simp_tac (simpset() addsimps [AUTH_ERRORS_def,maplet_def]
                           addsplits [expand_if]) 1);
qed"dom_tabs_contained_in_dom_pri_key_list";





(* now comes the first half of the HSD_1 proofs:
   if a user never logs in, he will not be in the session table.

   "[| t : Traces; n : %N |]
    ==> (! k: #0 .. n - #1. (t%^k,t%^(k + #1)) ~: userDoesLogin%^uid) =+=>
        uid ~: dom ((t%^n).session_table)"

   This corresponds to what has been proven in the SPIN case study.

 *)
(* XXX *)
val prems = goalw Analysis.thy []
"!!t. [|t:Traces ; n : %N |] ==>                                                 \
\     (!k : #0 .. n - #1.  (t %^ k, t %^ (k + #1)) ~: userDoesLogin %^ uid) -->  \
\     uid ~: dom (PROJ (t %^ n)                                                  \
\                      (% x. fst(snd(snd(snd(x)))))                                  \
\                      ''session_table'')";
by(res_inst_tac [("x","n")] naturals_induct 1); ba 1;
by(ALLGOALS Asm_full_simp_tac);
(* First part: *Base* exploit inital state. *)
bd traces_init_D1 2;
by (convert2hol_tac [] 2);
auto();

(* Second part: (* Step *). A: exploit contradicting assumptions: *)
by(eres_inst_tac [("x","k")] ballE 1);
auto();
by(eres_inst_tac [("Q","k ~: ( #0 .. ?X)")] contrapos2 1);
by(ALLGOALS Asm_simp_tac);
br numb_range_mem_subset2 1; ba 2;
by(ALLGOALS Asm_simp_tac);

(* Second part: (* Step *). B: specialize hypothesis to case k=x. *)
by(eres_inst_tac [("x","x")] ballE 1);
by(eres_inst_tac [("Q","x ~: ( #0 .. ?X)")] contrapos2 2);
by(ALLGOALS Asm_simp_tac);
by(asm_full_simp_tac (HOL_ss addsimps [numb_range_def,in_naturals RS sym]) 2);
by(Asm_simp_tac 2);
br zequalD1 2;
by (stac zadd_assoc 2);
by(Asm_simp_tac 2);

(* Second part: (* Step *). B: unfold userDoesLogin and bring
   it to self-contradiction with the hypothesis. *)
bd pair_rel_dom 1;
by(rotate_tac ~1 1);
be contrapos2 1;
by(Asm_full_simp_tac 1);
by(rotate_tac ~1 1);
be rev_mp 1;
by(rotate_tac ~1 1);
be rev_mp 1;
by(zstac (userDoesLogin_axdef RS DECL_D2) 1);
by(zdtac traces_init_D2 1);
by(zdtac traces_init_D2 2);
by(ALLGOALS(asm_simp_tac (simpset() addsimps[tfun_apply])));
qed"HSD_1a_core";


val [] = goalw Analysis.thy [HSD_1a_def,SSet_def,asSet_def,image_def]
"y : HSD_1a";
auto();by(tc_tac 1);
by(rotate_tac ~1 1);
be contrapos2 1;
br uid_not_in_session_table_implies_no_siglogChanges 1;
by(ALLGOALS(Asm_full_simp_tac));
br (HSD_1a_core RS mp) 1;
by(ALLGOALS(Asm_full_simp_tac));
qed"HSD_1a";

(* 18.9. 2004, 10:47 *)


val prems = goalw Analysis.thy []
"!!t. [|t:Traces ; n : %N |] ==>                                                 \
\     (! k: #0 .. n - #1.                                                         \
\            (t %^ k, t %^ (k + #1)) ~: userDoesLogin %^ uid |                   \
\            (? j: k + #1 .. n - #1. (t%^ j, t%^ (j+ #1)):userDoesLogout %^ uid))\
\      -->      uid ~: dom (PROJ (t %^ n)                                        \
\                                (% x. fst(snd(snd(snd(x)))))                    \
\                                ''session_table'')";
by(res_inst_tac [("x","n")] naturals_induct 1); ba 1;
by(ALLGOALS Asm_full_simp_tac);
(* First part: *Base* exploit initial state. *)
bd traces_init_D1 2;
by (convert2hol_tac [] 2);
auto();

(* Second part: (* Step *). A: exploit contradicting assumptions: *)
by(eres_inst_tac [("x","k")] ballE 1);
by(ALLGOALS Asm_full_simp_tac);
be bexE 1;
by(case_tac "j=x" 1);
by(rotate_tac ~2 1);
be contrapos2 1;
by(zstac (userDoesLogout_axdef RS DECL_D2) 1);
by(zftac traces_init_D2 1);
by(zftac traces_init_D2 2);
by(ALLGOALS(asm_simp_tac (simpset() addsimps[tfun_apply])));
by(eres_inst_tac [("x","j")] ballE 1);
by(Asm_full_simp_tac 1);
by(HINT "j ~: ( k + #1 .. x + #1 + #~01)" (K all_tac) 1);
by(Asm_full_simp_tac 1);
by(asm_full_simp_tac (simpset() addsimps [numb_range_def]) 1);
auto();
by(rotate_tac 7 1);
be swap 1;
by(rotate_tac 3 1);
bd zle_imp_zless_or_eq 1;
be disjE 1;
by(res_inst_tac [("t","x + #~01")] subst 1);
by(res_inst_tac [("m1","x")]  (less_zpred_eq_le RS iffD2) 2);
by(ALLGOALS Asm_simp_tac);
by(res_inst_tac [("t","x")] subst 2);
ba 3;
by (stac zadd_assoc 2);
by(Asm_simp_tac 2);
by(res_inst_tac [("t","x + #~01")] subst 1);
by(stac zsuc_zpred 2); br refl 2;
by(asm_full_simp_tac (HOL_ss addsimps [zpred_def]) 1);
auto();
by(HINT "x + #1 + #~01 = x" (K all_tac) 1);
by(Asm_full_simp_tac 1);
by (stac zadd_assoc 1);
by(Asm_simp_tac 1);

be swap 1;
br numb_range_mem_subset2 1; ba 2;
by(ALLGOALS Asm_simp_tac);


(* Second part: (* Step *). B: specialize hypothesis to case k=x. *)
by(eres_inst_tac [("x","x")] ballE 1);
by(eres_inst_tac [("Q","x ~: ( #0 .. ?X)")] contrapos2 2);
by(ALLGOALS Asm_simp_tac);
by(asm_full_simp_tac (HOL_ss addsimps [numb_range_def,in_naturals RS sym]) 2);
by(Asm_simp_tac 2);
br zequalD1 2;
by (stac zadd_assoc 2);
by(Asm_simp_tac 2);


(* Second part: (* Step *). B: unfold userDoesLogin and bring
   it to self-contradiction with the hypothesis. *)
bd pair_rel_dom 1;
by(rotate_tac ~1 1);
be contrapos2 1;
by(Asm_full_simp_tac 1);
be disjE 1;

by(rotate_tac ~1 1);
be rev_mp 1;
by(rotate_tac ~1 1);
be rev_mp 1;
by(zstac (userDoesLogin_axdef RS DECL_D2) 1);
by(zftac traces_init_D2 1);
by(zftac traces_init_D2 2);
by(ALLGOALS(asm_simp_tac (simpset() addsimps[tfun_apply])));

(* self contradiction : no userDoesLogout possible *)
be bexE 1;
by(HINT "x + #1 + #~01 = x" (K all_tac) 1);
by(rotate_tac ~1 1);
by(Asm_full_simp_tac 1);
by (stac zadd_assoc 2);
by(Asm_simp_tac 2);
by(asm_full_simp_tac (HOL_ss addsimps [numb_range_def]) 1);
auto();
qed"HSD_1b_core";
(*Sun Sep 19 19:40:59 MEST 2004 *)



val [] = goalw Analysis.thy [HSD_1b_def,SSet_def,asSet_def,image_def]
" y : HSD_1b";
auto();by(tc_tac 1);
be contrapos2 1;back();back();
by(Asm_full_simp_tac 1);
br uid_not_in_session_table_implies_no_siglogChanges 1;
by(ALLGOALS(Asm_full_simp_tac));
br (HSD_1b_core RS mp) 1;
by(ALLGOALS(Asm_full_simp_tac));
qed"HSD_1b";




val [] = goalw Analysis.thy [HSD_2a_def,SSet_def,asSet_def,image_def] "y : HSD_2a";
by(Asm_simp_tac 1);by(tc_tac 1);
by(stripS_tac 1);
by(rotate_tac ~1 1);
be rev_mp 1;
by(zstac (siglogChangedTo_axdef RS DECL_D2) 1);
by(zstac (signatureIsGenerated_axdef RS DECL_D2) 3);
by(zftac traces_init_D2 1);
by(zftac traces_init_D2 2);
by(zftac traces_init_D2 3);
by(zftac traces_init_D2 4);
by(ALLGOALS(asm_simp_tac (simpset() addsimps[tfun_apply])));

br State_Transition_Cases 1;
by(ALLGOALS(asm_simp_tac Z2HOL_ss));
by(zdtac AuthenticateUserL_inv_state_components 1);
by(zdtac NopOperationL_inv_state_components 1);
by(zftac GenerateSignatureL_inv_state_components 1);
by(zdtac LogoutL_inv_state_components 2);
by(case_tac "uid : dom s_tab" 1);
by(zdtac GenerateSignatureL_implies_not_siglogChanges 2);
be disjE 2;
by(ALLGOALS(Asm_simp_tac));
br impI 1;
by(REPEAT (etac conjE 1));
bd dom_tabs_contained_in_dom_pri_key_list 1; ba 1;

br conjI 1; br conjI 2;
br ballI 1;
by(zetac GenerateSignatureL_and_siglogChanges_implies_inv_others 1);
by(hyp_subst_tac 4);
by(zrtac GenerateSignatureL_and_siglogChanges_implies_prikey_use 4);
by (ALLGOALS(convert2hol_tac []));
auto();
qed"HSD_2a";
(* Mon Oct 18 14:20:35 MEST 2004 *)


goalw Analysis.thy [] "? y z. (($# x) = ($# y + $# z))";
by(res_inst_tac [("x","(0)::nat")] exI 1);
by(res_inst_tac [("x","(x)::nat")] exI 1);
auto();
qed"HSD_3_aux1";


goalw Analysis.thy []
" !!t.                                                                        \
\ [| t : Traces; n : %N;  uid : dom ssn_tbl; sid : dom (ssn_tbl %^ uid);      \
\    uid : dom slog;                                                          \
\    slog = PROJ(t %^ n)(% x. snd(snd(snd(snd(x)))))(''signature_log'');      \
\    ssn_tbl = PROJ (t %^ n) (% x. fst(snd(snd(snd(x))))) ''session_table'';  \
\    accept_read_prikey ~= PROJ (ssn_tbl %^ uid %^ sid) fst ''pkra'' |] \
\ ==> (t %^ n, t %^ (n + #1)) ~: siglogChangedTo %^ (uid, sig)";
by(zstac (siglogChangedTo_axdef RS DECL_D2) 1);
by(zftac traces_init_D2 1);
by(zftac traces_init_D2 2);
by(ALLGOALS(asm_simp_tac (simpset() addsimps[tfun_apply])));
by(rotate_tac 5 1);
be rev_mp 1;be rev_mp 1;
br State_Transition_Cases 1;
by(ALLGOALS(asm_simp_tac Z2HOL_ss));
by(ALLGOALS(strip_tac ));
by(ALLGOALS(hyp_subst_tac));
by(zdtac AuthenticateUserL_inv_state_components 1);
by(zdtac NopOperationL_inv_state_components 1);
by(zftac GenerateSignatureL_inv_state_components 1);
by(zdtac LogoutL_inv_state_components 2);
by(ALLGOALS(Asm_simp_tac));

(* inserting * the lemma * here that does the work at the
   data level : *)
by(zdtac GenerateSignatureL_not_accept_read_key_implies_inv 1);
br conjI 1; ba 1;
br conjI 1; ba 1;
by (convert2hol_tac [] 1);
auto();
qed"HSD_3_inv_implies_post";



goalw Analysis.thy []
"!!t.[| t : Traces; k : %N; uid : USER_ID;                                                \
\       sig : SIGNATURE; sig' : SIGNATURE;                                                \
\       ssn_tbl = PROJ (t %^(k + #1)) (% x. fst(snd(snd(snd(x)))))''session_table'';      \
\       uid : dom ssn_tbl & sid : dom(ssn_tbl %^ uid) &                                   \
\       accept_read_prikey ~= PROJ (ssn_tbl %^ uid %^ sid) fst ''pkra''                   \
\    |]                                                                                   \
\ ==>  (! j: k + #1 .. k + $# n. (t %^ j, t %^ (j + #1)) ~: userDoesLogout %^ uid)        \
\      --> (let ssn_tbl'=PROJ(t %^(k + $#n + #1))(% x. fst(snd(snd(snd(x)))))''session_table''\
\           in  (uid : dom ssn_tbl' & sid : dom(ssn_tbl' %^ uid) &                        \
\                accept_read_prikey ~= PROJ (ssn_tbl' %^ uid %^ sid) fst ''pkra''))";
by(REPEAT (etac conjE 1));
by(induct_tac "n" 1);
(* base case : *)
  br impI 1;
  by(thin_tac "Ball  ?X ?P" 1);
  by(asm_full_simp_tac (simpset() addsimps
                        [zadd_left_commute,zadd_commute,zadd_assoc,Let_def]
                        delsimps [inj_zint]) 1);
(* step: *)
  (* synchronize preconditions *)
  by(ALLGOALS(asm_full_simp_tac (simpset() addsimps
                            [numb_range_def, Ball_def])));
  br impI 1;be impE 1; br allI 1;
  by(eres_inst_tac [("x","x")] allE 1);
  by(Asm_simp_tac 1);
  by(eres_inst_tac [("x","zsuc (k + $# n)")] allE 1);
  by(thin_tac "ssn_tbl = ?X" 1);
  by(thin_tac "uid : dom ?X" 1);
  by(thin_tac "sid : dom ?X" 1);
  by(thin_tac "accept_read_prikey ~= ?X" 1);
  by(asm_full_simp_tac (simpset() addsimps
                        [zadd_left_commute,zadd_commute,zadd_assoc,Let_def]
                        delsimps [inj_zint]) 1);
  by(asm_full_simp_tac (HOL_ss addsimps
                        [zsuc_def, zadd_left_commute,zadd_commute,zadd_assoc]) 1);
  by(Asm_full_simp_tac 1);
  be impE 1;
  br (zle_refl RS zadd_zle_mono) 1;
  by (stac zadd_commute 1);
  br Nat_zle_zadd 1; br zle_refl 2; br naturalsI 1; br refl 1;

  (* now load the premises into the decomposition thm. *)
  by(rotate_tac ~2 1);
  be rev_mp 1; be rev_mp 1;
  by(res_inst_tac [("s","#1 + #1"),("t","#2")] subst 1);
  by(Asm_simp_tac 1);
  by(asm_full_simp_tac (HOL_ss addsimps
                        [zadd_assoc RS sym]) 1);
  by(zstac (userDoesLogout_axdef RS DECL_D2) 1);
  by(zftac traces_init_D2 1);
  by(zftac traces_init_D2 2);
  by(ALLGOALS(asm_simp_tac (simpset() addsimps[tfun_apply])));
  (* now standard decomposition a la carte ... *)
  br State_Transition_Cases 1;
  by(ALLGOALS(asm_simp_tac Z2HOL_ss));
  by(ALLGOALS(strip_tac ));
    (* side condition :  k + $# n + #1 : %N *)
    br Nat_zadd 1; br Nat_zadd 1;
    by(ALLGOALS(Asm_simp_tac ));

  by(zftac AuthenticateUserL_inv_state_components 1);
  by(zdtac NopOperationL_inv_state_components 2);
  by(zftac GenerateSignatureL_inv_state_components 2);
  by(zftac LogoutL_inv_state_components 3);
  by(ALLGOALS(fn x => (REPEAT(etac conjE x))));
  by(ALLGOALS(hyp_subst_tac));
  by(ALLGOALS(Asm_full_simp_tac));

  by(zdtac LogoutL_session_table_inv 3);
  by(Asm_full_simp_tac 3);
  by(zdtac GenerateSignatureL_not_accept_read_key_implies_inv 2);
  by (convert2hol_tac [] 2);
  by(Blast_tac 2);
  by(Asm_full_simp_tac 2);
  by(zdtac AuthenticateUserL_uid_auth_implies_session_table_inv 1);
  auto();
qed"HSD_3_core";


goalw Analysis.thy []
" !!t.                                                                               \
\ [| t : Traces; n : %N;                                                             \
\    slog = PROJ(t %^ (n + #1))(% x. snd(snd(snd(snd(x)))))(''signature_log'');      \
\    ssn_tbl = PROJ (t %^ (n + #1)) (% x. fst(snd(snd(snd(x))))) ''session_table'';  \
\    (t %^ n, t %^ (n + #1)) : siglogChangedTo %^ (uid, sig) |]                      \
\ ==> ? sid. uid : dom slog & uid : dom ssn_tbl & sid : dom(ssn_tbl %^ uid) &        \
\            accept_read_prikey ~= PROJ (ssn_tbl %^ uid %^ sid) fst ''pkra''";
by(rotate_tac 2 1);
be rev_mp 1;be rev_mp 1;be rev_mp 1;
by(zstac (siglogChangedTo_axdef RS DECL_D2) 1);
by(zftac traces_init_D2 1);
by(zftac traces_init_D2 2);
by(ALLGOALS(asm_simp_tac (simpset() addsimps[tfun_apply])));
br State_Transition_Cases 1;
by(ALLGOALS(asm_simp_tac Z2HOL_ss));
by(ALLGOALS(strip_tac ));
by(ALLGOALS(hyp_subst_tac));
by(zdtac AuthenticateUserL_inv_state_components 1);
by(zdtac NopOperationL_inv_state_components 2);
by(zftac GenerateSignatureL_inv_state_components 3);
by(zdtac LogoutL_inv_state_components 4);
by(ALLGOALS(fn x => (REPEAT(etac conjE x))));
by(ALLGOALS(hyp_subst_tac));
by(ALLGOALS(Asm_full_simp_tac));

(* prove first part of the invariant:
   uid : dom slog. This is essentially a consequence of
   siglogChangedTo and  GenerateSignatureL_siglog_mono *)
br conjI 1;
by(zftac GenerateSignatureL_siglog_mono 1);
by(Blast_tac 1);
(* prove crucial second part of the invariant:
   uid : dom ssn_tbl and existence of unique sids with
   accept_read_prikey ~= (ssn_tbl %^ uid %^ sid).pkra. This is essentially a
   consequence of GenerateSignatureL_implies_no_accept_key that does
   the real work at the data modeling level. *)
by(zftac GenerateSignatureL_siglogChanges_charn2 1);
by(Blast_tac 1);
br conjI 1;
by(Blast_tac 1);
br exI 1;
br conjI 1;
by(Blast_tac 1);
by(zdtac GenerateSignatureL_implies_no_accept_key 1);
by (convert2hol_tac [] 2);
auto();
qed "post_implies_HSD_3_inv";



val [] = goalw Analysis.thy [HSD_3_def,SSet_def,asSet_def,image_def] "y : HSD_3";
by(Asm_simp_tac 1);
(*
 1. ! t:Traces.
       ! n:%N.
          ! uid:USER_ID.
             ! sig:SIGNATURE.
                ! sig':SIGNATURE.
                   ! k: #0 .. n + #~01.
                      (t %^ k, t %^ (k + #1))
                      : siglogChangedTo %^ (uid, sig) /\
                      (t %^ n, t %^ (n + #1))
                      : siglogChangedTo %^ (uid, sig') =+=>
                      (? j: k + #1 .. n + #~01.
                          (t %^ j, t %^ (j + #1)) : userDoesLogout %^ uid)

 *)

by(stripS_tac 1);
(* index rectification *)
by(HINT "#0 <= k & k <= n + #~01" (K all_tac) 1);
by(asm_full_simp_tac (simpset() addsimps [numb_range_def,in_naturals,zless_eq_zadd]) 2);
by(REPEAT (etac conjE 1));
by(thin_tac "k : ?X" 1);
by(rotate_tac ~1 1);
bd(zless_eq_zadd RS iffD1) 1;
by(REPEAT (etac exE 1));
by(dres_inst_tac [("f","% x . (x::int) + #1")] arg_cong 1);
by(ALLGOALS(asm_full_simp_tac (simpset() addsimps
                          [zadd_left_commute,zadd_commute,zadd_assoc]
                          delsimps [inj_zint])));
by(hyp_subst_tac 1);
(*1. !!t n uid sig sig' k z.
       [| t : Traces; k + ($# z + #1) : %N;
          (t %^ k, t %^ (k + #1)) : siglogChangedTo %^ (uid, sig);
          (t %^ (k + ($# z + #1)), t %^ (k + ($# z + #1) + #1))
          : siglogChangedTo %^ (uid, sig');
          #0 <= k |]
       ==> ? j: k + #1 .. k + $# z.
              (t %^ j, t %^ (j + #1)) : userDoesLogout %^ uid
 *)
by(zftac post_implies_HSD_3_inv 1);
(*
1. !!t uid sig sig' k z.
       [| t : Traces; k + ($# z + #1) : %N;
          (t %^ k, t %^ (k + #1)) : siglogChangedTo %^ (uid, sig);
          (t %^ (k + ($# z + #1)), t %^ (k + ($# z + #1) + #1))
          : siglogChangedTo %^ (uid, sig');
          #0 <= k |]
       ==> k : %N
 2. !!t n uid sig sig' k z.
       [| t : Traces; k + ($# z + #1) : %N;
          (t %^ k, t %^ (k + #1)) : siglogChangedTo %^ (uid, sig);
          (t %^ (k + ($# z + #1)), t %^ (k + ($# z + #1) + #1))
          : siglogChangedTo %^ (uid, sig');
          #0 <= k;
          ? sid.
             uid : dom ((t %^ (k + #1)).signature_log) /\
             (uid : dom ((t %^ (k + #1)).session_table) /\
              (sid : dom ((t %^ (k + #1)).session_table %^ uid) /\
               accept_read_prikey ~=
               ((t %^ (k + #1)).session_table %^ uid %^ sid).pkra)) |]
       ==> ? j: k + #1 .. k + $# z.

 *)
  by(asm_full_simp_tac (simpset() addsimps [in_naturals]) 1);
by(REPEAT (etac exE 1));
by(REPEAT (etac conjE 1));
by(thin_tac "(t %^ k, ?X) : ?Y" 1);
by(eres_inst_tac [("Q","(?xa,?ya) : ?Y")] contrapos2 1);
by(ALLGOALS(Asm_full_simp_tac));
by(zftac HSD_3_core 1);
  by(asm_full_simp_tac (simpset() addsimps [in_naturals]) 1);
  by(Blast_tac 1);
(*
 1. !!t uid sig' k z sid.
       [| t : Traces; k + ($# z + #1) : %N; #0 <= k;
          uid : dom ((t %^ (k + #1)).signature_log);
          uid : dom ((t %^ (k + #1)).session_table);
          sid : dom ((t %^ (k + #1)).session_table %^ uid);
          accept_read_prikey ~=
          ((t %^ (k + #1)).session_table %^ uid %^ sid).pkra;
          ! j: k + #1 .. k + $# z.
             (t %^ j, t %^ (j + #1)) ~: userDoesLogout %^ uid |]
       ==> (t %^ (k + ($# z + #1)), t %^ (k + ($# z + #1) + #1))
           ~: siglogChangedTo %^ (uid, sig')
 *)

by(asm_full_simp_tac (simpset() addsimps [Let_def]) 1);
by(REPEAT (etac conjE 1));
br HSD_3_inv_implies_post 1;
br refl 7; br refl 6;

by(ALLGOALS(Asm_full_simp_tac));
by(ALLGOALS(asm_full_simp_tac (simpset() addsimps
                          [zadd_left_commute,zadd_commute,zadd_assoc]
                          delsimps [inj_zint])));
(*
 1. !!t uid k z sid.
       [| t : Traces; k + ($# z + #1) : %N; #0 <= k;
          uid : dom ((t %^ (k + #1)).signature_log);
          uid : dom ((t %^ (k + #1)).session_table);
          sid : dom ((t %^ (k + #1)).session_table %^ uid);
          accept_read_prikey ~=
          ((t %^ (k + #1)).session_table %^ uid %^ sid).pkra;
          ! j: k + #1 .. k + $# z.
             (t %^ j, t %^ (j + #1)) ~: userDoesLogout %^ uid;
          uid : dom ((t %^ (k + ($# z + #1))).session_table);
          sid : dom ((t %^ (k + ($# z + #1))).session_table %^ uid);
          accept_read_prikey ~=
          ((t %^ (k + ($# z + #1))).session_table %^ uid %^ sid).pkra |]
       ==> uid : dom ((t %^ (k + ($# z + #1))).signature_log)

 *)
by(res_inst_tac [("s","(k + #1) + $# z"), ("t","k + ($# z + #1)")] subst 1);
be (signature_log_mono_trace RS subsetD) 2; ba 3;
  by(asm_full_simp_tac (simpset() addsimps [in_naturals]) 2);
  by(ALLGOALS(asm_full_simp_tac (simpset() addsimps
                          [zadd_left_commute,zadd_commute,zadd_assoc]
                          delsimps [inj_zint])));
(* No subgoals!
 *)
qed "HSD_3";
*)
