(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * HSD.thy --- 
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
(* $Id: HSD.thy 8082 2008-06-06 10:39:53Z wolff $ *)

ML{*quick_and_dirty:=false; *}
theory  HSD
imports AccessController SessionManager

begin

section{* Loading a ZETA-unit and the Consequences *}

load_holz "HSD"

(* legacy : *)
lemma ifE: "[| if A then B else C; [|A;B|] ==> P; [|~A;C|] ==> P |] ==> P"
by(case_tac "A", auto)

lemma if_eqL_E:
"[| x = (if A then B else C); [|A;x=B|] ==> P; [|~A;x=C|] ==> P |] ==> P"
by(case_tac "A", auto)

lemma if_eqR_E: 
"[| (if A then B else C) = x; [|A;B=x|] ==> P; [|~A;C=x|] ==> P |] ==> P"
by(case_tac "A", auto)

(* \<dots> end legacy *)


zlemma AuthenticateUserL_inv_state_components:
"AuthenticateUserL \<longrightarrow> (signature_log' =  signature_log    \<and>      
                        access_control_list' = access_control_list \<and>
                        pri_key_list' = pri_key_list)"
apply(zstrip)
apply(zfrule AuthenticateUserL_def[zdecl [1]])
apply(zfrule AuthenticateUserL_def[zdecl [2]]) 
apply(zfrule AuthenticateUserL_def[zdecl [3]])
apply(simp add:Z2HOL);
done



zlemma AuthenticateUserL_uid_auth_implies_session_table_inv:
"AuthenticateUserL                                                    
  \<longrightarrow>  uid : dom session_table                                      
  \<longrightarrow>  (session_table' %^ uid = session_table %^ uid)"
apply(zstrip)
apply(zfrule AuthenticateUserL_def[zpred[2]])
apply(zfrule AuthenticateUserL_def[zpred[3]])
apply(thin_tac "Authentication = ?X")
apply(thin_tac "session_table' = ?X")
(* saturation of tc's *)
apply(zfrule AuthenticateUserL_def [zdecl [1]])
apply(zfrule AuthenticateUserL_def [zdecl [3]])
apply(zfrule AuthenticateUserL_def [zdecl [7]])
apply(zdrule DARMA_def [zdecl [4]])
apply(simp only: XI_def DELTA_def)
apply((erule conjE)+)
apply(zfrule SessionManager_def [zdecl [1]])
apply(zdrule SessionManager_def [zdecl [2]])
apply(zdrule AccessController_def [zdecl [1]])
(* <<< saturation *)
apply(zsubst AuthenticateUser_axdef[THEN DECL_D2])
apply(zsubst RegistSessionInformation_axdef[THEN DECL_D2])
apply(case_tac "User_authentication_uid = uid" )
sorry
(* does not work for unknwon  reason 
apply(simp_all add:maplet_def split: if_splits)
apply(drule (neq_sym[THEN iffD1];
apply(ALLGOALS(Asm simp));
done
*)



zlemma GenerateSignatureL_inv_state_components:
"GenerateSignatureL 
 \<longrightarrow> (access_control_list' = access_control_list \<and>  
      session_IDs = session_IDs'  \<and>    
      pri_key_list' = pri_key_list)"
apply(zstrip)
apply(zfrule GenerateSignatureL_def [zdecl [3]])
apply(zdrule GenerateSignatureL_def [zpred [6]])
apply (simp add: Z2HOL)
done


declare No_Dom_Restr [simp del]

(* <<<<<<<<<<<<<<<<<<<<<<< *)

zlemma GenerateSignatureL_siglog_mono:
"GenerateSignatureL \<longrightarrow> dom(signature_log) <= dom(signature_log')"
apply(zstrip);
apply(tactic{*full_expand_schema_tac [thm"GenerateSignatureL_def"] 1*})
apply auto
apply(simp only:XI_def DELTA_def)
apply((erule conjE)+)
apply(zfrule HysteresisSignature_def [zdecl[1]])
apply(zfrule SessionManager_def [zdecl[1]])
apply(zfrule AccessController_def [zdecl[1]])
apply(zfrule AccessController_def [zdecl[2]])
apply(simp only: Let_def)
(* zu brutal : apply(simp_all only: Let_def split: if_splits) *)
apply(erule if_eqL_E)

apply(frule_tac f="% x. fst(snd x)" in arg_cong)
thm pair_rel_dom_fst
apply(rotate_tac -1)
apply(drule pair_rel_dom_fst)

apply(frule_tac [2] f = "% x. fst(snd x)" in arg_cong)
apply(simp_all add: Let_def)
apply((erule conjE )+)
sorry
(*
apply(zsubst AppendSignatureRecord_axdef[THEN DECL_D2])
apply(simp_all)
apply(simp add: Let_def split: if_splits)
apply(rule impI)
apply(rule (CheckValidofSession_axdef[THEN DECL_D1, THEN tfun_apply_snd]);
apply(simp_all)
apply(simp add: Let_def split: if_splits)
apply auto
done
*)

zlemma GenerateSignatureL_inv_if_invalid_session:
"GenerateSignatureL \<longrightarrow>                                          
 Signature_generation_sid ~: dom (gen_un (ran session_table)) \<longrightarrow>
 signature_log' = signature_log & session_table' = session_table"
apply(zstrip)
apply(tactic{*full_expand_schema_tac [thm"GenerateSignatureL_def"] 1*})
apply(erule DECL_E)
apply(simp only: XI_def DELTA_def)
apply(erule conjE)+
apply(zfrule HysteresisSignature_def [zdecl[1]])
apply(zfrule SessionManager_def [zdecl[1]])
apply(zfrule AccessController_def [zdecl[1]])
apply(zfrule AccessController_def [zdecl[2]])
apply(simp only: Let_def)
apply(erule if_eqL_E)
apply(simp)
apply(subgoal_tac "(Signature_generation_sid, session_table, 
         pri_key_list) : ReadPrivateKeyFailure_")
apply(rotate_tac -1)
apply(simp)
apply(rule isValidSessionVSReadPrivateKeyFailure1[rule_format])
apply(simp_all)
done


zlemma 
"GenerateSignatureL =+=>                            
   (dom session_table <= dom pri_key_list &        
    dom signature_log <= dom pri_key_list) =+=>    
   (dom session_table' <= dom pri_key_list' &      
    dom signature_log' <= dom pri_key_list')";
apply(zstrip)
apply(zfrule GenerateSignatureL_inv_state_components] 1)
apply(zfrule ([zpred]  GenerateSignatureL_def 1)] 1)
apply(zfrule ([zpred]  GenerateSignatureL_def 2)] 1)
apply(zfrule ([zpred]  GenerateSignatureL_def 3)] 1)
apply(asm_full simp (HOL_ss addsimps [XI_def,DELTA_def]) 1)
apply(case_tac "Signature_generation_sid : dom (gen_un (ran session_table))" 1)
apply(drule(stripS GenerateSignatureL_inv_if_invalid_session) 2;
apply auto
apply(drule (stripS(get_conj  GenerateSignatureL_def 2)) 1)
apply(erule if_eqL_E 1;
apply(frule_tac [("f","% x. snd(snd x)")] arg_cong 1)apply(rotate_tac ~1 1)
apply(frule_tac [("f","% x. snd(snd x)")] arg_cong 2)apply(rotate_tac ~1 2)
apply(ALLGOALS(asm_full simp (prod_ss addsimps [Let_def])))
apply auto
apply(thin_tac "?X" 1)
apply(eres_inst_tac [("Q","(xa,ya) : ?Y")] contrapos2 1)
apply(stac (stripS(AppendSignatureRecord_axdef[THEN DECL_D2])) 1)
apply(ALLGOALS(Asm simp))
apply(asm simp (simpset() addsimps [Let_def] addsplits [expand_if]) 1)
apply(rule(ReadPrivateKey_axdef RS DECL_D1 RS tfun_apply_snd) 1;
apply(Asm simp 1)
apply(drule (stripS ([zpred]  SessionManager_def 1)) 1)
apply(drule (stripS ([zpred]  AccessController_def 2)) 1)
apply(drule (stripS ([zpred]  HysteresisSignature_def 1)) 2)
apply(ALLGOALS Asm_full simp)
apply(asm simp (simpset() addsimps [Let_def,maplet_def] addsplits [expand_if]) 1)
apply(rule conjI 1; apply(strip_tac 1)apply(strip_tac 2)
apply auto

apply(dres_inst_tac [("a","(xa, ya)")] pair_rel_dom_fst 1)
apply(Asm_full simp 1)
apply(drule (stripS ([zpred]  SessionManager_def 1)) 1)
apply(drule (stripS ([zpred]  AccessController_def 2)) 1)
apply(rotate_tac ~2 1)
apply(asm_full simp (HOL_ss addsimps [ReadPrivateKey_dom_session_table_inv]) 1)
apply auto

apply(dres_inst_tac [("a","(xa, ya)")] pair_rel_dom_fst 1)
apply(Asm_full simp 1)
apply(drule (stripS ([zpred]  SessionManager_def 1)) 1)
apply(drule (stripS ([zpred]  AccessController_def 2)) 1)
apply(rotate_tac ~2 1)
apply(eres_inst_tac [("Q","xa : ?X")] contrapos2 1)
apply(stac CheckValidofSession_dom_session_table_inv 1)
apply(rule (ReadPrivateKey_axdef RS DECL_D1 RS tfun_apply_snd) 1;
apply(Asm simp 1) ba 1;
apply(stac ReadPrivateKey_dom_session_table_inv 1)
apply(ALLGOALS(Asm simp))
apply auto

apply(drule (stripS(get_conj  GenerateSignatureL_def 2)) 1)
apply(erule if_eqL_E 1;
apply(frule_tac [("f","% x. snd(snd x)")] arg_cong 1)apply(rotate_tac ~1 1)
apply(frule_tac [("f","% x. snd(snd x)")] arg_cong 2)apply(rotate_tac ~1 2)
apply(ALLGOALS(asm_full simp (prod_ss addsimps [Let_def])))
apply auto

apply(frule_tac [("f","fst")] arg_cong 1)back()
apply(rotate_tac ~1 1)
apply(asm_full simp prod_ss 1)
apply(thin_tac "(fst ?X,snd ?Y) = ?Z" 1)
apply(dres_inst_tac [("a","(xa, ya)")] pair_rel_dom_fst 1)
apply(Asm_full simp 1)
apply(eres_inst_tac [("Q","xa : ?X")] contrapos2 1)
apply(drule (stripS ([zpred]  SessionManager_def 1)) 1)
apply(drule (stripS ([zpred]  AccessController_def 2)) 1)
apply(drule (stripS ([zpred]  HysteresisSignature_def 1)) 1)
apply(stac (stripS(AppendSignatureRecord_axdef[THEN DECL_D2])) 1)
apply(ALLGOALS(Asm simp))
apply(asm simp (simpset() addsimps [Let_def] addsplits [expand_if]) 1)
apply(rule impI 1;
apply(rule (CheckValidofSession_axdef RS DECL_D1 RS tfun_apply_snd) 1;
apply(ALLGOALS(Asm simp))
apply(simp_tac (prod_ss addsimps [Let_def,maplet_def] addsplits [expand_if]) 1)
apply auto

apply(eres_inst_tac [("Pa","fst(?X) : dom pri_key_list")] swap 1)
apply(drule CheckValidofSession_uid_in_dom_ssn_tbl2 1; ba 1;
apply auto

apply(eres_inst_tac [("Pa","fst(?X) : dom pri_key_list")] swap 1)
apply(drule CheckValidofSession_uid_in_dom_ssn_tbl2 1;
apply(rule (CheckValidofSession_axdef RS DECL_D1 RS tfun_apply_snd) 1;
apply(ALLGOALS(Asm simp))
apply(erule subsetD 1;

apply(asm_full simp (simpset() ) 1)
qed"GenerateSignatureL_implies_pri_key_list_bounds";


zlemma 
" GenerateSignatureL =+=> uid ~: dom session_table =+=>             
 ( uid : dom signature_log &                                       
   signature_log %^ uid = signature_log' %^ uid) |                 
 ( uid ~: dom signature_log & uid ~: dom signature_log')";
apply(zstrip)
apply(full_expand_schema_tac GenerateSignatureL_def 1)
apply(erule DECL_E 1;
apply(asm_full simp (HOL_ss addsimps [XI_def,DELTA_def]) 1)
apply(REPEAT (erule conjE 1))
apply(zfrule ([zpred]  HysteresisSignature_def 1)] 1)
(*apply(zfrule ([zpred]  SessionManager_def 1)] 1) *)
apply(zfrule ([zpred]  AccessController_def 1)] 1)
apply(zfrule ([zpred]  AccessController_def 2)] 1)
apply(asm_full simp (HOL_ss addsimps [Let_def])1)
apply(erule if_eqL_E 1;
apply(ALLGOALS(Asm_full simp))
apply(REPEAT (erule conjE 1))
apply(thin_tac "Signature = ?X" 1)
apply(dres_inst_tac [("f","fst")]arg_cong 1)back()apply(rotate_tac ~1 1)
apply(ALLGOALS(Asm_full simp))
apply(frule [not_ReadPrivateKeyFailure1VSisValidSession] 1)
apply(zfrule ([zpred]  SessionManager_def 1)] 2)
apply(ALLGOALS(Asm_full simp))
apply(thin_tac "Command = ?X" 1)
apply(thin_tac "SNAME AccessController ?X" 1)
apply(thin_tac "SNAME HysteresisSignature ?X" 1)
apply(frule [CheckValidofSession_uid_in_dom_ssn_tbl1] 1) (* nec ? *)
apply(erule (stripS ([zpred]  SessionManager_def 1)) 1;

apply(case_tac "uid : dom signature_log" 1)
apply(ALLGOALS(Asm simp))
apply(stac (stripS(AppendSignatureRecord_axdef[THEN DECL_D2])) 1)
apply(ALLGOALS(Asm simp))

apply(rule(ReadPrivateKey_axdef RS DECL_D1 RS tfun_apply_snd) 1;
apply(Asm simp 1)
apply(erule (stripS ([zpred]  SessionManager_def 1)) 1;
apply(asm simp (simpset() addsimps [Let_def] addsplits [expand_if]) 1)
apply(rule impI 1;
apply(stac oplus_apply2 1) apply(rule refl 2;
apply(drule CheckValidofSession_uid_in_dom_ssn_tbl2 1;
apply(rule(ReadPrivateKey_axdef RS DECL_D1 RS tfun_apply_snd) 1;
apply(Asm simp 1)
apply(erule (stripS ([zpred]  SessionManager_def 1)) 1;

apply(zfrule ([zpred]  SessionManager_def 1)] 1)
apply(rotate_tac ~1 1)
apply(asm_full simp (simpset() addsimps [Let_def,maplet_def]) 1)
apply(Blast_tac 1)

apply(stac (stripS(AppendSignatureRecord_axdef[THEN DECL_D2])) 1)
apply(ALLGOALS(Asm simp))
apply(rule(ReadPrivateKey_axdef RS DECL_D1 RS tfun_apply_snd) 1;
apply(Asm simp 1)
apply(erule (stripS ([zpred]  SessionManager_def 1)) 1;
apply(asm_full simp (simpset() addsimps [Let_def,maplet_def]) 1)

apply(asm_full simp (simpset() addsimps [Let_def,maplet_def]
                                addsplits [expand_if]) 1)
apply(rule impI 1;
apply(drule CheckValidofSession_uid_in_dom_ssn_tbl2 1;
apply(rule(ReadPrivateKey_axdef RS DECL_D1 RS tfun_apply_snd) 1;
apply(Asm simp 1)
apply(erule (stripS ([zpred]  SessionManager_def 1)) 1;
apply(zfrule ([zpred]  SessionManager_def 1)] 1)
apply(rotate_tac ~1 1)
apply(asm_full simp (simpset() addsimps [Let_def,maplet_def]) 1)
apply(Blast_tac 1)
qed"GenerateSignatureL_implies_not_siglogChanges";
(* This theorem is hard !!! *)



(* version pre facto *)
zlemma 
"GenerateSignatureL =+=>                                                        
 ((uid : dom signature_log' / uid ~: dom signature_log) /                  
  (uid : dom signature_log  / signature_log %^ uid ~= signature_log' %^ uid)) =+=> 
  uid : dom session_table /\\ Signature_generation_sid : dom (session_table %^ uid)";
apply(zstrip)
apply(full_expand_schema_tac GenerateSignatureL_def 1)
apply(erule DECL_E 1;
apply(asm_full simp (HOL_ss addsimps [XI_def,DELTA_def]) 1)
apply(REPEAT (erule conjE 1))
(* sig saturation *)
apply(zfrule ([zpred]  HysteresisSignature_def 1) 1)
(*apply(zfrule ([zpred]  SessionManager_def 1) 1) *)
apply(zfrule ([zpred]  AccessController_def 1) 1)
apply(zfrule ([zpred]  AccessController_def 2) 1)
(* <<< sig saturation *)
apply(asm_full simp (HOL_ss addsimps [Let_def])1)
apply(erule if_eqL_E 1;
apply(ALLGOALS(Asm_full simp))
apply(REPEAT (erule conjE 1))
apply(Blast_tac 1)
apply(asm_full simp (simpset() addsimps [Let_def])1)
apply(REPEAT (erule conjE 1))
apply (zfrule ([zpred]  SessionManager_def 1) 1)
apply(HINT "SESSION_ID = UNIV" (fn _ => (rtac set_ext 2) THEN (Asm simp 2)) 1)
apply (zfrule (not_ReadPrivateKeyFailure1VSisValidSession) 1)
apply (zfrule (AppendSignatureRecordFailure_VS_isValidSession RS mp) 1)
apply(ALLGOALS(Asm_full simp))
(* exploit in invertibility of session_table *)
apply(rule ballI 1; apply(rule ballI 1; apply(rule impI 1;
apply(erule (stripS(get_conj  SessionManager_def 1)) 1;
apply(ALLGOALS(Asm simp))
(* <<< exploit ... *)
apply(zfrule AppendSignatureRecord_lemma2 1)
apply(dres_inst_tac [("f","fst")] arg_cong 3)back()
apply(Asm_full simp 3)
apply(ALLGOALS tc_tac)
apply(zsubst (ReadPrivateKey_axdef[THEN DECL_D2]) 1)
apply(ALLGOALS(asm simp (simpset() addsimps [Let_def])))
(* exploit in invertibility of session_table *)
apply(rule ballI 1; apply(rule ballI 1; apply(rule impI 1;
apply(erule (stripS(get_conj  SessionManager_def 1)) 1;
apply(ALLGOALS(Asm simp))
(* <<< exploit ... *)
apply(HINT "uid : dom session_table" (K all_tac) 1)
apply(res_inst_tac [("t","uid")] subst 2) ba 2;
apply(rule CheckValidofSession_uid_in_dom_ssn_tbl1 2;
apply(ALLGOALS(Asm simp))
apply(zfrule isValidSession_2' 1)
apply(erule conjE 1; apply(erule exE 1;apply(REPEAT (erule conjE 1))
apply(HINT "uid = x" (K all_tac) 1)
apply(ALLGOALS(Asm simp))
(* <<< exploit ... *)
apply(erule (stripS(get_conj  SessionManager_def 1)) 1;
apply(ALLGOALS(Asm simp))
apply(rule exI 1; apply(rule conjI 1; ba 2;
apply(eres_inst_tac [("Q","?X = uid")] contrapos2 1)
apply(zsubst (CheckValidofSession_axdef[THEN DECL_D2]) 1)
apply(asm simp (simpset()
                 addsimps  [asSet_def,image_def,Let_def,maplet_def]
                 addsplits [expand_if] ) 1)
apply(HINT "NO_USER ~= uid"  (fn _ => (drule NO_USER_not_in_dom_SESSION_TABLE 2)
                              THEN (Blast_tac 2))   1)
apply(Asm simp 1)
apply(rule impI 1;
apply(rule choose_neq_X 1;
apply(Blast_tac 3)
apply(ALLGOALS(asm_full simp (simpset() addsimps
                               [asSet_def,choose_in_subset,aux1,aux2,aux2',aux3])))
qed"GenerateSignatureL_siglogChanges_charn";



(* version post facto *)
(* proof style: experimental. without tc-saturation *)
zlemma 
"GenerateSignatureL =+=>                                                        
 ((uid : dom signature_log' /\\ uid ~: dom signature_log) \/                  
  (uid : dom signature_log  /\\ signature_log %^ uid ~= signature_log' %^ uid)) =+=> 
  uid : dom session_table' /\\ Signature_generation_sid : dom (session_table' %^ uid)";
apply(zstrip)
apply(zfrule (GenerateSignatureL_siglogChanges_charn) 1)
apply(full_expand_schema_tac GenerateSignatureL_def 1)
apply(erule DECL_E 1;
apply(asm_full simp (HOL_ss addsimps [XI_def,DELTA_def]) 1)
apply(REPEAT (erule conjE 1))
apply(asm_full simp (HOL_ss addsimps [Let_def])1)
apply(erule if_eqL_E 1;
apply(ALLGOALS(Asm_full simp))
apply(REPEAT (erule conjE 1))
apply(thin_tac "Signature = ?X" 1)
apply(dres_inst_tac [("f","snd")] arg_cong 1)back()
apply(ALLGOALS(Asm_full simp))
apply(zsubst (AppendSignatureRecord_axdef[THEN DECL_D2]) 1)
  apply(zerule ([zpred]  HysteresisSignature_def 1) 2)
  apply(zfrule ([zpred]  SessionManager_def 1) 1)
  apply(zfrule ([zpred]  AccessController_def 2) 1)
  apply(tc_tac 1)
apply(ALLGOALS(asm simp (simpset() addsimps  [asSet_def,image_def,Let_def,maplet_def]
                                    addsplits [expand_if])))
apply(zsubst (stripS(ReadPrivateKey_axdef[THEN DECL_D2])) 1)
  apply(zfrule ([zpred]  SessionManager_def 1) 1)
  apply(zfrule ([zpred]  AccessController_def 2) 1)
  apply (zfrule (not_ReadPrivateKeyFailure1VSisValidSession) 1)
  apply(zfrule ([zpred]  SessionManager_def 1) 1)
  apply(zfrule ([zpred]  AccessController_def 2) 1)
apply(ALLGOALS(asm simp (simpset() addsimps  [asSet_def,image_def,Let_def,maplet_def]
                                    addsplits [expand_if])))
apply (zsubst CheckValidofSession_dom_session_table_inv 1)
apply (zsubst CheckValidofSession_dom_session_table_inv 3)
apply(Asm simp 5)
  apply(zfrule ([zpred]  SessionManager_def 1) 1)
  apply(zfrule ([zpred]  AccessController_def 2) 1)
  apply(tc_tac 1)
  apply(zfrule ([zpred]  SessionManager_def 1) 1)
  apply(zfrule ([zpred]  AccessController_def 2) 1)

apply(zfrule ([zpred]  SessionManager_def 1) 1)
apply(zdrule (AppendSignatureRecordFailure_VS_isValidSession RS mp) 1)
  apply(zfrule ([zpred]  AccessController_def 2) 1)
  apply(zerule ([zpred]  HysteresisSignature_def 1) 2)

apply(zstrip)
apply(HINT "SESSION_ID = UNIV" (fn _ => (rtac set_ext 2) THEN (Asm simp 2)) 1)
apply(erule (stripS(get_conj  SessionManager_def 1)) 1;
apply(ALLGOALS(Asm simp))

apply(zsubst sid_ind_dom_CheckValidofSession_inv2 1)
apply(zsubst sid_ind_dom_CheckValidofSession_inv 4)
apply(ALLGOALS(Asm simp))
apply(stripS_tac 5)
apply(HINT "SESSION_ID = UNIV" (fn _ => (rtac set_ext 6) THEN (Asm simp 6)) 5)
apply(zerule ([zpred]  SessionManager_def 1) 4)
apply(zrtac (get_conj  SessionManager_def 1) 4)
apply(ALLGOALS(Asm simp))

  apply(zfrule ([zpred]  SessionManager_def 1) 1)
  apply(zfrule ([zpred]  AccessController_def 2) 1)
apply(ALLGOALS(Asm simp))


  apply(zfrule ([zpred]  SessionManager_def 1) 1)
  apply(zfrule ([zpred]  AccessController_def 2) 1)
apply(ALLGOALS(Asm simp))

  apply(zfrule ([zpred]  SessionManager_def 1) 1)
  apply(zfrule ([zpred]  AccessController_def 2) 1)
apply(zstrip)
apply(rule (stripS(get_conj  SessionManager_def 1)) 1; ba 1;
apply(HINT "SESSION_ID = UNIV" (fn _ => (rtac set_ext 4) THEN (Asm simp 4)) 3)
apply(ALLGOALS(Asm_full simp))
apply(thin_tac "session_table' = ?X" 1)
apply(thin_tac "SNAME DARMA ?X" 1)
apply(thin_tac "?X | ?Y" 1)
apply(erule exE 1;
apply(REPEAT(erule conjE 1))
apply(drule sid_in_Check_implies_sid_in_ssn_tbl 1;
apply(drule sid_in_Check_implies_sid_in_ssn_tbl 5;
apply auto
apply(zrtac (get_conj  SessionManager_def 1) 2)
apply(zrtac (get_conj  SessionManager_def 1) 1)
apply auto
qed"GenerateSignatureL_siglogChanges_charn2";



zlemma 
"GenerateSignatureL =+=>                                            
   (signature_log %^ uid ~= signature_log' %^ uid |                
    uid ~: dom signature_log & uid : dom signature_log') =+=>      
   (! uid':dom signature_log - {uid}.                              
                    signature_log %^ uid' = signature_log' %^ uid')";
apply(zstrip)
apply(full_expand_schema_tac GenerateSignatureL_def 1)
apply(erule DECL_E 1;
apply(asm_full simp (HOL_ss addsimps [XI_def,DELTA_def]) 1)
apply(REPEAT (erule conjE 1))
apply(zfrule ([zpred]  HysteresisSignature_def 1)] 1)
(*apply(zfrule ([zpred]  SessionManager_def 1)] 1) *)
apply(zfrule ([zpred]  AccessController_def 1)] 1)
apply(zfrule ([zpred]  AccessController_def 2)] 1)
apply(asm_full simp (HOL_ss addsimps [Let_def])1)
apply(erule if_eqL_E 1;
apply(ALLGOALS(Asm_full simp))
apply(REPEAT (erule conjE 1))
apply(dres_inst_tac [("f","fst")] arg_cong 1)back()apply(rotate_tac ~1 1)
apply(ALLGOALS(Asm_full simp))
apply(frule [not_ReadPrivateKeyFailure1VSisValidSession] 1)
apply(zfrule ([zpred]  SessionManager_def 1)] 2)
apply(ALLGOALS(Asm_full simp))
apply(stac (stripS (AppendSignatureRecord_axdef[THEN DECL_D2])) 1)
apply(ALLGOALS(Asm simp))
apply(rule(ReadPrivateKey_axdef RS DECL_D1 RS tfun_apply_snd) 1;
apply(Asm simp 1)
apply(erule (stripS ([zpred]  SessionManager_def 1)) 1;
apply(asm simp (simpset() addsimps [Let_def] addsplits [expand_if]) 1)
apply(rule impI 1;
apply(simp_tac (simpset() addsimps [maplet_def]) 1)
apply(stac oplus_non_apply 1)
apply(rule refl 2;
apply(thin_tac "?X" 1)
apply(erule disjE 1;
apply(erule swap 1;
apply(Asm_full simp 1)
apply(thin_tac "uid' = ?X" 1)
apply(zfrule ([zpred]  SessionManager_def 1)] 1)
apply auto
apply(ALLGOALS(asm simp (simpset() addsimps [Let_def])))
apply(eres_inst_tac [("Pa","?X = ?Y")] swap 1)back()
apply(stac (stripS (ReadPrivateKey_axdef[THEN DECL_D2])) 2)
apply(stac (stripS (ReadPrivateKey_axdef[THEN DECL_D2])) 1)
apply(ALLGOALS(asm simp (simpset() addsimps [Let_def])))
apply(erule (stripS ([zpred]  SessionManager_def 1)) 3;
apply(erule (stripS ([zpred]  SessionManager_def 1)) 1;
apply(rule AppendSignatureRecord_lemma1 1;
apply(ALLGOALS(Asm simp))
apply(erule (stripS ([zpred]  SessionManager_def 1)) 2;
apply(rule disjI2 1;
apply auto
apply(eres_inst_tac [("Pa","?X = ?Y")] swap 1)
apply(rule AppendSignatureRecord_lemma1 1;
apply(ALLGOALS(Asm simp))
apply(erule (stripS ([zpred]  SessionManager_def 1)) 2;
apply(rule disjI1 1;
apply(dres_inst_tac [("a","(uid, ya)")] pair_rel_dom_fst 1)
apply(ALLGOALS(Asm_full simp))
qed"GenerateSignatureL_and_siglogChanges_implies_inv_others";




zlemma 
"GenerateSignatureL =+=>                                                        
 ((uid : dom signature_log' /\\ uid ~: dom signature_log) \/                  
\  (uid : dom signature_log  /\\ signature_log %^ uid ~= signature_log' %^ uid)) =+=> 
     (? siglog:SIGNATURE.                                                                
        ? hmg:seq CHAR.                                                        
            signature_log' %^ uid = hys_sig_gen %^ (hmg, pri_key_list %^ uid, siglog))";
apply(zstrip)
apply(full_expand_schema_tac GenerateSignatureL_def 1)
apply(erule DECL_E 1;
apply(asm_full simp (HOL_ss addsimps [XI_def,DELTA_def]) 1)
apply(REPEAT (erule conjE 1))
apply(zfrule ([zpred]  HysteresisSignature_def 1)] 1)
(*apply(zfrule ([zpred]  SessionManager_def 1)] 1) *)
apply(zfrule ([zpred]  AccessController_def 1)] 1)
apply(zfrule ([zpred]  AccessController_def 2)] 1)
apply(asm_full simp (HOL_ss addsimps [Let_def])1)
apply(erule if_eqL_E 1;
apply(ALLGOALS(Asm_full simp))
apply(REPEAT (erule conjE 1))
apply(rotate_tac ~2 1)
apply(Asm_full simp 1)
apply(REPEAT (erule conjE 1))
apply(dres_inst_tac [("f","fst")] arg_cong 1)back()
apply(rotate_tac ~1 1)
apply(ALLGOALS(Asm_full simp))
apply (zfrule ([zpred]  SessionManager_def 1)] 1)
apply(frule [not_ReadPrivateKeyFailure1VSisValidSession] 1)
apply(frule [AppendSignatureRecordFailure_VS_isValidSession RS mp] 4)
apply(ALLGOALS(Asm_full simp))
(* exploit in invertibility of session_table *)
apply(rule ballI 1;
apply(rule ballI 1; apply(rule impI 1;
apply(erule (stripS(get_conj  SessionManager_def 1)) 1;
apply(HINT "SESSION_ID = UNIV" (K all_tac) 3)
apply(rule set_ext 4;
apply(ALLGOALS(Asm simp))

(* unfold AppendSignatureRecord and side conditions *)
apply(zsubst (AppendSignatureRecord_axdef[THEN DECL_D2]) 1)
apply(ALLGOALS(asm simp (simpset() addsimps [Let_def,maplet_def])))
apply(zrtac (CheckValidofSession_axdef RS DECL_D1 RS tfun_apply_snd) 1)

(* Now reduce the main goal to the basics ... *)
apply(stac oplus_apply_pair_apply1 1)
apply(defer_tac 1) (* push away equality condition *)
apply(rule bexI 1; apply(rule bexI 1; ba 2;
apply(res_inst_tac [("t","uid")] subst 1)
apply(rule refl 2; (* thats it ... *)
apply(tc_tac 2)


(* Now cleanup: proof applicabilities,
   in particular

  fst (CheckValidofSession %^ (Signature_generation_sid,
                               read_prikey, session_table)) = uid

  and

  fst (CheckValidofSession %^ (Signature_generation_sid,
  write_siglog,
  snd (CheckValidofSession %^ (Signature_generation_sid, read_prikey,
                               session_table)))) = uid *)
apply(rule sym 2;
apply (zrtac AppendSignatureRecord_lemma1 2)
apply (zrtac AppendSignatureRecord_lemma2 1)
apply(defer_tac 1)

apply(rule ballI 1;
apply(rule ballI 1;
apply(rule impI 1;
apply(erule exE 1;
apply (zerule (get_conj  SessionManager_def 1) 1)
apply(res_inst_tac [("x","s")] bexI 1)
apply(Blast_tac 1)
apply(tc_tac 1)
apply(zsubst (ReadPrivateKey_axdef[THEN DECL_D2]) 2)
apply(zsubst (ReadPrivateKey_axdef[THEN DECL_D2]) 1)
apply(ALLGOALS(asm simp (simpset() addsimps [Let_def])))
qed"GenerateSignatureL_and_siglogChanges_implies_prikey_use";




zlemma 
"GenerateSignatureL =+=>                                                        
 ((uid : dom signature_log' /\\ uid ~: dom signature_log) \\/                  
  (uid : dom signature_log  /\\ signature_log %^ uid ~= signature_log' %^ uid)) =+=> 
  accept_read_prikey ~= PROJ (session_table' %^ uid %^ Signature_generation_sid) fst ''pkra''";
apply(zstrip)
apply(zfrule GenerateSignatureL_siglogChanges_charn 1)
apply(HINT "SESSION_ID = UNIV" (fn _ => (rtac set_ext 2) THEN (Asm simp 2)) 1)
apply(full_expand_schema_tac GenerateSignatureL_def 1)
apply(erule DECL_E 1;
apply(asm_full simp (HOL_ss addsimps [XI_def,DELTA_def]) 1)
apply(REPEAT (erule conjE 1))
apply(zfrule ([zpred]  HysteresisSignature_def 1)] 1)
(*apply(zfrule ([zpred]  SessionManager_def 1)] 1) *)
apply(zfrule ([zpred]  AccessController_def 1)] 1)
apply(zfrule ([zpred]  AccessController_def 2)] 1)
apply(asm_full simp (HOL_ss addsimps [Let_def])1)
apply(erule if_eqL_E 1;
apply(ALLGOALS(Asm_full simp))
apply(REPEAT (erule conjE 1))
apply(rotate_tac ~3 1)
apply(ALLGOALS(Asm_full simp))

apply(REPEAT (erule conjE 1))
apply(dres_inst_tac [("f","snd")] arg_cong 1)back()
apply(ALLGOALS(Asm_full simp))

apply(zfrule (not_ReadPrivateKeyFailure1VSisValidSession) 1)
apply(zerule ([zpred]  SessionManager_def 1) 1)
apply(thin_tac "session_table' = ?X" 1)
apply(zfrule ([zpred]  SessionManager_def 1) 1)
apply(ALLGOALS(Asm_full simp))
apply(zsubst (AppendSignatureRecord_axdef[THEN DECL_D2]) 1)
apply(simp_tac (HOL_ss addsimps [Let_def]) 1)
apply(tc_tac 1)
apply(asm simp (simpset() addsimps [Let_def] addsplits [expand_if]) 1)
apply(frule [AppendSignatureRecordFailure_VS_isValidSession RS mp] 1)
apply(ALLGOALS(Asm_full simp))
(* exploit in invertibility of session_table *)
apply(rule ballI 1; apply(rule ballI 1; apply(rule impI 1;
apply(erule (stripS(get_conj  SessionManager_def 1)) 1;
apply(ALLGOALS(Asm simp))
apply(zfrule isValidSession_2' 1)
apply(zfrule isValidSession_3' 1)
apply(REPEAT(erule conjE 1 ORELSE erule exE 1))
apply(zsubst (CheckValidofSession_axdef[THEN DECL_D2]) 1)
apply(simp_tac (simpset() addsimps [Let_def,asSet_def,image_def,maplet_def])1)
apply(stac if_P 1)
apply(Asm_full simp 1)
apply(stac if_not_P 1)
apply(Blast_tac 1)
apply(dres_inst_tac [("s","accept_read_prikey")] sym 1)
apply(ALLGOALS(Asm simp))
apply(res_inst_tac [("s","uid"),("t","SessionManager.choose %^ ?X")] subst 1)
apply(ALLGOALS(Asm simp))
apply(defer_tac 1)
apply(zsubst (CheckValidofSession_axdef[THEN DECL_D2]) 1)
apply(asm simp (simpset() addsimps [Let_def,asSet_def,image_def,maplet_def])1)
apply(stac if_not_P 1)
apply(Asm simp 1)
apply(zerule (isValidSession_2' RS conjunct1) 1)
apply(res_inst_tac [("s","uid"),("t","SessionManager.choose %^ ?X")] subst 1)
apply(zrtac (choose_unique RS sym) 1)
apply(rule ballI 1; apply(rule ballI 1; apply(rule impI 1;
apply(erule (stripS(get_conj  SessionManager_def 1)) 1;
apply(ALLGOALS(Asm simp))
apply(asm simp (simpset() addsimps [PROJ_def])1)
apply(rule(choose_unique' RS sym) 1;
apply(rule set_ext 1;
apply(ALLGOALS(Asm simp))
apply(stac (refl RS conj_cong) 1)
apply(erule sid_ind_dom_CheckValidofSession_inv 1;
apply(ALLGOALS(Asm simp))
apply(rule iffI 2;
apply(hyp_subst_tac 3)
apply(Asm simp 3)
apply(erule (stripS(get_conj  SessionManager_def 1)) 2;
apply(ALLGOALS(Asm simp))
apply(res_inst_tac [("x","Signature_generation_sid")] exI 2)
apply(Asm simp 2)
apply(zstrip)
apply(erule exE 1;
apply(erule (stripS(get_conj  SessionManager_def 1)) 1;
apply(ALLGOALS(Asm simp))
apply(res_inst_tac [("x","s")] exI 1)
apply(ALLGOALS(Asm simp))
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
zlemma 
"GenerateSignatureL =+=>                                              
 (uid : dom session_table /\\                                        
  sid : dom (session_table %^ uid) /\\                               
  accept_read_prikey ~=                                              \
\   PROJ (session_table %^ uid %^ sid) fst ''pkra'')                  
 --> (session_table' %^ uid = session_table %^ uid  /\\              
      signature_log' %^ uid = signature_log %^ uid)";
apply(zstrip)
apply(full_expand_schema_tac GenerateSignatureL_def 1)
apply(erule DECL_E 1;
apply(asm_full simp (HOL_ss addsimps [XI_def,DELTA_def]) 1)
apply(REPEAT (erule conjE 1))
apply(zfrule ([zpred]  HysteresisSignature_def 1)] 1)
(*apply(zfrule ([zpred]  SessionManager_def 1)] 1) *)
apply(zfrule ([zpred]  AccessController_def 1)] 1)
apply(zfrule ([zpred]  AccessController_def 2)] 1)
apply(asm_full simp (HOL_ss addsimps [Let_def])1)
apply(erule if_eqL_E 1;
apply(ALLGOALS(Asm_full simp))
apply(REPEAT (erule conjE 1))
apply(zfrule (not_ReadPrivateKeyFailure1VSisValidSession) 1)
apply(zerule ([zpred]  SessionManager_def 1) 1)
apply(zfrule isValidSession_2' 1)
apply(zerule ([zpred]  SessionManager_def 1) 1)
apply(erule conjE 1; apply(erule exE 1;
apply(REPEAT (erule conjE 1))
apply(case_tac "sid = Signature_generation_sid" 1)
   apply(hyp_subst_tac 1)
   apply(HINT "uid = x" (K all_tac) 1)
   apply(rotate_tac ~3 1)
   apply(Asm_full simp 1)
   apply (zdrule (get_conj  SessionManager_def 1) 1)
   apply(rule bexI 1;apply(rule X_in_SESSION_ID 2;
   apply(rule conjI 1; ba 2;
   apply(rotate_tac ~1 1)
   apply(Asm_full simp 1)

(* now the other case - essentially covered apply lemma: *)
apply(erule AppendSignatureRecord_imp_nosid_nochange 1;
apply(ALLGOALS Asm simp)
apply(zerule ([zpred]  SessionManager_def 1) 1)
apply(ALLGOALS stripS_tac)
apply(erule (stripS(get_conj  SessionManager_def 1)) 2;
apply(erule (stripS(get_conj  SessionManager_def 2)) 1;
apply(HINT "SESSION_ID = UNIV" (fn _ => (rtac set_ext 6) THEN (Asm simp 6)) 5)
apply auto
qed"GenerateSignatureL_not_accept_read_key_implies_inv";






zlemma 
"LogoutL =+=> (signature_log' =  signature_log &            
              session_IDs' = session_IDs &                 
              access_control_list' = access_control_list & 
              pri_key_list' = pri_key_list)";
apply(zstrip)
apply(zfrule ([zpred]  "LogoutL" 2)] 1)
apply(zfrule ([zpred]  "LogoutL" 3)] 1)
apply(drule (stripS (get_conj  "LogoutL" 4)) 1)
apply (simp add_ Z2HOL 1)
qed"LogoutL_inv_state_components";

zlemma 
"LogoutL =+=>                                                  
 (uid : (dom session_table) /\\ Logout_ID : (dom (session_table %^ uid))) 
 =+=>  uid ~: (dom session_table')";
apply(zstrip)apply(erule conjE 1;
apply(full_expand_schema_tac LogoutL_def 1)
apply(res_inst_tac [("t","session_table'")] subst 1)
apply(rule FreeSessionInformation_deletes_sid2 2;
apply auto
apply(frule_tac [("f","snd")] arg_cong 1)apply(rotate_tac ~1 1)
apply(frule_tac [("f","snd")] arg_cong 2)apply(rotate_tac ~1 2)
apply(asm_full simp (HOL_ss addsimps [DELTA_def]) 3)
apply(erule conjE 3;
apply(drule (stripS ([zpred]  SessionManager_def 1)) 3)
apply(ALLGOALS(asm_full simp (prod_ss)))
qed"LogoutL_delete_uid";


zlemma 
"LogoutL =+=>                                                  
 (uid : (dom session_table) /\\ Logout_ID ~: (dom (session_table %^ uid))) 
 =+=>  uid : (dom session_table')";
apply(zstrip)apply(erule conjE 1;
apply(full_expand_schema_tac LogoutL_def 1)
apply(res_inst_tac [("t","session_table'")] subst 1)
apply(rule FreeSessionInformation_deletes_sid3 2;
apply auto
apply(frule_tac [("f","snd")] arg_cong 1)apply(rotate_tac ~1 1)
apply(frule_tac [("f","snd")] arg_cong 2)apply(rotate_tac ~1 2)
apply(asm_full simp (HOL_ss addsimps [DELTA_def]) 3)
apply(erule conjE 3;
apply(drule (stripS ([zpred]  SessionManager_def 1)) 3)
apply(ALLGOALS(asm_full simp (prod_ss)))
qed"LogoutL_keep_uid";


zlemma 
"LogoutL =+=>  (uid : (dom session_table'))   
 =+=>  (session_table' %^ uid = session_table %^ uid)";
apply(zstrip)
apply(zfrule (get_conj  "LogoutL" 2)] 1)
apply(dres_inst_tac [("f","snd")]arg_cong 1)
apply(eres_inst_tac [("P","uid : ?X")] rev_mp 1)
apply(ALLGOALS(Asm_full simp))
apply(zsubst (FreeSessionInformation_axdef[THEN DECL_D2]) 1)
  apply(zfrule ([zpred]  "LogoutL" 1)] 1)
  apply(asm_full simp (HOL_ss addsimps [DELTA_def]) 1)
  apply(erule conjE 1;
  apply(zerule ([zpred]  SessionManager_def 1) 1)
apply(case_tac "Logout_ID : dom (gen_un (ran session_table))" 1)
apply(ALLGOALS(Asm simp))
apply(asm simp (simpset() addsimps [Let_def,maplet_def,asSet_def,image_def]) 1)
apply(asm simp (simpset() addsimps [Domain_def,rel_apply_def]) 1)
qed"LogoutL_session_table_inv";



(* Nop is really a Nop and does not change any component
   if the state. *)
zlemma 
"NopOperationL =+=> (session_table' = session_table &       
              session_IDs' = session_IDs &                 
              signature_log' =  signature_log &            
              access_control_list' = access_control_list & 
              pri_key_list' = pri_key_list)";
apply(zstrip)
apply(zfrule ([zpred]  "NopOperationL" 1)] 1)
apply(zfrule ([zpred]  "NopOperationL" 2)] 1)
apply(zfrule ([zpred]  "NopOperationL" 3)] 1)
apply (simp add_ Z2HOL 1)
qed"NopOperationL_inv_state_components";
*)


end
