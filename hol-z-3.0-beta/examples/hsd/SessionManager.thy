(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * SessionManager.thy
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
(* $Id: SessionManager.thy 6743 2007-08-03 06:39:08Z brucker $ *)

theory  SessionManager
imports Basics

begin

section{* Loading a ZETA-unit and the Consequences *}

load_holz "SessionManager"

ML{* ZTheory.print_TC (the_context()) *}

text{* Basics on RegistSessionInformation *}

lemma RegistSessionInformation_F[simp]:
"\<lbrakk> uid : dom ssn_tbl ; ssn_tbl : SESSION_TABLE ; ssn_IDs: %F SESSION_ID \<rbrakk> \<Longrightarrow>  
  RegistSessionInformation %^ (uid,ssn_tbl,ssn_IDs) = SAME_USER_ERR"
by(insert RegistSessionInformation_axdef[THEN DECL_D2],auto)

lemma RegistSessionInformation_N[simp]:
"\<lbrakk> uid ~: dom ssn_tbl ; ssn_tbl : SESSION_TABLE; ssn_IDs: %F SESSION_ID \<rbrakk> \<Longrightarrow>   
  RegistSessionInformation %^ (uid,ssn_tbl,ssn_IDs) = (new %^ ssn_IDs)"
by(insert RegistSessionInformation_axdef[THEN DECL_D2],auto)


lemma RegistSessionInformation_NOERROR_INV[simp]:
"\<lbrakk>  uid \<notin> dom ssn_tbl ; ssn_tbl : SESSION_TABLE; ssn_IDs: %F SESSION_ID  \<rbrakk> \<Longrightarrow>  
   RegistSessionInformation %^ (uid,ssn_tbl,ssn_IDs) \<notin> AUTH_ERRORS"
apply(subst RegistSessionInformation_N, auto)
apply(drule new_axdef[THEN DECL_D1,THEN tfun_apply], auto)
done


section{* FreeSessionInformation *}
text{* Basics on FreeSession *}

lemma choose_in_X[simp]:
"\<lbrakk> X\<in>%P (USER_ID - {NO_USER}); X \<noteq> {} \<rbrakk> \<Longrightarrow> ((SessionManager.choose %^ X)\<in> X)";
by(insert choose_axdef[THEN DECL_D2],auto)

lemma choose_in_subset[simp]:
"\<lbrakk> X \<in> %P (USER_ID - {NO_USER}); X\<noteq>{}; X <= Y \<rbrakk> \<Longrightarrow> ((SessionManager.choose %^ X) \<in>  Y)"
by(drule choose_in_X,auto)

lemma choose_neq_NO_USER[simp]:
"\<lbrakk> X \<in> %P (USER_ID - {NO_USER}); X\<noteq>{} \<rbrakk> \<Longrightarrow> ((SessionManager.choose %^ X) ~= NO_USER)"
by(frule choose_in_X,assumption,erule swap,auto)

lemma choose_neq_X:
"\<lbrakk> X \<in> %P (USER_ID - {NO_USER}); X \<noteq> {}; x \<notin> X \<rbrakk> \<Longrightarrow> ((SessionManager.choose %^ X) ~= x)"
by(drule choose_in_X,auto)

lemma choose_unique:
" \<lbrakk> s_tab : SESSION_TABLE;                           
    \<forall> x\<in>dom s_tab. \<forall> y\<in>dom s_tab.                                      
           (\<exists> s. s\<in>dom(s_tab%^x) \<and> s\<in>dom(s_tab%^y)) \<longrightarrow>  x = y;                               
    xa \<in> dom s_tab; sid \<in> dom (s_tab %^ xa) \<rbrakk>        
   \<Longrightarrow> (SessionManager.choose%^{y. y \<in> dom s_tab \<and> sid \<in> dom(s_tab%^y)}) = xa "
apply(erule_tac x=xa in ballE,simp_all)
apply(erule ballE, erule impE)
apply(erule_tac [2] sym)
apply(rule exI, rule conjI, assumption)
apply(subgoal_tac "{y. (y \<in> dom s_tab) \<and> sid\<in>(dom (s_tab %^ y))}: %P(USER_ID - {NO_USER})")
apply(drule choose_in_X)
prefer 2 apply simp
apply(rule_tac [2] PowI,erule_tac [2] aux1)
apply(erule_tac [2] Pa=" ?X %^ ?Y: ?Z" in swap)
apply(rule_tac [2] choose_in_subset) 
apply(rule_tac [2] PowI, rule_tac [2] aux1)
apply(auto elim!: aux2')
done


lemma choose_unique':
"\<lbrakk> X = {x}; x ~= NO_USER  \<rbrakk> \<Longrightarrow>  (SessionManager.choose %^ X) = x ";
by(insert choose_axdef[THEN DECL_D2], erule_tac x = "{x}" in ballE,auto)

section{* FreeSessionInformation *}

lemma FreeSessionInformation_N[simp]:
"\<lbrakk> sid : dom (gen_un (ran ssn_tbl)); ssn_tbl : SESSION_TABLE  \<rbrakk> \<Longrightarrow>            
  FreeSessionInformation %^ (sid,ssn_tbl) = (session_terminated, ?X)"
apply(insert FreeSessionInformation_axdef[THEN DECL_D2])
apply(erule ballE)+
apply(rule trans, assumption,auto)
done

lemma FreeSessionInformation_F[simp]:
"\<lbrakk> sid ~: dom (gen_un (ran ssn_tbl)); ssn_tbl : SESSION_TABLE  \<rbrakk> \<Longrightarrow> 
  FreeSessionInformation %^ (sid,ssn_tbl) = (invalid_session_id_err, ssn_tbl)"
apply(insert FreeSessionInformation_axdef[THEN DECL_D2])
apply(erule ballE)+
apply(rule trans, assumption,auto)
done

lemma FreeSessionInformation_deletes_sid1[simp]:
"\<lbrakk> sid : SESSION_ID; ssn_tbl : SESSION_TABLE  \<rbrakk> \<Longrightarrow>    
   sid ~: dom (gen_un (ran (snd(FreeSessionInformation %^ (sid,ssn_tbl)))))"
apply(cases "sid : dom (gen_un (ran ssn_tbl))")
apply(auto simp: asSet_def image_def maplet_def)
done


lemma FreeSessionInformation_deletes_sid2[simp]:
"\<lbrakk> uid : dom ssn_tbl ; sid : dom (ssn_tbl %^ uid); ssn_tbl : SESSION_TABLE \<rbrakk> \<Longrightarrow> 
   uid ~: dom(snd(FreeSessionInformation %^ (sid,ssn_tbl)))";
apply(cases "sid : dom (gen_un (ran ssn_tbl))")
apply(simp_all add: asSet_def image_def maplet_def SESSION_TABLE_def DECL_def 
                    UNIV_def[symmetric] Z2HOL)
apply (auto,auto simp: Union_def)
done


lemma FreeSessionInformation_deletes_sid3[simp]:
"\<lbrakk> uid : dom ssn_tbl ; sid ~: dom (ssn_tbl %^ uid); ssn_tbl : SESSION_TABLE \<rbrakk> \<Longrightarrow>
    uid : dom(snd(FreeSessionInformation %^ (sid,ssn_tbl)))"
apply(cases "sid : dom (gen_un (ran ssn_tbl))")
apply(simp_all add: asSet_def image_def maplet_def SESSION_TABLE_def DECL_def 
                    UNIV_def[symmetric] Z2HOL)
done

lemmas CheckValidofSession_axdef2 = CheckValidofSession_axdef[THEN DECL_D2,zstrip]
declare CheckValidofSession_axdef2[simp]
(* XXX *)


section{* CheckValidofSession *}

lemma CheckValidofSession_F1[simp]:
"\<lbrakk> sid ~: dom (gen_un (ran ssn_tbl)); ssn_tbl : SESSION_TABLE \<rbrakk> \<Longrightarrow>
   CheckValidofSession %^ (sid,X,ssn_tbl) = (NO_USER, ssn_tbl)"
apply(insert CheckValidofSession_axdef[THEN DECL_D2])
apply(erule ballE)+
apply(rule trans, assumption, auto)
done

ML{* show_full_sem:=true *}

text{* TODO : MOVE AND EXPLAIN ! *}
consts slwa_proj ::"'a \<Rightarrow> SIG_LOG_WRITE_ACCESS" ("(_).slwa" [100]101) 
       pkra_proj ::"'a \<Rightarrow> PRI_KEY_READ_ACCESS"  ("(_).pkra" [100]101) 

defs slwa_proj_1_def:
 "(X::(PRI_KEY_READ_ACCESS * SIG_LOG_WRITE_ACCESS)).slwa \<equiv> PROJ X snd ''slwa''"
defs pkra_proj_1_def:
 "(X::(PRI_KEY_READ_ACCESS * SIG_LOG_WRITE_ACCESS)).pkra \<equiv> PROJ X fst ''pkra''"

lemma CheckValidofSession_F2[simp]:
"\<lbrakk> sid : dom (gen_un (ran ssn_tbl)); 
   ALL x. x ~: dom ssn_tbl |
              (let uid = SessionManager.choose %^ 
                         {uid. uid : dom ssn_tbl & sid : dom (ssn_tbl %^ uid)}
              in (uid, ssn_tbl (+) {uid \<bar>--> {sid \<bar>--> 
                                   (refuse_read_prikey,(ssn_tbl%^uid%^sid).slwa)}})) =  
                 (NO_USER, ssn_tbl);
   ssn_tbl : SESSION_TABLE 
\<rbrakk>  \<Longrightarrow> CheckValidofSession %^ (sid,read_prikey,ssn_tbl) = (NO_USER, ssn_tbl)"
apply(insert CheckValidofSession_axdef[THEN DECL_D2])
apply((erule ballE)+,rule trans, assumption)
apply(auto simp:PROJ_def asSet_def slwa_proj_1_def)
done


lemma CheckValidofSession_F3[simp]:
"\<lbrakk> sid : dom (gen_un (ran ssn_tbl)); 
   ALL x. x ~: dom ssn_tbl |
           (let uid = SessionManager.choose%^{uid:dom ssn_tbl. sid:dom(ssn_tbl%^uid)}
            in (uid, ssn_tbl (+) {uid \<bar>--> {sid \<bar>--> ssn_tbl %^ uid %^ sid}})) =
               (NO_USER, ssn_tbl);
   ssn_tbl : SESSION_TABLE \<rbrakk> \<Longrightarrow>                                  
 CheckValidofSession %^ (sid,write_siglog,ssn_tbl) = (NO_USER, ssn_tbl)"
apply(insert CheckValidofSession_axdef [THEN DECL_D2])
apply((erule ballE)+,rule  trans,assumption)
apply(simp_all add: image_def Ball_def asSet_def,auto)
done


lemma CheckValidofSession_F4[simp]:
"\<lbrakk> sid : dom (gen_un (ran ssn_tbl));
   ALL x. x \<notin> dom ssn_tbl | ?X x;
   ssn_tbl : SESSION_TABLE \<rbrakk>  \<Longrightarrow>                                     
 CheckValidofSession %^ (sid,read_siglog,ssn_tbl) = (NO_USER, ssn_tbl)"
apply(insert CheckValidofSession_axdef [THEN DECL_D2])
apply((erule ballE)+,rule  trans,assumption)
apply(simp_all add: image_def Ball_def asSet_def,auto)
done


section{* isValidSession *}
lemma isValidSession_1[simp]:
"\<lbrakk> sid \<notin> dom (gen_un (ran ssn_tbl)); ssn_tbl : SESSION_TABLE \<rbrakk> \<Longrightarrow>   
  (sid,acc_typ,ssn_tbl) \<notin> isValidSession_"
apply(insert isValidSession__axdef [THEN DECL_D2])
apply((erule ballE)+)
apply(rule_tac P=Not in ssubst, assumption,auto)
done


lemma isValidSession_1':
"\<lbrakk>(sid,acc_typ,ssn_tbl): isValidSession_ ;                    
  ssn_tbl : SESSION_TABLE \<rbrakk> \<Longrightarrow>   
 sid : dom (gen_un (ran ssn_tbl))"
apply(erule  contrapos_pp)
apply(auto intro!: isValidSession_1)
done


lemma isValidSession_2[simp]:
"\<lbrakk> sid : dom (gen_un (ran ssn_tbl));                                          
   ! x. x ~: dom ssn_tbl | (sid ~: dom (ssn_tbl %^ x) |                       
            accept_read_prikey ~= (ssn_tbl %^ x %^ sid).pkra);   
   ssn_tbl : SESSION_TABLE \<rbrakk>                                                  
  \<Longrightarrow> (sid,read_prikey,ssn_tbl)~: isValidSession_"
apply(insert isValidSession__axdef [THEN DECL_D2])
apply((erule ballE)+)
apply(rule_tac P=Not in ssubst,assumption) 
apply(auto simp: Let_def pkra_proj_1_def PROJ_def asSet_def)
done


lemma isValidSession_2':
"\<lbrakk> (sid,read_prikey,ssn_tbl) : isValidSession_;                              
   ssn_tbl : SESSION_TABLE \<rbrakk>                                                 
  \<Longrightarrow>  (? x. x : dom ssn_tbl & (sid : dom (ssn_tbl %^ x) &                    
            accept_read_prikey = (ssn_tbl %^ x %^ sid).pkra))    
       & sid : dom (gen_un (ran ssn_tbl))"
apply(frule isValidSession_1', assumption)
apply(rule  conjI, erule contrapos_pp,rule isValidSession_2)
apply(auto)
done

lemma isValidSession_3[simp]:
"\<lbrakk> sid : dom (gen_un (ran ssn_tbl));                                  
   ! x. x ~: dom ssn_tbl | (sid ~: dom (ssn_tbl %^ x) |                       
            accept_write_siglog ~= (ssn_tbl %^ x %^ sid).slwa);  
   ssn_tbl : SESSION_TABLE \<rbrakk>                                                 
  \<Longrightarrow> (sid,write_siglog,ssn_tbl)~: isValidSession_"
apply(insert isValidSession__axdef [THEN DECL_D2])
apply((erule ballE)+)
apply(rule_tac P = "Not" in ssubst) apply(assumption)
apply(auto simp: Let_def pkra_proj_1_def slwa_proj_1_def PROJ_def asSet_def)
done


lemma isValidSession_3':
"\<lbrakk> (sid,write_siglog ,ssn_tbl) : isValidSession_;                             
   ssn_tbl : SESSION_TABLE \<rbrakk>                                                 
  \<Longrightarrow>  (? x. x : dom ssn_tbl & (sid : dom (ssn_tbl %^ x) &                    
             accept_write_siglog = (ssn_tbl %^ x %^ sid).slwa))    
       & sid : dom (gen_un (ran ssn_tbl))"
apply(frule isValidSession_1', assumption)
apply(rule  conjI, erule contrapos_pp)
apply(rule  isValidSession_3,auto)
done

declare CheckValidofSession_axdef2[simp del]

(* TODO : MOVE *)
lemma if_general_I1: " [| A; P B |] ==> P (if A then B else C)" by auto
lemma if_general_I2: "!!A. [| ~A; P C |] ==> P (if A then B else C)" by auto

lemma CheckValidofSession_uid_in_dom_ssn_tbl1:
"\<lbrakk> (sid,read_prikey,ssn_tbl): isValidSession_;  ssn_tbl : SESSION_TABLE  
 \<rbrakk> \<Longrightarrow> fst(CheckValidofSession %^ (sid, read_prikey, ssn_tbl)) : dom ssn_tbl"
apply(subst CheckValidofSession_axdef [THEN DECL_D2,zstrip])
apply(simp_all add: image_def Let_def)
apply(case_tac "sid : dom (gen_un (ran ssn_tbl))")
apply(drule_tac [2] isValidSession_1)
apply(simp_all)
prefer 2 apply blast
apply(simp add: asSet_def choose_in_subset aux1 aux2 aux3)
apply(erule contrapos_pp,rule  isValidSession_2)
apply(auto simp: PROJ_def pkra_proj_1_def)
apply(erule contrapos_np,rule choose_in_subset)
apply(auto dest!: NO_USER_not_in_dom_SESSION_TABLE)
done



lemma CheckValidofSession_uid_in_dom_ssn_tbl2: 
"\<lbrakk> (sid,write_siglog,ssn_tbl): isValidSession_;  ssn_tbl : SESSION_TABLE  
\<rbrakk> \<Longrightarrow>   fst(CheckValidofSession %^ (sid, write_siglog, ssn_tbl)) : dom ssn_tbl"
apply(subst CheckValidofSession_axdef [THEN DECL_D2, zstrip])
apply(simp_all add: image_def Let_def)
apply(case_tac "sid : dom (gen_un (ran ssn_tbl))")
apply(drule_tac [2] isValidSession_1)
apply(simp_all)
prefer 2 apply blast
apply(simp add: asSet_def choose_in_subset aux1 aux2 aux3)
apply(erule contrapos_pp)
apply(rule  isValidSession_3)
apply(auto simp: PROJ_def slwa_proj_1_def)
apply(erule contrapos_np,rule choose_in_subset)
apply(auto dest!: NO_USER_not_in_dom_SESSION_TABLE)
done


lemma CheckValidofSession_uid_in_dom_ssn_tbl3:
"\<lbrakk> (sid,read_siglog,ssn_tbl): isValidSession_ ; ssn_tbl : SESSION_TABLE   
\<rbrakk> \<Longrightarrow>   fst(CheckValidofSession %^ (sid, read_siglog, ssn_tbl)) : dom ssn_tbl"
apply(subst CheckValidofSession_axdef [THEN DECL_D2,zstrip])
apply(simp_all add: image_def Let_def)
apply(case_tac "sid : dom (gen_un (ran ssn_tbl))")
apply(drule_tac [2] isValidSession_1)
apply(auto simp: asSet_def choose_in_subset aux1 aux2 aux3)
apply(rule choose_in_subset,auto)
apply(drule NO_USER_not_in_dom_SESSION_TABLE)
apply auto
apply(rule_tac x=x in exI)
apply(auto simp: SESSION_TABLE_def)
done 

text{* The following is a nice little tricky lemma ... and a vital invariant ...
The premise can be weakened to $sid : dom (gen_un (ran ssn_tbl))$ *}
lemma sid_ind_dom_CheckValidofSession_inv:
assumes valid_session:"(sid, read_prikey, ssn_tbl) \<in> isValidSession_ "
assumes ssn_c:        "ssn_tbl \<in> SESSION_TABLE"
assumes uid_c:        "uid \<in> dom ssn_tbl"
assumes invert:       "\<forall> x \<in> dom ssn_tbl. \<forall> y \<in> dom ssn_tbl.                                           
                       (\<exists> s. s\<in>dom(ssn_tbl%^x) & s\<in>dom(ssn_tbl%^y)) \<longrightarrow> (x = y)"
shows   "(sid \<in> dom(snd(CheckValidofSession%^(sid,read_prikey,ssn_tbl))%^uid)) = 
         (sid \<in> dom(ssn_tbl%^uid))"
apply(insert ssn_c ssn_c [THEN valid_session[THEN isValidSession_2']])
apply(erule  conjE, erule  exE)
apply((erule conjE | erule exE)+)
apply(zsubst CheckValidofSession_axdef [THEN DECL_D2])
apply(simp_all add: Let_def asSet_def image_def maplet_def PROJ_def pkra_proj_1_def)
apply(rule_tac s=x and t="SessionManager.choose %^ ?X" in subst)
apply(rule invert [THEN ssn_c[THEN choose_unique [symmetric]]],assumption+)
apply(case_tac "sid : dom (ssn_tbl %^ uid)",simp_all)
apply(subgoal_tac " x = uid",simp) 
apply(erule invert[zstrip])
apply(rule  uid_c,blast)
apply(subgoal_tac " uid ~= x", simp)
apply(erule swap, simp)
done 


lemma sid_in_Check_implies_sid_in_ssn_tbl:
assumes quod         :"s \<in> dom (snd (CheckValidofSession %^ (sid,read_prikey, ssn_tbl)) %^ x)" 
assumes valid_session:"(sid, read_prikey, ssn_tbl) \<in> isValidSession_"
assumes ssn          :"ssn_tbl \<in> SESSION_TABLE"
assumes uid_c        :"x \<in> dom ssn_tbl"
assumes invert       :"\<forall> x \<in> dom ssn_tbl. \<forall> y \<in> dom ssn_tbl.                                           
                       (\<exists> s. s\<in>dom(ssn_tbl%^x) & s\<in>dom(ssn_tbl%^y)) \<longrightarrow> (x = y)"
shows   "s \<in> dom (ssn_tbl %^ x)"
apply(insert quod ssn ssn [THEN valid_session [THEN isValidSession_2']])
apply(erule  conjE, erule  exE)
apply((erule conjE | erule exE)+)
apply(erule  contrapos_pp)
apply(zsubst CheckValidofSession_axdef [THEN DECL_D2])
apply(simp_all add: Let_def asSet_def image_def maplet_def PROJ_def pkra_proj_1_def)
apply(rule_tac s=xa and
               t="SessionManager.choose %^ {y. y:dom ssn_tbl & sid:dom(ssn_tbl %^ y)}" in ssubst)
apply(erule invert[THEN ssn[THEN choose_unique]],simp)
apply(case_tac "x=xa", simp_all)
apply(erule  swap, simp)
done


lemma sid_ind_dom_CheckValidofSession_inv2:
assumes valid_session :"(sid, write_siglog, ssn_tbl) \<in> isValidSession_"
assumes ssn_c         :"ssn_tbl \<in> SESSION_TABLE"
assumes uid_c         :"uid \<in> dom ssn_tbl "
assumes invert        :"\<forall> x \<in> dom ssn_tbl. \<forall> y \<in> dom ssn_tbl.                                           
                       (\<exists> s. s\<in>dom(ssn_tbl%^x) & s\<in>dom(ssn_tbl%^y)) \<longrightarrow> (x = y)" 
shows   "sid \<in> dom(snd(CheckValidofSession %^ (sid,write_siglog,ssn_tbl)) %^ uid)   
         = (sid \<in> dom (ssn_tbl %^ uid))"
apply(insert ssn_c ssn_c [THEN valid_session [THEN isValidSession_3']])
apply(erule  conjE, erule  exE)
apply((erule conjE | erule exE)+)
apply(zsubst CheckValidofSession_axdef [THEN DECL_D2])
apply(simp_all add: Let_def asSet_def image_def maplet_def PROJ_def slwa_proj_1_def)
apply(rule_tac s=x and t="SessionManager.choose %^ ?X" in subst)
apply(rule invert [THEN ssn_c [THEN choose_unique [symmetric]]], assumption+)
apply(case_tac "sid : dom (ssn_tbl %^ uid)", simp_all)
apply(subgoal_tac " x = uid",simp)
apply(erule invert[zstrip],rule uid_c,blast)
apply(subgoal_tac "uid ~= x", simp)
apply(erule  swap,simp)
done 

end
