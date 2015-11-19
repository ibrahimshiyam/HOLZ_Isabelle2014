(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * Basics.thy --- 
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
(* $Id: Basics.thy 8059 2008-06-02 09:33:36Z wolff $ *)

theory  Basics
imports Z

begin

section{* Loading a ZETA-unit and the Consequences *}

load_holz "Basics"   

thm AXDEFS

ML{* ZTheory.print_TC (the_context()) *}

thm Basics.COMMAND.simps

lemma new_fresh [simp]: 
"X \<in> %F SESSION_ID \<Longrightarrow> (new %^ X) \<notin> X"
by(insert new_axdef,auto)

lemma  NULL_def : "NULL = Inr unit";
by(insert NO_USER_axdef,auto)

lemma NULL_KEY_def : "NULL_KEY = Inr unit"
by(insert NO_USER_axdef,auto)

lemma NO_USER_def : "NO_USER = Inr unit"
by(insert NO_USER_axdef,auto)

lemma NULL_is_SIGNATURE: "NULL \<in> SIGNATURE";
by(insert NO_USER_axdef,auto)

lemma NULL_KEY_is_PRI_KEY :  "NULL_KEY \<in> PRI_KEY"
by(insert NO_USER_axdef,auto)

lemma NO_USER_is_USER_ID: "NO_USER \<in> USER_ID";
by(insert NO_USER_axdef,auto)

declare NULL_is_SIGNATURE NULL_KEY_is_PRI_KEY NO_USER_is_USER_ID [simp]
declare NULL_def NULL_KEY_def NO_USER_def [simp del]
(* These definitions should not be automatically unfolded,
   as is HOL-Z default strategy. *)

lemmas axdef_preds = AXDEFS[THEN DECL_D2]

lemma CRYPT_ERR_def : "CRYPT_ERR = Inr crypt_err" by (auto simp: axdef_preds)
lemma NO_USER_ERR_def:"NO_USER_ERR = Inr no_user_err" by (auto simp: axdef_preds) 
lemma INVALID_PW_ERR_def: "INVALID_PW_ERR = Inr invalid_pw_err" by (auto simp: axdef_preds)
lemma SAME_USER_ERR_def: "SAME_USER_ERR = Inr same_user_err" by (auto simp: axdef_preds)

declare CRYPT_ERR_def NO_USER_ERR_def SAME_USER_ERR_def [simp del]
(* correcting default configuration *)

lemma AUTH_ERRORS_def :
"AUTH_ERRORS = {CRYPT_ERR, NO_USER_ERR, INVALID_PW_ERR, SAME_USER_ERR}"
by (auto simp: axdef_preds)

lemma CRYPT_ERR_in_AUTH_ERRORS : "CRYPT_ERR : AUTH_ERRORS" by (auto simp: axdef_preds)

lemma SAME_USER_ERR_in_AUTH_ERRORS: "SAME_USER_ERR : AUTH_ERRORS" by(auto simp: axdef_preds)

lemma NO_USER_ERR_in_AUTH_ERRORS: "NO_USER_ERR : AUTH_ERRORS" by(auto simp: axdef_preds)

lemma INVALID_PW_ERR_in_AUTH_ERRORS: "INVALID_PW_ERR : AUTH_ERRORS" by(auto simp: axdef_preds)

declare NO_USER_ERR_def INVALID_PW_ERR_def SAME_USER_ERR_def AUTH_ERRORS_def[simp del]
(* correcting default configuration *)
declare CRYPT_ERR_in_AUTH_ERRORS SAME_USER_ERR_in_AUTH_ERRORS
        NO_USER_ERR_in_AUTH_ERRORS INVALID_PW_ERR_in_AUTH_ERRORS [simp]

lemma X_in_SIGNATURE [simp,tc_simp] : "X : SIGNATURE"
by(auto simp: SIGNATURE_def Plus_def image_def,
   rule_tac s=X in sumE, auto)

lemma X_in_USER_ID [simp,tc_simp] : "X : USER_ID"
by(auto simp: USER_ID_def Plus_def image_def,
   rule_tac s=X in sumE, auto)

lemma X_in_PRI_KEY [simp,tc_simp] : "X : PRI_KEY"
by(auto simp: PRI_KEY_def Plus_def image_def,
   rule_tac s=X in sumE, auto)

lemma X_in_SESSION_ID [simp,tc_simp] : "X : SESSION_ID"
by(auto simp: SESSION_ID_def Plus_def image_def,
   rule_tac s=X in sumE, auto)


lemma NO_USER_not_in_dom_SESSION_TABLE: 
"ssn_tbl : SESSION_TABLE ==> NO_USER ~: dom ssn_tbl"
apply(simp add: SESSION_TABLE_def)
apply(rule contra_subsetD)
apply(rule Rel_Dom_subset)
apply(erule Pfun_Rel, auto)
done


lemma NO_USER_not_in_dom_SESSION_TABLE_rev [simp]:
"[| ssn_tbl : SESSION_TABLE; x : dom ssn_tbl |] ==> x ~= NO_USER"
apply(erule_tac Q="x : dom ssn_tbl" in contrapos_pn)
apply simp
apply(simp add: NO_USER_not_in_dom_SESSION_TABLE)
done


lemma CRYPT_ERR_not_in_dom_dom_SESSION_TABLE[simp]:
"[| ssn_tbl : SESSION_TABLE; x : dom ssn_tbl|] 
 ==> CRYPT_ERR ~: dom(ssn_tbl %^ x)"
apply(rule contra_subsetD, rule Rel_Dom_subset, rule Pfun_Rel,rule pfun_apply) 
apply(simp_all add: SESSION_TABLE_def AUTH_ERRORS_def, auto)
done


lemma NO_USER_ERR_not_in_dom_dom_SESSION_TABLE[simp]:
"[| ssn_tbl : SESSION_TABLE; x : dom ssn_tbl|] 
 ==> NO_USER_ERR ~: dom(ssn_tbl %^ x)"
apply(rule contra_subsetD, rule Rel_Dom_subset, rule Pfun_Rel,rule pfun_apply) 
apply(simp_all add: SESSION_TABLE_def AUTH_ERRORS_def, auto)
done

lemma INVALID_PW_ERR_not_in_dom_dom_SESSION_TABLE[simp]:
"[| ssn_tbl : SESSION_TABLE; x : dom ssn_tbl|] 
 ==> INVALID_PW_ERR  ~: dom(ssn_tbl %^ x)"
apply(rule contra_subsetD, rule Rel_Dom_subset, rule Pfun_Rel,rule pfun_apply) 
apply(simp_all add: SESSION_TABLE_def AUTH_ERRORS_def, auto)
done

lemma SAME_USER_ERR_not_in_dom_dom_SESSION_TABLE[simp]:
"[| ssn_tbl : SESSION_TABLE; x : dom ssn_tbl|] 
 ==> SAME_USER_ERR ~: dom(ssn_tbl %^ x)"
apply(rule contra_subsetD, rule Rel_Dom_subset, rule Pfun_Rel,rule pfun_apply) 
apply(simp_all add: SESSION_TABLE_def AUTH_ERRORS_def, auto)
done

lemma NO_USER_not_in_dom_ACCESS_CONTROL_LIST[simp]:
" acl : ACCESS_CONTROL_LIST ==> NO_USER ~: dom acl";
by(simp add: ACCESS_CONTROL_LIST_def,
   rule contra_subsetD, rule Rel_Dom_subset, rule Pfun_Rel, auto) 



lemma new_neq_CRYPT_ERR[simp]:
"X : %F SESSION_ID ==> (new %^ X) ~= CRYPT_ERR"
by(insert new_axdef AUTH_ERRORS_def, drule DECL_D1,
   drule tfun_apply, auto)

lemma new_neq_NO_USER_ERR[simp]:
"X : %F SESSION_ID ==> (new %^ X) ~= NO_USER_ERR"
by(insert new_axdef AUTH_ERRORS_def, drule DECL_D1,
   drule tfun_apply, auto)

lemma INVALID_PW_ERR [simp]:
"X : %F SESSION_ID ==> (new %^ X) ~= INVALID_PW_ERR"
by(insert new_axdef AUTH_ERRORS_def, drule DECL_D1,
   drule tfun_apply, auto)

lemma new_neq_SAME_USER_ERR[simp]:
"X : %F SESSION_ID ==> (new %^ X) ~= SAME_USER_ERR"
by(insert new_axdef AUTH_ERRORS_def, drule DECL_D1,
   drule tfun_apply, auto)


lemma pri_key_lst_apply_not_NULL_KEY[simp]:
"[| X : dom pri_key_lst;  pri_key_lst: PRI_KEY_LIST |] ==> 
    pri_key_lst %^ X ~= NULL_KEY"
apply(simp add:PRI_KEY_LIST_def)
apply(frule pfun_apply, auto) 
done

lemma aux1 :
"[| ssn_tbl : SESSION_TABLE |] ==>  
 {uid. uid : dom ssn_tbl & P uid}  <= USER_ID - {NO_USER}"
by(simp add: SESSION_TABLE_def, erule pfunE, drule Rel_Dom_subset, auto)



lemma aux2:
"[| ssn_tbl : SESSION_TABLE;  (sid, y) : X; (x, X) : ssn_tbl |]                      
 ==>  { uid. uid : dom ssn_tbl & sid : dom (ssn_tbl %^ uid)} ~= {}"
by(simp only: SESSION_TABLE_def all_not_in_conv[symmetric], auto)


lemma aux2':
"[| ssn_tbl : SESSION_TABLE;                               
    sid : dom(ssn_tbl %^ x); x : dom ssn_tbl |]           
  ==> { uid. uid : dom ssn_tbl & sid : dom (ssn_tbl %^ uid)} ~= {}"
by(simp only: SESSION_TABLE_def all_not_in_conv[symmetric], auto)


lemma aux3:
"[| ssn_tbl : SESSION_TABLE;                               
    (sid, y) : X; (x, X) : ssn_tbl |]                    
 ==> {uid. uid : dom ssn_tbl & sid : dom (ssn_tbl %^ uid)} <= dom ssn_tbl"
by(auto simp: SESSION_TABLE_def)

declare X_in_SIGNATURE X_in_USER_ID X_in_PRI_KEY X_in_SESSION_ID [tc_simp]


ML{* ZTheory.print_TC (the_context()) *}

end
