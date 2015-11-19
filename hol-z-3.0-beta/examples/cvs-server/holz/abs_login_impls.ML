(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_login_impls.ML --- 
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
(* $Id: abs_login_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)


(* some simple implications of abs_loginR *)

zgoal SysArchSec.thy "abs_loginR =+=> ?Y : Cvs_Uid";
by(stripS_tac 1);
by(full_expand_schema_tac abs_loginR_def 1);
be conjE 1;
bd DECL_D1 1;
by(atomizePremSolve 1);
qed"abs_loginR_implies_typeUid";

zgoal SysArchSec.thy "abs_loginR =+=> ?Y : Cvs_Passwd";
by(stripS_tac 1);
by(full_expand_schema_tac abs_loginR_def 1);
be conjE 1;
bd DECL_D1 1;
by(atomizePremSolve 1);
qed"abs_loginR_implies_typePwd";

(* This is a implication of    *)
(* the abs_login - Operation : *)
(* dom abs_passwd <=           *)
(*  dom abs_passwd'            *)


(* The Lemma used in the text results  *)
(* from using forward reasoning on     *)
(* abs_loginR_implies_abs_login and the*)
(* following lemma.                    *)
(* text-name:abs_loginR_domAbsPwd_mono *)

zgoal thy "abs_login =+=> (dom abs_passwd <= dom abs_passwd')";
by(stripS_tac 1);
by(full_expand_schema_tac abs_login_def 1);
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_keep["abs_passwd' ="] 1);
bd oplDomSubset 1;
ba 1;
qed"abs_login_domAbsPwd_mono";

zgoal SysArchSec.thy"abs_loginR =+=> abs_login";
by(stripS_tac 1);
by(convert2hol_tac [abs_loginR_def] 1);
qed"abs_loginR_implies_abs_login";



(*             *)
(* lemma       *)
(* absLoginR_chPwd_I_knows                   *)
(* from changed entry in abs_passwd conclude *)
(* aknows holds for the tuple.               *)

zgoal SysArchSec.thy "abs_loginR =+=> (a,b): abs_passwd' \
\ =+=> (a,b)~: abs_passwd =+=>                           \
\ (a,b):Aknows";
by(stripS_tac 1);
by(convert2hol_tac [abs_loginR_def, abs_login_def, maplet_def] 1);
auto();
qed"absLoginR_chPwd_I_knows";

(* slightly more comfortable version *)

zgoal thy "abs_loginR =+=> \
\ x ~: dom abs_passwd =+=> \
\ x : dom abs_passwd' =+=> \
\ (x, (abs_passwd' %^ x)) : Aknows";
by(stripS_tac 1);
zbr absLoginR_chPwd_I_knows 1;
ba 1;
br relAppl_refl_example 1;
ba 1;
br DomNotE 1;
ba 1;
qed"abs_loginR_domDiff_Aknows";

(*             *)
(* lemma       *)
(* absLoginRNeqPwd_I_uid                     *)
(* from changed entry in abs_passwd conclude *)
(* uid parameter was changed.                *)
(* This one allows us to imply Aknows        *)
(* (x, abs_passwdS %^ x) later.              *)

zgoal SysArchSec.thy "(abs_passwd, abs_passwdS, passwd, rep, repS, rep_permtab,\
\         rep_permtabS, uid, wc, wcS, wc_uidtab, wc_uidtabS, wfiles,   \
\         wfilesS) : abs_loginR =+=>                                   \
\       (abs_passwd %^ x ~= abs_passwdS %^ x)                          \
\        =+=> (x = uid)   ";
by(stripS_tac 1);

by(full_expand_schema_tac abs_loginR_def 1);
by(full_expand_schema_tac abs_login_def 1);
by(convert2hol_tac [] 1);
by(atomizePrem 1);
(* essential is:                                               *)
(* abs_passwd %^ x ~= (abs_passwd (+) {uid |--> passwd}) %^ x; *)
(* (via changeOverrid)                                         *)
br changeOverrid 1;
ba 1;
(*                *)
qed"absLoginRNeqPwd_I_uid";


(*                          *)
(* lemma                    *)
(* absLoginRNeqPwd_I_passwd *)
(* show pwd? = abspasswd' x *)
(* (modulo renaming.)       *)

zgoal SysArchSec.thy "(abs_passwd, abs_passwdS, passwd, rep, repS, rep_permtab,\
\         rep_permtabS, uid, wc, wcS, wc_uidtab, wc_uidtabS, wfiles,   \
\         wfilesS) : abs_loginR =+=>                                   \
\       (abs_passwd %^ x ~= abs_passwdS %^ x)                          \
\        =+=> ((abs_passwdS %^ x) = passwd)   ";
by(stripS_tac 1);

by(full_expand_schema_tac abs_loginR_def 1);
by(full_expand_schema_tac abs_login_def 1);
by(convert2hol_tac [] 1);
by(atomizePrem 1);
br fapply_overrid 1;

by(res_inst_tac [("P","abs_loginR(abs_passwd, abs_passwdS, passwd, rep, repS, rep_permtab, rep_permtabS, uid, wc, wcS, wc_uidtab, wc_uidtabS, wfiles, wfilesS)")] mp 1);

br impI 1;
br (stripS absLoginRNeqPwd_I_uid) 1;
by(convert2hol_tac [] 1);
ba 1;

by(full_expand_schema_tac abs_loginR_def 1);
by(full_expand_schema_tac abs_login_def 1);
by(convert2hol_tac [] 1);
auto();
qed"absLoginRNeqPwd_I_pwd";




(* show (x, abspasswd' x) : Aknows *)
(* (modulo renaming.)              *)

zgoal SysArchSec.thy "(abs_passwd, abs_passwdS, passwd, rep, repS, rep_permtab,\
\         rep_permtabS, uid, wc, wcS, wc_uidtab, wc_uidtabS, wfiles,  \
\         wfilesS) : abs_loginR =+=>                                  \
\       (abs_passwd %^ x ~= abs_passwdS %^ x)                         \
\        =+=> ((x, (abs_passwdS %^ x)): Aknows)   ";
by(stripS_tac 1);
by(res_inst_tac [("s", "(uid, passwd)"), 
		 ("t", "(x, abs_passwdS %^ x)")] subst 1);
by(convert2hol_tac [abs_loginR_def] 2);
br pairEq 1;
br sym 1;
br sym 2;

br (stripS absLoginRNeqPwd_I_uid) 1;
by(convert2hol_tac [] 1);
ba 1;

br (stripS absLoginRNeqPwd_I_pwd) 1;
by(convert2hol_tac [] 1);
ba 1;
qed"abs_loginR_fNeq_Aknows";



