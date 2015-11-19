(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * AService_impls.ML --- 
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
(* $Id: AService_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* implications of command steps    *)
(* on the abstract layer (AService) *)



(* ======================== *)
(* implications of AService *)
(* concerning abs_loginR.   *)
(* ======================== *)

(* one transition and a change  *)
(* in abs_passwd means:         *)
(* abs_loginR was carried out.  *)

(* not sure if this version will be *)
(* useful.                          *)
zgoal SysArchSec.thy "(((%theta AbsState, %theta AbsState') :  \
\  {.AService @ (%theta AbsState, %theta AbsState').} )        \
\  /\\   ((abs_passwd %^x) ~= (abs_passwd' %^ x)))             \
\ =+=> (? passwd? : Cvs_Passwd . (? uid? : Cvs_Uid . abs_loginR))";
by(stripS_tac 1);
(* use or-chain instead of other representation *)
br mp 1;
br (stripS AService_imp_Ops) 2;
by(atomizePremSolve 2);
br impI 1;
auto();
(* leaves 6 cases *)

(* abs_loginR *)
br bexI 1;
br bexI 1;
ba 1;
by(convert2hol_tac [abs_loginR_def] 1);
by(convert2hol_tac [abs_loginR_def] 1);

(* 5 times contradict on         *)
(* abs_passwd %^ x = abs_passwd' %^ x *)

(* case: abs_addR   *)
by(res_inst_tac [("P", "abs_passwd %^ x = abs_passwd' %^ x")] notE 1);
ba 1;
by(convert2hol_tac [abs_addR_def, abs_add_def] 1);

(* case: abs_ci     *)
by(res_inst_tac [("P", "abs_passwd %^ x = abs_passwd' %^ x")] notE 1);
ba 1;
by(convert2hol_tac [abs_ciR_def,abs_ci_def, theta_def] 1);

(* case: abs_up     *)
by(res_inst_tac [("P", "abs_passwd %^ x = abs_passwd' %^ x")] notE 1);
ba 1;
by(convert2hol_tac [abs_up_def] 1);

(* case: abs_cd     *)
by(res_inst_tac [("P", "abs_passwd %^ x = abs_passwd' %^ x")] notE 1);
ba 1;
by(convert2hol_tac [abs_cd_def] 1);

(* case: modifyR     *)
by(res_inst_tac [("P", "abs_passwd %^ x = abs_passwd' %^ x")] notE 1);
ba 1;
by(convert2hol_tac [modifyR_def, modify_def] 1);
qed"AServiceAbsPwdNeq_imp_absLoginR";




(* combining 2 lemmas:             *)
(*                                 *)
(* abs_loginR_fNeq_Aknows        *)
(* and                             *)
(* AServiceAbsPwdNeq_imp_absLoginR *)
(*                                 *)

zgoal SysArchSec.thy "((%theta AbsState, %theta AbsState') :  \
\  {.AService @ (%theta AbsState, %theta AbsState').} )       \
\  =+=>   ((abs_passwd %^x) ~= (abs_passwd' %^ x))            \
\        =+=> ((x, (abs_passwd' %^ x)): Aknows)   ";
by(stripS_tac 1);

bd (conjI RS (stripS AServiceAbsPwdNeq_imp_absLoginR)) 1;
ba 1;

be bexE 1;
be bexE 1;

br (stripS abs_loginR_fNeq_Aknows) 1;
ba 2;
by(convert2hol_tac [] 1);

qed"AServiceAbsPwdNeq_I_Aknows";


(* convert the lemma              *)
(* AServiceAbsPwdNeq_I_Aknows     *)
(* to avoid the theta formulation *)

zgoal SysArchSec.thy "(( (abs_passwd, rep, rep_permtab, wc, wc_uidtab, wfiles), \
\ (abs_passwdS, repS, rep_permtabS, wcS, wc_uidtabS, wfilesS)   \
\ ) :  \
\  {.AService @ (%theta AbsState, %theta AbsState').} )       \
\  =+=>   ((abs_passwd %^x) ~= (abs_passwdS %^ x))            \
\        =+=> ((x, (abs_passwdS %^ x)): Aknows)   ";
by(stripS_tac 1);
br (stripS AServiceAbsPwdNeq_I_Aknows ) 1;
ba 2;
by(convert2hol_tac [] 1);
qed"AServiceAbsPwdNeq_I_Aknows_nTh";


(* use small pattern for the following lemma *)
(* contradiction on abs_passwd = abs_passwd' *)
(* (experimental proof reuse)                *)
fun loginProofPattern invLemma 
  = (
     by(res_inst_tac [("P","abs_passwd = abs_passwd'")] notE 2);
     by(atomizePrem_ex 3);
     zbd invLemma 3;
     ba 3;
     br nsym 2;
     br chDom_implies_chFunc 2;
     ba 2;
     ba 2
     );
(* could be written more general using a    *)
(* goal number and THEN instead of always   *)
(* directly applying the tactics.           *)  

zgoal SysArchSec.thy "((%theta AbsState, %theta AbsState') :   \
\  {.AService @ (%theta AbsState, %theta AbsState').} )         \
\  =+=>   (x ~: dom abs_passwd)                                   \
\  =+=>   (x  : dom abs_passwd')                                  \
\ =+=> (? passwd? : Cvs_Passwd . (? uid? : Cvs_Uid . abs_loginR))";
by(stripS_tac 1);
zbd AService_imp_Ops 1;
be disjE 1;
(* case modifyR :*)
loginProofPattern modifyR_invariant_absPwd;
be disjE 1;
(* case abs_cd *)
loginProofPattern abs_cd_invariant_absPwd;
be disjE 1;
(* case abs_up *)
loginProofPattern abs_up_invariant_absPwd;
be disjE 1;
(* case abs_ci *)
loginProofPattern abs_ciR_invariant_absPwd;
be disjE 1;
(* case abs_addR *)
loginProofPattern abs_addR_invariant_absPwd;
(* case abs_loginR        *)
(* now, don't contradict. *)
by(atomizePrem_ex 1);
br bexI 1; 
br bexI 1;
ba 1;
zbd abs_loginR_implies_typeUid 1;
ba 1;
zbd abs_loginR_implies_typePwd 1;
ba 1;
qed"AService_domDiff_imp_absLoginR";


zgoal SysArchSec.thy "((%theta AbsState, %theta AbsState') :  \
\  {.AService @ (%theta AbsState, %theta AbsState').} )       \
\  =+=>   (x ~: dom abs_passwd)                               \
\  =+=>   (x  : dom abs_passwd')                              \
\        =+=> ((x, (abs_passwd' %^ x)): Aknows)   ";
by(stripS_tac 1);
zbd AService_domDiff_imp_absLoginR 1;
ba 1;
ba 1;
by(atomizePrem_ex 1);
zbd abs_loginR_domDiff_Aknows 1;
by(AtomizePremSolveAll);
qed"AService_domDiff_imp_Aknows";



(* ======================== *)
(* implications of AService *)
(* concerning abs_ciR       *)
(* ======================== *)



(*  lemma                   *)
(* AServiceRepNeq_imp_absCi *)
(*                          *)

(* one transition and a changed *)
(* file in the repository means:*)
(* abs_ci was carried out.      *)

zgoal SysArchSec.thy "(((%theta AbsState, %theta AbsState') :  \
\  {.AService @ (%theta AbsState, %theta AbsState').} )        \
\ /\\   (rep %^ f ~= rep' %^ f))                               \
\ =+=> ( ? files? : %P Abs_Name . abs_ciR)";
by(stripS_tac 1);
(* use or-chain instead of other representation *)
br mp 1;
br (stripS AService_imp_Ops) 2;
by(atomizePremSolve 2);
br impI 1;
auto();

(* leaves 5 cases. Now:          *)
(* 5 times contradict with theta *)
(* and  rep^f != rep'^f          *)

(* case: abs_loginR *)
by(res_inst_tac [("P", "rep %^ f ~= rep' %^ f")] notE 1);
ba 2;
by(convert2hol_tac [abs_loginR_def, abs_login_def, theta_def] 1);

(* case: abs_addR   *)
by(res_inst_tac [("P", "rep %^ f ~= rep' %^ f")] notE 1);
ba 2;
by(convert2hol_tac [abs_addR_def, abs_add_def, theta_def] 1);

(* case: abs_up     *)
by(res_inst_tac [("P", "rep %^ f ~= rep' %^ f")] notE 1);
ba 2;
by(convert2hol_tac [abs_up_def, theta_def] 1);

(* case: abs_cd     *)
by(res_inst_tac [("P", "rep %^ f ~= rep' %^ f")] notE 1);
ba 2;
by(convert2hol_tac [abs_cd_def, theta_def] 1);


(* case: modifyR     *)
by(res_inst_tac [("P", "rep %^ f ~= rep' %^ f")] notE 1);
ba 2;
by(convert2hol_tac [modifyR_def, modify_def, theta_def] 1);

qed"AServiceRepNeq_imp_absCi";


(* convert the lemma              *)
(* AServiceRepNeq_imp_absCi       *)
(* to avoid the theta formulation *)

zgoal SysArchSec.thy "(( (abs_passwd, rep, rep_permtab, wc, wc_uidtab, wfiles), \
\ (abs_passwdS, repS, rep_permtabS, wcS, wc_uidtabS, wfilesS)     \
\ ) :                                                             \
\  {.AService @ (%theta AbsState, %theta AbsState').} )           \
\ =+=>   (rep %^ f ~= repS %^ f)                                  \
\ =+=> ( ? filesq : (%P Abs_Name) .                               \
\  ((abs_passwd, abs_passwdS, filesq, rep, repS, rep_permtab,     \
\         rep_permtabS, wc, wcS, wc_uidtab, wc_uidtabS, wfiles,   \
\ wfilesS) : abs_ciR))";

by(stripS_tac 1);
br mp 1;
br (conjI RS(stripS  AServiceRepNeq_imp_absCi)) 2;
by(convert2hol_tac [] 1);
ba 3;

by(convert2hol_tac [] 2);
by(convert2hol_tac [] 1);
qed"AServiceRepNeq_imp_absCi_nTh";

