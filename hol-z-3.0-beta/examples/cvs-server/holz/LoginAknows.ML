(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * LoginAknows.ML --- 
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
(* $Id: LoginAknows.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* This file contains lemmata which *)
(* are about uid, pwd in Aknows,    *)
(* using abs_login. (over the hull) *)


(*                    *)
(* login-lemma        *)
(* with x~:dom absPwd *)
(* and x:dom absPwd   *)

zgoalw SysArchSec.thy [] "                                \
\    ((%theta AbsState, %theta AbsState') : AtransR)      \
\ =+=>                                                    \
\         ((%theta AbsState):  InitAbsState)             \
\ =+=>                                                    \
\           x : dom abs_passwd'                           \
\ =+=>                                                    \
\           x ~: dom abs_passwd                           \
\ =+=>                                                    \
\  ((x, (abs_passwd' %^ x)) : Aknows  )";
by(stripS_tac 1);
by(rewrite_goals_tac [AtransR_def]);
br mp 1;
(*by(move2End ["x : dom abs_passwd'"] 1);*)
by(guidedAssumption ["x ~: dom abs_passwd"] 2);
br mp 1;
by(guidedAssumption ["x : dom abs_passwd'"] 2);
br mp 1;
by(guidedAssumption ["InitAbsState"] 2);

(*br mp 1;*)
(*by(guidedAssumption ["InitAbsState"] 2);*)
br mp 1;
by(eres_inst_tac [("P","%(abs_passwd0, rep0, rep_permtab0, wc0, wc_uidtab0, wfiles0). \
                       \%(abs_passwd1,rep1,rep_permtab1,wcS,wc_uidtab1,wfiles1).     \
                       \ ((abs_passwd0, rep0, rep_permtab0, wc0, wc_uidtab0, wfiles0)\
                       \     : (asSet InitAbsState)) =+=>        \
                       \  x : dom abs_passwd1 =+=>                \
                       \  x ~: dom abs_passwd0 =+=>               \
                       \   ((x, (abs_passwd1 %^ x)) : Aknows  )   ")] 
                 zrtrancl_full_induct2 2);
by(convert2hol_tac [] 1);

(* first base case. *)
(* contradicts via x : dom abs_passwd1. *)
by(filterPrems_drop ["InitAbsState (abs_passwd"] 1);
by(split_all_tac 1);
by(convert2hol_tac [] 1);

(* second base case. *)
(* contradicts via x : dom abs_passwd1. *)
by(filterPrems_drop ["InitAbsState (abs_passwd"] 1);
by(split_all_tac 1);
by(convert2hol_tac [] 1);

(* induction step.   *)
by(filterPrems_drop ["(%theta AbsState) : InitAbsState"] 1);
by(split_all_tac 1);
by(convert2hol_tac [] 1);

by(rename_tac "  \
              \ abs_passwdx abs_passwdy abs_passwdz repx repy repz \
              \ rep_permtabx rep_permtaby rep_permtabz \
              \ wcx wcy wcz wc_uidtabx wfilesx wc_uidtaby \
              \ wfilesy wc_uidtabz wfilesz \
\ " 1);
by(stripS_tac 1);
(* get the IV, stripped of *)
(* the implications.       *)
be impE 1;
ba 1;
bd imp_change 1;
be impE 1;
ba 1;
(*--- L27 *)
by(case_tac "x : dom abs_passwdy" 1);
by(defer_tac 1);
(* Fall 1 :  x ~: dom abs_passwdy *)
zbr AService_domDiff_imp_Aknows 1;
by(convert2hol_tac [] 1);
ba 1;
ba 1;
(* Fall 2 : x : dom abs_passwdy *)
be impE 1;
ba 1;
by(case_tac "abs_passwdy %^ x = abs_passwdz %^ x" 1);
(* case equal: take IV to show goal. *)
by(res_inst_tac [("s", "abs_passwdy %^ x"), 
		 ("t", "abs_passwdz %^ x")] subst 1);
ba 1;
ba 1;
(* case different: login changed the value => Aknows. *)
zbr AServiceAbsPwdNeq_I_Aknows_nTh 1;
by(convert2hol_tac [] 1);
ba 1;
qed"domDiff_loginAknows";



(* show for 2 arbitrary states:   *)
(* changed abspwd %^ x means that *)
(* ((x, (abs_passwd' %^ x)) : Aknows  ) *)
(* (because login must have occured)    *)

(*main goal*)
zgoalw SysArchSec.thy [] "                                \
\ (( (abs_passwd, rep, rep_permtab, wc, wc_uidtab, wfiles), \
\    (abs_passwdS, repS, rep_permtabS, wcS, wc_uidtabS, wfilesS)) : Areachable)\
\ =+=>                                                    \
\ ((abs_passwd %^x) ~= (abs_passwdS %^ x))                \
\ =+=>                                                    \
\  ((x, (abs_passwdS %^ x)) : Aknows  )";
by(stripS_tac 1);

(*br (stripS abs_loginR_fNeq_Aknows) 1; *)

by(rewrite_goals_tac [Areachable_def, dom_restr_def]);
by(rewtac AtransR_def);
bd elemSetConj 1;
by(atomizePrem 1);
bd doubleMember 1;
(* collect the additional assumptions: *)
by(res_inst_tac [("P", "((abs_passwd %^x) ~= (abs_passwdS %^ x))")] mp 1);
ba 2;

br mp 1;
(* manually instantiate zrtrancl_full_induct  *)

(* test: force isabelle to use                 *)
(* variable vector instead of single variable. *)

by(eres_inst_tac [("P","%(abs_passwd, rep, rep_permtab, wc, wc_uidtab, wfiles) . \
                       \%(abs_passwdS,repS,rep_permtabS,wcS,wc_uidtabS,wfilesS). \
                       \ ((abs_passwd %^x) ~= (abs_passwdS %^ x)) \
                       \                        =+=>        \
                       \   ((x, (abs_passwdS %^ x)) : Aknows  )")] 
                 zrtrancl_full_induct2 2);

by(convert2hol_tac [] 1);
(* remove the base cases *)
by(convert2hol_tac [split_def] 1);
by(convert2hol_tac [split_def] 1);

(* drop                     *)
(* assumption from beginning*)
by(thin_tac "?a" 1);
by(thin_tac "?a" 1);
by(rewrite_goals_tac [split_def]);
br impI 1;
(* change happend *)
(* xa    y     z  *)
(*  -----         *)
(* here ?         *)

by(case_tac "(fst xa) %^ x = (fst y) %^ x" 1);

bd mp 2;
ba 2;(* -++-- *)


by(case_tac "(fst z) %^ x = (fst y) %^ x" 2);
by(Asm_full_simp_tac 2);

bd nTrans 1;
ba 1;
(* This leaves two cases:    *)
(*                           *)
(* both imply a change       *)
(* happened between y and z .*)

(* ================================= *)
(* einsetzen des lemmas:             *)

(* expand y to tuple ... *)
by(split_all_tac 1);
by(Asm_full_simp_tac 1);
bd (stripS AServiceAbsPwdNeq_I_Aknows_nTh) 1;
by(Simp_tac 2);
by(Asm_full_simp_tac 1);

(* duplicate the previous steps *)
(* in principle.                *)

(* keep only the needed ineq.   *)
(* important here are:          *)
(* y,z:Aservice , andalso :     *)
(* fst z %^ x ~= fst y %^ x;    *)
(*  *)
by(thin_tac "?a" 1);
by(rotate_tac 1 1);
by(thin_tac "?a" 1);
by(thin_tac "?a" 1);
by(thin_tac "?a" 1);
(*  *)
bd nsym 1;
(* assum. in wrong position*)
by(split_all_tac 1);
by(Asm_full_simp_tac 1);
bd (stripS AServiceAbsPwdNeq_I_Aknows_nTh) 1;
by(Simp_tac 2);
by(Asm_full_simp_tac 1);
qed"absPwdNeq_loginAknows";
(* qed"LoginAknows"; *)

(* extended version of *)
(* lemma above.        *)

(* Toplevel - Login - Lemma. *)

zgoal thy "((%theta AbsState, %theta AbsState') : AtransR) =+=>       \
\         ((%theta AbsState):  InitAbsState)              =+=>       \
\           x : dom abs_passwd'                            =+=>       \
\       (x, (abs_passwd' %^ x)) : Aknows";
by(stripS_tac 1);
by(case_tac "x : dom abs_passwd" 1);
(* InitAbs_implies_Aknows *)
by(case_tac "(abs_passwd %^ x) = (abs_passwd' %^ x)" 1);
(* 1. case : initial uid from InitAbsState: *)
by(res_inst_tac [("t", 
		  "abs_passwd' %^ x"),
		 ("s",
		  "abs_passwd %^ x")] subst 1);
ba 1;
zbr InitAbs_implies_Aknows 1;
ba 1;
br relAppl_refl_example 1;
ba 1;
(* 2. case : use absPwdNeq_loginAknows *)

zbd hullInit_implies_Areachable 1;
ba 1;
zbr absPwdNeq_loginAknows 1;
by(convert2hol_tac [] 1);
ba 1;
(* HH *)
zbd domDiff_loginAknows 1;
by(AtomizePremSolveAll);
qed"loginAknows";
