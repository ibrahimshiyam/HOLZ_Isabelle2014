(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_repModify_lemmata.ML --- 
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
(* $Id: abs_repModify_lemmata.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* first case of the case distinction. *)
(* - new file in the repository.       *)

zgoal SysArchSec.thy "(%theta AbsState'', %theta AbsState) :   \
\  AtransR                                                     \
\ =+=>                                                         \
\ (%theta AbsState'') : InitAbsState                           \
\ =+=>                                                         \
\ abs_ciR                                                      \
\ =+=>                                                         \
\   ((%theta AbsState, %theta AbsState') :                     \
\    {.AService @ (%theta AbsState, %theta AbsState').} )      \
\ =+=>                                                         \
\ f : dom rep'                                                 \
\ =+=>                                                         \
\ f ~: dom rep                                                 \
\ =+=>                                                         \
\ (? m:Aknows.                                                 \
\        (rep_permtab' %^ f, authtab %^ rep' %^ m)             \
\          : cvs_perm_order)                                   \
\ ";
by(stripS_tac 1);
by(duplPrem "abs_ciR" 1);
zbd abs_ciR_implies_abs_ci 1;

(* -- original -- *)

(* -------------------------------- *)
(* case 1 : f ~: dom rep *)

by(res_inst_tac [("x", 
		  "((wc_uidtab %^ f), (abs_passwd %^ (wc_uidtab %^ f)))")] 
		bexI 1);
(* -- insert "we trust in admin"  : *)
by(res_inst_tac [("t", "authtab %^ rep'"), 
		 ("s", "authtab %^ rep")] subst 1);
(* ---------------- 1. admin - equality ---- *)
(* br constAuthtab 1;*)
(* fst of four subgoals. *)

zbd auth_invariant 1;
ba 1;
ba 1;
ba 1;

(* Old version using the constraint in abs_ciR
zbr unch_abs_cvsauth_implies_auth_invariant 1;
zbd (abs_ci_valid_AbsState
     ZRS
     AbsState_implies_RepositoryState
     ) 1;
ba 1;
zbr (abs_ci_valid_AbsStateS
     ZRS
     AbsState_implies_RepositoryState
     ) 1;
ba 1;

zbr abs_ciR_implies_repAuth_invariant 1;
ba 1;
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(convert2hol_tac [theta_def] 1);
*)


(* ---------------- 1. admin - equality ---- *)

(* show : rep_ptab f, (role, abspwd role) ):cvspermorder *)
zbd abs_ci_domDiff_permOrder 1;
ba 1;
ba 1;
ba 1;
(* show : (role, abspwd role) : Aknows *)
zbr (removeTheta(stripS loginAknows)) 1;
by(convert2hol_tac [theta_def] 1);
by(convert2hol_tac [theta_def] 1);
(* now: wc_uidtab %^ f : dom abs_passwd *)
zbr (removeSNAME(removeTheta definedAbsPwd)) 1;
by(convert2hol_tac [theta_def, AtransR_def] 1);
by(convert2hol_tac [theta_def] 1);

zbr abs_ci_domDiff_defined_wcUtb 1;
ba 1;
ba 1;
ba 1;
qed"rep_domDiff_implies_perm";



(* first case of the case distinction. *)
(* - changed file in the repository.   *)


zgoal SysArchSec.thy "((%theta AbsState'', %theta AbsState) :  \
\  AtransR                                                     \
\ =+=>                                                         \
\ (%theta AbsState'') : InitAbsState                           \
\ =+=>                                                         \
\   ((%theta AbsState, %theta AbsState') :                     \
\    {.AService @ (%theta AbsState, %theta AbsState').} )      \
\ =+=>                                                         \
\ abs_ciR                                                      \
\ =+=>                                                         \
\ f : dom rep'                                                 \
\ =+=>                                                         \
\ f  : dom rep                                                 \
\ =+=>                                                         \
\ rep %^ f ~= rep' %^ f                                        \
\ =+=>                                                         \
\ (? m:Aknows.                                                 \
\        (rep_permtab' %^ f, authtab %^ rep' %^ m)             \
\          : cvs_perm_order))                                  \
\ ";
by(stripS_tac 1);

by(duplPrem "abs_ciR" 1);
zbd abs_ciR_implies_abs_ci 1;

(* *)


by(res_inst_tac [("x", 
		  "((wc_uidtab %^ f), (abs_passwd %^ (wc_uidtab %^ f)))")] 
		bexI 1);
(* -- insert "we trust in admin"  : *)
by(res_inst_tac [("t", "authtab %^ rep'"), 
		 ("s", "authtab %^ rep")] subst 1);

(* ---------------- 2. admin - equality ---- *)
(* br constAuthtab 1;*)
(* fst of four subgoals. *)


zbd auth_invariant 1;
ba 1;
ba 1;
ba 1;


(* Old version using the constraint in abs_ciR
zbr unch_abs_cvsauth_implies_auth_invariant 1;
zbd (abs_ci_valid_AbsState
     ZRS
     AbsState_implies_RepositoryState
     ) 1;
ba 1;
zbr (abs_ci_valid_AbsStateS
     ZRS
     AbsState_implies_RepositoryState
     ) 1;
ba 1;

zbr abs_ciR_implies_repAuth_invariant 1;
ba 1;
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(convert2hol_tac [theta_def] 1);
*)
(* ---------------- 2. admin - equality ---- *)
(* Level 109 *)

zbd abs_ci_fNeq_permOrder 1;
ba 1;
ba 1;
ba 1;
(*  *)

(* show : (role, abspwd role) : Aknows *)
zbr (removeTheta(stripS loginAknows)) 1;
by(convert2hol_tac [theta_def] 1);
by(convert2hol_tac [theta_def] 1);
(* now: wc_uidtab %^ f : dom abs_passwd *)

zbr (removeSNAME(removeTheta definedAbsPwd)) 1;
by(convert2hol_tac [theta_def, AtransR_def] 1);
by(convert2hol_tac [theta_def] 1);

(*  *)
zbr abs_ci_fNeq_defined_wcUtb 1;
ba 1;
ba 1;
ba 1;
qed"rep_fNeq_implies_perm";
