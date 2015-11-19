(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * initial_permAdmin.ML --- 
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
(* $Id: initial_permAdmin.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* 2 main lemmata / left and right subtrees of*)
(* the ND - proof.                            *)

zgoal SysArchSec.thy "                    \
\ (%theta AbsState'', %theta AbsState) :  \
\  AtransR                                \
\              =+=>                       \
\ (%theta AbsState'') : InitAbsState      \
\              =+=>                       \
\ abs_ci                                  \
\              =+=>                       \
\ authtab %^ rep = authtab %^ rep''       \
\              =+=>                       \
\ authtab %^ rep ~= authtab %^ rep'       \
\              =+=>                       \
\ (authtab %^ rep %^                      \
\  (wc_uidtab %^ abs_cvsauth,                       \
\      abs_passwd %^ (wc_uidtab %^ abs_cvsauth)))   \
\ ~= Basics.cvs_admin                               ";
by(stripS_tac 1);
by(res_inst_tac [("t", "authtab %^ rep"),
		 ("s", "authtab %^ rep''")] subst 1);
br sym 1;
ba 1;
zbr InitAbsState_implies_noPermAdmin 1;
by(convert2hol_tac [theta_def] 1);
zbr loginAknows 1;
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(removeTheta_tac 1);
by(duplPrem "abs_ci" 1);
zbr definedAbsPwd 1;
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(removeTheta_tac 1);
zbd auth_inDom_wcUtb 1;
ba 2;

zbr ch_authtab_implies_ch_abs_cvsauth 1;
ba 3;
zbd (abs_ci_valid_AbsState 
	 ZRS 
	 AbsState_implies_RepositoryState) 1;
ba 1;
zbd (abs_ci_valid_AbsStateS 
	 ZRS 
	 AbsState_implies_RepositoryState) 1;
ba 1;
qed"abs_ci_perm_neq_admin";



zgoal SysArchSec.thy "                    \
\ (%theta AbsState'', %theta AbsState) :  \
\  AtransR                                \
\              =+=>                       \
\ (%theta AbsState'') : InitAbsState      \
\              =+=>                       \
\ abs_ci                                  \
\              =+=>                       \
\ authtab %^ rep ~= authtab %^ rep'       \
\              =+=>                       \
\ (authtab %^ rep %^                      \
\  (wc_uidtab %^ abs_cvsauth,                       \
\      abs_passwd %^ (wc_uidtab %^ abs_cvsauth)))   \
\  = Basics.cvs_admin                               ";
by(stripS_tac 1);
zbr admin_perm_only 1;
(* get rid of the cvs_perm - Set constraint. *)
br pfun_appl 2;

zbr abs_ci_authNeq_defined 3;
ba 3;

zbr ch_authtab_implies_ch_abs_cvsauth 3;
ba 5;
zbd (abs_ci_valid_AbsState 
	 ZRS 
	 AbsState_implies_RepositoryState) 3;
ba 3;
zbd (abs_ci_valid_AbsStateS 
	 ZRS 
	 AbsState_implies_RepositoryState) 3;
ba 3;

zbd (abs_ci_valid_AbsState
	 ZRS
	 AbsState_implies_RepositoryState
	 ZRS 
	 validAuth) 2;
by(rewtac AUTH_TAB_def);
ba 2;
(* /get rid of the cvs_perm - Set constraint./ *)
(* 1. rep_permtab abs_cvsauth = cvs_admin *)
by(res_inst_tac [("t", "Basics.cvs_admin"),
		 ("s", "rep_permtab' %^ abs_cvsauth")] subst 1);
zbd (abs_ci_valid_AbsStateS
	 ZRS
	 AbsState_implies_RepositoryState) 1;
zbr RepState_implies_permCvsauth 1;
by(convert2hol_tac [] 1);
(* 2. ?term : cvs_perm_order *)
zbr abs_ci_fNeq_permOrder 1;
ba 1;
zbr abs_cvsauth_inDom_rep 1;
zbd (abs_ci_valid_AbsStateS 
    ZRS
    AbsState_implies_RepositoryState) 1;
ba 1;
(* 3. rep %^ abs_cvsauth ~= rep' %^ abs_cvsauth *)

zbr ch_authtab_implies_ch_abs_cvsauth 1;
ba 3;
zbd (abs_ci_valid_AbsState 
	 ZRS 
	 AbsState_implies_RepositoryState) 1;
ba 1;
zbd (abs_ci_valid_AbsStateS 
	 ZRS 
	 AbsState_implies_RepositoryState) 1;
ba 1;
qed"abs_ci_perm_admin";




(* the complete inductive proof *)

zgoal SysArchSec.thy "                   \
\ (%theta AbsState, %theta AbsState') :  \
\  AtransR                               \
\              =+=>                      \
\ InitAbsState                           \
\              =+=>                      \
\ authtab %^ rep = authtab %^ rep'       ";

by(stripS_tac 1);
by(rewtac AtransR_def);
br mp 1;
by(guidedAssumption ["InitAbsState"] 2);
br mp 1;

by(eres_inst_tac [("P","%(abs_passwd0, rep0, rep_permtab0,   \
		       \wc0, wc_uidtab0, wfiles0) .          \
		       \%(abs_passwd1,rep1,rep_permtab1,     \
		       \wc1,wc_uidtab1,wfiles1).             \
		       \                                     \
                       \  ((abs_passwd0, rep0, rep_permtab0, \ 
		       \ wc0, wc_uidtab0, wfiles0)           \
                       \  : (asSet InitAbsState)) =+=>       \
                       \ (authtab %^ rep0 = authtab %^ rep1) ")] 
                 zrtrancl_full_induct2 2);
by(convert2hol_tac [theta_def] 1);

(* solve base cases trivially - *)
(* using refl (identity)        *)

(* base case 1 *)
by(convert2hol_tac [split_def] 1);

(* base case 2 *)
by(convert2hol_tac [split_def] 1);

(* induction step *)
by(filterPrems_drop ["SNAME InitAbsState"] 1);
by(prune_params_tac);
(* -prepare induction step- *)
by(split_all_tac 1);
by(convert2hol_tac [] 1);
by(stripS_tac 1);

by(rename_tac "  \
              \ abs_passwdx abs_passwdy abs_passwdz repx repy repz \
              \ rep_permtabx rep_permtaby rep_permtabz \
              \ wcx wcy wcz wc_uidtabx wc_filesx wc_uidtaby \
              \ wfilesy wc_uidtabz wfilesz \
\ " 1);
(* The string had to be changed here: 'n' was removed! *)
br mp 1;
zbr (removeTheta AService_imp_Ops) 2;
by(convert2hol_tac [] 2);
br impI 1;
(* -/prepare induction step/- *)

(* note: authtab %^ repx = authtab %^ repz already *)
(* replaced by authtab %^ repy = authtab %^ repz   *)
be impE 1;
ba 1;

(* now: use Xi RepositoryState and solve goal by   *)
(* reflexivity.                                    *)

be disjE 1;
(* abs_loginR *)
by(atomizePrem_ex 1);
zbd abs_loginR_implies_rep_invariant 1;
by(hyp_subst_tac 1);
br refl 1;

be disjE 1;
(* abs_addR *)
by(atomizePrem_ex 1);
zbd abs_addR_implies_rep_invariant 1;
by(hyp_subst_tac 1);
br refl 1;

be disjE 1;
by(defer_tac 1);(* abs_ciR delayed. *)

be disjE 1;
(* abs_up   *)
by(atomizePrem_ex 1);
zbd abs_up_implies_rep_invariant 1;
by(hyp_subst_tac 1);
br refl 1;

be disjE 1;
(* abs_cd   *)
by(atomizePrem_ex 1);
zbd abs_cd_implies_rep_invariant 1;
by(hyp_subst_tac 1);
br refl 1;

(* abs_modifyR   *)
by(atomizePrem_ex 1);
zbd modifyR_implies_rep_invariant 1;
by(hyp_subst_tac 1);
br refl 1;

(* now: main case: abs_ciR .*)
br ccontr 1;
by(atomizePrem_ex 1);
br notE 1;
(* left subtree ----*)
zbr abs_ci_perm_neq_admin 1;
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(convert2hol_tac [theta_def] 1);
zbd abs_ciR_implies_abs_ci 1;
ba 1;
br sym 1;
ba 1;
ba 1;
(* right subtree ----*)

zbr abs_ci_perm_admin 1;
zbd abs_ciR_implies_abs_ci 3;
ba 3;
by(convert2hol_tac [AtransR_def, theta_def] 1);
by(convert2hol_tac [theta_def] 1);
ba 1;
qed"auth_invariant_init";



zgoal SysArchSec.thy "(%theta AbsState'', %theta AbsState) :   \
\  AtransR                                                     \
\ =+=>                                                         \
\ (%theta AbsState'') : InitAbsState                           \
\ =+=>                                                         \
\   ((%theta AbsState, %theta AbsState') :                     \
\    {.AService @ (%theta AbsState, %theta AbsState').} )      \
\ =+=>                                                         \
\ authtab %^ rep = authtab %^ rep'                             ";
by(stripS_tac 1);
by(res_inst_tac [("t", "authtab %^ rep"), 
		 ("s", "authtab %^ rep''")] 
		subst 1);

(* y -> x *)

zbr auth_invariant_init 1;
by(convert2hol_tac [] 2);
by(removeTheta_tac 1);
by(rewtac AtransR_def);
zbd zrtrancl_into_zrtrancl 1;
ba 1;
(* z -> x *)
zbr auth_invariant_init 1;
by(convert2hol_tac [] 2);
by(removeTheta_tac 1);
by(rewtac AtransR_def);
by(convert2hol_tac [] 1);
qed"auth_invariant";



(* interesting system property *)

zgoal thy "              \
\ (%theta AbsState, %theta AbsState') : AtransR =+=>           \
\ InitAbsState =+=>          \
\ ~(?  m:Aknows. (authtab %^ rep'%^ m) \
\   = cvs_admin) \
\  ";
by(stripS_tac 1);
br ccontr 1;
bd notnotD 1;
by(atomizePrem_ex 1);
by(res_inst_tac [("P", "authtab %^ rep %^ m = cvs_admin")] 
		notE 1);
by(convert2hol_tac [InitAbsState_def] 1);
by(res_inst_tac [("s", "authtab %^ rep'"),
		 ("t", "authtab %^ rep")] subst 1);
ba 2;
br sym 1;
zbr auth_invariant_init 1;
ba 1;
ba 1;
qed"neverAdmin";
