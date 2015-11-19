(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_writeSec.ML ---
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
(* $Id: abs_writeSec.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* ============================= *)


(* Inductive Proof for AWriteSec *)

(* First Version of this proof used this axiom:

val constAuthtab = 
       (assume_ax 
	    SysArchSec.thy 
	"((authtab %^ x) = (authtab %^ y))");
 The second version used a constraint in abs_ciR. 
 The final version uses the set Aknows combined
 with the initial state to restrict the model 
 such that authtab rep = authtab rep holds. 
 see lemma auth_invariant in file initial_permAdmin
 for more informations.
 grep admin\ -\ equal *.ML
 ... this command returns all critical points & files.
*)
(* later do that indirectly using permissions *)
(* val notAdmin = ... *)

zgoalw SysArchSec.thy [AWriteSec_def, Areachable_def] "AWriteSec";
by(stripS_tac 1);
auto();
by(convert2hol_tac [] 1);
by(asm_full_simp_tac (HOL_ss addsimps [AtransR_def, theta_def]) 1);

by(filterPrems_drop ["%Delta"] 1);
br mp 1;
ba 2;back();back();back();

br mp 1;

by(eres_inst_tac [("P","%(abs_passwd0, rep0, rep_permtab0, wc0, wc_uidtab0, wfiles0) .  \
                       \%(abs_passwd1,rep1,rep_permtab1,wcS,wc_uidtab1,wfiles1).        \
                       \  ((abs_passwd0, rep0, rep_permtab0, wc0, wc_uidtab0, wfiles0)  \
                       \              : (asSet InitAbsState)) =+=>                     \
                       \  (rep0, rep1, rep_permtab1) : AWriteProp_ ")] 
                 zrtrancl_full_induct2 2);
(* unvollstaendig *)
auto();

(* first base case: x *)
bd AbsStateBeforeAService_nTh 1;
by(split_all_tac 1);
by(asm_full_simp_tac ((simpset() addsimps [split_def])) 1);
br impI 1;
br AbsState_implies_eqAWriteProp 1;
by(convert2hol_tac [] 1);
by(convert2hol_tac [] 1);

(* second base case: y *)
bd AbsStateAfterAService_nTh 1;
by(split_all_tac 1);
by(asm_full_simp_tac ((simpset() addsimps [split_def])) 1);
br impI 1;
br AbsState_implies_eqAWriteProp 1;
by(convert2hol_tac [] 1);
by(convert2hol_tac [] 1);

(* Kernschritt *)
by(split_all_tac 1);
(* rename_tac als bestandteil des cleanups ? *)
by(asm_full_simp_tac ((simpset() addsimps [split_def])) 1);
by(duplPrem "(x, xd" 1);(*duplicate the command step*)
bd(asm_full_simplify(HOL_ss addsimps[theta_def])(stripS AService_imp_Ops)) 1; 

(*br (stripS bc_one) 1;*)
(*Fallunterscheidungen *)
auto();
(* cases on operations distinct from  *)
(* ci *)
(* Level 28  *)
(* abs_loginR *)
bd(stripS abs_loginR_implies_repPtab_invariant) 1;
by(atomizePrem 1);
by(hyp_subst_tac 1);
ba 1;

(* abs_addR *)
bd(stripS abs_addR_implies_repPtab_invariant) 1;
by(atomizePrem 1);
by(hyp_subst_tac 1);
ba 1;

(* defer ci - do it later *)
by(defer_tac 1);

(* abs_up *)
bd(stripS abs_up_implies_repPtab_invariant) 1;
by(atomizePrem 1);
by(hyp_subst_tac 1);
ba 1;

(* abs_cd *)
bd(stripS abs_cd_implies_repPtab_invariant) 1;
by(atomizePrem 1);
by(hyp_subst_tac 1);
ba 1;

(* abs_modifyR *)
bd(stripS modifyR_implies_repPtab_invariant) 1;
by(atomizePrem 1);
by(hyp_subst_tac 1);
ba 1;
(* Level 49 *)
by(duplPrem "abs_ciR" 1);
zbd abs_ciR_implies_abs_ci 1;
auto();
by(filterPrems_drop ["AbsState ", "<="] 1);
by(thin_tac "?a" 1);

by(prune_params_tac);

by(rename_tac "  \
              \ abs_passwdx abs_passwdy abs_passwdz repx repy repz \
              \ rep_permtabx rep_permtaby rep_permtabz \
              \ wcx wcy wcz wc_uidtabx wfilesx wc_uidtaby \
              \ wfilesy wc_uidtabz wfilesz filesq \
\ " 1);
(* Level 56 *)
(* ================ *)

zbr replace_AWriteProp 1;
(* match the resulting Set constraints *)

(*  repS : ABS_DATATAB *)
zbr AbsState_implies_repSC 1;
zbr abs_ci_valid_AbsStateS 1;
ba 1;
(*  rep_permtabS : ABS_PERMTAB *)
zbr AbsState_implies_repPtabSC 1;
zbr abs_ci_valid_AbsStateS 1;
by(convert2hol_tac [] 1);
(*  repx : ABS_DATATAB *)
zbr AbsState_implies_repSC 1;
zbr InitAbsState_implies_AbsState 1;
by(convert2hol_tac [] 1);
(* shrink goal a little. *)
br ballI 1;
br impI 1;
by(atomizePrem 1);
(* Level 69 *)
(* ------ from here: critical. ------*)

by(case_tac "f : dom repy" 1);
by(defer_tac 1);
(* -------------------------------- *)
(* case 1 : f ~: dom rep *)

(* ===================================== *)
(* case one outsourced - reuse possible  *)
(* for the read - property.              *)

zbd (removeTheta 
	 (asm_full_simplify 
	      (HOL_ss addsimps[AtransR_def]) 
	      rep_domDiff_implies_perm)) 1;
ba 1;
ba 1;
ba 1;
ba 1;
ba 1;
ba 1;

(* -------------------------------- *)
by(case_tac "repy %^ f = repz %^ f" 1);
by(defer_tac 1);
(* Level 98 *) 
(* -------------------------------- *)
(* case 2 : f: dom repy and (repy %^ f ~= repz %^ f) *)


(* ===================================== *)
(* case two outsourced - reuse possible  *)
(* for the read - property.              *)

zbd (removeTheta 
	 (asm_full_simplify 
	      (HOL_ss addsimps[AtransR_def]) 
	      rep_fNeq_implies_perm)) 1;
ba 1;
ba 1;
ba 1;
ba 1;
ba 1;
ba 1;
ba 1;

(* Level 86 *)
(* -------------------------------- *)
(* case 3 : f: dom repy and (repy %^ f = repz %^ f) *)
(* -- insert "we trust in admin"  : *)
by(res_inst_tac [("t","authtab %^ repz"),
		 ("s","authtab %^ repy")] subst 1);

(* ---------------- 3. admin - equality ---- *)
(* br constAuthtab 1;*)
(* fst of four subgoals. *)

zbd (removeTheta 
	 (asm_full_simplify 
	      (HOL_ss addsimps[AtransR_def]) 
	      auth_invariant)) 1;
ba 1;
ba 1;
ba 1;


(*
zbr unch_abs_cvsauth_implies_auth_invariant 1;
zbr (abs_ci_valid_AbsState
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

(* ---------------- 3. admin - equality ---- *)
(* Level 133 *)


by(res_inst_tac [("t","rep_permtabz %^ f"),
		 ("s","rep_permtaby %^ f")] subst 1);

zbr abs_ci_repPtab_invariant 1;
ba 2;
ba 1;
(* --- so far: independent from IV.  --- *)
(* Level 137 *)
zbr  AProp_implies_secGoal 1;
ba 1;
ba 2;
by(res_inst_tac [("t","repy %^ f"),("s","repz %^ f")] subst 2);
br sym 2;
ba 2;
ba 2;

(* match trivial set constraints *)
br conjI 1;

(* rep_permtaby : ABS_PERMTAB *)

zbd abs_ci_valid_AbsState 2;
zbd AbsState_implies_repPtabSC 2;
ba 2;
br conjI 1;
(* repy : ABS_DATATAB *)

zbd abs_ci_valid_AbsState 2;
zbd AbsState_implies_repSC 2;
ba 2;
(* repx : ABS_DATATAB *)
zbr (InitAbsState_implies_AbsState ZRS AbsState_implies_repSC) 1;
by(convert2hol_tac [] 1);
qed"AWriteSec";
(*sqed"AWriteSec";*)

