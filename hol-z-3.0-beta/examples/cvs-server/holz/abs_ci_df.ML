(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_ci_df.ML --- 
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
(* $Id: abs_ci_df.ML 6746 2007-08-03 07:25:55Z brucker $ *)


(* set constraint 1 *)

goal thy "!! A . [| A : TAB;wc:TAB ; TAB = X -|-> Y |] ==> \
\ ((A (+) (B <: wc)) (+) (C <: wc)) : TAB";
br pfunOplDomSubst 1;
ba 3;
br domRestr_inDom 2;
ba 3;
ba 2;
br pfunOplDomSubst 1;
ba 1;
ba 2;
br domRestr_inDom 1;
auto();
qed"SetConstraint_1";

(* set constraint 2 *)

zgoal SysArchConsistency.thy         
" RepositoryState =+=>    \
\rep_permtab (+) (%n. n |-->  \
\                                  (authtab %^ rep %^ (wc_uidtab %^ n,  \
\               (abs_passwd %^ (wc_uidtab %^ n))))) ``  \
\                           {n. n : wfiles /\\  \
\                               (n : x /\\  \
\                                (n ~: dom rep /\\  \
\                                 (n : dom wc_uidtab /\\  \
\                                  ((wc_uidtab %^ n),  \
\                                   (abs_passwd %^ (wc_uidtab %^ n)))  \
\                                  : dom (authtab %^ rep))))}  \
\           : ABS_PERMTAB ";

by(stripS_tac 1);
br pfunOplDomSubst 1;
by(convert2hol_tac [ABS_PERMTAB_def] 3);
by(convert2hol_tac [RepositoryState_def] 1);
by(convert2hol_tac [maplet_def, ABS_PERMTAB_def, 
		    partial_func_def, ClientState_def, rel_def] 1);
auto();
qed"SetConstraint_2";



(*           *)
(* Subgoal 1 *)
(*           *)

goal thy "!! x. x : dom A ==> x : dom ((A (+) B)(+) C)";
br oplDomLeft 1;
br oplDomLeft 1;
ba 1;
qed"Subgoal_1";

(*           *)
(* Subgoal 2 *)
(*           *)

goal thy "!! y . [| (! x. P x =+=> x : dom rep) |] ==> \
\ dom rep Un (dom ((%n. n) `` {n. (P n)} <: wc)) = dom rep";
auto();
qed"domRepUnDomRepOld_is_domRep";

goal thy "!! y . [| ! z. P z =+=> z : dom wc |] ==>    \
\ dom ((%n. n) `` {n. (P n)} <: wc)                    \
\ = dom ((%n. n |--> (f n))`` {m. P m})";
by(convert2hol_tac [maplet_def, image_def] 1);
auto();
qed"MeqMDash";


zgoal SysArchConsistency.thy 
"(((wfiles Int files_63) <= dom wc                                             \
\    /\\ (dom rep = dom rep_permtab))                                        \
\    /\\ dom wc = dom wc')                                                   \
\   =+=>                                                                     \
\ dom (rep (+) (%n. n) ``                                                    \
\                        {n. n : wfiles /\\                                  \
\                            (n : files_63 /\\                               \
\                             (n ~: dom rep /\\                              \
\                              (n : dom wc_uidtab /\\                        \
\                               ((wc_uidtab %^ n),                           \
\                                (abs_passwd %^ (wc_uidtab %^ n)))           \ 
\                               : dom (authtab %^ rep))))} <: wc (+) (%n.    \ 
\                                  n) ``                                     \
\                              {n. n : wfiles /\\                            \
\                                  (n : files_63 /\\                         \
\                                   (n : dom rep /\\                         \
\                                    (n : dom wc_uidtab /\\                  \
\                                     (rep_permtab, rep, abs_passwd, n,      \
\  (wc_uidtab %^ n))                                                         \
\                                     : has_access_)))} <: wc) =             \
\           dom (rep_permtab (+) (%n. n |-->                                 \
\  (authtab %^ rep %^ (wc_uidtab %^ n, (abs_passwd %^ (wc_uidtab %^ n))))) `` \
\                                {n. n : wfiles /\\                          \
\                                    (n : files_63 /\\                       \
\                                     (n ~: dom rep /\\                      \
\  (n : dom wc_uidtab /\\                                                    \
\  ((wc_uidtab %^ n), (abs_passwd %^ (wc_uidtab %^ n)))                      \
\  : dom (authtab %^ rep))))}) ";
by(stripS_tac 1);
by(atomizePrem 1);
br trans 1;
br oplDomUn 1;
br trans 1;
br oplDomUnMultiple 1;
br trans 1;
br DomUnMultipleKomm 1;
(* the 'UnAss - Step' from my    *)
(* studienarbeit can be dropped. *)
br trans 1;
br mp 1;br eqWithUnion 1;
br domRepUnDomRepOld_is_domRep 1;
by(Asm_simp_tac 1);

by(res_inst_tac [("t","?X Un dom rep = ?Y"),("s","?X Un dom rep_permtab = ?Y")] subst 1);
by(convert2hol_tac [] 1);
(* now, start from the other end       *)
(* of the equation using oplDomUn      *)
(* for:                                *)
(* dom(rep_permtab(+)rep_permtab_neu)  *)
(* =dom(rep_ptab) Un dom(rep_ptab_neu) *)
br sym 1;
br trans 1;
br oplDomUn 1;

(* simplify the goal by        *)
(* eliminating dom rep_permtab *)

br sym 1;
br trans 1;
br UnKomm 1;
br (stripS eqWithUnion) 1;

br (stripS MeqMDash) 1;
(**)
br allI 1;
br impI 1;
by(atomizePrem 1);
bd subsetD 1;
ba 2;
br IntI 1;
ba 1;
ba 1;
(**)
qed"Subgoal_2";



(*             *)
(* subgoal 3   *)
(*             *)

goal thy " !!z. [| ! y . P y =+=> y ~: dom A; \
\ x : dom A |] ==> \
\ x ~: dom ((%n. n |--> (f n))`` {m. P m}) \
\ ";
by(convert2hol_tac [maplet_def, image_def] 1);
auto();
qed"get_contr_sg3";

zgoal thy "(abs_cvsauth : dom rep                                             \
\   /\\ ((rep_permtab %^ abs_cvsauth) = cvs_admin)  )                         \
\  =+=>                                                                       \
\(rep_permtab (+) (%n. n |-->                                                 \
\                                   (authtab %^ rep %^ ((wc_uidtab %^ n),     \
\                (abs_passwd %^ (wc_uidtab %^ n))))) ``                       \
\                            {n. n : wfiles /\\                            \
\                                (n : filesq      /\\                         \
\                                 (n ~: dom rep /\\                        \
\                                  (n : dom wc_uidtab /\\                  \
\                                   ((wc_uidtab %^ n),                     \
\                                    (abs_passwd %^ (wc_uidtab %^ n)))     \
\                                   : dom                                  \
\(authtab %^ rep))))}) %^ abs_cvsauth =                                    \
\           cvs_admin     ";
by(stripS_tac 1);
br trans 1;
br (stripS applOpl) 1;
be conjE 2;
ba 2;
(* abs_cvsauth ~: dom {n. ... n : dom rep}*)
(* contradicts on abs_cvsauth : dom rep   *)
br get_contr_sg3 1;
by(atomizePremSolve 2);
auto();
qed"Subgoal_3";



(*                                 *)
(* Main-proof                      *)
(*                                 *)

zgoalw SysArchConsistency.thy [] "                         \
\ ((rep (+) (((%n. n) ``                                   \
\                              (asSet                      \
\                               (%n. ((n : wfiles) /\\     \
\                                     ((n : ?X ) /\\       \
\ ((n ~: (dom rep)) /\\                                    \
\ ((n : (dom wc_uidtab)) /\\                               \
\  (((wc_uidtab %^ n), (abs_passwd %^ (wc_uidtab %^ n)))   \
\   : (dom (authtab %^ rep)))))))))) <: wc)) (+) (((%n. n) ``  \
\            (asSet                                    \
\              (%n. ((n : wfiles) /\\                  \
\                    ((n : ?X) /\\                     \
\                     ((n : (dom rep)) /\\             \
\                      ((n : (dom wc_uidtab)) /\\      \
\                       ((rep_permtab, rep, abs_passwd, n, (wc_uidtab %^ n))             \
\                        : has_access_)))))))) <: wc)) %^ abs_cvsauth : dom abs_auth_of  \
\                                                      \
\  /\\  rep : dom authtab =+=> abs_ci_df               \
\ ";
by(stripS_tac 1);
by(atomizePrem 1);

by(full_expand_schema_tac abs_ci_df_def 1);
by(openDFobligation abs_ci_def);
by(rewrAtomSubgoals);
by(do_improve []);
br refl 1;
by(full_expand_schema_tac RepositoryState_def 1);
by(rewrAtomSubgoals);
(* first set constraint *)
br SetConstraint_1 1;
by(atomizePremSolve 1);
by(filterPrems_keep ["ClientState"] 1);
by(convert2hol_tac [ClientState_def] 1);
by(convert2hol_tac  [ABS_DATATAB_def] 1);
(* second set constraint *)
zbr SetConstraint_2 1;
by(convert2hol_tac [RepositoryState_def] 1);
by(atomizePrem 1);
by(res_inst_tac [("s","dom rep"),
		 ("t","dom rep_permtab")] subst 1);
by(atomizePremSolve 1);
by(atomizePremSolve 1);

(* after solving the 2 set constraints, *)
(* solve the 4 Predicates of Repository *)
(* state. (fourth one by assumption)    *)

(* 4th pred. of RepositoryState *)
by(filterPrems_keep ["rep (+)"] 4);
by(convert2hol_tac [] 4);
(* 1st pred. of RepositoryState *)
br Subgoal_1 1;
by(atomizePremSolve 1);
(* 3rd pred. of RepositoryState *)
zbr Subgoal_3 2;
by(atomizePremSolve 2);
br conjI 2;
ba 2;
ba 2;
(* 2nd pred. of RepositoryState *)
zbr Subgoal_2 1;
br conjI 1;
br refl 2;
br conjI 1;
ba 1;
by(atomizePremSolve 1);
qed"abs_ci_deadlockFree";
