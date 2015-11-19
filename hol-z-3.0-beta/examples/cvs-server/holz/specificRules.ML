(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * specifyRules.ML --- 
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
(* $Id: specificRules.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* simple version. *)
goal thy"dom ((%n. (n |--> B n))``(asSet (%n. (n : A)))) <= A";
by(convert2hol_tac [image_def, maplet_def] 1);
auto();
qed"dom_of_restricted_maplet";


goal thy"dom ((%n. (n |--> B n))``(asSet (%n. (n : A /\\ P n)))) <= A";
by(convert2hol_tac [image_def, maplet_def] 1);
auto();
qed"dom_of_restricted_maplet_ext";

(*---*)
goal thy "f : A =+=> \
\ ((%n. (n |--> B n))``(asSet (%n. (n : A)))) %^ f = B f";
by(convert2hol_tac [maplet_def, image_def, rel_apply_def] 1);
auto();
qed"appl_of_restricted_maplet";

goal thy "f : A =+=> \
\ P f  =+=>          \
\ ((%n. (n |--> B n))``(asSet (%n. (n : A /\\ P n)))) %^ f = B f";
by(convert2hol_tac [maplet_def, image_def, rel_apply_def] 1);
auto();
qed"appl_of_restricted_maplet_ext";


(*---*)
zgoal thy "\
\ f : dom ((%n. (n |--> B n))``(asSet (%n. (n : A /\\ P n)))) \
\ =+=> P f";
by(convert2hol_tac [image_def, maplet_def] 1);
auto();
qed"inDom_implies_setProp";

zgoal thy "\
\ f : dom ((%n. (n |--> B n))``(asSet (%n. (n : A /\\ P n)))) \
\ =+=> f : A";
by(convert2hol_tac [image_def, maplet_def] 1);
auto();
qed"inDom_implies_setConstr";

zgoal thy " \
\  f : dom (((%n . n) `` (asSet (%n. (P n)))) <: A) \
\ =+=> (P f)";
by(convert2hol_tac [image_def, dom_restr_def] 1);
auto();
qed"inDom_restrProp";

(* Often used instead of this rule: *)
(* eps_from_exists_example . But    *)
(* better use this one in future    *)
(* proofs, it is more abstract than *)
(* the other one.                   *)

goal thy "!! x . (? a:(dom abs_passwd). (P a)) \
\ ==> (mu id:dom abs_passwd. P id) \
\                  : dom abs_passwd";
by(prune_params_tac);
by(convert2hol_tac [Mu_def] 1);
br (stripS eps_from_exists_example_pred) 1;
auto();
qed"inDom_pred";
