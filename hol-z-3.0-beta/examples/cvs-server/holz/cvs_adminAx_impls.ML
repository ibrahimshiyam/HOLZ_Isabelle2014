(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * cvs_adminAx_impls.ML --- 
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
(* $Id: cvs_adminAx_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* this file contains implications *)
(* of the cvs_admin_axdef          *)


zgoal thy "(! x:Cvs_Perm. ? y:Cvs_Perm. (x, y) : cvs_perm_order)";
by(cut_facts_tac [cvs_admin_axdef] 1);
bd DECL_D2 1;
by(atomizePrem 1);
ba 1;
qed"cvsPerms_allIn_Order";

zgoal thy "cvs_perm_order = cvs_perm_order %*";
by(cut_facts_tac [((cvs_admin_axdef RS DECL_D2)RS conjunct1)] 1);
ba 1;
qed"cvsPermOrderStar";

goal thy "cvs_perm_order : Cvs_Perm <--> Cvs_Perm";
by(cut_facts_tac [cvs_admin_axdef] 1);
bd DECL_D1 1;
by(atomizePremSolve 1);
qed"type_cvsPermOrder";

goal thy "!! x. x : dom cvs_perm_order Un ran cvs_perm_order \
\  ==> (x,x): cvs_perm_order";
by(res_inst_tac [("s", "cvs_perm_order %*"), 
		 ("t", "cvs_perm_order")] subst 1);
br sym 1;
br cvsPermOrderStar 1;
br zrtrancl_refl0 1;
ba 1;
qed"refl_cvsPermOrder";

goal thy "!! x. x : Cvs_Perm ==> (x,x): cvs_perm_order";
br refl_cvsPermOrder 1;
by(cut_facts_tac [cvsPerms_allIn_Order] 1);
bd bspec 1;
ba 1;
be bexE 1;
auto();
qed"cvsPerm_in_refl";

goal thy "!! x . [| x ~= cvs_admin ;  x:Cvs_Perm |] \
\ ==> (cvs_admin, x) ~: cvs_perm_order";
by(cut_facts_tac [(cvs_admin_axdef RS DECL_D2) 
		      RS conjunct2 
		      RS conjunct2 
		      RS conjunct2 
		      RS conjunct1] 1);
auto();
qed"adminTop";

(* If the left element of a valid tuple *)
(* in cvs_perm_order is cvs_admin, then *)
(* the right element also has to be     *)
(* cvs_admin.                           *)

goal thy "!! x . [| (cvs_admin,x) : cvs_perm_order; x:Cvs_Perm|] \
\ ==> x = cvs_admin";
br ccontr 1;
by(res_inst_tac [("P","(cvs_admin, x) : cvs_perm_order")]  notE 1);
ba 2;
br adminTop 1;
by(AtomizePremSolveAll);
qed"admin_perm_only";
