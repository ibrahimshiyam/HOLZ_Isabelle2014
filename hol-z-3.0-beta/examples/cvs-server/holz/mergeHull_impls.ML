(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * mergeHull_impls.ML --- 
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
(* $Id: mergeHull_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)

zgoal SysArchSec.thy "?merge : Abs_Data %x Abs_Data ---> Abs_Data";
by(stripS_tac 1);
br (merge_axdef RS DECL_D1) 1; 
qed"type_merge";


goal thy " !! n .                                     \
\  [| do : Abs_Data; d : Abs_Data; n : Abs_Name |]    \
\    ==> (n, merge %^ (do, d)) : Abs_Name %x Abs_Data ";
auto();
qed"type_mergeInst";


zgoal SysArchSec.thy "              \
\ S :  %P (Abs_Name %x Abs_Data)    \
\ =+=>                              \
\ x : (Abs_Name %x Abs_Data)        \
\ =+=>                              \
\         (x : S \\/                \
\          (? a:Abs_Name.           \
\             ? y:Abs_Data.         \
\                ? mdata:Abs_Data.  \
\                   (a, y) : MH %^ S /\\               \
\                   (x = (a, merge %^ (y, mdata)) \\/  \
\                   x = (a, merge %^ (mdata, y)))))    \
\ =+=>                              \
\       (x : MH %^ S)               ";
by(stripS_tac 1);
by(res_inst_tac [("t", 
		  "x : MH %^ S")] subst 1);
br sym 1;
by(res_inst_tac [("x", "x")] bspec 1);
ba 2;
by(res_inst_tac [("x", "S")] bspec 1);
ba 2;
br (MH_axdef RS DECL_D2) 1;
ba 1;
qed"MH_I";


zgoal SysArchSec.thy "     \
\ do : Abs_Data            \
\ =+=>                     \
\ d  : Abs_Data            \
\ =+=>                     \
\ n  : Abs_Name            \
\ =+=>                     \
\ (n, d) : Ainvents =+=>   \
\ (n, (merge %^ (do, d) ))  : Ainvents  \
\  ";
by(stripS_tac 1);
by(res_inst_tac [("t", 
		  "Ainvents")] subst 1);
br sym 1;
br Ainvents_MH 1;
zbr MH_I 1;
br type_Ainvents_base 1;
br type_mergeInst 1;
ba 1;
ba 1;
ba 1;

(* extract the goal (n, d) : Ainvents *)

br disjI2 1;
br bexI 1;
ba 2;
br bexI 1;
by(guidedAssumption ["d : Abs_Data"] 2);
br bexI 1;
ba 2;
br conjI 1;
by(res_inst_tac [("s", "Ainvents"),
		 ("t", "MH %^ Ainvents_Base")] subst 1);
br Ainvents_MH 1;
ba 1;
br disjI2 1;
br refl 1;
qed"Ainv_implies_rMergeAinv";
