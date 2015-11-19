(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * secAx_impls.ML --- 
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
(* $Id: secAx_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* specific implications of AWriteProp *)


zgoalw SysArchSec.thy [] "rep:ABS_DATATAB     \
\  =+=> rep_permtab : ABS_PERMTAB  =+=>       \
\  (rep, rep, rep_permtab) : AWriteProp_";

by(stripS_tac 1);
by(cut_facts_tac [AWriteProp__axdef] 1);
auto();
qed"rep_invariant_implies_AWriteProp";
(* Addsimps [stripS rep_invariant_implies_AWriteProp];*)

bind_thm("AbsState_implies_eqAWriteProp",
	 (
	  [(stripS AbsState_implies_repSC), 
	   (stripS AbsState_implies_repPtabSC)]
	      MRS 
	      (stripS rep_invariant_implies_AWriteProp)
	      ));

(* this lemma allows to unfold AWriteProp. *)
(* (using rtac)                        *)

zgoalw SysArchSec.thy [] "                                      \
\ rep': ABS_DATATAB                                             \
\ =+=>                                                          \
\ rep_permtab':ABS_PERMTAB                                      \
\ =+=>                                                          \
\ rep : ABS_DATATAB                                             \
\ =+=>                                                          \
\ (! f:dom rep'.                                                \
\                     rep %^ f ~= rep' %^ f  =+=>               \
\                     (? m:Aknows.                              \
\                         (rep_permtab' %^ f, authtab %^ rep' %^ m)  \
\                         : cvs_perm_order))                    \
\ =+=>                                                          \
\ (rep, rep', rep_permtab') : AWriteProp_                            \
\ ";
by(stripS_tac 1);
by(cut_facts_tac [AWriteProp__axdef] 1);
bd DECL_D2 1;
bd bspec 1;
back();
by(guidedAssumption ["rep : ABS_DATATAB"] 1);
bd bspec 1;
back();
by(guidedAssumption ["rep' : ABS_DATATAB"] 1);
bd bspec 1;
back();
by(guidedAssumption ["rep_permtab' : ABS_PERMTAB"] 1);
(* ---- change AWriteProp with its def. *)
br subst 1;
br sym 1;
ba 1;
ba 1;
(* ----- *)
qed"replace_AWriteProp";

(* *)

(* setCons in text already in-   *)
(* tegrated to simplify drawing  *)
(* the prooftree.                *)
(* simplified version from text. *)
(* text-name:AProp_implies_sec   *)
zgoal thy "                             \
\ (rep, rep', rep_permtab') : AWriteProp_   \
\ =+=> rep:ABS_DATATAB /\\              \
\      rep':ABS_DATATAB /\\             \
\     rep_permtab':ABS_PERMTAB          \
\ =+=>                                  \
\ f : dom rep'                          \
\ =+=>                                  \
\  rep %^ f ~= rep' %^ f  =+=>          \
\                     (? m:Aknows.                           \
\                         (rep_permtab' %^ f, authtab %^ rep' %^ m) \
\                         : cvs_perm_order) \
\ ";
by(stripS_tac 1);
by(cut_facts_tac [AWriteProp__axdef] 1);
be DECL_E 1;
by(atomizePrem 1);
bd bspec 1;
by(guidedAssumption ["rep : ABS_DATATAB"] 1);
bd bspec 1;
by(guidedAssumption ["rep' : ABS_DATATAB"] 1);
bd bspec 1;
by(guidedAssumption ["rep_permtab' : ABS_PERMTAB"] 1);
br mp 1;
ba 2;
by(res_inst_tac [("P", "% x . x =+=> ?Y")] subst 1);
br sym 1;
ba 1;
by(filterPrems_drop ["AWriteProp"] 1);
br impI 1;
bd bspec 1;
ba 1;

(*now: ainvents-specific.*)

br mp 1;
ba 1;
auto();
qed"AProp_implies_secGoal";
