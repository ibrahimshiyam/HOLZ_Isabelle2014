(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ProdContrib.thy ---  1998-1999 GMD First, Germany
 * This file is part of HOL-Z.
 *
 * Copyright (c) 2000-2003, University Freiburg, Germany
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
(* $Id: ProdContrib.thy 6729 2007-08-03 05:25:17Z brucker $ *)

theory    ProdContrib 
imports   Main (* Product_Type: *)
begin

(* unfortunately, this rule loops! *)
lemma split_paired_Lam: "P = (\<lambda>  (a,b). P (a,b))"
apply (rule ext)
apply (simp (no_asm_simp) only: split_tupled_all)
apply (simp (no_asm))
done

lemma split_paired_split: "(% x. split f x) = (% (a,b). split f (a,b))"
apply (rule ext)
apply (simp (no_asm_simp) only: split_tupled_all)
apply (simp (no_asm))
done

lemma split_paired_CollectL: "{(a,b). P a b} = {((a,c),b). P (a,c) b}"
apply auto
apply (tactic {* TRYALL split_all_tac *} )
done

lemma split_pattern: assumes a: "z=(x,y)" shows "(% (x,y). F x y) z = F x y"
apply (simp (no_asm) add: a)
done

lemma split_paired_Ex: "(EX x. P x) = (EX a b. P (a,b))"
apply auto
done

ML
{*
val split_pattern = thm "split_pattern"
*}

declare split_paired_Ex [simp]

(* das evtl. mit addbefore als Vorverarbeitung zum claset() setzen! *)
ML {* 
val norm_split_apply_tac = 
    (SELECT_GOAL (CHANGED 
     (EVERY1 [(match_tac [split_pattern RS ssubst]),
              (rtac refl)])
     THEN flexflex_tac))

*}

(*-----------------------------------------------------------------------*)
(* Meta-Simplification for unit                                          *)
(*-----------------------------------------------------------------------*)

lemma  "METACOND x ==> ((x::unit),y) = ((),y)"
apply (subst unit_eq)
apply (rule refl)
done

lemma METACOND_pair_snd_unit: "METACOND y ==> (x,(y::unit)) = (x,())"
apply (subst unit_eq)
apply (rule refl)
done

lemma unit_eq_true: "((x::unit) = y) = True"
apply ((subst unit_eq))
apply (simp (no_asm))
done

declare unit_eq_true [simp]
(*
fun is_not_unit_const (Const ("()",Type ("unit",[]))) = false
  | is_not_unit_const _ = true
*)

end


