(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * FunAbs.thy --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 1998-1999 GMD First, Germany
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
(* $Id: FunAbs.thy 6729 2007-08-03 05:25:17Z brucker $ *)


header{* Support for a rudimentary lifter *}
theory FunAbs imports ZMathTool  ZFun begin


types

  ('a, 'b) typeabs = "('b set) * ('a => 'b) * ('b => 'a)"

constdefs

(* pseudo type-definition -- Typeabs may be empty for some ('a, 'b) *)

TASet :: "('a, 'b) typeabs => ('b set)"
"TASet == fst"

TARep :: "('a, 'b) typeabs => ('a => 'b)"
"TARep == fst o snd"

TAAbs :: "('a, 'b) typeabs => ('b => 'a)"
"TAAbs == snd o snd"

Typeabs :: "('a, 'b) typeabs => bool"
"Typeabs TA == (let T = TASet TA; 
                   R = TARep TA;
                   A = TAAbs TA
               in T ~= {} 
                & (ALL (x::'a). (R x) : (T::'b set))
                & (ALL (x::'a). (A (R x)) = x)
                & (ALL (y::'b). y : T --> (R (A y)) = y))"


(* 
* lifting type abstraction 
* to level of functions and set-theoretic relations 
*)

FRep :: "[('a, 'b) typeabs, 'a => 'c] => ('b <=> 'c)"
"FRep TA f == {z. EX x. z = ((TARep TA x), (f x))}"

FAbs :: "[('a, 'b) typeabs, ('b <=> 'c), 'a] => 'c"
"FAbs TA g == (% x. g %^ (TARep TA x))"

PRep :: "['a => 'b] => ('a <=> 'b)"
"PRep f == {p. EX x. p = (x, f x)}"

PAbs :: "[('a <=> 'b), 'a] => 'b"
"PAbs R == (% x. R%^x)"


lemma TASet: "TASet (T,R,A) = T"
apply (unfold TASet_def)
apply auto
done

lemma TARep: "TARep (T,R,A) = R"
apply (unfold TARep_def)
apply auto
done

lemma TAAbs: "TAAbs (T,R,A) = A"
apply (unfold TAAbs_def)
apply auto
done

declare TASet [simp] TARep [simp] TAAbs [simp]

lemma TASet_nonempty[rule_format] : "Typeabs TA --> (TASet TA) ~= {}"
apply (unfold Typeabs_def Let_def)
apply auto
done

lemma TARep_in_TASet[rule_format] : "Typeabs TA --> (TARep TA x) : (TASet TA)"
apply (unfold Typeabs_def Let_def)
apply auto
done

lemma TAAbs_inverse[rule_format] : "Typeabs TA --> (TAAbs TA (TARep TA x)) = x"
apply (unfold Typeabs_def Let_def)
apply auto
done

lemma TARep_inverse[rule_format] : "Typeabs TA --> y : (TASet TA) --> (TARep TA (TAAbs TA y)) = y"
apply (unfold Typeabs_def Let_def)
apply auto
done

declare TASet_nonempty [simp] TARep_in_TASet [simp] TAAbs_inverse [simp] TARep_inverse [simp]

lemma TARep_inj[rule_format] : "Typeabs TA --> (inj (TARep TA))"
apply (unfold Typeabs_def Let_def inj_on_def)
apply (rule impI)
apply (rule ballI)+
apply (erule conjE)+
apply (rule impI)
apply (erule_tac x = "x" in allE)
apply (subgoal_tac "TAAbs TA (TARep TA y) = y")
apply (erule_tac x = "x" in allE)
apply simp
apply fast
done

lemma TARep_iff_inj[rule_format] : "Typeabs TA --> ((TARep TA x) = (TARep TA y)) = (x = y)"
apply (rule impI)
apply (rule iffI)
apply (cut_tac TA = "TA" in TARep_inj)
apply (unfold inj_on_def)
apply fast+ 
done

declare TARep_iff_inj [simp]

lemma FRep_apply[rule_format] : "Typeabs TA --> ((FRep TA f) %^ (TARep TA x)) = (f x)"
apply (unfold FRep_def rel_apply_def)
apply (simp (no_asm) cong add: conj_cong)
done

lemma FRep_rel[rule_format] : "Typeabs TA --> (FRep TA f) : ((TASet TA) <--> UNIV)"
apply (unfold FRep_def rel_def Typeabs_def Let_def)
apply fast
done

declare FRep_rel [simp]

lemma FRep_pfun[rule_format] : "Typeabs TA --> (FRep TA f) : ((TASet TA) -|-> UNIV)"
apply (unfold pfun_def)
apply (simp (no_asm))
apply (unfold FRep_def)
apply simp
apply auto
done

declare FRep_pfun [simp]

lemma FRep_dom[rule_format] : "Typeabs TA --> dom (FRep TA f) = TASet TA"
apply (unfold dom_simp [THEN eq_reflection])
apply auto
apply (rule_tac Y = "UNIV" and f = "FRep TA f" in rel_dom_member)
apply (simp (no_asm_simp))
apply assumption
apply (unfold FRep_def Typeabs_def Let_def)
(* need to reverse equality in goal *)
apply (rule eq_sym_conv [THEN ext, THEN ext, THEN ssubst])
apply (simp (no_asm))
apply fast
done

declare FRep_dom [simp]

lemma FRep_total_fun[rule_format] : "Typeabs TA --> (FRep TA f) : ((TASet TA) ---> UNIV)"
apply (unfold tfun_def)
apply (simp (no_asm))
done

declare FRep_total_fun [simp]

lemma FAbs_inverse[rule_format] : "Typeabs TA --> (FAbs TA (FRep TA f)) = f"
apply (unfold FAbs_def FRep_def)
apply (simp (no_asm) add: rel_apply_def some_equality)
done

declare FAbs_inverse [simp]

lemma FRep_inverse [simp]: "Typeabs TA --> r : ((TASet TA) ---> UNIV) --> (FRep TA (FAbs TA r)) = r"
apply (unfold FAbs_def FRep_def)
apply auto
apply (rule rel_apply_in_rel)
apply (rule total_is_partial)
apply assumption
apply (unfold Typeabs_def Let_def)
apply (fast intro:total_func_dom)
apply (subgoal_tac "a: TASet TA")
apply (rule_tac x = "TAAbs TA a" in exI)
apply (drule total_is_partial)
apply simp
apply (drule total_is_partial)
apply (drule Pfun_Rel)
apply (drule rel_pair_dom )
apply assumption+
done

lemma Typeabs_Fun:
assumes prems: "Typeabs TA"
shows "Typeabs (TASet TA ---> UNIV, FRep TA, FAbs TA)"
apply (unfold Typeabs_def Let_def)
apply (simp (no_asm) add: prems)
done

lemma apply_FAb[rule_format] : 
"Typeabs TA --> x : TASet TA --> (g %^ x) = (FAbs TA g) (TAAbs TA x)"
apply (unfold FAbs_def)
apply (simp (no_asm))
done

lemma TAAbs_inj_onto[rule_format]: 
"Typeabs TA --> inj_on (TAAbs TA) (TASet TA)"
apply (unfold Typeabs_def Let_def)
apply (rule impI)+
apply (erule conjE)+
apply (rule inj_on_inverseI)
apply (rule TARep_inverse)
prefer 2 
apply (assumption)
apply (unfold Typeabs_def Let_def)
apply auto
done

lemma TAAbs_iff_inj_onto[rule_format]: 
"Typeabs TA --> x : TASet TA --> y : TASet TA -->  
((TAAbs TA x) = (TAAbs TA y)) = (x = y)"
apply (rule impI)+
apply (rule iffI)
apply (cut_tac TA = "TA" in TAAbs_inj_onto)
apply (unfold inj_on_def)
apply fast+
done

lemma PRep_inverse[rule_format]: "R : (UNIV ---> UNIV) --> ((PRep (PAbs R)) = R)"
apply (unfold PRep_def PAbs_def)
apply auto
apply (rule rel_apply_in_rel)
apply (rule total_is_partial)
apply assumption
apply (fast intro: total_func_dom)
apply (drule total_is_partial)
apply (simp (no_asm_simp))
done


lemma PAbs_inverse:"(PAbs (PRep f)) = f"
apply (unfold PRep_def PAbs_def rel_apply_def)
apply (simp (no_asm) add: rel_apply_def some_equality)
done

lemma PRep_apply: "(f x) = ((PRep f) %^ x)"
apply (unfold PRep_def rel_apply_def)
apply (simp (no_asm) cong add: conj_cong)
done

lemma PAbs_apply: "(R %^ x) = ((PAbs R) x)"
apply (unfold rel_apply_def PAbs_def)
apply (rule refl)
done
end
