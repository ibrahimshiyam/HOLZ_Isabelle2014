(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ZFinite.thy --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 1998-1999 GMD First, Germany
 *               2000-2003 University Freiburg, Germany
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
(* $Id: ZFinite.thy 6729 2007-08-03 05:25:17Z brucker $ *)

(*************************************************************************)
(*   Title              : ZFinite.thy                                    *)
(*   Project            : Encoding Z in Isabelle                         *)
(*   Author             : T. Santen, T. Neustupny, S. Helke, GMD First   *)
(*   $Id: ZFinite.thy 6729 2007-08-03 05:25:17Z brucker $  *)
(*   This theory        : Theorems about Finite Sets and Functions       *)
(*   Copyright          : GMD First, Berlin                              *)
(*                        Germany                                        *)
(*************************************************************************)

header{* Finite Sets for the Mathematical Toolkit *}
 
theory ZFinite imports ZFun begin 


axioms
Fin_subset: "[| A <= B;  B: %F M |] ==> A: %F M"


lemma Fin_mono: "!!A B. A <= B ==> %F A <= %F B"
apply (unfold Fin.defs)
apply (rule lfp_mono)
apply auto
done

lemma Fin_mono2: "[| X <= Y; a : %F X |] ==> a : %F Y"
apply (cut_tac Fin_mono)
prefer 2
apply assumption
apply fast
done

lemma Fin_subset_Pow: "%F A <= %P A"
apply (unfold Fin.defs)
apply (rule lfp_lowerbound)
apply fast
done


lemmas FinD = Fin_subset_Pow [THEN subsetD [THEN PowD]]

(*Discharging ~ x:y entails extra work*)
lemma Fin_induct:
assumes major1: "F : %F A"
assumes major2: "P ({})" 
assumes prems: "!!F x. [| x : A;  F : %F A;  x ~: F;  P(F) |] ==> P(insert x F)"
shows  "P(F)"
apply (rule major1 [THEN Fin.induct])
defer 1
apply (case_tac "a : b")
apply (erule insert_absorb [THEN ssubst], assumption)
apply (assumption, rule prems)+
done


declare Fin.insertI [simp]
declare Fin.emptyI [simp]

declare Fin.intros [simp]

(*The union of two finite sets is finite*)
lemma Fin_UnI:
assumes major: "F : %F A"
assumes prems: "G : %F A"
shows "F Un G : %F A"
apply (rule prems [THEN Fin_induct])
apply (simp add: prems Un_insert_left)+
done


(*
(*Every subset of a finite set is finite*)
lemma Fin_subset:  "\<lbrakk>A <= B; B: %F M\<rbrakk> \<Longrightarrow> A: %F M"
proof -
 assume "B : %F M"
 thus "!!A. A \<subseteq> B \<Longrightarrow> A \<in> %F M"
 proof induct
  case emptyI
  thus ?case by simp
 next
  case (insertI x F A)
  have A: "A \<subseteq> insert x F" and r: "A - {x} \<subseteq> F \<Longrightarrow> (A - {x})\<in> %F M".
  show "A \<in> %F M"
  proof cases
    assume x: "x \<in> A"
    with A have "A - {x} \<subseteq> F" by (simp add: subset_insert_iff) 
    with r have "(A - {x}) \<in> %F M". 
    hence "(insert x (A - {x})) \<in> %F M" sorry
    also have "insert x (A - {x}) = A" by (rule insert_Diff)
    finally show ?thesis .
  next
    show "A \<subseteq> F \<Longrightarrow> ?thesis" .
    assume "x \<notin> A"
    with A show "A \<subseteq> F" by (simp add: subset_insert_iff)
   qed
  qed
 qed


lemma Fin_subset1: 
assumes prem1: "A \<subseteq> B"
assumes prem2: "B \<in> %F M"
shows "A \<in> %F M"
apply (subgoal_tac "ALL C. C \<subseteq> B \<longrightarrow> C: %F M", rule mp, erule spec, rule prem1)
apply (rule prem2 [THEN Fin_induct])
apply (simp add:subset_Un_eq)
apply (safe del: insert_Diff subset_insert_iff [THEN iffD1])
apply simp*)

lemma subset_Fin [simp]: "(F Un G : %F A) = (F : %F A & G : %F A)"
apply (fast intro: Fin_UnI dest: Un_upper1 [THEN Fin_subset] Un_upper2 [THEN Fin_subset])
done


lemma insert_Fin [simp]: "(insert a A : %F M) = (a : M & A : %F M)"
apply (auto intro!: Fin.emptyI Fin.insertI dest: FinD)
apply (rule mp)
prefer 2 
apply (assumption)
apply (subst insert_is_Un)
apply (subst subset_Fin)
apply auto
done


(*The image of a finite set is finite*)
lemma Fin_imageI: "F : %F A ==> h`F : %F (h`A)"
apply (erule Fin.induct)
apply (simp (no_asm))
apply (simp (no_asm_simp) add: image_eqI [THEN Fin.insertI] image_insert del: insert_Fin)
done

lemma aux:
assumes major: "c : %F A"
assumes prem1:  "b: %F A"                                   
assumes prem2: "       P(b)"                                            
assumes prem3: " !!(x::'a) y. \<lbrakk>x : A; y : %F A;  x : y;  P(y) \<rbrakk> \<Longrightarrow> P(y-{x}) " 
shows " c<=b \<longrightarrow> P(b-c)"
apply (rule major [THEN Fin_induct])
prefer 2
apply (subst Diff_insert)
prefer 2
apply (simp (no_asm_simp) add : prem1 prem2 prem3 Diff_subset [THEN Fin_subset])+
done 

lemma Fin_empty_induct: "[| b : %F A; P(b); !!x y. [| x : A; y : %F A;  x : y;  P(y) |] ==> P(y - {x})|] ==> P({})"
apply (rule Diff_cancel [THEN subst])
apply (rule aux [THEN mp])
apply assumption+
apply auto
done

section{* Finite Sets*}

lemma Fin_Diff_Set: "[|(A - B) : %F X; B : %F X|] ==> A : %F X"
apply (drule Fin_UnI)
apply fast
apply (rule_tac B = "A - B Un B" in Fin_subset)
apply fast
apply fast
done
      
lemma size_empty: "(# {}) = int 0"
apply (unfold zsize_def)
apply (simp (no_asm))
done
declare size_empty [simp]

lemma card_empty_set: "(t = {}) ==> (card t = 0)"
apply auto
done


lemma Fin_finite: "A: %F X ==> finite A"
apply (unfold lfp_def insert_def Un_def Inter_def Finites.defs Fin.defs)
apply simp
apply (rule allI)
apply (rule impI)
apply (erule allE)
apply (erule impE)
apply auto
done

lemma finite_Fin: "[|finite A; A <= X |] ==> A : %F X"
apply (rule_tac F = "A" in finite_subset_induct)
apply assumption+
apply (rule Fin.emptyI)
apply (rule Fin.insertI)
apply fast+
done

lemma finite_vs_Fin: "(finite A & A <= X) = (A : %F X)"
apply (rule iffI)
apply (blast intro: Fin_finite finite_Fin)
apply (rule conjI)
apply (blast intro!: Fin_finite finite_Fin FinD)
apply (blast intro!: Fin_finite finite_Fin FinD)
done

lemma Collect_Dom_Insert: "{d. EX n : insert x F. d = xa n} = {d. EX n : F. d = xa n} Un {xa x}"
apply auto
done

lemma Collect_Fin_Func: 
assumes prem1: "A : %F X"
assumes prem2: " {d. EX x:X. d = f x} <= X"
shows  "{d. EX n : A. d = (f n) } : %F X"
apply (cut_tac prem2)
apply (rule mp)
prefer 2 
apply (assumption)
apply (cut_tac prem1)
apply (rule mp)
prefer 2 
apply (assumption)
apply (rule_tac x = "f" in spec)
apply (rule_tac F = "A" and A = "X" in Fin_induct)
apply safe
apply simp
apply (erule_tac x = "xa" in allE)
apply (subst Collect_Dom_Insert)
apply auto
done

lemma Collect_Fin_Func_Subset: "[|A : %F X ; {d. EX x:X. d = f x} <= X|] ==> {d. EX n : A. d = (f n) } : %F X"
apply (rule Collect_Fin_Func)
apply assumption
apply assumption
done

lemma insert_card_eq: 
  "[|x ~: F; y ~: G; finite F; finite G; card F = card G|] ==> 
   card (insert x F) = card (insert y G)"
apply auto
done


lemma Nat_Fin_Add_Collect: "[|A : %F %N ; m : %N|] ==> {d. EX n : A. d = (n + m)}: %F %N"
apply (rule Collect_Fin_Func)
apply assumption
apply auto
done

lemma Collect_Dom_Insert: 
 "{d. EX n : insert x F. d = xa n} = insert (xa x) {d. EX n : F. d = xa n}"
apply auto
done


lemma size_image: 
 "!!A. [|A : %F X ; inj_on f A |] ==> #(f ` A) = #A"
apply (unfold zsize_def)
apply auto
apply (rule card_image)
apply (drule Fin_finite)
apply auto
done


(* I don't see the use of this ... bu 
val prems = goalw thy [] 
 "[|A : %F %N ; m : %N|] ==> #{d. EX n : A. d = (n + m)} = #A"
by (rewtac zsize_def);
by (Simp_tac 1);
by (cut_facts_tac prems 1);
by (rotate_tac 1 1);
by (rtac mp 1);
by (assume_tac 2);
by (rotate_tac 1 1);
by (rtac mp 1);
by (assume_tac 2);
by (res_inst_tac [("x","m")] spec 1);
by (res_inst_tac [("F","A"),("A","%N")] Fin_induct 1);
by Safe_tac;
by (Asm_full_simp_tac 1);
by (eres_inst_tac [("x","xa")] allE 1);
by (stac Collect_Dom_Insert 1);
by (rtac insert_card_eq  1);
by Auto_tac;
by (res_inst_tac [("X","%N")] (Fin_finite) 2);
by (Asm_simp_tac 2);
by (rotate_tac 2 1);
by (dtac (zadd_commute RS subst) 1);
by (rotate_tac 8 1);
by (dtac sym 1);
by (rotate_tac 8 1);
by (dtac (zadd_commute RS subst) 1);
by (rotate_tac 8 1);
by (dtac zadd_left_cancel 1);
by Auto_tac;
by (etac Fin_finite 1);
qed "Nat_Size_Add_Collect";
Addsimps [Nat_Size_Add_Collect];
*)


lemma fin_finite: "!!A. A : %F X ==> finite A"
apply (erule Fin_induct)
apply auto
done

lemma size_insert_disjoint [simp]:  "!!A. [|A : %F X ; x ~: A|] ==> #(insert x A) =  zsuc (# A)"
apply (unfold zsize_def)
apply (drule fin_finite)
apply (subst znat_Suc [THEN sym])
apply auto
done


lemma card_size_eq: "(card m) = ($i (# m))"
apply (unfold zsize_def)
apply simp 
done

lemma Size_Naturals [simp]: "#m : %N"
apply (unfold zsize_def)
apply (subst card_size_eq)
apply auto
apply (case_tac "#m = 0")
apply auto
done


lemma size_empty2: "!!x. m : %F X  ==> (# m = 0) = (m = {})"
apply (erule Fin_induct)
apply (simp_all add: zsuc_def)
apply (auto)
apply(subgoal_tac "0 \<le> # F",arith) 
apply(subgoal_tac "#F : %N", simp add: in_naturals[symmetric])
apply(simp add: Size_Naturals)
done


lemma card_empty2: "m : %F X ==> ((card m = 0) = (m = {}))"
apply (erule Fin_induct)
apply (simp (no_asm))
apply (subst card_insert_disjoint)
apply (erule Fin_finite)
apply  assumption
apply simp
done


lemma size_set_notempty [rule_format]: "!!m. m : %F X ==> m ~= {} --> 0 < #m"
apply (erule Fin_induct)
apply auto
done


lemma size_set_empty: "# {} = 0"
apply (rule size_empty2 [THEN iffD2])
apply auto
done


lemma card_notempty: "!!x. [|x ~= {} ; x : %F X|] ==> card x ~= 0"
apply auto

apply (drule card_empty2 [THEN subst])
apply fast+
done


section {* Finite Functions *}

lemma empty_fin_pfun[simp, intro!]: "{} : (S -||-> R)"
apply (unfold fin_part_func_def)
apply auto
done

lemma empty_fin_pinj[simp, intro!]: "{} : (S >-||-> R)"
apply (unfold fin_part_inj_def)
apply auto
done

lemma override_fpfun[simp]: "[|f:(A -||-> B) ; g:(A -||-> B)|] ==> ((f (+) g):(A -||-> B))"
apply (unfold fin_part_func_def)
apply simp
done

lemma fin_part_fun_single [simp]: "[|fst p : A ; snd p : B |] ==> {p} : (A -||-> B)"
apply (unfold fin_part_func_def)
apply auto
done


lemma Fin_Dom_Partial: "!!t.[|t : %F (X %x Y) ; t : (X -|-> Y)|] ==> (dom t: %F X)"
apply (erule Fin_induct)
apply auto
done

lemma Dom_Partial_Fin_lemma [rule_format (no_asm)]: 
"!! dt. dt : %F X ==> ALL t .  t:(X -|-> Y) --> dom t = dt --> t : Fin (X %x Y)"
apply (erule Fin_induct)
apply auto
apply (erule_tac x = "t - { (x,t%^x) }" in allE)
apply (auto intro: Fin_Diff_Set)
done

lemma Dom_Partial_Fin: "!! t. [|t : (X -|-> Y); dom t : %F X|] ==> (t : Fin (X %x Y))"
apply (auto intro: Dom_Partial_Fin_lemma)
done

lemma Fin_Partial_Func[simp]: "!!t. t : (X -||-> Y) ==> t : %F (X %x Y)"
apply (unfold fin_part_func_def)
apply (simp add: Dom_Partial_Fin)
done

lemma Fin_Partial_Dom_Func [simp]: "!!t. t : (X -||-> Y) ==> dom t : %F X"
apply (unfold fin_part_func_def)
apply auto
done

lemma Fin_Partial_Partial_Func [simp]: "t : (X -||-> Y) ==> t: (X -|-> Y)"
apply (unfold fin_part_func_def)
apply auto
done


lemma Dom_Int_Fin_Func_Add: 
"[|dom t : %F %Z ; t : (%Z -|-> X); m : %Z|] ==>  
   dom {p. EX n:dom t. p = (n + m, t%^n)} : %F %Z"
apply (subst Dom_Collect_Rel_fst)
apply (rule Collect_Fin_Func_Subset)
apply auto
done (* really useful ? *)


lemma Dom_Nat_Fin_Func_Add: 
"[|dom t : %F %N ; t : (%N -|-> X) ; m : %N|] ==>  
 dom {p. EX n:dom t. p = (n + m, t%^n)} : %F %N"
apply (subst Dom_Collect_Rel_fst)
apply (rule Collect_Fin_Func_Subset)
apply auto
done

lemma Dom_Nat_Fin_Part_Func_Add [simp]:"[|t : (%N -||-> X) ; m : %N|] ==>  {p. EX n:dom t. p = (n + m, t%^n)} : (%N -||-> X)"
apply (unfold fin_part_func_def)
apply safe
apply (rule_tac [2] Dom_Nat_Fin_Func_Add)
apply auto
done
 (* really useful ? *)


lemma Fin_Part_Func_Dom_Size_aux: 
assumes prem1: "(dom t) = dt"
assumes prem2: "t:(X -|-> Y)"
assumes prem3: "dt : %F X"
shows " # t = # (dom t)"
apply (unfold zsize_def)
apply auto
apply (insert prem1 prem2 prem3)
apply (rule mp)
prefer 2 
apply (assumption)
apply (rotate_tac 2)
apply (rule mp)
prefer 2 
apply (assumption)
apply (rotate_tac 2)
apply (rule mp)
prefer 2 
apply (assumption)
apply (rule_tac x = "t" in spec)
apply (rule_tac x = "Y" in spec)
apply (rule_tac F = "dt" and A = "X" in Fin_induct)
apply safe
apply simp
apply (erule_tac x = "xa" in allE)
apply (erule_tac x = "xb-{ (x,xb%^x) }" in allE)
apply auto
apply (rotate_tac 7)
apply (rotate_tac 7)
apply (rule_tac s = "Suc (card F) " and t = "card (insert x F) " in subst)
apply (rule card_insert_disjoint [THEN sym])
apply (rotate_tac 5)
apply (drule finite_vs_Fin [THEN iffD2])
apply (drule conjE)
apply auto
apply (rotate_tac 1)
apply (drule sym)
apply auto
apply (rule card_Suc_Diff1 [THEN sym])
apply auto
apply (rule_tac X = "X%xxa" in Fin_finite)
apply (rule Dom_Partial_Fin)
apply auto
done

 
lemma Fin_Part_Func_Dom_Size: "t : (X -||-> Y) ==> # t = # (dom t)"
apply (rule_tac X = "X" and Y = "Y" in Fin_Part_Func_Dom_Size_aux)
apply auto
done


lemma Fin_part_func_union [simp]:
"[|f : (X -||-> Y) ; g : (X -||-> Y) ; ((dom f) Int (dom g)) = {}|] ==> 
         f Un g : (X -||-> Y)"
apply (unfold fin_part_func_def)
apply (rule CollectI)
apply (rule conjI)
apply (erule CollectE)+
apply (erule conjE)+
apply (rule Partial_Union_Distr)
apply fast
apply (simp (no_asm))
apply (rule conjI)
apply auto
done

section{* Finite Number Range *}

lemma fin_x_upto_x: "(x .. x) : %F %Z"
apply simp
done


lemma numb_range_Fin_add: "a:%N \<Longrightarrow>(a .. (a + int b)) : %F %N"
apply (induct_tac "b")
apply (simp (no_asm))
apply (simp (no_asm))+
apply (rule_tac t = "a + (1 + int n)" and s = "zsuc (a + int n)" in subst)
prefer 2
apply (rule numb_range_insert_last [THEN ssubst])
apply simp+
apply (unfold zsuc_def)
apply (simp add: ring_eq_simps)
done


lemma numb_range_Fin_zadd_aux: "[|a:%N;b:%N|] ==> (a..a+b) : %F %N"
apply (rule_tac t = "b" in znat_inverse [THEN ssubst])
apply assumption
apply (rule numb_range_Fin_add)
apply assumption
done


lemma numb_range_Size_add: "a:%N ==> #(a .. (a + int b)) = zsuc (int b)"
apply (induct_tac "b")
apply (simp add: zsuc_def zsize_def)
apply auto
apply (rotate_tac 1)
apply (rule_tac t = "a + (1 + int n)" and s = "zsuc (a + int n)" in subst)
prefer 2
apply (rule numb_range_insert_last [THEN ssubst])
apply simp
apply (unfold zsize_def)
apply (rule_tac t = "1 + int n" and s = "zsuc (int n)" in subst)
prefer 2
apply (rule card_insert_disjoint [THEN ssubst])
apply auto
apply (rule_tac X = "%N" in Fin_finite)
apply (simp add: numb_range_Fin_zadd_aux)
apply (subst znat_inverse)
apply auto
apply (unfold zsuc_def)
apply (simp add: ring_eq_simps)+
done



lemma  numb_range_Size_zadd1: "!!b. [|b:%N ; a:%N|] ==> #(a .. (a + b)) = zsuc b"
apply (rule_tac t = "b" in znat_inverse [THEN ssubst])
apply assumption
apply (rule numb_range_Size_add)
apply assumption
done


lemma numb_range_Size_zadd [simp]: "!!a. [|a : %N ; a <= (b + 1)|] ==> #(a .. b) = zsuc (b - a)"
apply (case_tac "a <= b")
apply (rule_tac a1 = "a" in numb_range_Size_zadd1 [THEN subst])
prefer 2
apply assumption
apply (unfold Naturals_def)
apply auto
apply (unfold zsuc_def)
apply arith
done


lemma aux:  "!!z. ~ z <= w ==> w < (z::int)"
apply auto
done


lemma numb_range_Fin_zadd: "!!a. [|a : %N|] ==> (a .. b) : %F %N"
apply (case_tac "a <= b")
prefer 2
apply (drule aux)
prefer 2
apply (simp add: zless_eq_zadd)
apply (erule exE)
apply auto
apply (simp add: numb_range_Fin_zadd_aux)
done
declare numb_range_Fin_zadd [simp]


lemma zadd_numb_range_Fin_Nat [simp]: "!!a. [| a : %N ; c : %N|] ==> (a+c .. b+c) : %F %N"
apply auto
done


lemma numb_range_set_notempty [simp]: "!!x. [|x: %F X ; x ~= {} |]==> ( 1: ( 1..#x))"
apply (unfold Naturals_def numb_range_def)
apply simp
apply (drule size_set_notempty)
apply simp
apply auto
done

lemma numb_range_mem [simp]: "[|a <= n ; n <= b|] ==> n : (a .. b)"
apply (unfold numb_range_def)
apply auto
done


lemma upto_size_empty: "y < x ==> #(x .. y) = int 0"
apply auto
done


lemma size_x_upto_x:  "card ( x .. x) = 1"
apply auto
done

(*
Goal "(x .. y) : %F %Z"
by (case_tac "y < x" 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (HINT "( x .. y) = ( x .. (x + $# z))" (K all_tac) 1);
by (Asm_full_simp_tac 1);
by (nat_ind_tac "z" 1);
by (Asm_full_simp_tac 1);


val prem = goal thy "x<=y ==> card ( x .. y + $# 1) = card ( x .. y) + 1";
by (cut_facts_tac prem 1);
by (res_inst_tac [("b3","y")] (numb_range_Un RS mp RS mp RS subst) 1);
back();
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (HINT "(y + #1 .. y + $# 1) = {y+ #1}" (K all_tac) 1);
by (asm_simp_tac (set_ss) 1);
by (HINT "(x .. y) Un {y + #1} = insert(y + #1)(x .. y)" (K all_tac) 1);
by (asm_simp_tac (set_ss) 1);
by (rtac trans 1);
by (rtac card_insert_disjoint 1);
by (Asm_simp_tac 3);
by (Asm_simp_tac 3);
by (asm_simp_tac (simpset() addsimps 
    [zadd_zminus_inverse_conc,zadd_zminus_inverse2_conc,znat_bin_0]) 3);
by (simp_tac (set_ss addsimps [numb_range_def]) 2);
by (Asm_simp_tac 2);
by (rtac (Fin_finite) 1);
*)




end
