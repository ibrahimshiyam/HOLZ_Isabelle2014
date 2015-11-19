(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ZInteg.thy --- 
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
(* $Id: ZInteg.thy 6729 2007-08-03 05:25:17Z brucker $ *)

header{* Integers in the Mathematical Toolkit *}

theory ZInteg imports  ZMathTool begin 

constdefs
  zpred       :: "int=>int"
  "zpred(Z) == Z - 1"

  zsuc        :: "int=>int"
  "zsuc(Z) == Z + 1"


subsection{* znat and zint *}

lemma znat_bin_0: "(int 0) = 0"
apply auto
done

lemma zint_inverse[simp]: "$i(int i) = i"
apply auto
done


lemma zless_def_Suc: "(n < m) = (? x. m = n + int (Suc x))"
apply (rule iffI)
apply (simp add: zless_iff_Suc_zadd)
apply (erule exE)
apply (erule ssubst)
apply arith
done

lemma zle_imp_zless_or_eq: "z <= w \<Longrightarrow> z < w| z = (w::int)"
apply auto
done


lemma znat_inverse: "(b \<in> %N) ==> (b = int($i b))"
apply (unfold Naturals_def)
apply auto
done

lemma iter_0[simp]: "(iter R (int 0)) = (idZ (dom R))"
apply (unfold iter_def Naturals_def)
apply (simp (no_asm) del: znat_bin_0)
done

lemma znat_pred[simp]: "!!n. n ~= 0 ==> (int (n - 1)) = zpred (int n)"
apply auto
apply (unfold zpred_def)
apply arith
done

lemma znat_Suc_not_zint_conc_Zero[simp]: " Suc n ~= $i 0"
apply (subst znat_bin_0 [symmetric])
apply (subst zint_inverse)
apply (simp (no_asm))
done

lemma inj_zint[simp]: "\<lbrakk> n: %N; m: %N \<rbrakk> \<Longrightarrow> (($i n) = ($i m)) = (n = m)"
apply auto
apply (subst znat_inverse)
prefer 2
apply (subst znat_inverse)
back back
apply auto
done



lemma in_naturals: "(0 <= n) = (n : %N)"
apply (unfold Naturals_def)
apply auto
done

lemma zero_is_natural: "0 : %N"
apply (unfold Naturals_def)
apply auto
done

lemma one_is_natural: "1 : %N"
apply (unfold Naturals_def)
apply auto
done

lemma two_is_natural: "2 : %N"
apply (unfold Naturals_def)
apply auto
done

declare zero_is_natural [simp] one_is_natural [simp] two_is_natural [simp]

lemma in_naturals2[simp]: "!!n. 0 < n ==> (n : %N)"
apply (unfold Naturals_def)
apply (simp add: symmetric)
done



lemma zpred_zint: "!!n. 0 < n ==> (($i n) - 1) = ($i (zpred n))"
apply (rule_tac t = "($i n) - 1 " in zint_inverse [THEN subst])
apply (rule znat_pred [THEN ssubst])
apply auto
done


subsection{* inequalities *}

lemma zless_not_refl3: "((z::int) < w) ==> z ~= w"
apply (subst eq_sym_conv)
apply (simp add: less_imp_neq)
done

lemma less_zsuc_eq_le [simp]: "(a < zsuc m) = (a <= m)"
apply (unfold zsuc_def)
apply simp
done


lemma less_zpred_eq_le [simp]: "(a <= zpred m) = (a < m)"
apply (unfold zpred_def)
apply simp
done


subsection{* Number range *}

lemma num_range_empty: "({} = (a .. b)) = (b < a)"
apply (unfold numb_range_def)
apply (rule iffI)
apply auto
done

lemma num_range_empty2: "((a .. b) = {}) = (b < a) "
apply (unfold numb_range_def)
apply (rule iffI)
apply auto
done

declare num_range_empty [simp] num_range_empty2 [simp]

lemma num_range_empty_imp[simp]: "!!a. b < a ==> (a .. b)={}"
apply (unfold numb_range_def)
apply auto
done

lemma zadd_numb_range_collect[simp]: "{d. EX n: (q..m). d = ((n::int)+s)} = ((q+s)..(m+s))"
apply (unfold numb_range_def)
apply auto
apply (rule_tac x = "x - s" in exI)
apply (simp)
done


lemma num_range_zless_mem[simp]: "!!a::int. n < a ==> (n ~: (a..b))"
apply (unfold numb_range_def)
apply auto
done

lemma num_range_zless_mem2[simp]: "!!b::int. b < n ==> (n ~: (a..b))"
apply (unfold numb_range_def)
apply auto
done

(* this rule loop -- don't put in simpset! *)
lemma num_range_Naturals_mem: 
"!!a. [| a:%N; n : (a..b) |] ==> n: %N"
apply (unfold numb_range_def Naturals_def)
apply auto
done


lemma numb_range_single[simp]: "(a .. a) = {a}"
apply (unfold numb_range_def)
apply auto
done

 
lemma numb_range_insert_first: "!!a. a <= b ==>  ((zpred a) .. b) = insert (zpred a) (a .. b)"
apply (unfold numb_range_def zpred_def)
apply auto
done
 
lemma numb_range_insert_last: "!!a. a <= b ==>  (a .. (zsuc b)) = insert (zsuc b) (a .. b)"
apply (unfold numb_range_def zsuc_def)
apply auto
done

lemma zadd_to_zdiff_zle: "((a::int) <= b + c) = (a - c <= b)"
apply auto
done


lemma numb_range_mem_zadd[simp]: "((a + b) : (m .. n))  =  (a : (m-b .. n-b))"
apply (unfold numb_range_def)
apply (simp (no_asm) add: zadd_to_zdiff_zle)
apply auto
done
 

lemma numb_range_mem_neq_zsuc: "!!a. a ~= m ==> (a : (zsuc m .. n)) = (a : (m .. n))"
apply (unfold numb_range_def zsuc_def)
apply auto
done

(* Superflouos due to next one ...
Goalw [numb_range_def]
"!!a. a ~= zsuc m ==> (a : (n .. zsuc m)) = (a : (n .. m))"
by Auto_tac;
qed "numb_range_mem_neq_zsuc2";*)

declare numb_range_mem_neq_zsuc [symmetric, simp] (*numb_range_mem_neq_zsuc2 [simp]*)
 

lemma numb_range_mem_neq_zpred: 
"!!a. a ~= m ==> (a : (n .. m)) = (a : (n .. zpred m))"
apply (unfold numb_range_def)
apply auto
done
declare numb_range_mem_neq_zsuc [symmetric, simp] numb_range_mem_neq_zpred [simp]


lemma numb_range_subset[simp]:  "!!k. k <= m ==> (m .. n) <= (k .. n)"
apply (unfold numb_range_def)
apply auto
done


lemma numb_range_mem_subset[simp]: "!!k. [| k < m ;a : (m .. n) |] ==> (a : (k .. n))"
apply (drule order_less_imp_le)
apply (rule subsetD)
apply auto
done


lemma numb_range_mem_subset2[simp]: 
"!!n. [| n <= k; a : ( m .. n) |] ==> a : ( m .. k)"
apply (unfold numb_range_def)
apply auto
done


lemma numb_range_mem_zsuc_zpred[simp]: "!!a. [| a : (m .. zpred n) |] ==> (zsuc a : (m .. n))"
apply (unfold numb_range_def zsuc_def)
apply auto
done

lemma empty_numb_range[simp]: "!!b. b < c ==> (((a .. b) Int (c .. d))) = {}"
apply (unfold numb_range_def)
apply auto
done


lemma numb_range_Un [simp]: "!!a. [| a <= (b + 1); b <= c |] ==>  
   ((a .. b) Un (b + 1 .. c)) = (a .. c)"
apply (unfold numb_range_def zsuc_def)
apply auto
done

subsection{* Integers and Naturals *}

lemma Integers_Subset[simp]: "{(n::int). (P n)}<= %Z"
apply (unfold Integers_def)
apply auto
done

lemma Naturals_1_Mem[simp]: "((n::int):%Z)"
apply (unfold Integers_def)
apply (simp (no_asm))
done

lemma Naturals_Mem[simp]: " ~ neg n --> n:%N"
apply (unfold Naturals_def neg_def)
apply auto
done


lemma Nat_zless_zadd[simp]: "!!b. [| b:%N; a < c |] ==> (a < c + b)"
apply (unfold numb_range_def Naturals_def)
apply auto
done


lemma Nat_zle_zadd[simp]: "!!b.[| b:%N ; a <= c |] ==> a <= c + b"
apply (unfold numb_range_def Naturals_def)
apply auto
done


lemma Nat_zsuc[simp]: "!!x. x:%N ==> zsuc x:%N"
apply (unfold zsuc_def Naturals_def)
apply auto
done

lemma Nat_zadd [simp]: "!!n. [| n:%N ;  m:%N |] ==> n+m:%N"
apply (unfold Naturals_def)
apply auto
done

lemma zsuc_simp:  "(zsuc x) = (x + 1)"
apply (unfold zsuc_def)
apply auto
done


lemma Naturals_1_zadd_zle [simp]: "!!n. (1::nat) <= n ==> ~ (c + n <= c)"
apply auto
done


lemma Naturals_1_Mem[simp]: "!!a. [| a : %N ; a~=0 |] ==>  (a : Naturals_1)"
apply (unfold Naturals_1_def Naturals_def)
apply auto
done

lemma zless_eq_zadd_Suc: "w < z \<Longrightarrow>? n. z = w + int (Suc n)"
apply (simp only: zless_iff_Suc_zadd)
done

lemma zless_eq_zadd: "x <= y = (? z::nat. y = x + int z)"
apply (rule iffI)
apply (drule order_le_less [THEN iffD1])
apply (erule disjE);
apply (drule zless_eq_zadd_Suc)
apply fast
apply (rule_tac x = "0" in exI)
apply simp
apply (erule exE)
apply simp
done

lemma znatprop1: "!!x. x = int xnat ==> P(xnat::nat) = P($i x)"
apply simp
done

lemma znatprop2: 
"!!x. [|x = int xnat;y = int ynat|] ==> P(xnat::nat)(ynat::nat) = P($i x)($i y)"
apply simp
done


lemma znat_Suc[simp]: "int (Suc n) = zsuc (int n)"
apply (unfold zsuc_def)
apply (arith)
done


lemma naturalsI: "!!x. x = int xnat ==> (x : %N)"
apply simp
done

lemma nat2naturals:  "(? xnat. x = int xnat) = (x : %N)"
apply (rule iffI)
apply (erule exE)
apply simp
apply (unfold Naturals_def)
apply simp
apply (drule zless_eq_zadd [THEN iffD1])
apply simp
done



lemma naturals_induct: 
assumes prem1: "x : %N"
assumes prem2: "!! x. P(x) ==> P(x + int 1)"
assumes prem3: "P(int 0)"
shows "P(x)"
apply (insert prem1)
apply (drule nat2naturals [THEN iffD2])
apply (erule exE)
apply (rule_tac s = "P (int xnat)" in subst)
prefer 2
apply (induct_tac "xnat")
apply (rule prem3)
apply (rule_tac P = "P" in subst)
prefer 2
apply (rule prem2)
apply assumption
apply (rule_tac s = "int (xnat + 1)" and t = "int xnat + int 1" in subst)
apply simp
apply auto
done


(* New Version: Stronger premisse in step *)
lemma naturals_induct: 
assumes prem1: "x : %N"
assumes prem2: "!! x.[| x:%N; P(x) |] ==> P(x + int 1)"
assumes prem3:  "P(int 0)"
shows "P(x)"
apply (insert prem1)
apply (drule nat2naturals [THEN iffD2])
apply (erule exE)
apply (tactic {*hyp_subst_tac 1*})
apply (induct_tac "xnat")
apply (rule prem3)
apply (rule_tac P = "P" in subst)
prefer 2
apply (rule prem2)
prefer 2
apply assumption
apply (simp add: ring_eq_simps)+
done


lemma z_add_induct: 
assumes prem1: "P(k::int)"
assumes prem2:  "k <= x"
assumes prem3:  "!! x. P(x) ==> P(x + int 1)"
shows "P(x)"
apply (insert prem1 prem2 prem3)
apply (drule zless_eq_zadd [THEN iffD1])
apply (erule exE)
apply (simp)
apply (induct_tac "z")
apply simp
apply (rule_tac s = "(k + int n) + int 1" and t = "k + int (Suc n)" in subst)
apply (simp add: ring_eq_simps)
apply auto
done

lemma naturals_shift:
"\<lbrakk>n \<in> %N ; n \<noteq> 0 \<rbrakk> \<Longrightarrow> \<exists> m. (m \<in> %N \<and> n = m + 1)"
apply(rule_tac P = "n \<noteq> 0" in mp)
by(erule naturals_induct,simp_all)

lemma naturals_exhaust :
assumes typing : "n \<in> %N"
assumes H1     : "\<lbrakk>n \<in> %N ; n = 0 \<rbrakk> \<Longrightarrow> P 0"
assumes H2     : "\<lbrakk>n \<in> %N ; \<exists> m. (m \<in> %N \<and> n = m + 1) \<rbrakk> \<Longrightarrow> P n"
shows   "P n"
apply (insert typing)
apply (cases "n = 0")
apply (simp add: H1)
apply (rule H2,simp)
apply (frule naturals_shift,simp_all)
done


end

