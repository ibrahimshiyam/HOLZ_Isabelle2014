(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ZSeq.thy --- 
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
(* $Id: ZSeq.thy 6729 2007-08-03 05:25:17Z brucker $ *)

header{* Sequences in the Mathematical Toolkit *}

theory ZSeq imports ZFinite Wellfounded_Relations begin

types
  'a "seq" = "int <=> 'a"

  
constdefs
  seq        ::"'a set => ('a seq) set" 
 "seq S      == { f. (f: (Naturals -||-> S)) & (dom f = ( 1 .. (# f)))}" 
  seq1       ::"'a set => ('a seq) set"
 "seq1 S     == {f. f: (seq S) & ((int (0::nat)) < (# f))}"
  iseq       ::"'a set => ('a seq) set"
 "iseq S     == (seq S) Int (Naturals >-||-> S)"

  emptyseq   ::"'a seq"                            ("%<%>")
 "emptyseq   == {}"
  insertseq  ::"['a, 'a seq] => 'a seq"
 "insertseq x s == insert (1,x) {p. EX n: dom s. p = (zsuc n,s%^n)}"

  insertseq_rel :: "'a set => ('a seq * 'a seq) set"
  "insertseq_rel A == {(s,s'). s : seq A & (? a. s' = insertseq a s)}"

  seq_case :: "['a set, 'b, ('a => 'a seq => 'b), 'a seq] => 'b"
  "seq_case A b f s == @z.  (s = %<%> --> z = b)  & (! a:A. ! t:seq A. s = insertseq a t --> z = f a t)"

  seq_rec :: "['a set, 'b, ['a, 'a seq, 'b] => 'b, 'a seq] => 'b"
  "seq_rec A b d == wfrec (insertseq_rel A) (%f. seq_case A b (%a t. d a t (f t)))"

  mhead :: "'a set => 'a seq <=> 'a"
  "mhead A == lambda s: seq A. s %^ 1"

  mtail :: "'a set => 'a seq <=> 'a seq"
  "mtail A == lambda s : seq A. lambda n : (1 .. ((# s) - (1))) . s %^ (n+1)"

	      
syntax
  "@Sequence" :: "args => 'a seq "                   ("%<(_)%>")

translations
  "%< x, xs %>"    == "insertseq x %<xs%>"
  "%< x %>"        == "insertseq x %<%>"



axioms

lem1: "!!x s.  [| s : seq A; x : s |] ==> x = (1, mhead A %^ s) | (EX n : 1 .. # s - 1. x = (zsuc n, mtail A %^ s %^ n))"
insert_mhead_mtail: "!!s. [| s : seq A; s ~= %<%> |] ==> s = insertseq (mhead A %^ s) (mtail A %^ s)"
seq_mem_dom_neq_first:   "[|s: seq X ; a:s ; a ~= (1,s%^1)|] ==> ((fst a) : (2..#s)) "
Dom_insertseq: "[|y:X;t:seq X|] ==> dom (insertseq y t) = (1..#(insertseq y t))"
insertseq_eq: "[|s:seq X; t:seq Y; insertseq a s = insertseq b t|] ==> (a=b)"

ML
{*
fun au i = (by (SELECT_GOAL (auto_tac (claset(), simpset())) 1))
*}

lemma seqI: "!!s. [| s : %N -||-> A ; dom s = ( 1 .. # s) |] ==> s : seq A"
apply (unfold seq_def)
apply auto
done

lemma seqE: "[| s:seq A; [| s : %N -||-> A ; dom s = ( 1 .. # s) |] ==> R |] ==> R"
apply (unfold seq_def)
apply auto
done

lemma emptyseqI [simp]: "!!s. x:s ==> s ~= %<%>"
apply (unfold emptyseq_def)
apply auto
done

lemma mhead_eq[simp]: "!!s. [| s : seq A; s ~= %<%> |] ==> mhead A %^ s = s%^1"
apply (unfold mhead_def)
apply auto
done


lemma mtail_eq [simp]: "!!s. [| s : seq A; s ~= %<%> |] ==> mtail A %^ s = (lambda n : (1 .. ((# s) - (1))) . s %^ (n + 1))"
apply (unfold mtail_def)
apply (simp)
done


lemma aux: "zpred 2 = 1"
apply (unfold zpred_def)
apply auto
done


lemma aux1: " zsuc (x - int 1) = x"
apply (unfold zsuc_def)
apply auto
done

(*
lemma lem1: "!!x s.  [| s : seq A; x : s |] ==>  
  x = (1, mhead A %^ s) | (EX n : 1 .. # s - 1. x = (zsuc n, mtail A %^ s %^ n))"
apply (simp (no_asm_simp))
apply (unfold seq_def)
apply (simp (no_asm_use))
apply (simp (no_asm_simp) only: split_tupled_all)
apply (subgoal_tac "(a = 1) | (? n: 1 .. #s - 1. a = zsuc n)")
apply (erule disjE)
defer 1
apply (rule disjI2)
apply (erule bexE)
apply (rule_tac x = "n" in bexI)
apply auto
prefer 2
apply (rotate_tac )
apply (drule DomainI)
apply (erule_tac x = "a - 1" in ballE)
apply auto
apply (simp add: numb_range_def aux aux1 zsuc_def)+
apply auto
done
*)


subsection {* sequences-general *}

lemma seq_ran_subset [simp]: "(s : seq X) ==> (ran s <= X)"
apply (unfold seq_def fin_part_func_def pfun_def rel_def)
apply (simp (no_asm) add: ran_simp)
apply auto
done

lemma size_emptyseq [simp]: "# %<%> = 0"
apply (unfold emptyseq_def zsize_def)
apply (simp (no_asm))
done


lemma ran_emptyseq [simp]: "ran (%<%>) = {}"
apply (unfold emptyseq_def)
apply (simp (no_asm))
done

lemma dom_emptyseq [simp]: "dom (%<%>) = {}"
apply (unfold emptyseq_def)
apply (simp (no_asm))
done

lemma seq_imp_Fin_func: "t: seq X --> t : (%N -||-> X)"
apply (unfold seq_def)
apply auto
done

lemma seq_imp_numb_range: "t: seq X ==> (dom t) = (1 ..#t)"
apply (unfold seq_def)
apply auto
done

lemma empty_seq [simp]: "%<%> : seq UNIV"
apply (unfold emptyseq_def seq_def fin_part_func_def pfun_def rel_def zsize_def Pow_def Naturals_def)
apply simp
done


lemma empty_seq2 [simp]: "%<%> : seq G"
apply (unfold emptyseq_def seq_def fin_part_func_def pfun_def rel_def zsize_def Pow_def Naturals_def)
apply simp
done

lemma Seq_Subset [simp]: "[|X <= Y ; s:seq X|] ==> s: seq Y"
apply (unfold seq_def fin_part_func_def)
apply (simp add: Partial_Func_Ran_Subset)
done


lemma first_elem_notemptyseq [simp]: "[|x: seq X ; x ~= %<%>|] ==> (1, x%^1) : x"
apply (unfold emptyseq_def seq_def)
apply (rule_tac  X = "%N" and Y = "X" 
       in rel_apply_in_rel)
apply simp
apply simp
apply (rule_tac X = "%N %x X" in numb_range_set_notempty)
apply auto
done

lemma zsuc_zpred: "zsuc( zpred z) = z"
apply (unfold zsuc_def zpred_def)
apply auto
done


(*
lemma seq_mem_dom_neq_first: "[|s: seq X ; a:s ; a ~= (1,s%^1)|] ==> ((fst a) : (2..#s)) "
apply (unfold seq_def fin_part_func_def)
apply auto
apply (rotate_tac 3)
apply (rule_tac t = 2 in zsuc_zpred [THEN subst])
apply (rule numb_range_mem_neq_zsuc [THEN ssubst])
apply (simp add:zpred_def)
apply (rotate_tac 2)
apply (drule_tac s = "a" in surjective_pairing [THEN subst])
apply auto
apply (rule_tac P = "snd a = s %^ 1" in notE)
defer 1
apply (rule_tac X3 = "%N" and Y3 = "X" in beta_apply_pfun [THEN mp [THEN mp [THEN sym]]])
apply simp
apply (rotate_tac 4)
apply (drule sym)
apply (simp add: surjective_pairing)
prefer 2
apply (simp (no_asm_simp) add: zpred_def)
apply (drule sym)
apply simp
prefer 2
apply auto
sorry*)
declare seq_mem_dom_neq_first [simp]


lemma seq_Collect_zpred_zsuc_Fin_Func: "x : seq X ==>  
  {p. EX n: 1..zpred (#x). p = (n, x%^(zsuc n))} : (%N -||-> X)"
apply (unfold seq_def fin_part_func_def)
apply auto
apply (unfold pfun_def rel_def)
apply auto
apply (rule num_range_Naturals_mem)
prefer 2
apply fast
apply simp
apply (rule_tac X = "%N" in 
      Rel_Apply_in_Partial_Ran)
apply (unfold pfun_def rel_def)
apply fast
apply (simp (no_asm_simp))
apply (rule_tac X = "%N" and Y = "X" in rel_apply_in_rel)
apply (unfold pfun_def rel_def)
apply fast
apply (simp (no_asm_simp))
done


lemma unknown: 
"!!x. [|x : seq X ; x ~= %<%>|] ==> 0 < #x"
apply (unfold seq_def emptyseq_def)
apply auto
done


(*
val prems = goalw thy []
"[|x : seq X ; x ~= %<%>|] ==> #x =  
  zsuc(#{p. EX n: 1..zpred (#x). p = (n, x%^(zsuc n))})"
by (cut_facts_tac prems 1);
by (res_inst_tac [("X1","Naturals"),("Y1","X")] 
                 (Fin_Part_Func_Dom_Size RS ssubst) 1);
by (Asm_full_simp_tac 1); 
by (rtac (seq_Collect_zpred_zsuc_Fin_Func) 1);
by (Asm_simp_tac 1);
by (rewtac seq_def);
by (Asm_full_simp_tac 1); 
by (case_tac "1 <= zpred (#x)" 1);
by (stac numb_range_Size_zadd 1);
by (Asm_simp_tac 1);
by (rtac (znat_bin_1 RS subst) 1);
by (fold_goals_tac [zsuc_def]);
by (rtac zle_zsucI 1);
by (Asm_full_simp_tac 1);
by (SELECT_GOAL (rewrite_goals_tac [zle_def,zpred_def,zsuc_def,zsuc_def]) 1);
by (Asm_full_simp_tac 1);
by (SELECT_GOAL (rewrite_goals_tac [zpred_def,zle_def,zsuc_def,emptyseq_def]) 1);
by (asm_full_simp_tac (simpset () addsimps [zadd_assoc]) 1);

by (asm_full_simp_tac (simpset () addsimps [zsuc_to_zpred_le RS sym]) 1);
by (etac conjE 1);
by (rotate_tac 2 1);
by (dtac Fin_Partial_Func 1);
by (rotate_tac ~1 1);
by (dtac size_set_notempty 1);
by (assume_tac 1);
by Auto_tac;
by (rtac (zintervall_single RS mp) 1);
by (SELECT_GOAL (rewrite_goals_tac [zsuc_def,zpred_def]) 1);
by (rtac conjI 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
qed "seq_Collect_zpred_zsuc_Size";
*)
(*Delsimps [zadd_to_zdiff]
*)

lemma size_ge_zero [simp]: "0 <= # s"
apply (subst znat_bin_0 [symmetric])
apply (unfold zsize_def)
apply (simp (no_asm))
done

(* strange, but holds due to construction via Hilbert on nat's
   (thus have a solution in nat even for infinite sets in nat)
   that were embedded into integer ... *)

lemma size_is_Nat [simp]: " int x : %N "
apply (simp add: Naturals_def size_ge_zero)
done


lemma numb_range_size_front [simp]: "#(1 .. #s) = #s"
apply (rule numb_range_Size_zadd [THEN ssubst])
apply simp
apply (rule_tac t = "1" in zadd_0 [THEN subst])
back
back
apply (subst add_le_cancel_right)
apply (simp (no_asm))
apply (unfold zsuc_def)
apply arith
done

subsection {* insertseq *}

lemma Insertseq_Partial_Func [simp]: 
"[|y : X ; t : (%N -|-> X) ; ((dom t) = (1..#t))|]  
 ==> insertseq y t : (%N -|-> X)"
apply (unfold insertseq_def zsuc_def)
apply (rule Partial_Dom_Insert, auto)
apply(drule sym,simp)
done


lemma Insertseq_Dom_Fin_Nat [simp]: "!!t. dom t : Fin %N  ==> dom (insertseq y t) : %F %N"
apply (unfold insertseq_def zsuc_def)
apply auto
apply (rule Nat_Fin_Add_Collect)
apply (rule Fin_subset)
apply auto
done



lemma Insertseq_Fin_Part_Func_Nat: "[|y : X ; t : (%N -||-> X) ; ((dom t) = (1..#t))|] ==>  
      insertseq y t : (%N -||-> X)"
apply (unfold fin_part_func_def)
apply auto
done

declare size_insert_disjoint [simp del]
declare size_ge_zero [simp del] numb_range_size_front [simp del]

lemma Dom_size_insert_seq [simp]: "t : seq X  ==> #(dom (insertseq y t))= 1 + (#(dom t))"
apply (unfold seq_def insertseq_def fin_part_func_def zsuc_def)
apply auto
apply (rule size_insert_disjoint [THEN ssubst])
apply auto
apply (rule numb_range_Fin_zadd)
apply (simp add: zsuc_def ring_eq_simps)+
done


lemma size_insert_seq: 
"!!t. [|t : seq X ; y: X|] ==> #(insertseq y t) = zsuc  (# t)"
apply (unfold seq_def)
apply (auto del: fin_part_funcE)
apply (simplesubst Fin_Part_Func_Dom_Size)
apply assumption
apply (subst Fin_Part_Func_Dom_Size)
apply (rule Insertseq_Fin_Part_Func_Nat)
apply assumption+
apply (subst Dom_size_insert_seq)
apply (simp_all (no_asm_simp) add: seq_def)
apply (simp add: Ring_and_Field.ring_eq_simps zsuc_simp)
done
declare size_insert_seq [simp]

declare size_ge_zero [simp del] numb_range_size_front [simp del]

(*
lemma Dom_insertseq:  "[|y : X ; t : seq X|] ==> dom (insertseq y t) = ( 1..#(insertseq y t))"
apply (rule_tac X1 = "%N" and Y1 = "X" in Fin_Part_Func_Dom_Size [THEN ssubst])
apply (simp (asm_lr) add: seq_def Insertseq_Fin_Part_Func_Nat)
apply (rule sym)
apply (simp add: Insertseq_Fin_Part_Func_Nat)
apply auto
sorry*)

declare Dom_insertseq [simp]
declare size_ge_zero [simp] numb_range_size_front [simp]

lemma insertseq_seq_pred [simp]:  "[|t:(seq X) ; y:X|] ==> (insertseq y t):(seq X)"
apply (unfold seq_def)
apply simp
apply (rule conjI)
prefer 2
apply (rule Dom_insertseq)
apply (unfold seq_def)
apply auto
done
declare insertseq_seq_pred [simp]

lemma insertseq_not_empty [simp]: "insertseq a b ~= %<%>"
apply (unfold emptyseq_def insertseq_def)
apply auto
done

lemma insertseq_not_empty2 [simp]: "%<%> ~= insertseq a b"
apply (unfold emptyseq_def insertseq_def)
apply auto
done

(*
Addsimps [not_less_iff_geq,geq_and_neq_iff_greater,
          leq_and_neq_iff_less,less_imp_neq,
          less_imp_neqR,greater_imp_neq,greater_imp_neqR];*)

(* from contrib *)
lemma insert_not_absorb2 [simp]: "~(b <= c) --> insert a b ~= c"
apply auto
done


lemma insertseq_not_absorb [simp]: "b: seq X ==> insertseq a b ~= b"
apply (unfold insertseq_def seq_def zsuc_def)
apply (case_tac "b = {}")
apply (simp (no_asm_simp))
apply (rule insert_not_absorb2 [THEN mp])
apply simp

apply (rule notI)
apply (erule_tac c = " (#b + 1,b%^#b) " in subsetCE)
apply (rotate_tac -1)
apply (erule notE)
apply simp

apply (rule numb_range_mem)
apply auto
apply (drule pair_rel_dom)
apply simp
done

(*
Delsimps [not_less_iff_geq,geq_and_neq_iff_greater,
          leq_and_neq_iff_less,less_imp_neq,
          less_imp_neqR,greater_imp_neq,greater_imp_neqR];*)

(*
lemma insertseq_eq: "[|s: seq X ; t : seq Y ; insertseq a s = insertseq b t|] ==> (a=b)"
apply (unfold insertseq_def seq_def)
apply simp
sorry*)

(*
Addsimps [zadd_to_zdiff]
*)

(*
lemma 
 insertseq_eq_lemma:  "\<lbrakk> s: seq X ; t : seq Y;
 {p. EX x: dom s . p=(x+(n::int),s%^x)} =  
 {p. EX x: dom t . p=(x+n,t%^x)} \<rbrakk> \<Longrightarrow>  
 {p. EX x: dom s . p=(x,s%^x)} = {p. EX x: dom t . p=(x,t%^x)}"

apply (rule set_ext)
apply (simp ) 
apply (erule_tac  c=x in equalityCE)
thm seq_def

apply (auto simp: fin_part_func_def seq_def )

apply (unfold fin_part_func_def seq_def)
apply auto
apply (rotate_tac 4)
apply (erule equalityE)
apply (simp)
apply (auto del: equalityI Orderings.linorder_antisym_conv2 Orderings.linorder_antisym_conv1 )
sorry 
(*
apply auto
apply
apply (rotate_tac 4, erule equalityE, auto)+
done
*)
(* from contrib  *)

lemma insert_eq: "insert a m = insert a n --> a ~:m --> a~: n --> m = n"
apply auto
done




*)
 
  (* TODO 2005 *)
axioms insertseq_eq_lemma:  "!!s. \<lbrakk> s: seq X ; t : seq Y\<rbrakk> \<Longrightarrow>
 {p. EX x: dom s . p=(x+(n::int),s%^x)} =  
 {p. EX x: dom t . p=(x+n,t%^x)} -->  
 {p. EX x: dom s . p=(x,s%^x)} = {p. EX x: dom t . p=(x,t%^x)}"
(*
apply (unfold fin_part_func_def seq_def)
apply auto
apply (rotate_tac 4)
apply (erule equalityE)
apply (simp)
apply (auto del: equalityI Orderings.linorder_antisym_conv2 Orderings.linorder_antisym_conv1 )
sorry 
(*
apply auto
apply
apply (rotate_tac 4, erule equalityE, auto)+
done
*)
*)
(* from contrib  *)

lemma insert_eq: "insert a m = insert a n --> a ~:m --> a~: n --> m = n"
apply auto
done


lemma insertseq_eq_seq_help: 
assumes prem1: "s: seq X"
assumes prem2: "t : seq Y"
assumes prem3: "insertseq a s = insertseq a t" 
shows "(s=t)"
apply (insert prem1 prem2 prem3)
apply (unfold insertseq_def zsuc_def)
apply (rotate_tac -1)
apply (drule insert_eq [THEN mp [THEN mp [THEN mp]]])
apply (simp add: seq_def)
apply (simp add: seq_def)
apply (drule insertseq_eq_lemma [THEN mp])
apply fast
apply (simp (no_asm))
apply (insert prem1 prem2 prem3)
apply (rule_tac X1 = "%N" and Y1 = "Y" in apply_ident [THEN ssubst])
apply (unfold seq_def fin_part_func_def)
apply simp
apply (rule sym)
apply (rule_tac X1 = "%N" and Y1 = "X" in apply_ident [THEN ssubst])
apply simp+
done


lemma insertseq_eq_seq: 
"[| s: seq X; t : seq Y; insertseq a s = insertseq b t|]  ==> (s=t)"
apply (frule_tac s = "s" and t = "t" and a = "a" and b = "b" in insertseq_eq)
apply fast
apply simp
apply (rotate_tac -1)
apply simp
apply (drule_tac s = "s" and t = "t" in insertseq_eq_seq_help)
apply auto
done

lemma insertseq_relI: 
"!!s. [| s : seq A; s' = insertseq a s|] ==> (s,s') : insertseq_rel A"
apply (unfold insertseq_rel_def)
apply auto
done

lemma insertseq_relE: "[| (s,s') : insertseq_rel A; !!a. [| s : seq A; s' = insertseq a s|] ==> R |]  ==> R"
apply (unfold insertseq_rel_def)
apply (simp (no_asm_use))
apply (erule conjE)
apply (erule exE)
apply auto
done

declare insertseq_relI [intro!]
declare insertseq_relE [elim!]


lemma insertseq_wf_lem: "insertseq_rel A <= measure (% x. zint(zsize(dom x)))"
apply (unfold measure_def inv_image_def)
apply auto
(*
apply (rule zless_int [THEN iffD1])
apply (subst znat_inverse [THEN sym])
apply simp
apply (subst znat_inverse [THEN sym])
apply simp+*)
done


lemmas insertseq_wf =  insertseq_wf_lem [THEN wf_measure [THEN wf_subset]] (*|> standard*)


lemma mhead_closed: "!!s. [| s : seq A; s ~= %<%> |] ==> mhead A %^ s : A"
apply (frule first_elem_notemptyseq)
apply (assumption)
apply (simp (no_asm_simp))
apply (drule seq_ran_subset)
apply (erule subsetD)
apply (erule RangeI)
done

lemma empty2_lem: "{(x,y). False} = {}"
apply auto
done

lemma insert_lem: 
"{(xa,y). xa : insert x F & y = f xa} =  
  insert (x, f x) {(xa, y). xa : F & y = f xa}"
apply auto
done

lemma finite_lem: "!! f. finite A ==> finite {(x,y). x:A & y = f x}"
apply (erule finite_induct)
prefer 2
apply (rule insert_lem [THEN ssubst])
apply (auto simp add: empty2_lem)
done

lemma zsize_lambda: "!!f. A : %F X ==> (# (Lambda A f)) = (# A)"
apply (unfold Lambda_def zsize_def)
apply (erule Fin_induct)
prefer 2
apply (rule insert_lem [THEN ssubst])
apply (drule fin_finite)
apply (auto simp add: empty2_lem finite_lem)
done

lemma numb_range_empty: "!! x. y < x ==> x .. y = {}"
apply (unfold numb_range_def)
apply auto
done

ML {*
fun int_case_tac x = res_inst_tac [("z",x)] int_cases;
*}

lemma numb_range_lemma: "((1::int) .. # (1 .. n)) = (1 .. n)"
apply (tactic {*int_case_tac "n" 1*})
apply (simp add: zsuc_def)
apply (simp add: zpred_def)
done

lemma lambda_total1:
"(!! x. x:A ==> f x : B) ==> (lambda x : A. f x) : A ---> B"
apply (unfold Lambda_def tfun_def pfun_def rel_def)
apply auto
done

lemma lem2: "!!n. 1 <= n ==>int 0 <= n"
apply (rule zle_trans)
apply auto
done


lemma mtail_closed: "!!s. [| s : seq A; s ~= %<%> |] ==> mtail A %^ s : seq A"
apply (simp (no_asm_simp))
apply (erule seqE)
apply (rule seqI)
prefer 2
apply (simp add: numb_range_Fin_zadd [THEN zsize_lambda] numb_range_lemma)
apply (rule fin_part_funcI)
prefer 2
apply simp
apply (rule_tac a = "1 .. (#s - 1) " in pfun_subset)
apply (rule total_is_partial)
apply (rule lambda_total1)
apply (erule fin_part_funcE)
apply (erule pfun_apply)
apply (auto simp add: Naturals_def numb_range_def lem2)
done

lemma seqE_lem: 
"!! s. s: seq A  
   ==> (EX s' : seq A. EX a:A. s = insertseq a s') | s = %<%> "
apply (rule disjCI)
apply (rule_tac x = "mtail A %^ s" in bexI)
apply (rule_tac x = "mhead A %^ s" in bexI)
apply (erule insert_mhead_mtail) 
apply assumption
apply (erule mhead_closed)
apply assumption
apply (erule mtail_closed)
apply assumption
done


lemma seq_cases: 
assumes p1: "s:seq A"
assumes p2: "s = %<%> ==> P s"
assumes p3: "!!a s'. [| s' : seq A; a:A; s = (insertseq a s') |] ==> P s" 
shows "P s"
apply (rule p1 [THEN seqE_lem, THEN disjE])
apply (erule_tac [2] p2)
apply (erule bexE)
apply (erule bexE)
apply (erule p3)
apply assumption+
done

lemma seq_case_emptyseq: "seq_case A a f %<%> = a"
apply (unfold seq_case_def)
apply (rule some_equality)
apply auto
done


lemma seq_case_insertseq: 
"!!s. [| s: seq A; x : A |] ==> seq_case A a f (insertseq x s) = f x s"

apply (unfold seq_case_def)
apply (rule some_equality)
apply (auto dest: insertseq_eq_seq insertseq_eq)
done

declare seq_case_emptyseq [simp] seq_case_insertseq [simp]

lemma seq_rec_unfold_help: 
"(%s. seq_rec A c d s) =  
  wfrec (insertseq_rel A) (%f. seq_case A c (%a t. d a t (f t)))"
apply (unfold seq_rec_def )
apply (simp (no_asm))
done

lemmas seq_rec_unfold = insertseq_wf [THEN seq_rec_unfold_help [ THEN eq_reflection [THEN def_wfrec]]]
 
 
lemma seq_rec_emptyseq: "seq_rec A c h %<%> = c"
apply (rule seq_rec_unfold [THEN trans])
apply simp
done 

lemma seq_rec_insertseq: "!!s. [| s: seq A; a:A|] ==>  
  seq_rec A c h (insertseq a s) = h a s (seq_rec A c h s)"
apply (rule seq_rec_unfold [THEN trans])
apply (simp (no_asm_simp) add: insertseq_relI cut_apply)
done


lemma def_seq_rec_emptyseq: 
assumes rew: "!!s. f s == seq_rec A c h s"
shows "f(%<%>) = c"
apply (unfold rew)
apply (rule seq_rec_emptyseq)
done

lemma def_seq_rec_insertseq:
assumes rew: "!!s. f s == seq_rec A c h s"
assumes p1: "s : seq A"
assumes p2: "a : A"  
shows "f(insertseq a s) = h a s (f s)"
apply (unfold rew)
apply (rule p2 [THEN p1 [THEN seq_rec_insertseq]])
done

lemma seq_induct:
assumes p1: "s:seq A"
assumes p2: "P %<%>"   
assumes p3: "!! a s. [| s : seq A; a:A; P s|] ==> P(insertseq a s)"
shows "P s"
apply (rule p1 [THEN rev_mp])
apply (rule insertseq_wf [THEN wf_induct])
apply (rule impI)
apply (erule seq_cases)
apply (auto intro!: p2 p3 simp add: insertseq_rel_def)
done



lemma seq_imp_fin: "!! X. list : seq X  ==> list : %F (%N %x X)"
apply (unfold seq_def)
apply simp_all
done



lemma card_list_zero_imp_list_empty: 
"!! X. list : seq X ==> (# list = 0) = (list = %<%>)"
apply (unfold emptyseq_def)
apply (rule iffI)
apply simp_all
apply (rule size_empty2 [THEN iffD1])
apply simp_all
apply (rule seq_imp_fin) 
apply (assumption)
done

lemma card_list_zero_imp_list_empty2: "!! X. list : seq X ==> (# list <= 0) = (list = %<%>)"
apply (rule iffI, simp_all)
apply (rule card_list_zero_imp_list_empty [THEN iffD1], assumption)
apply (drule zle_imp_zless_or_eq)
apply (erule disjE)
apply (subgoal_tac "# list : %N")
apply (simp only: ZInteg.in_naturals[symmetric])
apply (simp_all add: Size_Naturals)
done

lemma card_list_zero_imp_list_empty3: "!! X. list : seq X ==> (# list < 1) = (list = %<%>)"
apply (rule trans)
apply (rule_tac [2] card_list_zero_imp_list_empty2)
apply auto
done



declare card_list_zero_imp_list_empty [simp] card_list_zero_imp_list_empty2 [simp] 
          card_list_zero_imp_list_empty3[ simp]

declare card_list_zero_imp_list_empty [simp del] card_list_zero_imp_list_empty2[simp del]
          card_list_zero_imp_list_empty3[simp del]


lemma zsize_image: "!!f. [| inj f; x :%N |] ==>  #(f ` (x..y)) =  #(x..y)"
(* precondition x :%N inherited from too weak basic lemma numb_range_Fin_add *)
apply (unfold zsize_def)
apply (subst card_image)
apply (simp_all)
apply (unfold inj_on_def)
apply auto
done

end
