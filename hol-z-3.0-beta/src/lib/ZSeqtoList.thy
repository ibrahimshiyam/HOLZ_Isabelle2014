(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 *  --- 
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
(* $Id: ZSeqtoList.thy 6729 2007-08-03 05:25:17Z brucker $ *)


header{* A rudimentery Theory-Morphism from List to Sequences *}

theory ZSeqtoList imports ZSeq FunAbs begin 

consts
    Rep_seqtype :: "'a list => ('a seq)"

primrec 
  seqOfList_Nil:  "Rep_seqtype [] = %<%>"
  seqOfList_Cons: "Rep_seqtype (x#xs) = insertseq x (Rep_seqtype xs)"

constdefs
(* Foundational stuff for ytheorem lifter .... *)
  seqtype      :: "('a seq) set" 
  "seqtype     == seq UNIV"
  Abs_seqtype  :: "('a seq) => 'a list"
  "Abs_seqtype == (% y. @x . Rep_seqtype(x)=y)"
  ListSeqAbs   :: "('a list, 'a seq) typeabs"
  "ListSeqAbs  == (seqtype, Rep_seqtype, Abs_seqtype)"
   

(* base definition for concat, snoc (cons inverse).  *)
(* The latter gives rise for alternative case dist-  *)
(* inction and induction rules ... *)
  concatseq    :: "('a seq * 'a seq) <=> 'a seq"
  "concatseq   == {((s,t),y). y = TARep ListSeqAbs 
                           ((TAAbs ListSeqAbs s) @ (TAAbs ListSeqAbs t))}"   

  snoc_rel     :: "'a set => ('a seq * 'a seq) set"
  "snoc_rel A  == {(s,s'). s : seq A &(? a:A. s'=concatseq%^(s,%<a%>))}"

  snoc_case    :: "['a set, 'b, ('a => 'a seq => 'b), 'a seq] => 'b"
  "snoc_case A b f s == @z.  (s = %<%> --> z = b)  & 
                             (! a:A. ! t:seq A. s =concatseq%^(t,%<a%>)--> 
			                        z = f a t)"


(* other crucial list definitions *) 
  foldrseq     :: "[(('a * 'b) set <=> 'b),'b] => ('a seq <=> 'b)"
  "foldrseq f g== UNIV" (* Pfusch !!! *)
 
  foldlseq     :: "['b,(('b * 'a) set <=> 'b)] => ('a seq <=> 'b)"
  "foldlseq f g== UNIV" (* Pfusch !!! *)

  foldseq      :: "[(('a * 'a) set <=> 'a)] => ('a seq <=> 'a)"
  "foldseq f   == UNIV" (* Pfusch !!! *)
 

  headseq      :: "'a seq <=> 'a"
  "headseq     == {(s,h). h = (hd(TAAbs ListSeqAbs s))}" 

  lastseq      :: "'a seq <=> 'a"
  "lastseq     == {(s,l). l = (last(TAAbs ListSeqAbs s))}"

  frontseq     :: "'a seq <=> 'a seq"
  "frontseq    == {(s,f). f = TARep ListSeqAbs(butlast(TAAbs ListSeqAbs s))}"

  tailseq      :: "'a seq <=> 'a seq"
  "tailseq     == {(s,t). t = TARep ListSeqAbs(tl(TAAbs ListSeqAbs s))}"

  revseqseq    :: "'a seq <=> 'a seq"
  "revseqseq   == {(s,r). r = TARep ListSeqAbs (rev (TAAbs ListSeqAbs s))}"
 
  filtering    :: "('a seq * 'a set) <=> 'a seq"
  "filtering   == {((s,V),F). F = TARep ListSeqAbs (filter
                                                    (% a. a : V) (TAAbs ListSeqAbs s))}"

  extraction   ::"(int set * 'a seq) <=> 'a seq"
  "extraction  == UNIV"   (* Pfusch !!! *)

  prefixseq    :: "'a seq <=> 'a seq"
  "prefixseq   == {(s,t). ? v:seq UNIV. (concatseq%^(s,v)) = t}"
  suffixseq    :: "'a seq <=> 'a seq"
  "suffixseq   == {(s,t). ? u:seq UNIV. (concatseq%^(u,s)) = t}"
  inseq        :: "'a seq <=> 'a seq"
  "inseq       == {(s,t). ? v:seq UNIV. (concatseq%^(v,s)) = t}"

 
   
syntax
  "*concatseq" ::"['a seq, 'a seq] => 'a seq"     ("(2 _ %&^/ _)" [70,71] 70)
  "*headseq"   ::"('a seq) => 'a"                 ("(1 head _)" 70) 
  "*lastseq"   ::"('a seq) => 'a"                 ("(1 last _)" 70) 
  "*frontseq"  ::"('a seq) => ('a seq)"           ("(1 front _)" 70)
  "*tailseq"   ::"('a seq) => ('a seq)"           ("(1 tail _)" 70)
  "*filtering" ::"['a seq, 'a set] => 'a seq"     ("(2 _ %|`/ _)" [70,71] 70)
  "*revseqseq" ::"('a seq) => ('a seq)"           ("(1 revseq _)" 70) 
  "*prefix"    ::"['a seq, 'a set] => 'a seq"     ("(2 _ prefix/ _)" [70,71] 70)
  "*suffix"    ::"['a seq, 'a set] => 'a seq"     ("(2 _ suffix/ _)" [70,71] 70)
  "*in"        ::"['a seq, 'a set] => 'a seq"     ("(2 _ in/ _)" [70,71] 70)




translations
  "s %&^ t"    == "concatseq%^(s,t)"
  "head s"     == "headseq%^s"
  "last s"     == "lastseq%^s"
  "front s"    == "frontseq%^s"
  "tail s"     == "tailseq%^s"
  "revseq s"   == "revseqseq%^s"
  "s %|` m"    == "filtering%^(s,m)"
  "s prefix t" == "(s,t):prefixseq"
  "s suffix t" == "(s,t):suffixseq"
  "s in t"     == "(s,t):inseq"



axioms
  snoc_neq_empty: " t %&^ %< aa %> ~=  %<%> "
  snoc_inj1:   "[| t:seq A; t':seq A; aa: A; aa':A |] ==>
               t %&^ %< aa %> = t' %&^ %< aa' %> ==> t = t'"
  snoc_inj2:   "[| t:seq A; t':seq A; aa: A; aa':A |] ==>
               t %&^ %< aa %> = t' %&^ %< aa' %> ==> aa = aa'" 

  rev_insert_eq_snoc: 
              "[| s:seq A;a:A |] ==> 
               revseq (insertseq a s) = s %&^ %< a %> "

  seq_card_dom: "s:seq A ==> #(dom s) = # s"



(* nur diese hier sind neu... lb*)

mem_concatseq: "s : seq X --> t : seq Y --> x : (ran(s %&^ t)) = (x: (ran s) | x : (ran t))"
mem_filtering: "s : seq X --> x : (ran(s %|` V)) = (x : (ran s) & (x : V))"
snoc_wf_lem: "snoc_rel A <= measure (% x. zint(zsize(dom x)))"



lemma Rep_seqtype [simp]: "Rep_seqtype(x): seqtype"
apply (unfold seqtype_def)
apply (induct_tac "x")
apply (simp)
apply auto
done

lemma insertseq_not_absorb_seqtype [simp]: "s : seqtype ==> (insertseq a s ~= s)"
apply (unfold seqtype_def)
apply auto
done

lemma Rep_seqtype_inj [simp]: "inj Rep_seqtype"
apply (unfold inj_on_def)
apply (rule ballI)
apply (induct_tac "x")
apply (rule ballI)
apply (induct_tac "y")
apply (simp (asm_lr))
apply (simp (asm_lr))
apply (rule ballI)
apply (induct_tac "y")
apply (simp (asm_lr))
apply (erule_tac x = "lista" in ballE)
apply (simp (asm_lr))
apply (rule impI)
apply (rule conjI)
apply (rule_tac s = "Rep_seqtype list" and X = "UNIV::'a set" and t = " (Rep_seqtype lista) " and Y = "UNIV::'a set" in insertseq_eq)
apply (fold seqtype_def)
apply (simp (asm_lr))
apply (simp (asm_lr))
apply (simp (asm_lr))
apply (rotate_tac 1)
apply (erule impE)
prefer 2
apply (simp (asm_lr))
apply (rule_tac a = "a" and X = "UNIV::'a set" and b = "aa" and Y = "UNIV::'a set" in insertseq_eq_seq)
apply (fold seqtype_def)
apply (simp (asm_lr))
apply (simp (asm_lr))
apply (simp (asm_lr))
apply (simp (asm_lr))
done


lemma Inv_f_f: "inj(f) ==> (@ xa. f xa = f x) = x"
apply (rule injD)
apply assumption
apply (rule someI)
apply (rule refl)
done

lemma Rep_seqtype_inverse [simp]: "Abs_seqtype(Rep_seqtype(x)) = x"
apply (unfold Abs_seqtype_def)
apply (rule Inv_f_f)
apply (simp (asm_lr))
done


lemma List_of_seq_emptyseq: "((Abs_seqtype %<%>) = [])"
apply (unfold Abs_seqtype_def)
apply (rule some_equality)
apply auto
apply (rule mp)
prefer 2 
apply (assumption)
apply (induct_tac "x")
apply auto
done


lemma seq_Collect_Fin_Func: 
"!!x. [|x : (Naturals -||-> UNIV) ; 
      (ka + 1) = (card x) ; ((dom x) = (1.. zsuc (int ka)))|] ==>                 
      {p. EX n: 1..(int ka). p = (n, x%^n + 1)} : (Naturals -||-> UNIV)"
apply (unfold fin_part_func_def)
apply auto
apply (unfold pfun_def rel_def)
apply auto
apply (rule num_range_Naturals_mem)
apply auto
done

lemma seq_Collect_Size: "[|x : (Naturals -||-> UNIV) ;  
      ((Suc ka) = (card x)) ; ((dom x) = ( 1.. zsuc (int ka)))|] ==>  
      (ka = card {p. EX n: 1..int ka. p = (n, x%^n + 1::int)})"
apply (simp add: card_size_eq)
apply (rule_tac X1 = "Naturals" and Y1 = "UNIV" in Fin_Part_Func_Dom_Size [THEN ssubst])
apply (erule seq_Collect_Fin_Func);
apply (simp add: card_size_eq)
apply (unfold zsuc_def)
apply simp
apply simp
apply (case_tac "1<=(int ka)")
apply (unfold zsuc_def)
apply simp
apply simp
done



lemma inj_Abs_seqtype2: 
        "!!x. x : seqtype ==> (EX y. x = Rep_seqtype y)"
apply (unfold seqtype_def)
apply (erule seq_induct)
apply (rule_tac x = "[]" in exI)
apply (erule_tac [2] exE)
apply (rule_tac [2] x = "op# a y" in exI)
apply auto
done

lemma f_Inv_f: "y : range(f) ==> f (@ x. f x = y) = y"
apply (rule rangeE)
apply assumption
apply (rule someI)
apply (erule sym)
done


lemma Abs_seqtype_inverse [simp]:"y : seqtype ==> (Rep_seqtype (Abs_seqtype y)) = y"
apply (unfold Abs_seqtype_def)
apply (rule f_Inv_f)
apply (unfold image_def Bex_def)
apply (simp (no_asm))
apply (erule inj_Abs_seqtype2)
done



lemma seqtype_notempty [simp]: "seqtype ~= {}"
apply (unfold seqtype_def)
apply (rule x_in_S_implies_S_nonempty)
apply (rule empty_seq)
done


lemma ListSeqAbsIsTypeabs [simp]: "Typeabs ListSeqAbs"
apply (unfold Typeabs_def Let_def ListSeqAbs_def)
apply auto
done


lemma Rep_seqtype_lemma: "Rep_seqtype = TARep ListSeqAbs"
apply (unfold TARep_def ListSeqAbs_def)
apply (simp (no_asm))
done

lemma Abs_seqtype_lemma: "Abs_seqtype = TAAbs ListSeqAbs"
apply (unfold TARep_def ListSeqAbs_def)
apply (simp (no_asm))
done

lemma seqtype_lemma: "seqtype = TASet ListSeqAbs"
apply (unfold TARep_def ListSeqAbs_def)
apply (simp (no_asm))
done

lemma TARep_LSAbs_Nil: "TARep ListSeqAbs [] = %<%>"
apply (simp (no_asm) add: Rep_seqtype_lemma [symmetric])
done

lemma TARep_LSAbs_Cons: "TARep ListSeqAbs (x#xs) = insertseq x (TARep ListSeqAbs xs)"
apply (simp (no_asm) add: Rep_seqtype_lemma [symmetric])
done

lemma TAAbs_LSAbs_emptyseq: "(TAAbs ListSeqAbs %<%>) = []"
apply (rule_tac TA1 = "ListSeqAbs" in TARep_iff_inj [THEN subst])
apply (simp (no_asm))
apply (subst TARep_inverse)
apply (simp (no_asm))
apply (simp (no_asm) add: TARep_LSAbs_Nil [symmetric])
apply (simp (no_asm) add: TARep_LSAbs_Nil [symmetric])
done

lemma seqtype_emptyseq [simp]: "%<%> : TASet ListSeqAbs"
apply (simp (no_asm) add: seqtype_lemma [symmetric] seqtype_def)
done

lemma seq_seqtype: "s: seq X ==> s: seqtype"
apply (unfold seqtype_def)
apply (simp (no_asm_simp))
done

lemma dom_insertseq: "(dom (insertseq a s)) =  
                            (insert 1 {d . EX x: dom s. d = (x+1)})"
apply (unfold insertseq_def zsuc_def)
apply auto
done
 
ML
{*
fun au i = by (SELECT_GOAL (auto_tac (claset(), simpset()) )i)
*}

lemma insert_ran [simp]: "ran (insert (a, b) R) = insert b (ran R)"
apply auto
done


lemma ran_lem: 
"!!s. s: seq A ==>  
  Range {p. ? n:Domain s. p = (zsuc n, s %^ n)} = Range s"
apply (unfold seq_def)
apply auto
apply (rule_tac a = "n" in RangeI)
apply (rule_tac [2] a = "zsuc xa" in RangeI)
apply (drule_tac [2] sym)
apply auto
done

lemma ran_insertseq [simp]: 
"!!s. s:seq X ==> ran (insertseq a s) = (insert a (ran s))"
apply (unfold insertseq_def)
apply (simp add: ran_lem)
done
 
lemma ran_insertseq_TAAbs [simp]: "s: TASet ListSeqAbs ==> ran (insertseq a s) = (insert a (ran s))"
apply (rule mp)
prefer 2 
apply (assumption)
apply (simp (no_asm) add: seqtype_lemma [symmetric] seqtype_def)
done


(* -------------------------------------------------------- *)
(*  TypeAbs_Operator-Theoreme, die aus der Definition       *)
(*                    abgeleitet werden                     *)
(* -------------------------------------------------------- *)

lemma concatseq_TypeAbs: "(concatseq %^ (s,t)) =  
  TARep ListSeqAbs ((TAAbs ListSeqAbs s) @ (TAAbs ListSeqAbs t))"
apply (unfold concatseq_def)
apply (subst apply_single_tuple)
apply (rule refl)
done

lemma revseqseq_TypeAbs: "(revseq s) = (TARep ListSeqAbs (rev (TAAbs ListSeqAbs s)))"
apply (unfold revseqseq_def)
apply (subst apply_single)
apply (rule refl)
done


lemma last_TypeAbs: "(last s) = (List.last (TAAbs ListSeqAbs s))"
apply (unfold lastseq_def)
apply (subst apply_single)
apply (rule refl)
done

lemma head_TypeAbs: "(head  s) = (hd(TAAbs ListSeqAbs s))"
apply (unfold headseq_def)
apply (subst apply_single)
apply (rule refl)
done

lemma front_TypeAbs: "(front s) = (TARep ListSeqAbs (butlast(TAAbs ListSeqAbs s)))"
apply (unfold frontseq_def)
apply (subst apply_single)
apply (rule refl)
done

lemma tail_TypeAbs: "(tail s) = (TARep ListSeqAbs (tl(TAAbs ListSeqAbs s)))"
apply (unfold tailseq_def)
apply (subst apply_single)
apply (rule refl)
done

lemma filtering_TypeAbs: "(filtering%^(s,V)) =  TARep ListSeqAbs (filter (% a. a : V) (TAAbs ListSeqAbs s))"
apply (unfold filtering_def)
apply (subst apply_single_tuple)
apply (rule refl)
done

lemma sizeseq_TypeAbs_seq: "s:seq X ==> (# s)  = int (length (TAAbs ListSeqAbs s))"
apply (drule seq_seqtype)
apply (subgoal_tac "ALL l. l = (TAAbs ListSeqAbs s) --> (# s) = int (length l) ")
apply simp
apply (rule allI)
apply (rule mp)
prefer 2 
apply (assumption)
apply (rule_tac x = "s" in spec)
apply (induct_tac "l")
apply (rule allI)
apply (rule impI)
apply (simp add: TAAbs_LSAbs_emptyseq [THEN sym] TARep_LSAbs_Nil TAAbs_iff_inj_onto seqtype_lemma)
apply (rule allI)
apply (rule impI)
apply (rule_tac x1 = "a # list" in TARep_iff_inj [THEN subst])
apply (rule ListSeqAbsIsTypeabs)
apply (subst TARep_inverse)
apply (simp (no_asm))
apply (simp add: seqtype_lemma)
apply (simp add: TARep_LSAbs_Cons)
apply (rule impI)
apply (rotate_tac -1)
apply (drule sym)
apply (simp add: seqtype_lemma)
apply (rule_tac X1 = "UNIV" in size_insert_seq [THEN ssubst])
apply (fold seqtype_def)
apply (simp add: seqtype_lemma)
apply (simp (no_asm))
apply (erule_tac x = "TARep ListSeqAbs list" in allE)
apply auto
apply (rotate_tac 2)
apply (drule sym)
apply auto
apply (rotate_tac 2)
apply (unfold zsuc_def)
apply (simp add: ring_eq_simps)
done

lemma sizeseq_TypeAbs: "!!s. s: TASet ListSeqAbs ==> (# s)  = int (length (TAAbs ListSeqAbs s))"
apply (simp add: seqtype_lemma [symmetric] seqtype_def)
apply (subst sizeseq_TypeAbs_seq) 
apply auto
done

lemma insertseq_TypeAbs: "!!s. t:TASet ListSeqAbs ==>  insertseq x t = TARep ListSeqAbs (x # (TAAbs ListSeqAbs t))"
apply (subst TARep_LSAbs_Cons)
apply (simp (no_asm_simp))
done


lemma ran_mem_TypeAbs_seq: "s:seq X ==> a : (ran s) = (a mem (TAAbs ListSeqAbs s))"
apply (drule seq_seqtype)
apply (subgoal_tac "ALL l. l = (TAAbs ListSeqAbs s) --> a : (ran s) = (a mem l) ")
apply simp
apply (rule allI)
apply (rule mp)
prefer 2 
apply (assumption)
apply (rule_tac x = "s" in spec)
apply (induct_tac "l")
apply (rule allI)
apply (rule impI)
apply (rule impI)
apply (simp (no_asm))
apply (simp add: TAAbs_LSAbs_emptyseq [symmetric] TARep_LSAbs_Nil TAAbs_iff_inj_onto seqtype_lemma)
apply (rotate_tac -1)
apply (rule allI)
apply (rule impI)
apply (rule_tac x1 = "aa # list" in TARep_iff_inj [THEN subst])
apply (rule ListSeqAbsIsTypeabs)
apply (subst TARep_inverse)
apply (simp add: seqtype_lemma)
apply (simp add: seqtype_lemma)
apply (rule impI)
apply (rotate_tac -1)
apply (drule sym)
apply (simp (no_asm_simp))
apply (simp add: TARep_LSAbs_Cons)(*
apply (simp (no_asm))*)
apply (erule_tac x = "TARep ListSeqAbs list" in allE)
apply (case_tac "aa = a")
apply (simp (no_asm_simp))
apply auto
apply (simp add: seqtype_lemma)
apply (simp add: seqtype_lemma)
done

lemma ran_mem_TypeAbs:"s: TASet ListSeqAbs ==> a : (ran s) = (a mem (TAAbs ListSeqAbs s))"
apply (simp add: seqtype_lemma [symmetric] seqtype_def)
apply (erule ran_mem_TypeAbs_seq)
done

(* -------------------------------------------------------- *)
(*     Taktiken zum Ueberfuehren von Seq-Theoremen zu       *)
(*                   Listen-Theoremen                       *)    
(* -------------------------------------------------------- *)

ML
{*
(*from contrib*)
val concatseq_TypeAbs = thm "concatseq_TypeAbs"
val revseqseq_TypeAbs = thm "revseqseq_TypeAbs"
val sizeseq_TypeAbs = thm "sizeseq_TypeAbs"
val TARep_in_TASet = thm "TARep_in_TASet"

val holempty_ss = HOL_basic_ss

val TypeAbs_Op_ss = holempty_ss addsimps [concatseq_TypeAbs,
                    revseqseq_TypeAbs,sizeseq_TypeAbs, thm "ListSeqAbsIsTypeabs",
                    TARep_in_TASet,thm "last_TypeAbs",thm "head_TypeAbs",
                    thm "front_TypeAbs", thm "tail_TypeAbs",thm "filtering_TypeAbs",
                    thm "insertseq_TypeAbs", thm "ran_mem_TypeAbs"]

val TypeAbs_Const_ss = holempty_ss addsimps [thm "TARep_LSAbs_Nil" RS sym]

val TypeAbs_norm_ss = holempty_ss addsimps [thm "seqtype_lemma"]
*}

ML
{*
fun seq_type t = 
    let val typ = (snd t)
    fun typ_test (Type("set",[(Type("*",[(Type("int",[])),_]))])) = true
     |  typ_test (_) = false
    in
        typ_test (typ)
    end
 *}
ML 
{*   
fun rep_abs_op t = 
    let val operator = (fst t)
    fun op_test (("TAAbs",_),("ListSeqAbs",_)) = false
      | op_test (_) = true
    in
        (op_test(operator))
    end
*}


ML
{*
val TARep_inverse = thm "TARep_inverse"
val ListSeqAbsIsTypeabs = thm "ListSeqAbsIsTypeabs"
val TARep_iff_inj = thm "TARep_iff_inj"
val seq_seqtype = thm "seq_seqtype"


fun find_var_tac t = 
  let fun const_var (Abs _) = []
        | const_var ((Const a)$(Const b)$(Free f)) = [((a,b),f)]
        | const_var (Const _) = []
        | const_var (Var _) = []
        | const_var (Bound _) = []
        | const_var (Free _) = []
        | const_var (t1$t2) = (const_var t1) union (const_var t2)
      fun single_var (Abs _) = []
        | single_var ((Const a)$(Const b)$(Free f)) = []
        | single_var (Const _) = []
        | single_var (Var _) = []
        | single_var (Bound _) = []
        | single_var (Free f) = [f]
        | single_var (t1$t2) = (single_var t1) union (single_var t2)
      val v = (const_var t)
      val f = (single_var t)
      val f_seq = (filter seq_type f)
      val v_abs = (map snd (filter rep_abs_op v))
  in 
      f_seq union v_abs
  end

fun make_tac i t = 
          (TRY (EVERY [(res_inst_tac [("t",fst t)] 
                     (TARep_inverse RS sym RS ssubst)i),
                     (rtac ListSeqAbsIsTypeabs i), 
                     (Asm_full_simp_tac i)]))

*}

(* taken from ROOT.ML *)
ML
{*
fun STATE tacfun st = tacfun st st;

fun getgoal_new top i =
      (case  Library.drop (i-1, prems_of top) of
            [] => error"getgoal: Goal number out of range"
          | Q::_ => Q);

fun goal_params_new top i =
  let val gi = getgoal_new top i
      val frees = map Free (Logic.strip_params gi)
  in (gi,frees) end;

fun concl_of_goal_new top i = 
  let val (gi,frees) = goal_params_new top i
      val B = Logic.strip_assums_concl gi
  in subst_bounds(frees,B) end;
*}

ML 
{*
fun var_replace_tac i = (STATE (fn top => 
         let val list = (find_var_tac (concl_of_goal_new (topthm()) i))
             val tactic_list = (map (make_tac i) list)
          in
          if (list = []) then no_tac
          else 
              EVERY tactic_list
          end))
*}

ML
{*
fun TARep_inj_tac i = EVERY [(stac TARep_iff_inj i),
                             (rtac ListSeqAbsIsTypeabs i)]
               
fun seq_to_list_tac  i = (EVERY [(asm_full_simp_tac TypeAbs_Op_ss i),
                                 (asm_full_simp_tac TypeAbs_Const_ss i),
                                 TRY (var_replace_tac i),
                                 TRY (TARep_inj_tac i)])

fun seq_norm i = EVERY [ (rtac impI i),
                         (rotate_tac ~1 1),
                         (dmatch_tac [seq_seqtype] i)]


fun seq_to_list_auto_tac i =
                 EVERY [REPEAT (seq_norm i),
                        (asm_full_simp_tac TypeAbs_norm_ss i),
                        (seq_to_list_tac i),
                        (Simp_tac i)]


*}
(*
ML
{*
find_var_tac (thm "concl_of_goal" (topthm()) 1)
*}*)


(* -------------------------------------------------------- *)
(*               Beispiele fuer concatseq                   *)
(* -------------------------------------------------------- *)


lemma concatseq_assoc: "s %&^ t %&^ u = s %&^ (t %&^ u)"
apply (tactic {*seq_to_list_auto_tac 1*})
apply auto
done

lemma concatseq_emptyseq[rule_format] : "s :seq X --> %<%> %&^ s = s"
apply (tactic {*seq_to_list_auto_tac 1*})
apply auto
done

lemma concatseq_emptyseq2[rule_format]: "s :seq X --> s %&^ %<%> = s"
apply (tactic {*seq_to_list_auto_tac 1*})
apply auto
done

lemma concatseq_is_empty[rule_format]:
"s : seq X --> t : seq Y -->  
  (s %&^ t = %<%>) = (s = %<%> & t = %<%>)"
apply (tactic {*seq_to_list_auto_tac 1*})
apply (rule iffI)
apply (erule conjE)
apply (rule_tac t = "[]" in subst)
back
apply assumption
back
apply (rule_tac t = "[]" in subst)
apply assumption
apply (subst TARep_inverse)
prefer 3
apply (subst TARep_inverse)
apply simp_all
done


lemma same_concatseq_eq[rule_format] :
 "s : seq X --> t : seq Y --> u: seq Z --> (s %&^ t = s %&^ u) = (t = u)"
apply (tactic {*seq_to_list_auto_tac 1*})
apply (rule iffI)
apply (tactic {*asm_full_simp_tac (HOL_ss addsimps [thm "Abs_seqtype_lemma" RS sym, thm "Abs_seqtype_def"]) 1*})
apply (subgoal_tac "Rep_seqtype (Abs_seqtype u) = u")
apply (tactic {*asm_full_simp_tac (HOL_ss addsimps [thm "Abs_seqtype_lemma" RS sym,  thm "Abs_seqtype_def"]) 1*})
apply (subgoal_tac "Rep_seqtype (Abs_seqtype t) = t")
apply (tactic {*asm_full_simp_tac (HOL_ss addsimps [thm "Abs_seqtype_lemma" RS sym, thm "Abs_seqtype_def"]) 1*})
apply (rule Abs_seqtype_inverse)
apply (subst seqtype_lemma)
apply assumption
apply (rule Abs_seqtype_inverse)
apply (subst seqtype_lemma)
apply assumption
apply simp
done

declare concatseq_emptyseq [simp] concatseq_emptyseq2 [simp] concatseq_is_empty [simp] (*same_concatseq_eq[simp]*)


(* -------------------------------------------------------- *)
(*               Beispiele fuer revseq                      *)
(* -------------------------------------------------------- *)


lemma revseq_revseq_ident[rule_format] : "s : seq X --> (revseq (revseq s)) = s"
apply (tactic {*seq_to_list_auto_tac 1*})
apply auto
done

lemma revseq_concatseq[rule_format]: "s:seq X --> t:seq Y -->  
     (revseq (s %&^ t)) = ((revseq t) %&^ (revseq s))"
apply (tactic {*seq_to_list_auto_tac 1*})
apply auto
done

(* -------------------------------------------------------- *)
(*               Beispiele fuer size                        *)
(* -------------------------------------------------------- *)

lemma size_revseq[rule_format]: "s : seq X --> #(revseq s) = #s"
apply (tactic {*seq_to_list_auto_tac 1*})
apply auto
done

(*
lemma size_concatseq[rule_format] : "s : seq X --> t : seq Y --> #(s %&^ t) = #s + #t"
apply (tactic {*seq_to_list_auto_tac 1*})
apply simp
done
*)


(* -------------------------------------------------------- *)
(*               Beispiele fuer last                        *)
(* -------------------------------------------------------- *)

lemma last_cons[rule_format] : 
"t : seq X -->  
 (last (insertseq x (insertseq y t))) = (last (insertseq y t))"
apply (tactic {*seq_to_list_auto_tac 1*})
apply auto
done


lemma last_concatseq[rule_format] : 
"t : seq X --> s : seq Y -->  
 (last (s %&^ (insertseq y t))) = (last (insertseq y t))"
apply (tactic {*seq_to_list_auto_tac 1*})
apply auto
done


lemma laSt_single: "(last (insertseq x %<%>)) = x"
apply (tactic {*seq_to_list_auto_tac 1*})
apply (tactic {*seq_to_list_auto_tac 1*})
apply auto
done

(* -------------------------------------------------------- *)
(*               Beispiel fuer front                        *)
(* -------------------------------------------------------- *)

lemma front_mt: "front(%<%>) = %<%> "
apply (tactic {*seq_to_list_auto_tac 1*})
apply auto
done


lemma aux: 
"(x : seq Z & y : Z) --> front(x %&^ %< y %>) = x "
apply (tactic {*seq_to_list_auto_tac 1*})
apply (subst insertseq_TypeAbs)
apply (tactic {*seq_to_list_auto_tac 1*})
apply (rule impI)
apply (simp add: TARep_inverse)
apply (simp (no_asm_simp) add: ListSeqAbs_def seqtype_def)
apply (rule Abs_seqtype_inverse)
apply (unfold seqtype_def)
apply auto
done

lemma front_snoc: 
"!!x . [| x : seq Z; y : Z |] ==> front(x %&^ %< y %>) = x "
apply (cut_tac aux)
apply auto
done

declare front_mt [simp] front_snoc [simp]

(* todo: insert butlast_append retten ... *)



(* -------------------------------------------------------- *)
(*               Beispiel fuer head                         *)
(* -------------------------------------------------------- *)

(*
lemma head_concatseq[rule_format] : "s : seq X --> t : seq Y --> (head (s %&^ t)) =  
                (if s = %<%> then (head t) else (head s))"
apply (tactic {*seq_to_list_auto_tac 1*})
apply auto
done*)


(* -------------------------------------------------------- *)
(*                  Beispiele fuer mem                      *)
(* -------------------------------------------------------- *)
(*
lemma mem_concatseq[rule_format]: "s : seq X --> t : seq Y -->  
 x : (ran(s %&^ t)) = (x: (ran s) | x : (ran t))"
apply (tactic {*seq_to_list_auto_tac 1*});
apply auto
done
*)
(*
lemma mem_filtering[rule_format]:  "s : seq X --> x : (ran(s %|` V)) = (x: (ran s) & (x : V))"
apply (tactic {*seq_to_list_auto_tac 1*})
apply auto
*)

lemma TAAbs_LSA: "TAAbs ListSeqAbs = (%u. @ x. (TARep ListSeqAbs) x = u)"
apply (subst Rep_seqtype_lemma [symmetric])
apply (subst Abs_seqtype_lemma [symmetric])
apply (unfold Abs_seqtype_def)
apply (rule refl)
done

lemma TASet_LSA:  "TASet ListSeqAbs = seq UNIV"
apply (subst seqtype_lemma [symmetric])
apply (unfold seqtype_def)
apply (rule refl)
done

lemma TARep_in_seqUNIV: "TARep ListSeqAbs l : seq UNIV"
apply (subst TASet_LSA [symmetric])
apply (rule TARep_in_TASet)
apply auto
done


lemma TAAbs_LSA_cons: "(x#xs) = TAAbs ListSeqAbs (insertseq x (TARep ListSeqAbs xs))"
apply (rule_tac x1 = "x # xs" in TARep_iff_inj [THEN subst])
apply (rule ListSeqAbsIsTypeabs)
apply (subst TARep_inverse)
apply (rule ListSeqAbsIsTypeabs)
apply (subst TASet_LSA)
apply (rule insertseq_seq_pred)
apply (subst TASet_LSA [symmetric])
apply (simp (no_asm))
apply (simp (no_asm))
apply (subst TARep_LSAbs_Cons)
apply (rule refl)
done



lemma insertseq_concat: "a:X --> s :seq X --> t :seq X -->  
  (insertseq a s) %&^ t = insertseq a (s %&^ t)"
apply (tactic {*seq_to_list_auto_tac 1*})
apply auto
apply (subst insertseq_TypeAbs)
apply auto
apply (subst TASet_LSA)
apply auto
done
declare insertseq_concat [simp]


lemma concatseq_closed: 
"!!a. [|a : seq G; b : seq G|] ==> (a %&^ b) : seq G"
apply (erule_tac s = "a" in seq_induct)
apply simp
apply auto
done
declare concatseq_closed [simp]

lemma snoc_closed: 
"!!a. [|s : seq G; b : G|] ==> (s %&^ %<b%>) : seq G"
apply (rule concatseq_closed)
apply auto
done
declare snoc_closed [simp]

(* -------------------------------------------------------- *)
(*         Alternative Cases und Induktionen:snoc           *)
(* -------------------------------------------------------- *)

declare seq_card_dom [simp]

lemma aux: "(int m < int n) = (m < n)"
apply (simp add: ring_eq_simps)
done

(*
lemma snow_wf_lem: " snoc_rel A <= measure (% x. zint(zsize(dom x)))"
apply (unfold measure_def inv_image_def zsuc_def snoc_rel_def)
apply auto
sorry*)



lemmas snoc_wf =  snoc_wf_lem [THEN wf_measure [THEN wf_subset]] (*|> standard*)



lemma snocE_lem: 
"!! s. s: seq A  
   ==> (? t : seq A. ? a:A. s = t %&^ %<a%> ) | s = %<%> "
apply (erule_tac s = "s" in seq_induct)
apply auto
apply (rule_tac x = "insertseq a t" in bexI)
apply (rule_tac x = "aa" in bexI)
apply (rule_tac [4] x = "%<%>" in bexI)
apply (rule_tac [4] x = "a" in bexI)
prefer 4
apply (subst concatseq_emptyseq)
apply (rule insertseq_seq_pred)
apply auto
done


lemma seqsnoc_cases:
assumes p1: "s:seq A"  
assumes p2: "s = %<%> ==> P s"  
assumes p3: "!!a s'. \<lbrakk> s' : seq A; a:A; s = s' %&^ %< a %> \<rbrakk> \<Longrightarrow> P s"  
shows  "P s"
apply (rule p1 [THEN snocE_lem [THEN disjE]])
prefer 2
apply (erule p2)
apply (erule bexE)
apply (erule bexE)
apply (erule p3)
apply assumption+
done

lemma seq_snocinduct:
assumes p1: "s:seq A"
assumes p2: "P %<%>"
assumes p3: "!! a s. [| s : seq A; a:A; P s|] ==> P(s %&^ %< a %>)"
shows "P s"
apply (rule p1 [THEN rev_mp])
apply (rule snoc_wf [THEN wf_induct])
apply (rule impI)
apply (erule seqsnoc_cases)
apply (auto intro!: p2 p3 simp add: snoc_rel_def)
done



declare snoc_neq_empty [simp] snoc_neq_empty [THEN not_sym, simp]


lemma snoc_case_mt: "snoc_case A a f %<%> = a"
apply (unfold snoc_case_def)
apply (rule some_equality)
apply (simp (no_asm_simp))
apply auto
done


lemma snoc_case_conc: 
"!!s. [| s: seq A; x : A |] ==> snoc_case A a f (s %&^ %< x %>) = f x s"
apply (unfold snoc_case_def)
apply (rule some_equality)
apply (auto dest: snoc_inj1 snoc_inj2)
done

declare snoc_case_mt [simp] snoc_case_conc [simp]


lemma front_closed: 
"!!a. [|a : seq G|] ==> front(a) : seq G"
apply (erule_tac s = "a" in seq_snocinduct)
apply auto
done
declare front_closed [simp]

end
