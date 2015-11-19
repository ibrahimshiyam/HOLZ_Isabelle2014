(*******************************************************************************

  module: CryptoLib/TemporalRules.thy
  
  temporal logic proof rules

  ID:     $Id: TemporalRules.thy 12417 2004-10-29 15:38:52Z csprenge $
  author: Christoph Sprenger

*******************************************************************************)

header {* Temporal Logic Proof Rules *}

theory TemporalRules = TemporalLogic :

text {* This theory provides proof rules that reduce temporal reasoning to
reasoning about assertions and Hoare triples. *}


subsection {* Hoare triples *}

constdefs
  HoareTr :: "['s pred, ('s * 's) set, 's pred] => bool"   
             ("(3{|_|} _ {|_|})" [0, 0, 0] 90)
  "{| P |} tran {| Q |} == tran `` P <= Q"


text {* The following lemma is just a reality check. *}

lemma HoareTr_semantics: 
  "{| P |} tran {| Q |} = (ALL s t. s: P & (s,t): tran --> t: Q)"
by (auto simp add: HoareTr_def)


subsection {* Invariance rules *}

text {* A monotonicity rule for invariants. *}

lemma inv_impl: 
  "[| P <= Q; T |= [++](Pred P) |] ==> (T |= [++](Pred Q))" 
by (auto simp add: Sat_def sat_Always)

lemma inv_conj: 
  "[| T |= [++](Pred P); T |= [++](Pred Q) |] ==> (T |= [++](Pred (P Int Q)))" 
by (auto simp add: Sat_def sat_Always)


text {* The general invariance rule. *}

lemma inv_rule: 
  "[| (init T) <= I; I <= P; {| I |} (trans T) {| I |} |] 
  ==> (T |= [++](Pred P))"
apply (erule_tac inv_impl)
apply (simp add: Sat_def sat_Always HoareTr_def run_defs, safe)
apply (induct_tac j, auto)
done


text {* The incremental invariance rule allows us to use already established
invariants in the proof of a new invariant. *}

lemma incr_inv_rule: 
  "[| T |= [++](Pred J); 
      (init T) <= I; I Int J <= P; 
      {| I Int J |} (trans T) {| I |} 
   |] ==> (T |= [++](Pred P))"
apply (erule_tac inv_impl, rule inv_conj, simp_all)
apply (simp add: Sat_def sat_Always HoareTr_def, safe)
apply (drule_tac x=r in bspec, auto simp add: run_defs)
apply (induct_tac j, auto)
apply (drule_tac x=n in spec, force)
done


subsection {* Precedence rules *}

lemma precedence_rule:
  "[| (init T) <= I; I <= P; {| I |} (trans T) {| I Un Q |} |] 
  ==> (T |= (Pred P) W+ (Pred Q))"
apply (simp add: Sat_def Unless_def sat_derived HoareTr_def runs_def is_run_def, safe)
apply (subgoal_tac "r j : I", auto)
apply (rule less_induct, case_tac n, auto)
apply (rename_tac r l, drule_tac x=l in spec)
apply (case_tac "r (Suc l) : Q", force)
apply (subgoal_tac "r l : I", blast, force)
done


subsection {* Causality rules *}

lemma causality_trans: 
  "[| T |= [++](p =-> <-->q); T |= [++](q =-> <-->r) |] 
  ==> (T |= [++](p =-> <-->r))"
by (force simp add: Sat_def sat_derived)


lemma causality_rule:
  "[| (init T) <= I; I <= - P; {| I |} (trans T) {| I Un Q |} |] 
  ==> (T |= [++]((Pred P) =-> <-->(Pred Q)))"
apply (simp add: causality_as_precedence [unfolded Equiv_def])
apply (rule Congr_Sat_subst [OF Neg_Pred [THEN Congr_sym]])
  apply (simp add: derived_op_defs, intro ltl_context.intros)

  apply (fast elim: precedence_rule)
done


end
