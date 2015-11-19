(*******************************************************************************

  module: TemporalLogic.thy
  
  linear-time temporal logic with past operators

  ID:     $Id: TemporalLogic.thy 12194 2004-10-25 20:20:15Z csprenge $
  author: Christoph Sprenger

*******************************************************************************)

header {* Temporal Logic *}

theory TemporalLogic = TransitionSystems :

text {* Define a linear-time temporal logic language with past operators. *}


subsection {* Syntax *}

types
  's pred = "'s set"

datatype 's ltl =
    Pred "'s pred"
  | Neg "'s ltl"
  | Conj "'s ltl" "'s ltl"      (infixl "And" 60) 
  | Next "'s ltl"               ("(++)")
  | Prev "'s ltl"               ("(--)")
  | Until "'s ltl" "'s ltl"     (infixr "U+" 65) 
  | Since "'s ltl" "'s ltl"     (infixr "S-" 65) 


subsection {* Semantics *}

consts  
  sat  :: "['s run, nat, 's ltl] => bool"

primrec
  "sat r i (Pred p)    = ((r i) : p)"
  "sat r i (Neg f)     = (~(sat r i f))"
  "sat r i (Conj f g)  = ((sat r i f) & (sat r i g))"
  "sat r i (Next f)    = (sat r (i + 1) f)"
  "sat r i (Prev f)    = ((0 < i) & (sat r (i - 1) f))"
  "sat r i (Until f g) = (EX k: {i..}. (sat r k g) & 
                                       (ALL j: {i..k(}. (sat r j f)))"
  "sat r i (Since f g) = (EX k: {..i}. (sat r k g) & 
                                       (ALL j: {)k..i}. (sat r j f)))"

constdefs
  Sat  :: "['s trsys, 's ltl] => bool"
  "Sat T f == ALL r: runs T. sat r 0 f"

syntax   
  "@validS" :: "['s, bool] => bool"      ("(1_) |= (1_)" 50)

translations
  "T |= f" == "Sat T f"


subsection {* Equivalence and congruence *}

constdefs 
  Equiv :: "['s ltl, 's ltl] => bool"            (infixr "=~=" 50)
  "Equiv f g == ALL T. (T |= f) = (T |= g)"

lemma Equiv_refl [simp]: "f =~= f"
by (simp add: Equiv_def)

lemma Equiv_sym: "f =~= g ==> g =~= f"
by (simp add: Equiv_def)

lemma Equiv_trans: "[| f =~= g; g =~= h |] ==> f =~= h"
by (simp add: Equiv_def)


constdefs 
  Congr :: "['s ltl, 's ltl] => bool"            (infixr "=~~=" 50)
  "Congr f g == ALL T. ALL r: runs T. ALL i. (sat r i f) = (sat r i g)"

lemma Congr_impl_Equiv: "f =~~= g ==> f =~= g"
by (simp add: Congr_def Equiv_def Sat_def)

lemma Congr_refl [simp]: "f =~~= f"
by (simp add: Congr_def)

lemma Congr_sym: "f =~~= g ==> g =~~= f"
by (simp add: Congr_def)

lemma Congr_trans: "[| f =~~= g; g =~~= h |] ==> f =~~= h"
by (simp add: Congr_def)


lemma Neg_congr: "f =~~= g ==> Neg f =~~= Neg g"
and Conj_congr: "[| f =~~= f'; g =~~= g' |] ==> f And g =~~= f' And g'"
and Next_congr: "f =~~= g ==> (++) f =~~= (++) g"
and Prev_congr: "f =~~= g ==> (--) f =~~= (--) g"
and Until_congr: "[| f =~~= f'; g =~~= g' |] ==> f U+ g =~~= f' U+ g'"
and Since_congr: "[| f =~~= f'; g =~~= g' |] ==> f S- g =~~= f' S- g'"
by (auto simp add: Congr_def)

lemmas ltl_congruences = 
  Neg_congr Conj_congr Next_congr Prev_congr Until_congr Since_congr


consts ltl_context :: "('s ltl => 's ltl) set"

inductive ltl_context
intros
  c_hole: "(%f. f) : ltl_context"
  c_form: "(%f. g) : ltl_context"
  c_neg: "C: ltl_context ==> (%f. Neg (C f)): ltl_context"
  c_conj: "[| C1: ltl_context; C2: ltl_context |] 
           ==> (%f. (C1 f) And (C2 f)) : ltl_context"
  c_next: "C: ltl_context ==> (%f. (++) (C f)): ltl_context"
  c_prev: "C: ltl_context ==> (%f. (--)(C f)): ltl_context"
  c_until: "[| C1: ltl_context; C2: ltl_context |] 
           ==> (%f. (C1 f) U+ (C2 f)) : ltl_context"
  c_since: "[| C1: ltl_context; C2: ltl_context |]
           ==> (%f. (C1 f) S- (C2 f)) : ltl_context"
  
lemma Congr_congr: "[| C: ltl_context; f =~~= g |] ==> (C f) =~~= (C g)"
apply (induct C rule: ltl_context.induct)
apply (auto intro: ltl_congruences)
done


subsubsection {* Substitution rules *}

lemma Equiv_Sat_subst: "[| f =~= g; T |= f |] ==> T |= g"
by (simp add: Equiv_def) 

lemma Congr_sat_subst: 
  "[| f =~~= g; C: ltl_context; sat r i (C f) |] ==> sat r i (C g)"
apply (subgoal_tac "EX T. r: runs T",  clarify)
apply (subgoal_tac "(C f) =~~= (C g)", simp add: Congr_def)
apply (auto intro: Congr_congr run_reflection)
done

lemma Congr_Sat_subst: 
  "[| f =~~= g; C: ltl_context; T |= (C f) |] ==> (T |= (C g))"
by (simp add: Sat_def, force elim: Congr_sat_subst)



subsection {* Derived operators *}

subsubsection {* Boolean operators *}

constdefs  
  TT :: "'s ltl"
  "TT == Pred UNIV"

  FF :: "'s ltl"
  "FF == Pred {}"

  Disj :: "['a ltl, 'a ltl] => 'a ltl"           (infixl "Or" 55) 
  "Disj f g == Neg (Conj (Neg f) (Neg g))" 

  Impl :: "['a ltl, 'a ltl] => 'a ltl"           (infixr "=->" 50)
  "Impl f g == Disj (Neg f) g"

lemmas boolean_op_defs = TT_def FF_def Disj_def Impl_def

lemma sat_TT [simp]: "sat r i TT"
and sat_FF [simp]: "~(sat r i FF)"
and sat_Disj [simp]: "(sat r i (f Or g)) = ((sat r i f) | (sat r i g))"
and sat_Impl [simp]: "(sat r i (f =-> g)) = ((sat r i f) --> (sat r i g))"
by (auto simp add: boolean_op_defs) 


subsubsection {* Future temporal operators *}

constdefs
  Release :: "['s ltl, 's ltl] => 's ltl"         (infixr "V+" 65)
  "f V+ g == Neg ((Neg f) U+ (Neg g))"

  Eventually :: "'a ltl => 'a ltl"               ("<++>")  
  "<++> f == TT U+ f"

  Always   :: "'a ltl => 'a ltl"                 ("[++]")
  "[++] f == FF V+ f"

  Unless :: "['s ltl, 's ltl] => 's ltl"         (infixr "W+" 65)
  "f W+ g == [++]f Or (f U+ g)"

lemmas future_op_defs = Release_def Always_def Eventually_def Unless_def

lemma sat_Always: "(sat r i ([++]f)) = (ALL j: {i..}. (sat r j f))"
and sat_Eventually: "(sat r i (<++>f)) = (EX j: {i..}. (sat r j f))"
by (auto simp add: future_op_defs)


subsubsection {* Past temporal operators *}

constdefs
  Before :: "'s ltl => 's ltl"                   ("(-?)")
  "(-?) f == Neg ((--) (Neg f))"

  Once :: "'s ltl => 's ltl"                     ("<-->")
  "<--> f == TT S- f"

  Sofar :: "'s ltl => 's ltl"                    ("[--]")
  "[--] f == Neg (<-->(Neg f))"

  Backto :: "['s ltl, 's ltl] => 's ltl"         (infixr "B-" 65)
  "f B- g == Neg ((Neg f) S- (Neg (f And g)))"   (* BULLSHIT? *)

lemmas past_op_defs = Before_def Backto_def Sofar_def Once_def
lemmas derived_op_defs = boolean_op_defs future_op_defs past_op_defs

lemma sat_Before: "(sat r i ((-?)f)) = ((i = 0) | (sat r (i - 1) f))"
and sat_Once: "(sat r i (<-->f)) = (EX j: {..i}. (sat r j f))"
and  sat_Sofar: "(sat r i ([--]f)) = (ALL j: {..i}. (sat r j f))"
by (auto simp add: past_op_defs)

lemmas sat_derived =
  sat_Always sat_Eventually sat_Before sat_Once sat_Sofar


subsection {* Properties *}

text {* Some basic properties of the boolean and temporal operators. *}

subsubsection {* Properties of boolean operators *}

lemma Neg_Neg: "Neg (Neg p) =~~= p"
by (simp add: Congr_def Sat_def)

lemma Neg_Pred: "Neg (Pred P) =~~= Pred (- P)"
by (simp add: Congr_def Sat_def)


subsubsection {* Duality *}

lemma Next_self_dual: "(++) f =~~= Neg ((++) (Neg f))"
by (simp add: Congr_def Sat_def)

lemma Always_Eventually_dual: "[++] f =~~= Neg (<++> (Neg f))"
by (simp add: Congr_def Sat_def future_op_defs boolean_op_defs)

lemma Eventually_Always_dual: "<++> f =~~= Neg ([++] (Neg f))"
by (simp add: Congr_def Sat_def future_op_defs boolean_op_defs)


subsubsection {* Unfolding *}

text {* Fixed point characterisations of temporal operators. *}

lemma Until_unfold: "f U+ g =~~= g Or (f And ((++) (f U+ g)))"
apply (simp add: Congr_def, clarify, rule iffI)
  apply (clarify, case_tac "i = k", simp, force)

  apply (safe, force) 
  apply (rule_tac x=k in bexI, safe)
  apply (case_tac "i = j", auto) 
done

lemma Since_unfold: "f S- g =~~= g Or (f And ((--) (f S- g)))"
apply (simp add: Congr_def, clarify, rule iffI)
  apply (elim bexE conjE, simp)
  apply (case_tac "k = i", simp) 
  apply (intro disjI2 conjI, force, arith) 
  apply (rule_tac x=k in bexI, auto)
  apply (drule_tac x=j in bspec, simp_all, arith, arith)  
  apply (rule_tac x=k in bexI, safe)
  apply (case_tac "j = i", safe)
  apply (drule_tac x=j in bspec, simp_all, arith+)
done



subsubsection {* Other characterisations *}

(* Original proof under 2004 by Christoph :
lemma causality_as_precedence: 
  "[++] (p =-> (<--> q)) =~= (Neg p) W+ q"
apply (simp add: Equiv_def Sat_def derived_op_defs, rule)
apply (rule sym, rule iffI, force)
apply (rule ballI, case_tac "ALL i. ~(sat r i p)", simp_all)
apply (rule disjI2, erule exE)
apply (subgoal_tac 
         "ALL i. (sat r i p) --> 
           (EX k:{..i}. (sat r k q) & (ALL j: {..k(}. ~(sat r j p)))", 
       force)
apply (rule allI, rule less_induct, clarify)
apply (drule_tac x=r in bspec, simp)
apply (case_tac "ALL i:{..n(}. ~(sat r i p)", simp_all) 
  apply (drule_tac x=n in spec, simp, clarify)
  apply (rule_tac x=k in bexI, rule, simp_all, force)

  apply (clarify, atomize)                              -- {* how w/o atomize? *}
  apply (drule_tac x=ia in spec, simp, clarify) 
  apply (rule_tac x=k in bexI, auto)
done

*)

lemma causality_as_precedence: 
  "[++] (p =-> (<--> q)) =~= (Neg p) W+ q"
apply (simp add: Equiv_def Sat_def derived_op_defs, rule)
apply (rule sym, rule iffI, force)
apply (rule ballI, case_tac "ALL i. ~(sat r i p)", simp_all)
apply (rule disjI2, erule exE)
apply (subgoal_tac 
         "ALL i. (sat r i p) --> 
           (EX k:{..i}. (sat r k q) & (ALL j: {..<k}. ~(sat r j p)))", 
       force)
apply (rule allI, rule less_induct, clarify)
apply (drule_tac x=r in bspec, simp)
apply (case_tac "ALL i:{..<n}. ~(sat r i p)", simp_all) 
  apply (drule_tac x=n in spec, simp, clarify, atomize)
  apply (rule_tac x=k in bexI, rule, simp_all,clarify)

  apply (drule_tac x=ia in spec, simp, safe) 
  
sorry
(* Do not restore proof since bu's proof available *)



lemma precedence_as_causality: "p W+ q =~= [++](p Or (<--> q))"
apply (rule_tac g="[++]((Neg p) =-> (<--> q))" in Equiv_trans, rule Equiv_sym)
apply (rule_tac g="(Neg (Neg p)) W+ q" in Equiv_trans)
  apply (rule causality_as_precedence)

  apply (rule Congr_impl_Equiv)
  apply (rule_tac C="%p. p W+ q" in Congr_congr, 
         simp add: derived_op_defs, intro ltl_context.intros)
  apply (rule Neg_Neg)

  apply (unfold Impl_def, rule Congr_impl_Equiv)
  apply (rule_tac C="%p. [++](p Or <--> q)" in Congr_congr, 
         simp add: derived_op_defs, intro ltl_context.intros)
  apply (rule Neg_Neg)
done

end
