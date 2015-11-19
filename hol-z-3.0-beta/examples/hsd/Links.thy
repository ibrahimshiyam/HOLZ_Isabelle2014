(*****************************************************************************
 *          HOL-TestGen - specification based test case generation
 *                                                                            
 * squareroot_test.thy - 
 * Copyright (C) 2005 Achim D. Brucker <brucker@inf.ethz.ch>   
 *                    Burkhart Wolff   <bwolff@inf.ethz.ch>    
 *                                                                            
 * This file is part of HOL-TestGen.              
 *                                                                            
 * HOL-TestGen is free software; you can redistribute it and/or modify it 
 * under   
 * the terms of the GNU General Public License as published by the Free       
 * Software Foundation; either version 2 of the License, or (at your option)  
 * any later version.                                                         
 *                                                                           
 * HOL-TestGen is distributed in the hope that it will be useful, but WITHOUT 
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for 
 * more details.                                                              
 *                                                                            
 * You should have received a copy of the GNU General Public License along    
 * with this program; if not, write to the Free Software Foundation, Inc.,    
 * 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.                  
 ******************************************************************************)
(*
ML {* add_path "/home/wolff/infsec/projects/IBM-ZISC/Isabelle/CryptoLib"; *} 
*)
theory Links = TemporalRules:

section{* Proving Equivalence from HSD_1b to Temporal Representation *}


text{* Syntax Stuff *}

syntax (latex) 
  "_Neg"       :: "'s ltl => 's ltl"            ("\<MathOclNot>")
  "_Conj"      :: "['s ltl,'s ltl] => 's ltl"   (infixl "\<MathOclAnd>" 60) 
  "_Disj"      :: "['s ltl,'s ltl] => 's ltl"   (infixl "\<MathOclOr>" 60) 
  "_Impl"      :: "['s ltl,'s ltl] => 's ltl"   (infixl "\<MathOclImplies>" 60) 
  "_Next"      :: "'s ltl => 's ltl"            ("\<odot>")
  "_Prev"      :: "'s ltl => 's ltl"            ("\<ominus>")
(*"_Until"     :: "['s ltl,'s ltl] => 's ltl"   (infixr "U+" 65) 
  "_Since"     :: "['s ltl,'s ltl] => 's ltl"   (infixr "S-" 65) *)
  "_always"    :: "'s ltl => 's ltl"            ("\<box>")
  "_eventually":: "'s ltl => 's ltl"            ("\<diamond>")
  "_equiv"     :: "['s ltl,'s ltl] => bool"     (infixr "\<MathOclStrongEq>" 65)
  (* \<MathOclStrongEq> \<cong> 
     ~ » =~= 
     \<approx> » =~~= *)

translations
  "\<MathOclNot> A"     == "Neg A" 
  "\<odot> A"     == "Next A"
  "\<ominus> A"     == "Prev A"
  "A \<MathOclAnd> B "  == "A And B"
  "A \<MathOclOr> B "  == "A Or B"
  "A \<MathOclImplies> B " == "A =-> B"
  "A \<MathOclStrongEq> B "  == "A =~= B"
  "\<box> A"     == "[++] A"
  "\<diamond> A"     == "<++> A"

lemmas TL_sugar = Equiv_def Congr_def Sat_def 
                  TT_def FF_def Disj_def Impl_def 
                  future_op_defs
                  past_op_defs

lemma HSD1_temporal_sem:
assumes A     : "Gen' uid = Gen0' uid \<MathOclAnd> \<odot> (Gen1' uid)"
assumes B     : "In' uid = In0' uid \<MathOclAnd> \<odot> (In1' uid)"
assumes C     : "Out' uid = Out0' uid \<MathOclAnd> \<odot> (Out1' uid)"

assumes A_sem : "\<forall>r k. (Gen uid (r k, r(Suc k))) = (sat r k (Gen' uid))"
assumes B_sem : "\<forall>r k. (In  uid (r k, r(Suc k))) = (sat r k (In'  uid))"
assumes C_sem : "\<forall>r k. (Out uid (r k, r(Suc k))) = (sat r k (Out' uid))"

shows   "(T |= \<box> (Gen' uid \<MathOclImplies> \<MathOclNot> (Out' uid) S- In' uid)) = 
         (\<forall>r\<in>runs T.
          \<forall>k. Gen uid (r k, r (Suc k)) \<longrightarrow>
             (\<exists>ka\<in>{..k}.
                 In uid (r ka, r (Suc ka)) \<and>
                 (\<forall>j\<in>{)ka..k}. ¬ Out uid (r j, r (Suc j)))))"
apply (simp add: A B C A_sem B_sem C_sem TL_sugar sat.simps)
apply (simp add: imp_conjL [symmetric] conj_commute conj_left_commute)
done



lemma aux1 : "0 < k \<Longrightarrow> {..k - Suc 0} = {..k(}"sorry
lemma aux2 : "0 < k \<Longrightarrow> {)j..k - Suc 0} = {)j..k(}"sorry
lemma aux3[simp] : "{)(j::'a::linorder)..j} = {}" by auto


lemma HSD1_temporal_sem':
assumes A     : "(Gen' uid) = (Gen0' uid) And ((++) (Gen1' uid))"
assumes B     : "(In'  uid) = (In0'  uid) And ((++) (In1'  uid))"
assumes C     : "(Out' uid) = (Out0' uid) And ((++) (Out1' uid))"

assumes A_sem : "\<forall>r k. (Gen uid (r k, r(Suc k))) = (sat r k (Gen' uid))"
assumes B_sem : "\<forall>r k. (In  uid (r k, r(Suc k))) = (sat r k (In'  uid))"
assumes C_sem : "\<forall>r k. (Out uid (r k, r(Suc k))) = (sat r k (Out' uid))"

shows   "(T |= \<box> (Gen' uid \<MathOclImplies> \<ominus> (\<MathOclNot> (Out' uid) S- In' uid))) = 
         (\<forall>r\<in>runs T.
          \<forall>k. Gen uid (r k, r (Suc k)) \<longrightarrow>
              0 < k \<and>
             (\<exists>ka\<in>{..k(}.
                 In uid (r ka, r (Suc ka)) \<and>
                 (\<forall>j\<in>{)ka..k(}. ¬ Out uid (r j, r (Suc j)))))"
apply (simp add:  A B C A_sem B_sem C_sem TL_sugar sat.simps)
apply (simp add:  imp_conjL [symmetric] conj_commute conj_left_commute)
apply (simp cong: conj_cong add: aux1 aux2)
done
(* Feasible, but will also require side-conditions that
   are only valid in the model. 
   In particular, it requires that $¬ Gen uid (r 0, r 1))$
   (which has in fact been used by our actual proof).
*)


lemma HSD1_temporal_sem'':
assumes A     : "(Gen' uid) = (Gen0' uid) And ((++) (Gen1' uid))"
assumes B     : "(In'  uid) = (In0'  uid) And ((++) (In1'  uid))"
assumes C     : "(Out' uid) = (Out0' uid) And ((++) (Out1' uid))"

assumes A_sem : "\<forall>r k. (Gen uid (r k, r(Suc k))) = (sat r k (Gen' uid))"
assumes B_sem : "\<forall>r k. (In  uid (r k, r(Suc k))) = (sat r k (In'  uid))"
assumes C_sem : "\<forall>r k. (Out uid (r k, r(Suc k))) = (sat r k (Out' uid))"

shows   "(T |= \<box> (Gen' uid \<MathOclImplies> -? (\<MathOclNot> (Out' uid) S- In' uid))) = 
         (\<forall>r\<in>runs T.
          \<forall>k. Gen uid (r k, r (Suc k)) \<longrightarrow>
             (k = 0 \<or> 
             (\<exists>ka\<in>{..k(}.
                 In uid (r ka, r (Suc ka)) \<and>
                 (\<forall>j\<in>{)ka..k(}. ¬ Out uid (r j, r (Suc j))))))"
apply (simp add: A B C A_sem B_sem C_sem TL_sugar sat.simps)
apply (simp add: imp_conjL [symmetric] conj_commute 
                 conj_left_commute)
apply (simp cong: disj_cong add: Nat.neq0_conv aux1 aux2)
done


section{* Using Semantic equivalences of the Concrete HSD Architecture *}

lemma sem_equiv_HSD_1b:

assumes H1 : "\<forall>r k. (Gen uid (r k, r(Suc k))) 
                       \<longrightarrow> ¬ In uid (r k, r (Suc k))"
assumes H2 : "\<forall>r k. (Gen uid (r k, r(Suc k))) 
                       \<longrightarrow> ¬ Out uid (r k, r (Suc k))"
shows   "(\<forall>r\<in>runs T.
          \<forall>k. Gen uid (r k, r (Suc k)) \<longrightarrow>
             (\<exists>ka\<in>{..k}.
                 In uid (r ka, r (Suc ka)) \<and>
                 (\<forall>j\<in>{)ka..k}. ¬ Out uid (r j, r (Suc j))))) =
         (\<forall>r\<in>runs T.
          \<forall>k. Gen uid (r k, r (Suc k)) \<longrightarrow>
             (\<exists>ka\<in>{..k(}.
                 In uid (r ka, r (Suc ka)) \<and>
                 (\<forall>j\<in>{)ka..k(}. ¬ Out uid (r j, r (Suc j)))))"
apply(rule_tac t="%k. {..k}" and s="%k. insert k {..k(}" in subst)
apply(rule ext) apply(rule set_ext)
apply (simp, arith)
apply (simp add: H1)
apply(rule_tac t="%r k. \<exists>ka\<in>{..k(}.
                          In uid (r ka, r (Suc ka)) \<and>
                        (\<forall>j\<in>{)ka..k}. ¬ Out uid (r j, r (Suc j)))" and 
               s="%r k. \<exists>ka\<in>{..k(}.
                          In uid (r ka, r (Suc ka)) \<and>
                        (\<forall>j\<in>{)ka..k(} \<union> {k}. ¬ Out uid (r j, r (Suc j)))" 
               in subst)
apply(rule ext) apply(rule ext) 
prefer 2 apply(simp add: H2, safe) apply(simp only: ivl_disj_un_singleton) 
prefer 2 apply(simp only: ivl_disj_un_singleton[symmetric],auto)
done


thm trans [OF  HSD1_temporal_sem sem_equiv_HSD_1b]

(* Does not work for suspicious reasons: 
lemmas temporal_equiv_HSD1b = 
       trans [OF HSD1_temporal_sem sem_equiv_HSD_1b]
 *)

lemma temporal_equiv_HSD1b:
assumes A     : "(Gen' uid) = (Gen0' uid) And ((++) (Gen1' uid))"
assumes B     : "(In'  uid) = (In0'  uid) And ((++) (In1'  uid))"
assumes C     : "(Out' uid) = (Out0' uid) And ((++) (Out1' uid))"

assumes A_sem : "\<forall>r k. (Gen uid (r k, r(Suc k))) = (sat r k (Gen' uid))"
assumes B_sem : "\<forall>r k. (In  uid (r k, r(Suc k))) = (sat r k (In'  uid))"
assumes C_sem : "\<forall>r k. (Out uid (r k, r(Suc k))) = (sat r k (Out' uid))"

assumes H1 : "\<forall>r k. (Gen uid (r k, r(Suc k))) 
                       \<longrightarrow> ¬ In uid (r k, r (Suc k))"
assumes H2 : "\<forall>r k. (Gen uid (r k, r(Suc k)))
                       \<longrightarrow> ¬ Out uid (r k, r (Suc k))"

shows   
  " (T |= \<box> (Gen' uid \<MathOclImplies> \<MathOclNot> (Out' uid) S- In' uid)) =
    (\<forall>r\<in>runs T.
       \<forall>k. Gen uid (r k, r (Suc k)) \<longrightarrow>
           (\<exists>ka\<in>{..k(}.
               In uid (r ka, r (Suc ka)) \<and>
               (\<forall>j\<in>{)ka..k(}. ¬ Out uid (r j, r (Suc j)))))"
apply(rule trans)
apply(rule HSD1_temporal_sem) apply(assumption)+
apply(rule sem_equiv_HSD_1b)
apply(rule H1)
apply(rule H2)
done



section{* Action-Lifting of Kripke Structures*}

text{* 
  A foundational problem of LTL is that the atoms 
  are just sets of states (or, equivalently, assertions
  over states $\sigma$, i.e. functions of type 
  $\<sigma> \<longrightarrow> bool$). If action predicates are understood
  as assertions on state transitions (i.e. $\<sigma>×\<sigma> \<longrightarrow> bool$), 
  not all action predicates can be expressed in the form:
  \[ action(A_1,A_2) = E A_1 A_2 \]
  where $E A1 A2$ is a propositional formula over the assertions 
  literals $A_1$ and $A_2$ or, viewed semantically, 
  $E$ is a function composition of the negation and the
  conjunction with $A_1$ and $A_2$. 

  Thus, LTL seems to have less expressive power than a logic
  built over action predicates as atoms such as TLA at first
  sight: a propositional formula over a finite number
  of atoms $E Atom_1 \<dots> Atom_n$ can not represent all predicates
   $E' Action_1 \<dots> Action_m$ since some actions are not finitely
  representable. Among the class of such predicates there are
  pragmatically relevant cases such as $s' \<noteq> s$ or $s'.a \<noteq> s.a$#
  or $s' = s + 1$ provided that $\<sigma>$ is infinite.

  However, this does not mean that LTL as foundational concept
  has less expressive power than a logic such as TLA. The
  reason is that LTL is in principle parameterized over the
  notion of state and nothing hampers from tupling state
  transitions in one Kripke Structure to build a new one.

  This is what the following construction does, which allows
  for encoding TLA in LTL without loss of expressive power.

*}

constdefs
   kripke2action :: "'\<sigma> trsys => ('\<sigma> × '\<sigma>) trsys"
   "kripke2action K \<equiv> (| init = {(s,s') . s \<in> init K \<and> (s,s') \<in> trans K}, 
                         trans = {((s,s'),(t,t')) . s' = t \<and> 
                                                    (s,s') \<in> trans K  \<and> 
                                                    (t,t') \<in> trans K} |)"

section{* Past vs. Future Formulas *}

(* SCHEISSDRECK - das war früher nicht nötig !!! *)

lemma le_iff_add: " (x::nat) \<le> y = (\<exists> k. y = x + k)"
by(auto simp: Nat.le_eq_less_or_eq dest!:Nat.less_imp_Suc_add)

lemma [simp]:"l \<le> k \<Longrightarrow> {)k..(l::nat)} = {}"
apply(rule set_ext)
apply(simp add:greaterThanAtMost_def greaterThan_def atMost_def)
done

text{* The following two lemmas serve as an abstract interface to
       the Least-Operator. They represent the major weapon to
       Past-Future-Proofs. In particular, the second is quite
       tricky \<dots> *}

lemma ExFirst :  
  "\<lbrakk> P (x::nat); x \<in> {j..} \<rbrakk> \<Longrightarrow> 
     \<exists> first\<in>{j..x}. P first \<and> (\<forall>j\<in>{j..first(}. ¬ P j)"
apply(rule_tac x = "LEAST x.  j\<le>x \<and> P x" in bexI,safe, simp_all)
apply(rule conjunct2,rule LeastI, fast)
apply(safe, drule not_less_Least, simp)
apply(rule conjunct1,rule LeastI, fast)
apply(auto intro!: Least_le)
done

(* generalization too complicated \<dots> 
lemma ExLast :  
  "\<lbrakk> P (x::'a::{linorder,ordered_ring,wellorder}); x \<in> {..k} \<rbrakk> \<Longrightarrow> 
     \<exists> last\<in>{x..k}. P last \<and> (\<forall>j\<in>{)last..k}. ¬ P j)"

*)


lemma ExLast :  
  "\<lbrakk> P (x::nat); x \<in> {..k} \<rbrakk> \<Longrightarrow> 
     \<exists> last\<in>{x..k}. P last \<and> (\<forall>j\<in>{)last..k}. ¬ P j)"
  apply(rule_tac x="k - (LEAST x. x \<le> k \<and> P (k-x))" in bexI, auto)
  apply(rule conjunct2,rule_tac k="k - x" in LeastI,simp)
  apply(subgoal_tac "k - j < (LEAST x. x \<le> k \<and> P (k - x))")
  apply(drule not_less_Least, simp, arith)
  apply(subst le_diff_conv2)
  apply(rule conjunct1,rule_tac k="k - x" in LeastI,simp)
  apply(subst add_commute,subst le_diff_conv2[symmetric],
        auto intro!: Least_le)
  done



lemma PastHSD_vs_FutureHSD:
   "\<box> (Gen \<MathOclImplies> (\<MathOclNot> Out S- In)) \<MathOclStrongEq> 
    (\<MathOclNot> Gen W+ In \<MathOclAnd> \<box> (Out \<MathOclImplies> \<MathOclNot> Gen W+ In))"
proof - 
  { fix r ka kb
    have 
    "\<lbrakk>\<forall>k. sat r k Out \<longrightarrow>
            (\<forall>k\<in>{k..}. ¬ sat r k Gen) \<or>
            (\<exists>ka\<in>{k..}. sat r ka In \<and> (\<forall>j\<in>{k..<ka}. ¬ sat r j Gen));
      sat r kb In; \<forall>j\<in>{0..<kb}. ¬ sat r j Gen; sat r ka Gen\<rbrakk>
    \<Longrightarrow> \<exists>k\<in>{..ka}. sat r k In \<and> (\<forall>j\<in>{k<..ka}. ¬ sat r j Out)"
    
    apply(case_tac "ka\<in>{0..<kb}", auto)
    apply(simp add: le_def [symmetric])
    txt{* Now we establish the following case distinction:
      either an $Out$ does not occur in the interval
      between $kb$ and $ka$ (the occurences of the
      $In$ and the $Gen$. Then the witness for the
      goal is trivial. *}
    apply(case_tac "(\<forall>j\<in>{kb..ka}. ¬ sat r j Out)")
    apply(rule_tac x=kb in bexI, auto)

    txt{* Otherwise, there must be an $Out$.
      Now we follow from its existence within
      the interval from $kb$ and $ka$ the existence of
      a ``latest Out'' within this interval - implying 
      that there is no later ``Out'' before the ``Gen''
      at $ka$. *}
    apply(frule_tac P="\<lambda> x. sat r x Out" and k=ka in ExLast, simp)
    apply(erule bexE, simp)
    apply(erule_tac x=last in allE, simp) 
    txt{* The disjunction in our main hypothesis
      imposes a case distinction. *}
    apply(erule disjE)
    txt{* The first case contradicts with $sat r ka Gen$,
      the existence of a $Gen$ occurence. *}
    apply(blast)
    txt{* The second case implies the existence of 
      an $In$-occurence. However, there are again
      two cases to consider: This occurence may
      be before or after the occurence of $Gen$ at $ka$. *}
    apply(safe) (* cleanup *)
    apply(rename_tac "kaa")

    apply(case_tac "ka < kaa")
    txt{*This case is contradictuous since the existence of
      the occurence of $Gen$ at $ka$.*}
    apply(erule_tac x=ka in ballE) back apply simp_all
    txt{*Otherwise, we are there: we have a witness for
      an occurence of $In$ fulfilling all constraints.*}
    apply(rule_tac x=kaa in bexI, simp_all)
    done
  } note H1 = this 
moreover
  { fix r k
    have
    "\<lbrakk>\<forall>k. sat r k Gen \<longrightarrow> 
            (\<exists>ka\<in>{..k}. sat r ka In \<and> (\<forall>j\<in>{ka<..k}. ¬ sat r j Out));
      sat r k Gen\<rbrakk>
    \<Longrightarrow> \<exists>k. sat r k In \<and> (\<forall>j\<in>{0..<k}. ¬ sat r j Gen)"
    apply(frule_tac P="\<lambda>x. sat r x Gen" and j=0 in ExFirst,simp,safe)
    apply(erule_tac x=first in allE, auto)
    done
  } note H2 = this
moreover
  { fix r ka kb
    have
    "\<lbrakk>\<forall>k. sat r k Gen \<longrightarrow>
            (\<exists>ka\<in>{..k}. sat r ka In \<and> (\<forall>j\<in>{ka<..k}. ¬ sat r j Out));
      sat r ka Out; ka \<le> kb; sat r kb Gen\<rbrakk>
    \<Longrightarrow> \<exists>k\<in>{ka..}. sat r k In \<and> (\<forall>j\<in>{ka..<k}. ¬ sat r j Gen)"
    apply(frule_tac P="\<lambda> x. sat r x Gen" and j=ka in ExFirst,simp,safe)
    apply(erule_tac x=first in allE, simp, safe) 
    apply(rename_tac "kaa")
    apply(case_tac "kaa<ka")
    apply(erule_tac x=ka in ballE,simp_all)
    apply(simp add:le_def[symmetric])
    apply(rule_tac x=kaa in bexI,simp_all)
    done
  } note H3 = this
show ?thesis
apply (simp add: TL_sugar  sat.simps)
apply (rule allI, rule iffI)
apply (rule ballI,erule_tac x = r in ballE, simp_all)
apply(case_tac "(\<forall>k. ¬ sat r k Gen)",simp)
prefer 2
apply (rule ballI,erule_tac x = r in ballE, simp_all)
apply(case_tac "(\<forall>k. ¬ sat r k Gen)",simp_all)
apply safe
apply(blast intro!: H1)
apply(erule contrapos_np,blast intro!: H2)
apply(erule contrapos_np, simp, blast intro!: H3)
done
qed

subsubsection {* Properties of boolean operators *}
(* MOVE TO THERE !!! *)


lemma Neg_TT : "Neg (TT) =~~= FF"
by (simp add: Congr_def Sat_def)

lemma Neg_FF : "Neg (FF) =~~= TT"
by (simp add: Congr_def Sat_def)

lemma FF_implies : "(FF \<MathOclImplies> p) =~~= TT"
by (simp add: Congr_def Sat_def)

lemma TT_implies : "(TT \<MathOclImplies> p) =~~= p"
by (simp add: Congr_def Sat_def)

lemma TT_and1 : "(TT \<MathOclAnd> p) =~~= p"
by (simp add: Congr_def Sat_def)

lemma TT_and2 : "(p  \<MathOclAnd> TT) =~~= p"
by (simp add: Congr_def Sat_def)

lemma FF_and1 : "(FF \<MathOclAnd> p) =~~= FF"
by (simp add: Congr_def Sat_def)

lemma FF_and2 : "(p  \<MathOclAnd> FF) =~~= FF"
by (simp add: Congr_def Sat_def)

lemma TT_or1 : "(TT \<MathOclOr> p) =~~= TT"
by (simp add: Congr_def Sat_def)

lemma TT_or2 : "(p  \<MathOclOr> TT) =~~= TT"
by (simp add: Congr_def Sat_def)

lemma FF_or1 : "(FF \<MathOclOr> p) =~~= p"
by (simp add: Congr_def Sat_def)

lemma FF_or2 : "(p  \<MathOclOr> FF) =~~= p"
by (simp add: Congr_def Sat_def)


lemma next_TT: "\<odot> TT =~~= TT"
by (simp add: Congr_def Sat_def TL_sugar)

lemma next_FF: "\<odot> FF =~~= FF"
by (simp add: TL_sugar)

lemma next_and: "\<odot> (A \<MathOclAnd> B) =~~= (\<odot> A \<MathOclAnd> \<odot> B)"
by (simp add: TL_sugar)

lemma next_or: "\<odot> (A \<MathOclOr> B) =~~= (\<odot> A \<MathOclOr> \<odot> B)"
by (simp add: TL_sugar)

lemma next_implies: "\<odot> (A \<MathOclImplies> B) =~~= (\<odot> A \<MathOclImplies> \<odot> B)"
by (simp add: TL_sugar)

lemma next_not: "\<odot> (\<MathOclNot> A) =~~= \<MathOclNot>(\<odot> A)"
by (simp add: TL_sugar)

lemma next_prev: "\<odot> ((--) A) =~~= A"
by (simp add: TL_sugar)

lemma prev_next: "(--)(\<odot> A) =~~= A"
apply (simp add : TL_sugar cong: conj_cong)
oops (* does not hold !!! *)
text{* This suggests a particular strategy:
   drive (--) inside and \<odot> outside and try
   to eliminate them. next_TT and next_FF
   can be handled on the propositional level.*}


lemma prev_TT: "(--) TT =~~= TT"
apply (simp add: Congr_def Sat_def TL_sugar)
(* does not hold at the beginning *)
oops

lemma prev_FF: "(--) FF =~~= FF"
by (simp add: TL_sugar)

lemma always_TT: "\<box> TT =~~= TT"
by (simp add: TL_sugar)
(*the dual does not hold *)

lemma eventually_FF: "\<diamond> FF =~~= FF"
by (simp add: TL_sugar)
(*the dual does not hold *)

lemma until_FF: "(X U+ FF) =~~= FF"
by (simp add: TL_sugar)

lemma since_FF: "(X S- FF) =~~= FF"
by (simp add: TL_sugar)


lemma Congr_Sat_subst_in_equiv: 
  "\<lbrakk> f =~~= g; C \<in> ltl_context\<rbrakk> \<Longrightarrow> (C f) \<MathOclStrongEq> (C g)"
apply (simp add: Equiv_def, safe)
apply(erule Congr_Sat_subst, simp_all)
apply(drule Congr_sym)
apply(erule Congr_Sat_subst, simp_all)
done

(* rectified version : *)
lemma PastHSD_vs_FutureHSD':
   "\<box> (Gen \<MathOclImplies> (Out S- In)) \<MathOclStrongEq> 
    (\<MathOclNot> Gen W+ In \<MathOclAnd> \<box> (\<MathOclNot>Out \<MathOclImplies> \<MathOclNot> Gen W+ In))"
apply(rule Equiv_trans)
apply(rule Congr_Sat_subst_in_equiv [OF Neg_Neg[THEN Congr_sym, of Out]])
apply(simp add: TL_sugar, intro ltl_context.intros)

apply(rule Equiv_trans)
apply(rule PastHSD_vs_FutureHSD)

apply(rule Equiv_refl)
done




text{* Now we reconstruct the proof causality_as_precedence
       as rewriting proof from more general equivalences
       and the congruences above: *}

lemma causality_as_precedence:
   "\<box>(p \<MathOclImplies> <--> q) \<MathOclStrongEq> \<MathOclNot> p W+ q"
apply(simp add:  Once_def)

apply(rule Equiv_trans)
apply(rule PastHSD_vs_FutureHSD')

apply(rule Equiv_trans)
apply(rule Congr_Sat_subst_in_equiv [OF Neg_TT])
apply(simp add: TL_sugar, intro ltl_context.intros)

apply(rule Equiv_trans)
apply(rule Congr_Sat_subst_in_equiv [OF FF_implies])
apply(simp add: TL_sugar, intro ltl_context.intros)

apply(rule Equiv_trans)
apply(rule Congr_Sat_subst_in_equiv [OF  always_TT])
apply(simp add: TL_sugar, intro ltl_context.intros)

apply(rule Equiv_trans)
apply(rule Congr_Sat_subst_in_equiv [OF TT_and2])
apply(intro ltl_context.intros)

apply(rule Equiv_refl)
done

text{* This gives rise for a decision procedure based on the
       congruences and a rewrite procedure \<dots> Prerequisite 
       would be a completion of the rule set \<dots> *}

text{* Lemmas from "Temporal Verification of Reactive Systems --- safety"
       by Manna and Pnueli, pp. 59. *}

lemma Lib1:
   "\<box>(p \<MathOclImplies> \<box> q) \<MathOclStrongEq> \<box>(<-->p \<MathOclImplies> q)" oops

lemma Lib2:
   "(p W+ q) \<MathOclStrongEq> \<box>(<--> (\<MathOclNot> p) \<MathOclImplies> <--> q)" oops

lemma Lib3:
   "(p \<MathOclImplies> \<diamond> q) \<MathOclStrongEq> \<diamond>(<-->(first \<MathOclAnd> p) \<MathOclImplies> q)" oops

lemma Lib4:
   "(p U+ q) \<MathOclStrongEq> \<diamond>(q  \<MathOclAnd>  (Strictlybefore q))" oops

lemma Lib5:
   "(p W+ (\<diamond> q)) \<MathOclStrongEq> \<box> (p \<MathOclOr> \<diamond> q)" oops

constdefs
 WeakSince :: "['s ltl, 's ltl] => 's ltl"       (infixr "B+" 65)
  "p B+ q \<equiv> ([--]p) \<MathOclOr> (p S- q)"   


lemma Lib6:
   "\<box>(p \<MathOclImplies> \<diamond> q) \<MathOclStrongEq> \<box>(\<diamond>((\<MathOclNot> p) B+  q))" oops

lemma Lib7:
   "\<box>(p \<MathOclImplies> \<box>(\<diamond> q)) \<MathOclStrongEq> \<diamond>(\<box>(<--> p \<MathOclImplies> q))" oops

lemma Lib8:
   "\<box>(\<box>(\<diamond> p) \<MathOclImplies> (\<diamond> q)) \<MathOclStrongEq> (\<box>(\<diamond> q) \<MathOclOr> \<box>(\<MathOclNot> p))" oops


section{* Proof Rules *}

(* This version is probably bullshit:
   Valid, but not instantiable for useful things \<dots> *)
lemma SafeSince :
   assumes Init     : "\<And> r. r 0 \<in> R \<or> INV (r 0)" 
   assumes InvI     : "\<And> x. x \<notin> Q \<Longrightarrow> INV (x)"
   assumes Entry    : "\<And> r n. \<lbrakk>INV (r n)\<rbrakk> \<Longrightarrow> r n \<in> R "
   assumes Inv_Post : "\<And> x. INV x \<Longrightarrow> x \<notin> P"
   shows   "T |= \<box> ((Pred P) \<MathOclImplies> ((Pred Q) S- (Pred R)))"

   apply (simp add: TL_sugar  sat.simps)
   apply (safe)
   apply (erule_tac Q = "r k \<in> P" in contrapos_pp) 
   apply (rule Inv_Post, simp)

   apply (erule_tac P = "Ball ?X ?Y" in rev_mp)
   apply (induct_tac "k", simp_all)
   apply (insert Init, fast)
   apply (simp add: Ball_def Bex_def)
   apply (auto)
   apply (erule_tac x=x in allE, simp)
   apply (safe)
   apply (subgoal_tac "xa = Suc n \<or> xa < Suc n")
   prefer 2 apply arith
   apply (auto dest: InvI)
   apply (erule_tac x=n in allE, simp)
   apply (erule impE)
   prefer 2
   apply auto
   apply (subgoal_tac "x = Suc n")
   apply (auto intro!: InvI Entry)
   done

(* Big Problem: Entry is not what I want !!! *)

lemma SafeSince :
   assumes Init     : "\<And> r. r 0 \<in> R \<or> INV (r 0)" 
   assumes InvI     : "\<And> x. INV (x) \<Longrightarrow> x \<in> Q"
   assumes Entry    : "\<And> r n. \<lbrakk>r n \<notin> R \<rbrakk> \<Longrightarrow> INV (r n)"
   assumes Inv_Post : "\<And> x. x \<in> P \<Longrightarrow> INV x"
   shows   "T |= \<box> ((Pred P) \<MathOclImplies> ((Pred Q) S- (Pred R)))"
   oops


text{* Our goal here is to reconstruct the proof architecture
       used in the HSD case study. It turns out, that the
       Version with Prev comes closest to the used 
       Invariants and local lemmas --- the problem is
       the Inv_Post assumption, which must hold
       \textbf{before} ``not P''. *}

lemma SafeSince' :
   assumes Init     : "\<And> r. r (0::nat) \<notin> P \<and> INV (r 0)"
   assumes Inv      : "\<And> r n. \<lbrakk> INV(r n);r n \<notin> R\<rbrakk> \<Longrightarrow> INV (r (Suc n))"  
   assumes InvI     : "\<And> r n. r n \<notin> Q \<Longrightarrow> INV (r (Suc n))"
   assumes InvD     : "\<And> r n. \<lbrakk>r n \<in> R \<rbrakk> \<Longrightarrow> ¬ INV (r (Suc n))"
   assumes Inv_Post : "\<And> x. INV x \<Longrightarrow> x \<notin> P"
   shows   "T |= \<box> (Pred P \<MathOclImplies>  \<ominus> (Pred Q S- Pred R))"

   apply (simp add: TL_sugar  sat.simps,safe)
   apply (erule_tac Q = "r k \<in> P" in contrapos_pp,simp)
   apply (rule conjunct1, rule Init)
   apply (case_tac "k=0",simp_all)

   apply (insert Init, fast, simp add: aux1 aux2 gr0_conv_Suc, safe)
   apply (erule_tac Q = "r (Suc m) \<in> P" in contrapos_pp) 

   apply (rule Inv_Post, simp)
   apply (erule_tac P = "Ball ?X ?Y" in rev_mp)
   apply (induct_tac "m", auto)
   apply (erule_tac x=0 in ballE, auto intro: Inv)
   apply (erule contrapos_np, simp) 
   apply (erule_tac x=k in ballE, auto)
   apply (erule_tac x=j in ballE, auto)
   apply (subgoal_tac "j = Suc n")
   apply (auto intro: InvI) 
   apply (case_tac "r (Suc n) \<notin> R") 
   apply (auto intro : Inv)
   apply (erule_tac x="Suc n" in ballE, auto)
   done



end
 
