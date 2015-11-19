(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ZFun.thy --- 
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
(* $Id: ZFun.thy 6729 2007-08-03 05:25:17Z brucker $ *)

header{* Functions in the Mathematical Toolkit *}

theory ZFun imports ZMathTool ZInteg begin 


declare dom_implies_ran [simp]

section{* Relation Apply *}


lemma apply_singleton_rel[simp]: "({(x,y)}%^x) = y"
apply (unfold rel_apply_def)
apply (simp (no_asm))
done

lemma mem_apply[rule_format]: "x:dom R & (R%^x) = y --> (x,y):R"
apply (unfold rel_apply_def dom_def Ex_def)
apply (auto intro: someI)
done

lemma override_apply [simp]: 
"(R (+) {(x,y)}) %^ x = y"
apply (simp (no_asm) add: override_def dom_substr_def 
                          rel_apply_def some_equality)
done

lemma override_by_pair_apply2 [simp]: 
"!!x. x ~= z ==> (R (+) {(z,y)}) %^ x = R %^ x"
apply (simp (no_asm) add: override_def dom_substr_def 
                          rel_apply_def some_equality)
apply auto
done

lemma override_by_pair_apply1[simp]:
"x = z ==> (R (+) {(z, y)}) %^ x = y"
by(auto simp:override_def dom_substr_def rel_apply_def)


lemma apply_single: "({(x,y). y = F x}%^z) = (F z)"
apply (unfold rel_apply_def)
apply (simp (no_asm))
done

lemma apply_single_tuple: 
"({((x1,x2),y). (y = (F x1 x2))}%^(z1,z2)) = (F z1 z2)"
apply (unfold rel_apply_def)
apply (simp (no_asm))
done

declare dom_implies_ran [simp del]

lemma dom_un_apply[rule_format]: "(z ~: (dom Q)) --> (((R Un Q)%^z) = (R%^z))"
apply (unfold rel_apply_def)
apply auto
apply (simp add: dom_simp)
done
declare dom_un_apply [simp]
declare dom_implies_ran [simp]


lemma insert_apply: "!!a. z ~= fst a ==> (insert a R) %^ z = R %^ z"
apply (subst insert_is_Un)
apply (subst Un_commute)
apply (rule dom_un_apply)
apply auto
done

lemma insert_apply2: "!!a. z ~: dom R ==> (insert a R) %^ z = {a} %^ z"
apply (subst insert_is_Un)
(*
back *)
apply (rule dom_un_apply)
apply assumption
done

declare insert_apply [simp] insert_apply2 [simp]



lemma dom_substr_apply [simp]: "z ~: S ==> (S <-: R) %^ z = R %^ z"
apply (unfold dom_substr_def rel_apply_def)
apply auto
done


lemma override_apply2 [simp]: 
"(z ~: (dom S)) ==> (((R (+) S)%^z) = (R%^z))"
apply (unfold override_def)
apply auto
done

lemma override_apply1 :
"z : dom S ==> (R (+) S) %^ z = S %^ z"
by(auto simp: override_def dom_substr_def rel_apply_def)
declare override_apply override_apply2[simp]



section{* Relations *}

lemma Rel_Dom_subset: "f : (A <--> B) ==> dom f <= A"
apply (unfold dom_def rel_def)
apply auto
done

lemma Rel_Dom_Elem: "[| f : (A <--> B); x : dom f |] ==> x : A"
apply (unfold dom_def rel_def)
apply auto
done

lemma empty_rel [simp]: "{} : (A <--> B)"
apply (unfold rel_def)
apply auto
done


lemma select_rel [rule_format,simp]: "R ~= {} --> {(x,y). x : S & y = (@y. y:R)} : (S <--> R)"
apply (unfold rel_def)
apply auto
apply (rule someI)
apply assumption
done


lemma rel_dom_member: "[| f : (X <--> Y); (x,y) : f |] ==> x : X"
apply (unfold rel_def)
apply fast
done

(* these two loop -- don't put in simpset! *)
lemma rel_pair_dom[rule_format]: 
"r : (X <--> Y) --> (a,b) : r --> a : X"
apply (unfold rel_def)
apply auto
done

lemma rel_pair_ran[rule_format]: 
"r : (X <--> Y) --> (a,b) : r --> b : Y"
apply (unfold rel_def)
apply auto
done

lemma rel_pair_dom_fst[rule_format]: 
"r :(X<-->Y) --> (x:r) --> fst x: X"
apply (unfold rel_def)
apply auto
done

lemma Dom_Collect_Rel_fst [simp]: 
"dom {p. EX x:A. p = (f x) } = {d. EX x:A. d = fst (f x)}"
apply (simp (no_asm) add: dom_simp)
apply auto
apply (rule_tac x = "xa" in bexI)
apply (simp add: Pair_fst_snd_eq)+
apply (rule_tac x = "snd (f xa) " in exI)
apply (rule_tac x = "xa" in bexI)
apply (simp add: surjective_pairing [symmetric])
apply assumption
done

lemma Rel_Dom_Restr_Ident [rule_format]: 
"x: (X <--> Y) --> (X <: x = x)"
apply (unfold rel_def)
apply auto
done

lemma Rel_Dom_Pow [rule_format]:  "x: (X <--> Y) --> dom x : (Pow X)"
apply (unfold Pow_def)
apply (simp add: Rel_Dom_Restr_Ident)
done
declare Rel_Dom_Pow [simp]

lemma x_in_S_implies_S_nonempty: "x : S ==> S ~= {}"

apply auto
done

lemma nonempty_Pow [simp]: "Pow S ~= {}"
apply (unfold Pow_def)
apply (rule x_in_S_implies_S_nonempty)
apply auto
done

lemma nonempty_Rel [rule_format,simp]: "R ~= {} --> (D <--> R) ~= {}"
apply (unfold rel_def)
apply (simp (no_asm))
done

subsection{* Partial Functions *}
lemma pfunI: 
assumes p1: "f : A <--> B"  
assumes p2: "!! x y1 y2. [| (x,y1) : f; (x,y2) : f |] ==> y1 = y2"
shows "f : A -|-> B"
apply (unfold pfun_def)
apply (auto intro: p1 simp add: p2)
done


lemma pfunE: 
"[| f : A -|-> B;  
    [| f : A <--> B;  ! x y1 y2. (x,y1) : f & (x,y2) : f --> y1 = y2 |] ==> R  
  |] ==> R"
apply (unfold pfun_def)
apply auto
done

lemma Pfun_Single[simp]: "{p} : (A -|-> B) = (fst p : A & snd p : B)"
apply (unfold pfun_def rel_def Pow_def)
apply (rule_tac p = "p" in PairE)
apply (rule iffI)
apply simp+
done

lemma Partial_Union_Distr[rule_format]: 
"(f : (X -|-> Y) & g : (X -|-> Y) & (dom f Int dom g) = {}) 
 --> (f Un g : (X -|-> Y))"
apply (unfold pfun_def dom_simp [THEN eq_reflection])
apply (simp cong add: conj_cong)
apply (rule Rel_Union_Distr [THEN subst])
apply simp
apply (rule impI)
apply (rule allI)+
apply (rule impI)
apply (fast elim: equalityCE)
done

lemma Partial_Union_Distr_rule [simp]:
    "[| f : (X -|-> Y); g : (X -|-> Y);(dom f Int dom g) = {}|] 
    ==> (f Un g : (X -|-> Y))"
apply (simp (no_asm_simp) add: Partial_Union_Distr)
done

lemma Partial_Dom_Restr [simp]: 
"[|f:(A -|-> B); s: (Pow A) |] ==> ((s <: f) : (A -|-> B))"
apply (unfold pfun_def dom_simp [THEN eq_reflection])
apply (simp cong add: conj_cong)
apply safe
apply fast
done

lemma override_pfunI[simp]: 
"[|f:(A -|-> B); g:(A -|-> B)|] ==> ((f (+) g):(A -|-> B))"
apply (unfold override_def)
apply (rule Partial_Union_Distr_rule)
apply (simp add: Dom_Anti_Restr)
apply (rule Partial_Dom_Restr)
apply simp
apply (unfold pfun_def rel_def dom_simp [THEN eq_reflection])
apply (simp add: Pow_def)
apply fast+
done

lemma pfun_subset[elim!]: "[| f: (a -|-> c); a <= b |] ==> (f: (b -|-> c))"
apply (unfold pfun_def rel_def Pow_def)
apply auto
done


lemma tfun_implies_pfun: " f : A ---> B ==> f : A -|-> B"
apply (unfold tfun_def)
apply auto
done


lemma Pfun_Rel: " f : (A -|-> B) ==> f : (A <--> B)"
apply (unfold pfun_def)
apply auto
done
declare tfun_implies_pfun [simp] Pfun_Rel [simp]

(* nicht Pfun_Rel fuehrt zur Endlosrekursion beim Beweis der Bedingung,
   sondern Rel_Dom_Elem bzw. Pfun_Dom_Elem (s.u.)!! *)

(* non-emptiness of function spaces *)

lemma empty_is_pfun [simp]: "{} : (S -|-> R)"
apply (unfold pfun_def)
apply auto
done


(* from Contrib **************************************** *)
lemma ex_elim4 [simp]: "(EX x. x : S) = (S ~= {})"
apply auto
done


lemma select_partial [rule_format,simp]: 
"R ~= {} --> {(x,y). x : S & y = (SOME y. y:R)} : (S -|-> R)"
apply (unfold pfun_def rel_def)
apply (simp (no_asm))
apply (subst ex_elim4 [symmetric])
apply auto
apply (erule someI)
done

lemma beta_apply_pfun[rule_format,simp]: 
"r : (X -|-> Y) --> (a,b) : r --> (r %^ a) = b"
apply (unfold pfun_def rel_apply_def)
apply auto
done


lemmas beta_apply_tfun = tfun_implies_pfun [THEN beta_apply_pfun]


lemma rel_apply_in_rel[rule_format,simp]: 
"r : (X -|-> Y) -->( a : dom r) --> (a,r %^ a) : r"
apply (unfold pfun_def rel_apply_def)
apply (auto)
apply (simplesubst some_eq_ex)
apply (simp (no_asm_simp))
done

lemma collect_apply_rel[rule_format]: 
"r : (X -|-> Y) --> {(x,y). x : dom r & (r %^ x) = y} = r"
apply auto
done

lemma Insert_Partial[rule_format]: 
"((insert x F) : (X -|-> Y)) --> (F : (X -|-> Y))"
apply (unfold pfun_def insert_def rel_def)
apply simp
apply safe
apply fast+
done

lemma Set_Diff_Partial [rule_format,simp]: 
"(F : (X -|-> Y)) --> ((F - A) : (X -|-> Y))"
apply (unfold pfun_def insert_def rel_def)
apply simp
apply safe
apply fast+
done

declare dom_implies_ran [simp del]

lemma Set_Diff_Dom_Partial [rule_format,simp]:
 "(F : (X -|-> Y)) --> (G :(X -|-> Y)) --> (G <= F) -->  
                               ((dom (F - G)) = ((dom F) - (dom G)))"
apply (unfold pfun_def)
apply blast
done

lemma Rel_Apply_in_Partial_Ran[rule_format]: 
"(F : (X -|-> Y)) --> (x: dom F) --> (x,F%^x):F --> ((F%^x) : Y)"
apply (unfold rel_apply_def pfun_def rel_def)
apply (simp add: dom_simp)
apply auto
done

declare Rel_Apply_in_Partial_Ran [simp]

lemma pfun_apply[simp]: 
"[|F : (X -|-> Y); x: dom F |] ==> (F%^x) : Y"
apply (simp add: dom_simp)
done


lemma Partial_Dom_Insert[rule_format]: 
"t : (X -|-> Y)-->a ~: dom t-->a:X --> b:Y--> insert (a,b) t : (X -|-> Y)"
apply (unfold insert_def)
apply auto
apply (unfold pfun_def rel_def)
apply (simp add: dom_simp)
apply (rule allI)+
apply auto
apply (erule allE)
apply (erule_tac x = "x" in allE)
apply (erule_tac x = "y1" in allE)
apply (erule_tac x = "y2" in allE)
apply auto
done


lemma Dom_Nat_Part_Func_Add[rule_format,simp]: 
"t : (Naturals -|-> X) --> m: Naturals --> {p. EX n:dom t. p = (n + m, t%^n)} : (Naturals -|-> X)"
apply (unfold pfun_def rel_def)
apply auto
apply (subst beta_apply_pfun)
apply (auto simp add: rel_def pfun_def)
done


lemma apply_ident: "f : (X -|-> Y) \<Longrightarrow> (f={p. EX n: dom f. p = (n,f%^n)})"
apply auto
done

lemma Partial_Func_Ran_Subset[rule_format]: 
"Y <= Z --> f: (X -|-> Y) --> f: (X -|-> Z)"
apply (unfold pfun_def rel_def)
apply auto
done

declare dom_implies_ran [simp]

lemma part_func_select[rule_format,simp]:	
"R : (X -|-> Y) --> (x, y) : R --> y = (@ z. (x, z) : R)"
apply (fold rel_apply_def)
apply (rule impI)+
apply (rule sym)
apply (rule beta_apply_pfun)
apply assumption+
done

lemma nonempty_PFun [rule_format,simp]: "R ~= {} --> (D -|-> R) ~= {}"
apply (unfold pfun_def)
apply (rule impI)
apply (rule x_in_S_implies_S_nonempty)
apply auto
done

subsection{* Total Functions *}

lemma empty_fun: "{} : ({} ---> R)"
apply (unfold tfun_def)
apply auto
done
declare empty_fun [simp]


lemma select_total [rule_format,simp]: 
"R ~= {} --> {(x,y). x : S & y = (@y. y:R)} : (S ---> R)"
apply (unfold tfun_def pfun_def rel_def 
              dom_simp [THEN eq_reflection])
apply auto
apply (rule someI)
apply assumption
done

lemma empty_is_pfun[simp]: "{} \<in> A -|-> B"
by(auto simp: tfun_def pfun_def rel_def)


lemma empty_biject[simp]: "{} : ({} >-->> {})"
apply (auto simp: biject_def total_surj_def partial_surj_def
                  total_inj_def partial_inj_def)
done


lemma total_func_dom[rule_format]: "r : (X ---> Y) -->  x : X --> x : dom r"
apply (unfold tfun_def)
apply auto
done
declare total_func_dom[simp]


lemma total_is_partial[rule_format,simp]: "f : (X ---> Y) --> f : (X -|-> Y)"
apply (unfold tfun_def)
apply auto
done

lemma nonempty_Fun[rule_format,simp]: "R ~= {} --> (D ---> R) ~= {}"
apply (unfold tfun_def pfun_def rel_def)
apply (rule impI)
apply (rule_tac x = "{ (x,y) | x y. x : D & y = (@x. x:R) }" 
       in x_in_S_implies_S_nonempty)
apply auto
apply (rule someI)
apply assumption
done

subsection{* Partial Injections *}

lemma empty_pinj_fun[simp,intro!]: "{} : (S >-|-> R)"
apply (unfold partial_inj_def)
apply auto
done
declare empty_pinj_fun [simp]

subsection{* Total Injections *}

lemma empty_total_inj: "{} : ({} >--> R)"
apply (unfold total_inj_def)
apply auto
done
declare empty_total_inj [simp]

subsection{* Partial Surjections *}

lemma empty_psurj_fun[simp]: "{} : (S -|->> {})"
apply (unfold partial_surj_def)
apply auto
done


subsection{* Total Surjections *}

lemma empty_total_surj[simp]: "{} : ({} -->> {})"
apply (unfold total_surj_def)
apply auto
done
declare empty_total_surj [simp]

declare dom_implies_ran [simp del]



subsection{* Simplified Definitions *}


declare Pfun_Rel [simp del]

lemma partial_func_simp [simp]: 
"(f : (A -|-> B)) =  (f : (A <--> B) & 
                      (! x y1 y2. (x,y1):f & (x,y2):f --> y1=y2))"
apply (unfold pfun_def)
apply simp
done
(* loopt mit Pfun_Rel! "f : (A -|-> B) ==> f : (A<-->B)" *)


lemma total_func_simp[simp]: 
"(f : (A ---> B)) = (f : (A -|-> B) & dom f = A)"
apply (unfold tfun_def)
apply simp
done
 
lemma partial_inj_simp [simp]: 
"(f : (A >-|-> B)) = (f : (A -|-> B) & (! x1 x2. (? y. (x1,y):f & (x2,y):f) --> x1=x2))"
apply (unfold partial_inj_def)
apply simp
done

lemma total_inj_simp [simp]: 
"(f : (A >--> B)) = (f : (A >-|-> B) & dom f = A)"
apply (unfold total_inj_def Int_def)
apply simp
apply fast
done

lemma partial_surj_simp [simp]: 
"(f : (A -|->> B)) = (f : (A -|-> B) & ran f = B)"
apply (unfold partial_surj_def)
apply simp
done

lemma total_surj_simp [simp]: 
"(f : (A -->> B)) = (f : (A -|-> B) & dom f = A & ran f = B)"
apply (unfold total_surj_def)
apply simp
apply fast
done

(*
Goalw [biject_def,Int_def]
   "(f : (A >-->> B)) = X"
by (Asm_full_simp_tac 1);
*)

declare partial_func_simp [simp del]
declare total_func_simp [simp del]
declare partial_inj_simp [simp del]
declare total_inj_simp [simp del]
declare partial_surj_simp [simp del]
declare total_surj_simp [simp del]
declare Pfun_Rel [simp]


lemma fin_part_funcI: 
"!! f. [| f : A -|-> B; dom f : Fin A |] ==>  f : A -||-> B"
apply (unfold fin_part_func_def)
apply auto
done
declare fin_part_funcI [intro!]

lemma fin_part_funcE: 
"\<lbrakk>f : A -||-> B; [| f : A -|-> B; dom f : %F A |] ==> P \<rbrakk> \<Longrightarrow> P"
apply (unfold fin_part_func_def)
apply auto
done
declare fin_part_funcE [elim!]



lemma insert_is_pfun[simp]:
"[| x:A;y:B; x\<notin>dom S; S : A -|-> B |] ==> (insert (x,y) S) : A -|-> B"
by(auto simp: tfun_def pfun_def rel_def,fast)

lemma pair_pfunI[simp]:
"[| x:A;y:B |] ==> {(x,y)} : A -|-> B"
by simp (*remove ?*)


lemma tfun_apply[simp]:
"[| F : X ---> Y; x : X |] ==> F %^ x : Y"
by(simp only: total_func_simp, erule conjE, 
   rule pfun_apply, auto)



lemma pair_exhaust:
"[| x: B %x C |] ==> EX y z. x = (y,z)"
by auto

lemma tfun_apply_fst:
"[| f : A ---> B %x C; x : A |] ==> fst(f %^ x) : B"
apply(drule  tfun_apply, assumption)
by   (frule pair_exhaust, (erule exE)+, simp)


lemma tfun_apply_snd:
"[| f : A ---> B %x C; x : A |] ==> snd(f %^ x) : C"
apply(drule tfun_apply, assumption)
by   (frule pair_exhaust, (erule exE)+, simp)


lemma pfun_apply_fst:
"[| f : A -|-> B %x C; x : dom f |] ==> fst(f %^ x) : B"
apply(drule pfun_apply, assumption)
by   (frule pair_exhaust, (erule exE)+, simp)


lemma pfun_apply_snd:
"[| f : A -|-> B %x C; x : dom f |] ==> snd(f %^ x) : C"
apply(drule pfun_apply, assumption)
by   (frule pair_exhaust, (erule exE)+, simp)


lemma Pow_right_subset[simp,elim!]:
"[| f : %P (a %x b); b <= c |] ==> f : %P (a %x c)"
by(auto simp: Pow_def)


lemma Pow_left_subset[simp,elim!]:
"[| f : %P (a %x b); a <= c |] ==> f : %P (c %x b)";
by(auto simp: Pow_def)


lemma rel_ran_subset[elim!]:
"[| f : a <--> b; b <= c |] ==> f : a <--> c";
by(auto simp: rel_def)


lemma rel_dom_subset[elim!]:
"[| f : a <--> c; a <= b |] ==> f : b <--> c"
by(auto simp: rel_def)


lemma pfun_ran_subset[elim!]:
"[| f : a -|-> b; b <= c |] ==> f : a -|-> c"
apply(simp only: pfun_def)
apply(auto)
done

lemma dom_override_I:
"[|x:dom X; x:dom Y|] ==> x : dom (X (+) Y)"
by(simp add: override_Domain)

lemma dom_Un_I:
"[|x:dom X; x:dom Y|] ==> x : dom (X Un Y)"
by(simp add: Dom_Union)

lemma dom_insert_I1:
"[|x = fst a|] ==> x : dom (insert a Y)"
by(simp add: Dom_Insert)


lemma dom_insert_I2:
"[|x \<noteq> fst a; x:dom Y|] ==> x : dom (insert a Y)"
by(simp add: Dom_Insert)


lemma dom_dres_I:
"[|x:X; x:dom Y|] ==> x : dom (X <: Y)"
by(simp add: Dom_Restrict)

lemma dom_LambdaI:
"[|x:A|] ==> x : dom (Lambda A f)"
by(simp add: Lambda_dom)


lemma pfun_implies_dom_bounded: "f : A -|-> B \<Longrightarrow> dom f \<subseteq> A"
by(simp only: pfun_def rel_def, auto) 


lemma override_tfunI1[simp]:
"\<lbrakk> f : A --->  B; g : A -|-> B \<rbrakk> \<Longrightarrow> f(+)g : A ---> B"
by(simp only: tfun_def, auto dest!: pfun_implies_dom_bounded)

lemma override_tfunI2[simp]:
"\<lbrakk> f : A -|->  B; g : A ---> B \<rbrakk> \<Longrightarrow> f(+)g : A ---> B"
by(simp only: tfun_def, auto dest!: pfun_implies_dom_bounded)


lemma pfun_ext:
assumes f_pfun: "f : A -|->  B"
assumes g_pfun: "g : A -|-> B"
assumes dom_eq: "dom f = dom g"
assumes cong: "!! i. \<lbrakk> i : dom f; dom f = dom g \<rbrakk> \<Longrightarrow> f %^ i = g %^ i"
shows  "f = g"
apply(rule set_ext, insert f_pfun g_pfun dom_eq, auto)
apply(rule_tac t=b in subst) defer 1
apply(erule rel_apply_in_rel,auto)
apply(rule_tac t=b in subst) defer 1
apply(erule rel_apply_in_rel,auto)
apply(subst beta_apply_pfun [of f _ _ a b,symmetric],assumption+)
apply(rule cong[symmetric], auto)
apply(subst beta_apply_pfun [of g _ _ a b,symmetric]) prefer 3
apply(rule cong)
apply auto
done

text{* Due to internal translation restrictions, certain expressions were  
       represented by $rel\_appl f ` ( j .. k)$. The following property 
       removes this artifact: *}
lemma rel_appl_norm :  
"rel_appl f ` ( j .. k) = {a. EX i:j..k. f %^ i = a}" 
by(auto)


end

  
