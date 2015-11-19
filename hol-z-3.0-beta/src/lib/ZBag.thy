(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ZBag.thy --- 
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
(* $Id: ZBag.thy 6729 2007-08-03 05:25:17Z brucker $ *)

(*************************************************************************)
(*   Title              : ZBag.thy                                       *)
(*   Project            : Encoding Z in Isabelle                         *)
(*   Author             : T. Santen, T. Neustupny, S. Helke, GMD First   *)
(*   $Id: ZBag.thy 6729 2007-08-03 05:25:17Z brucker $  *)
(*   This theory        : Z Bags                                         *)
(*   Copyright          : GMD First, Berlin                              *)
(*                        Germany                                        *)
(*************************************************************************)

header{* Bags from the Mathematical Toolkit  *}
  
theory ZBag imports ZSeqtoList begin

types

  ('a) "bag" = "'a <=> int"

constdefs
  bag :: "'a set => ('a bag) set"
  "bag S == S -|-> Naturals_1"

  emptybag :: "'a bag"                           ("%[%]")
  "%[%] == {}"

  insertbag :: "['a, 'a bag] => 'a bag"
  "insertbag x B == (if x : dom B 
                     then (B (+) {(x, 1 + (B %^ x))}) 
                     else B Un {(x,1)})"

  count :: "'a bag <=> ('a <=> int)"
  "count == {(B,c). c = ((lambda x:UNIV . 0) (+) B)}"

  infixcount :: "['a bag, 'a] => int"            ("(_ [#]/ _)" [70,71]70)
  "B [#] x == count %^ B %^ x"

  bagelem :: "'a <=> ('a bag)"
  "bagelem == {(x,B). x : dom B}"

  bagelem_fun :: "['a,'a bag] => bool"           ("(_ [:/ _)"  [60,61]60)
  "x [: B == (x,B) : bagelem"

  bagunion :: "('a bag * 'a bag) <=> 'a bag"
  "bagunion == {((B,C),D). dom D = dom B Un dom C &
                           (ALL x. D [#] x = B [#] x + C [#] x)}"

  bagunion_fun
    :: "['a bag, 'a bag] => 'a bag"          ("(_ BUn/ _)"  [70,71]70)
  "B BUn C == bagunion %^ (B,C)"

  itemsbag :: "('a seq) <=> ('a bag)"
  "itemsbag == {(S,B). ALL x. (B : (bag UNIV)) &  \
  \                           (B [#] x = # {i. (i: dom S) & \
  \                                            ((S %^ i) = x)})}"

  items :: "('a seq) => ('a bag)"
  "items S == (itemsbag %^ S)"
  
syntax
"@Bag" :: "args => 'a bag"                         ("%[ (_) %]")

translations
"%[ x, xs %]"    == "insertbag x %[xs%]"
"%[ x %]"        == "insertbag x %[%]"




axioms  
  dom_ran_item: "t:seq X --> ((dom (items t)) = (ran t))"
  mem_bagunion: "(A : (bag X)) --> (B : (bag Y)) --> 
                (x [: (A BUn B)) = ((x [: A) | (x [: B))"
  bagunion_not_emptybag: "(B ~= %[%]) --> ((A BUn B) ~= %[%])"
  bagunion_is_bag: "(A : (bag X)) --> (B : (bag X)) --> ((A BUn B) : (bag X))"
  items_concatseq: "(S : (seq X)) --> (T : (seq X)) -->
                    ((items (S %&^ T)) = ((items S) BUn (items T)))"
  bagunion_emptybag:  "(A : (bag X)) --> ((%[%] BUn A) = A)"
  bagunion_emptybag2: "(A : (bag X)) --> ((A BUn %[%]) = A)"
  count_bagunion: "(A : (bag X)) --> (B : (bag X)) --> 
                  (((A BUn B) [#] x) = (A [#] x + B [#] x))"
  items_emptybag: "items %<%> = %[%]" 
  items_singletonbag: "items %< x %> = %[ x %]" 
  items_mem_ran: "(s : (seq X)) --> ((x [: (items s)) = (x : (ran s)))"
  dom_bagunion: "A : bag X --> B : bag X --> 
                  (dom (A BUn B)) = ((dom A) Un (dom B))"
  domsubstr_bagunion: "A : bag X --> B : bag X --> dom B <= M -->
                        ((M <-: (A BUn B)) = (M <-: A))"



declare bagunion_not_emptybag [simp] bagunion_is_bag [simp] 
        items_singletonbag [simp] 
        items_concatseq bagunion_emptybag bagunion_emptybag2 
        dom_bagunion domsubstr_bagunion

section{*Basic Theorems*}

lemma BagDomPow [simp]: "x: bag X --> dom x : (Pow X)"
apply (unfold bag_def pfun_def)
apply (rule impI)
apply (rule Rel_Dom_Pow)
apply fast
done

lemma BagDomMem [simp]: "(a [: B) = (a : (dom B))"
apply (unfold bagelem_fun_def bagelem_def)
apply (simp (no_asm))
done

lemma BagSingleton: "%[ x %] = {(x,1)}"
apply (unfold insertbag_def emptybag_def)
apply simp
done
  
lemma BagEmpty[simp]:  "%[%] : (bag X)"
apply (unfold emptybag_def bag_def)
apply auto
done
  
lemma SizeBagEmpty[simp]: "# %[%] = 0"
apply (unfold emptybag_def)
apply auto
done
declare SizeBagEmpty [simp]

lemma SizeBagSingleton[simp]: "# %[ x %] = 1"
apply (unfold emptybag_def insertbag_def zsize_def)
apply auto
done

lemma NotBagEmptyEqualSingleton [simp]: " %[x %] ~= %[%]"
apply (unfold emptybag_def insertbag_def)
apply auto
done

lemma NotBagEmptyEqualSingleton2 [simp]: "%[%] ~= (%[x %])"
apply (unfold emptybag_def insertbag_def)
apply auto
done


lemma BagSingletonEqual [simp]: "(%[ x %] = %[ y %]) = (x = y)"
apply (unfold emptybag_def insertbag_def)
apply (rule iffI)
apply auto
done

lemma DomBagEmpty [simp]: "dom %[%] = {}"
apply (unfold emptybag_def)
apply auto
done

lemma DomBagSingleton [simp]: "dom %[ x %] = {x}"
apply (unfold emptybag_def insertbag_def)
apply auto
done
 
lemma NotMemBagEmpty [simp]: "~ x [: %[%]"
apply (unfold emptybag_def insertbag_def bagelem_fun_def bagelem_def)
apply auto
done

lemma MemBagSingleton [simp]: "(x [: %[y%]) = (x = y)"
apply (unfold emptybag_def insertbag_def bagelem_fun_def bagelem_def)
apply auto
done
 
lemma CountBagEmpty [simp]: "%[%] [#] x = 0"
apply (unfold infixcount_def count_def emptybag_def Lambda_def)
apply auto
apply (subst apply_single)
apply (simp (no_asm))
apply (subst apply_single)
apply (simp (no_asm))
done


lemma count_bagsingleton: 
"%[x%] [#] y = (if x=y then 1 else 0)"
apply (unfold infixcount_def count_def 
              emptybag_def insertbag_def Lambda_def)
apply (subst apply_single)
apply (unfold override_def rel_apply_def)
apply (case_tac "x=y")
apply auto
done


lemma single_is_bag [rule_format,simp]: 
"((fst a) : X) --> ((snd a) : Naturals_1) --> ({a} : (bag X))"
apply (unfold Naturals_1_def bag_def)
apply auto
done

lemma single_is_bag2 [rule_format,simp]: 
"(a: G) --> (%[ a %] : (bag G))"
apply (unfold insertbag_def emptybag_def)
apply (simp (no_asm))
done


lemma single_bagset[rule_format,simp]: 
"(a = (fst b)) --> ((snd b) = 1) --> (%[ a %] = {b})"
apply (unfold insertbag_def emptybag_def)
apply auto
apply (rule sym)
apply (rule_tac t = "1" in subst)
apply assumption
apply (rule surjective_pairing)
done

lemma not_mem_emptybag [simp]: "a ~: %[%]"
apply (unfold emptybag_def)
apply (simp (no_asm))
done

section{*Bag Union*}

lemma bagunion_emptybag_singlebag [simp]: "(%[%] BUn %[ a %]) = %[ a %]"
apply (rule_tac X1 = "UNIV" in bagunion_emptybag [THEN mp])
apply (simp (no_asm))
done

lemma bagunion_emptybag_singlebag2 [simp]: "(%[ a %] BUn %[%]) = %[ a %]"
apply (rule_tac X1 = "UNIV" in bagunion_emptybag2 [THEN mp])
apply (simp (no_asm))
done

lemma domsubstr_bagunion_singlebag [rule_format,simp]: 
"(i : G) --> A : bag G --> ({i} <-: (A BUn %[ i %])) = ({i} <-: A)"
apply  (rule impI)+
apply (rule domsubstr_bagunion [THEN mp, THEN mp, THEN mp])
apply auto
done


lemma dom_BagSingleton_I:
"[|x = a|] ==> x : dom (%[ a %])"
by(simp add: DomBagSingleton)



end


