(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ZMathTool.thy --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 1998-1999 GMD First, Germany
 *               1998-1999 University Bremen, Germany
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
(* $Id: ZMathTool.thy 6729 2007-08-03 05:25:17Z brucker $ *)

header{* Core of the Mathematical Toolkit *}

theory ZMathTool imports  Finite_Set Sum_Type Main begin

types        ('a,'b) "<=>" = "('a*'b) set"     (infixr 20)

consts

idZ          ::"'a set => ('a <=> 'a)"
forw_comp    ::"['a <=> 'b, 'b <=> 'c] => ('a <=> 'c)"  ("_ %; _"  [60,61] 60)
dom_restr    ::"['a set , 'a <=> 'b] => ('a <=> 'b)"    ("_ <: _"  [71,70] 70)
ran_restr    ::"['a <=> 'b, ('b)set] => 'a <=> 'b"      ("_ :> _"  [65,66] 65)
dom_substr   ::"[ ('a)set , 'a <=> 'b] => 'a <=> 'b"    ("_ <-: _" [71,70] 70)
ran_substr   ::"['a <=> 'b, ('b) set] => ('a <=> 'b)"   ("_ :-> _" [65,66] 65)

trans_clos   ::"('a <=> 'a) => ('a <=> 'a) "            ("_ %+"     [1000] 999)
ref_trans_clos::"('a <=> 'a) => ('a <=> 'a) "           ("_ %*"     [1000] 999)

partial_func ::"['a set,'b set] => ('a <=> 'b) set"     ("_ -|-> _"   [54,53] 53)
(* alias: pfun *)
total_func   ::"['a set,'b set] => ('a <=> 'b) set"     ("_ ---> _"   [54,53] 53)
(* alias: tfun *)
partial_inj  ::"['a set,'b set] => ('a <=> 'b) set"     ("_ >-|-> _"  [54,53] 53)
(* alias: pinj *)
total_inj    ::"['a set,'b set] => ('a <=> 'b) set"     ("_ >--> _"   [54,53] 53)
(* alias: tinj *)
partial_surj ::"['a set,'b set] => ('a <=> 'b) set"     ("_ -|->> _"  [54,53] 53)
(* alias: psurj *)
total_surj   ::"['a set,'b set] => ('a <=> 'b) set"     ("_ -->> _"   [54,53] 53)
(* alias: tsurj *)
biject       ::"['a set,'b set] => ('a <=> 'b) set"     ("_ >-->> _"  [54,53] 53)
(* alias: bij *)
fin_part_func::"['a set,'b set] => ('a <=> 'b) set"     ("_ -||-> _"  [54,53] 53)
(* alias: fpfun *)
fin_part_inj ::"['a set,'b set] => ('a <=> 'b) set"     ("_ >-||-> _" [54,53] 53)
(* alias: fpinj *)
rel          ::"['a set, 'b set] => ('a <=> 'b) set"    ("_ <--> _"   [54,53] 53)
rel_appl     ::"['a<=>'b,'a] => 'b"                     ("_ %^ _"     [90,91] 90)
override     ::"['a <=> 'b, 'a <=> 'b] => ('a <=> 'b)"  ("_ '(+') _"  [55,56] 55)
iter         ::"['a <=> 'a, int] => ('a <=> 'a) "
numb_range   ::"[int,int] => (int) set"                 (" _ .. _"    [50,51] 50)


syntax (xsymbols)
idZ          ::"'a set => ('a <=> 'a)"                  ("\<id>")
forw_comp    ::"['a <=> 'b, 'b <=> 'c] => ('a <=> 'c)"  ("_ \<comp> _"  [60,61] 60)
dom_restr    ::"['a set , 'a <=> 'b] => ('a <=> 'b)"    ("_ \<dres> _"  [71,70] 70)
ran_restr    ::"['a <=> 'b, ('b)set] => 'a <=> 'b"      ("_ \<rres> _"  [65,66] 65)
dom_substr   ::"[ ('a)set , 'a <=> 'b] => 'a <=> 'b"    ("_ \<ndres> _" [71,70] 70)
ran_substr   ::"['a <=> 'b, ('b) set] => ('a <=> 'b)"   ("_ \<nrres> _" [65,66] 65)

trans_clos   ::"('a <=> 'a) => ('a <=> 'a) "            ("_ \<plus> "   [1000] 999)
ref_trans_clos::"('a <=> 'a) => ('a <=> 'a) "           ("_ \<star>"    [1000] 999)

partial_func ::"['a set,'b set] => ('a <=> 'b) set"     ("_ \<pfun> _"  [54,53] 53)
total_func   ::"['a set,'b set] => ('a <=> 'b) set"     ("_ \<fun> _"   [54,53] 53)
partial_inj  ::"['a set,'b set] => ('a <=> 'b) set"     ("_ \<pinj> _"  [54,53] 53)
total_inj    ::"['a set,'b set] => ('a <=> 'b) set"     ("_ \<inj> _"   [54,53] 53)
partial_surj ::"['a set,'b set] => ('a <=> 'b) set"     ("_ \<psurj> _" [54,53] 53)
total_surj   ::"['a set,'b set] => ('a <=> 'b) set"     ("_ \<surj> _"  [54,53] 53)
biject       ::"['a set,'b set] => ('a <=> 'b) set"     ("_ \<bij> _"   [54,53] 53)
override::"['a <=> 'b, 'a <=> 'b] => ('a <=> 'b)"  ("_ \<oplus> _" [55,56] 55)
numb_range   ::"[int,int] => (int) set"                 ("_ \<upto> _"  [50,51] 50)
fin_part_func::"['a set,'b set] => ('a <=> 'b) set"     ("_ \<ffun> _"  [54,53] 53)
fin_part_inj ::"['a set,'b set] => ('a <=> 'b) set"     ("_ \<finj> _"  [54,53] 53)
rel          ::"['a set, 'b set] => ('a <=> 'b) set"    ("_ \<rel> _"   [54,53] 53)
rel_appl     ::"['a<=>'b,'a] => 'b"                     ("_\<rappll>_\<rapplr>" [90,91] 90)


syntax
  dom       ::"('a <=> 'b) => 'a set"
  ran       ::"('a <=> 'b) => 'b set"
  zinverse  ::"('a <=> 'b) => ('b <=> 'a)"             ("_ %~"    [1000]999) 
  rel_image ::"('a <=> 'b) => ('a set) => 'b set"     ("_'(|_|')"[1000,0]999)
  back_comp ::"['b <=> 'c, 'a <=> 'b] => ('a <=> 'c)"  ("_ %o _"  [60,61] 60)
  prodZ     ::"['a set,'b set] => ('a <=> 'b) "        ("_ %x _"  [81,80] 80)
  sumZ      ::"['a set,'b set] => ('a + 'b) set"       ("_ %+ _"  [66,65] 65)
  gen_un    ::"'a set set => 'a set" 
  gen_int   ::"'a set set => 'a set"
  zint      :: "int => nat"                            ("$i")

syntax (xsymbols)
  dom       ::"('a <=> 'b) => 'a set"                  ("\<dom>")
  ran       ::"('a <=> 'b) => 'b set"                  ("\<ran>")
  zinverse  ::"('a <=> 'b) => ('b <=> 'a)"             ("_\<inv>"    [1000]999) 
  rel_image ::"('a <=> 'b) => ('a set) => 'b set"      ("_\<limg>_\<rimg>"[1000,0]999)
  back_comp ::"['b <=> 'c, 'a <=> 'b] => ('a <=> 'c)"  ("_ \<circ> _"  [60,61] 60)
  prodZ     ::"['a set,'b set] => ('a <=> 'b) "        ("_ \<times> _" [81,80] 80)
  sumZ      ::"['a set,'b set] => ('a + 'b) set"       ("_ \<sumZ> _"  [66,65] 65)
  gen_un    ::"'a set set => 'a set"                   ("\<bigcup> _")
  gen_int   ::"'a set set => 'a set"                   ("\<bigcap> _")


translations
  "dom r"         == "Domain r"
  "ran r"         == "Range r"
  "r %~"          == "converse r"
  "rel_image r s" == "r``s"
  "r %o s"        == "r O s"
  "a %x b"        == "a <*> b"
  "a %+ b"        == "a Plus b"
  "gen_un s"      == "Union s"
  "gen_int s"     == "Inter s"
  "zint"          == "nat"  


consts
  zsize        ::"('a set) => int"                       ("#" )
  String       ::"string set"
  Integers     ::"int set"                               ("%Z")
  Naturals     ::"int set"                               ("%N")
  Naturals_1   ::"int set"
  "<->"        ::"[bool, bool] => bool"                  (infixr 25)
  maplet       ::"['a, 'b] => ('a * 'b)"                 ("(2_ \<bar>-->/ _)" [60,61] 60) 
  disjoint     ::"('a <=> ('b set)) => bool"
  partition    ::"[('a <=> ('b set)), ('b set)] => bool" (infixl 60)


syntax(xsymbols)
  zsize        ::"('a set) => int"                       ("\<zsize>" )
  String       ::"string set"                            ("\<String>")
  Integers     ::"int set"                               ("\<num>")
  Naturals     ::"int set"                               ("\<nat>")
  Naturals_1   ::"int set"                               ("\<natone>")
  maplet       ::"['a, 'b] => ('a * 'b)"                 ("(2_ \<mapsto>/ _)" [60,61] 60) 
  disjoint     ::"('a <=> ('b set)) => bool"             ("\<disjoint>")
  partition    ::"[('a <=> ('b set)), ('b set)] => bool" ("_ \<partition> _" [60,61]60)


consts Fin :: "'a set => 'a set set"                     ("%F")
syntax (xsymbols)
  Fin :: "'a set => 'a set set"                          ("\<finset>")

inductive "Fin(A)"
  intros
    emptyI : "{} : Fin(A)"
    insertI: "[| a: A;  b: Fin(A) |] ==> insert a b : Fin(A)"

  
defs
  
idZ_def:            "idZ X       == {p. ? x:X . p = (x,x)}"
rel_def:            "A <--> B    == Pow (A %x B)"
pfun_def:   "S -|-> R    == {f. f:(S <--> R)
                                       & (! x y1 y2. (x,y1):f & (x,y2):f  --> (y1=y2))}"

forw_comp_def:      "r %; s      == {(x,z). ? y. (x,y):r & (y,z):s }"
dom_restr_def:      "s <: r      == {(x,y). (x,y) : r & x : s}"
ran_restr_def:      "r :> s      == {(x,y). (x,y) : r & y : s}"
dom_substr_def:     "s <-: r     == {(x,y). (x,y) : r & x ~: s}"
ran_substr_def:     "r :-> s     == {(x,y). (x,y) : r & y ~: s}"


defs

ref_trans_clos_def: "r%*         == lfp (% s. idZ(dom r Un ran r) Un (r %o s))"
trans_clos_def:     "r%+         == r %o r%*"


tfun_def:     "S ---> R    == {s. s : S -|-> R & dom s = S}"
partial_inj_def:    "S >-|-> R   == {s. s : S -|-> R &
                                       (ALL x1 x2 y. (x1,y) : s & (x2,y) : s 
                                        --> x1 = x2)}"
total_inj_def:      "S >--> R    == (S >-|-> R) Int (S ---> R)"
partial_surj_def:   "S -|->> R   == {s. s : S -|-> R & ran s = R}"
total_surj_def:     "S -->> R    == (S -|->> R) Int (S ---> R)"
biject_def:         "S >-->> R   == (S -->> R) Int (S >--> R)"
override_def:       "S (+) R     == (dom R <-: S) Un R"

String_def:         "String      == UNIV"
Integers_def:       "Integers    == {a::int. True}"
Naturals_def:       "Naturals    == {a::int. 0 <= a }"
Naturals_1_def:     "Naturals_1  == {a::int. 1 <= a }"


iff_def:            "A <-> B     == A = B"

zsize_def:          "# S         == int (card S)"
(*
SHOULD BE (But will require a lot of work:
          # S = {(x,y) . x=S & finites y & y = card S }

lemma: "x : dom (#) = x : Fin Z"
 *)
iter_def:           "iter R n    == if (n:Naturals) 
                                    then (nat_rec (idZ(dom R)) 
                                                  (%n it. R %o it) 
                                                  ($i n))
                                    else (nat_rec (idZ(dom (R %~))) 
                                                  (%n it. (R %~) %o it))   
                                                  ($i ( n))"    
  	                   
numb_range_def:     "(a .. b)    == { k. a <= k & k<= b}"
fin_part_func_def:  "S -||-> R   == {s. s : S -|-> R & dom(s) : Fin(S)}"
fin_part_inj_def:   "S >-||-> R  == (S >-|-> R) Int (S -||-> R)"
rel_apply_def:      "R %^ x      == (@y. (x,y) : R)"
maplet_def:         "maplet a b  == (a,b)"
disjoint_def:       "disjoint f  == (! p:f. ! q:f. p ~= q -->  
                                                  (snd p) Int (snd q) = {})"
partition_def:      "f partition a == (disjoint f & gen_un(ran f) = a)"


(* --------------------------------------- *)
(* function abstraction, hilbert operator  *)
(* --------------------------------------- *)


constdefs
   Lambda     :: "['a set, 'a => 'b] => 'a <=> 'b"
  "Lambda A f == {(x,y). x : A & y = f x}"
   Mu         :: "['a set, 'a => bool] => 'a"
  "Mu A P     == @ x. x : A & P x" 

syntax
  "*Lambda"   :: "[pttrn,'a set,'a => 'b]   => 'a<=>'b" ("(3lambda (_):(_)./ _)" [0,0,10]10)
  "*Mu"       :: "[pttrn,'a set,'a => bool] => 'a"      ("(3mu (_):(_)./ _)"     [0,0,10]10)

(* does not work for stange reasons ... *)
translations
  "lambda x:A. E" == "Lambda A (% x. E)" 
  "mu x:A. P"     == "Mu A (% x. P)"
  



(* ----------------------------- *)
(* empty, rel-image expressions  *)
(* ----------------------------- *)

syntax 
  "@powset"   :: "('a set) => ('a set)set"       ("%P")
  "@emptyset" :: "('a set) => ('a set)"          ("emptyset_" 10)

syntax (xsymbols)
  "@powset"   :: "('a set) => ('a set)set"       ("\<power>")
  "@emptyset" :: "('a set) => ('a set)"          ("\<emptyset>_" 10)

translations 
   "%P A"       == "Pow A"  
   "emptyset a" => "{}"
   
(* *** LAMBDA LEMMAS *** *)
subsection{* Lambda Lemmas *}


lemma Lambda_total: "Lambda A f : (A ---> (range f))"
apply (unfold Lambda_def tfun_def pfun_def rel_def single_valued_def)
apply auto
done


lemma Lambda_dom: "dom(Lambda A f) = A"
apply (unfold Lambda_def tfun_def pfun_def rel_def) 
apply auto
done


lemma Lambda_ran: "ran(Lambda A f) <= range f"
apply (unfold Lambda_def)
apply auto
done


lemma Lambda_beta: "!! A. a : A ==> ((Lambda A f) %^ a) = f a"
apply (unfold Lambda_def rel_apply_def)
apply auto
done

lemma Mu_equality: 
"[|a : A ; P a; ! x:A. P x --> x = a|] ==> (Mu A P) = a"
apply (unfold Mu_def)
apply blast
done

declare Lambda_total[simp] Lambda_beta[simp] Lambda_ran[simp] 
        Mu_equality[simp] Lambda_dom[simp]

(* *** SET LEMMAS *** *)
subsection{* Set Lemmas *}

lemma Int_empty[simp]: "A Int B = {} ==> A - B = A"
apply auto
done

lemma subset_union_mono[simp]: "A <= B ==> A <= B Un C"
apply fast
done

lemma union_subset_distr[simp]: "(A Un B <= C) = (B <= C & A <= C)"
apply fast
done

(* ***** DEFINITION REFORMULATIONS (SIMPLIFICATIONS) ***** *)
subsection{* Simpler Definitions*}

lemma idZ_simp: "idZ X = {(x,x) | x. x:X}"
apply (unfold idZ_def)
apply auto
done

lemma inverse_simp:  "R %~ = {(y,x) | x y. (x,y):R}"
apply auto
done

lemma dom_simp: "dom R = {x. ? y. (x,y):R}"
apply auto
done

lemma ran_simp: "ran R  = {y. ? x. (x,y):R}"
apply auto
done


(*** Equality : the diagonal relation ***)

lemma idZ_eqI: "!! A.[| a=b;  a:A |] ==> (a,b) : idZ(A)"
apply (unfold idZ_def)
apply blast
done

lemmas idZI = refl [THEN idZ_eqI]  (*|>standard*)

(*The general elimination rule*)
lemma idZE:
assumes p1: "c : idZ(A) "
assumes p2: "!!x y. \<lbrakk> x:A;  c = (x,x)\<rbrakk> \<Longrightarrow> P"  
shows "P"
apply (cut_tac p1)
apply (cut_tac CollectD)
apply (unfold idZ_def)
apply (erule bexE)
apply (erule p2)
apply assumption
apply auto
done

declare idZI [intro!]
declare idZE [elim!]

lemma idZ_iff: "((x,y) : idZ A) = (x=y & x : A)"
apply (unfold idZ_def)
apply blast
done

lemma idZ_subset_Times: "idZ(A) <= A <*> A"
apply (unfold idZ_def)
apply blast
done

(* **** DOMAIN and RANGE properties ***** *)
subsection {* Domain and Range Properties *}

lemma Dom_In: "x:dom R = (? y. y:ran(R) & (x,y):R)"
apply auto
done

lemma Ran_In: "y:ran R = (? x. x:dom R & (x,y):R)"
apply auto
done

lemma Dom_Union[simp]: "dom(Q Un R) = dom(Q) Un dom(R)"
apply auto
done

lemma Ran_Union[simp]: "ran(Q Un R) = ran(Q) Un ran(R)"
apply auto
done

lemma Dom_Inter[simp]: "dom(Q Int R) <= dom(Q) Int dom(R)"
apply auto
done

lemma Ran_Inter[simp]: "ran(Q Int R) <= ran(Q) Int ran(R)"
apply auto
done

lemma Dom_Empty[simp]: "dom {} = {}"
apply auto
done

lemma Ran_Empty [simp]: "ran {} = {}"
apply auto
done

lemma Dom_Insert0: "(dom (insert (x,y) S)) = insert x (dom S)"
apply auto
done

lemma Dom_Insert [simp]: "dom (insert p A) = (insert (fst p) (dom A))"
apply (subst surjective_pairing)
apply (simp only: Dom_Insert0)
done


lemma Ran_Insert0: "(ran (insert (x,y) S)) = insert y (ran S)"
apply auto
done

lemma Ran_Insert[simp]: "(ran (insert p S)) = insert (snd p) (ran S)"
apply (subst surjective_pairing)
apply (simp only: Ran_Insert0)
done


(* superfluous
lemma Dom_Single [simp]: "(dom {(x,y)}) = {x}"
apply auto
done

lemma Ran_Single [simp]: "(ran {(x,y)}) = {y}"
apply auto
done
*)

lemma pair_rel_dom [simp]: "(a,b):r ==> (a : (dom r))"
apply auto
done
  
lemma pair_rel_dom_fst [simp]: "a:r ==> ((fst a) : (dom r))"
apply (rule pair_rel_dom)
apply (subst surjective_pairing [symmetric])
apply assumption
done

lemma pair_rel_ran [simp]: "(a,b):r ==> b : ran r"
apply auto
done

lemma pair_rel_dom_snd [simp]: "a:r ==> snd a : ran r"
apply (rule pair_rel_ran)
apply (subst surjective_pairing [symmetric])
apply assumption
done

lemma dom_implies_ran : "a : dom r ==> (EX b. (a,b) : r)"
apply (simp add: dom_simp)
done
(* This loops with dom_simp --- Addsimps at end of file ! *)


lemma Dom_Rel_Empty [simp]:"(dom f = {}) = (f = {})"
apply auto
done

lemma Ran_Rel_Empty [simp]: "(ran f = {}) = (f = {})"
apply auto
done


(* *** DOMAIN and RANGE RESTRICTION *** *)
subsection{* Domain and Range Restriction *}
lemma dom_restrI [rule_format]: "p : r --> fst p : s --> p : (s <: r)"
apply (unfold dom_restr_def)
apply auto
done
declare dom_restrI [intro!]

lemma dom_restrD1:"p : (s <: r) ==> p : r"
apply (unfold dom_restr_def)
apply auto
done

lemma dom_restrD2: "p : (s <: r) ==> fst p :s"
apply (unfold dom_restr_def)
apply auto
done

lemma dom_restrE2:
assumes p1: "p : (s <: r)"
assumes p2: "[| p : r; fst p :s |] ==> P "
shows       "P"
apply (rule p2)
apply (rule dom_restrD1)
apply (rule p1)
apply (rule dom_restrD2)
apply (rule p1)
done
(*AddSEs [dom_restrE2];*)

lemma dom_restrE :
assumes p1: "p : (s <: r)"
assumes p2: "!! a b.[| p = (a, b); (a,b) : r; a:s |] ==> P"
shows "P"
apply (rule surjective_pairing [THEN p2])
apply (rule surjective_pairing [THEN subst])
apply (rule dom_restrD1) 
apply (rule p1)
apply (rule dom_restrD2) 
apply (rule p1)
done
declare dom_restrE [elim!]

lemma ran_restrI [rule_format]: "p : r --> snd p : s --> p : (r :> s)"
apply (unfold ran_restr_def)
apply auto
done
declare ran_restrI [intro!]

lemma ran_restrD1:"p : (r :> s) ==> p : r"
apply (unfold ran_restr_def)
apply auto
done


lemma ran_restrD2:"!!r. p : (r :> s) ==> snd p :s"
apply (unfold ran_restr_def)
apply auto
done

lemma ran_restrE2:
assumes p1: "p : (r :> s)"
assumes p2: "[| p : r; snd p :s |] ==> P"
shows "P"
apply (rule p2)
apply (rule ran_restrD1)
apply (rule p1)
apply (rule ran_restrD2)
apply (rule p1)
done
(*AddSEs [ran_restrE2];*)

lemma ran_restrE:
assumes p1: "p : (r :> s)"
assumes p2: "!! a b.[| p = (a, b); (a,b) : r; b:s |] ==> P"
shows "P"
apply (rule surjective_pairing [THEN p2])
apply (rule surjective_pairing [THEN subst])
apply (rule ran_restrD1)
apply (rule p1)
apply (rule ran_restrD2)
apply (rule p1)
done
declare ran_restrE [elim!]


lemma Dom_Restrict [simp]: "dom (S<:R) = S Int (dom R)"
apply auto
done

lemma Ran_Restrict [simp]: "ran (S:>R) = ran(S) Int R"
apply auto
done

lemma Dom_Rest_Subset [simp]: "(S<:R) <= R"
apply auto
done

lemma Ran_Rest_Subset [simp]: "(S:>R) <= S"
apply auto
done

lemma Dom_Restr_mt[simp]: "X <: {} = {}"
by(simp add:dom_restr_def)


lemma Dom_Ran_Restr_Comp : "((S <: R) :> T) = (S<: (R :> T))"
apply auto
done

lemma Dom_Dom_Restr_Comp [simp]: "(S <: (R <: T)) = ((S Int R) <: T)"
apply auto
done

lemma Ran_Ran_Restr_Comp [simp]: "((S :> R) :> T) = (S :> (R Int T)) "
apply auto
done


lemma No_Dom_Restr [simp]: "(dom R <= S) = (S <: R = R)"
(*apply unfold dom_restr_def)*)
apply auto
done

lemma Empty_Dom_Restr [simp]: "{} <: R = {}"
apply auto
done

lemma No_Ran_Restr [simp]:    "(ran R <= S) = (R :> S = R)"
(*apply (unfold ran_restr_def)*)
apply auto
done

lemma Empty_Ran_Restr [simp]: "R :> {} = {}"
apply auto
done


lemma UNIV_Ran_Restr [simp]:  "x :> UNIV = x"
apply auto
done

(*
: "(dom R <: R) = R"
by Auto_tac;

: "(R :> ran R) = R";
by Auto_tac;
*)

lemma dom_restr_single [simp]: "!!R. fst p : R ==> p : R <: f = (p:f)"
apply auto
done


(* *** DOMAIN and RANGE ANTI-RESTRICTION *** *)
subsection {* Domain and Range Anti-Restriction *}

lemma dom_substrI [rule_format (no_asm)]: "p : r --> fst p ~: s --> p : (s <-: r)"
apply (unfold dom_substr_def)
apply auto
done
declare dom_substrI [intro!]

lemma dom_substrD1: "!!r. p : (s <-: r) ==> p : r"
apply (unfold dom_substr_def)
apply auto
done

(*********************************************************)
lemma dom_substrD2:
 "!!r. p : (s <-: r) ==> fst p ~:s"
apply (unfold dom_substr_def)
apply auto
done

lemma dom_substrE2:
assumes p1: "p : (s <-: r)"
assumes p2: "[| p : r; fst p ~:s |] ==> P"
shows "P"
apply (rule p2)
apply (rule dom_substrD1)
apply (rule p1)
apply (rule dom_substrD2)
apply (rule p1)
done
(*AddSEs [dom_substrE2];*)

lemma dom_substrE:
assumes p1: "p : (s<-:r)"
assumes p2: "!! a b.[| p = (a, b); (a,b) : r; a ~:s |] ==> P"
shows "P"
apply (rule surjective_pairing [THEN p2])
apply (rule surjective_pairing [THEN subst])
apply (rule dom_substrD1)
apply (rule p1)
apply (rule dom_substrD2)
apply (rule p1)
done
declare dom_substrE [elim!]

lemma ran_substrI [rule_format (no_asm)]: "p : r --> snd p ~: s --> p : (r :-> s)"
apply (unfold ran_substr_def)
apply auto
done
declare ran_substrI [intro!]

lemma ran_substrD1: "!!r. p : (r :-> s) ==> p : r"
apply (unfold ran_substr_def)
apply auto
done


lemma ran_substrD2:"!!r. p : (r :-> s) ==> snd p ~:s"
apply (unfold ran_substr_def)
apply auto
done


lemma ran_substrE2:
assumes p1: "p : (r :-> s)"
assumes p2: "[| p : r; snd p ~:s |] ==> P"
shows "P"
apply (rule p2)
apply (rule ran_substrD1)
apply (rule p1)
apply (rule ran_substrD2) 
apply (rule p1)
done
(*AddSEs [ran_substrE2];*)


lemma ran_substrE:
assumes p1: "p : (r :-> s)"
assumes p2: "!! a b.[| p = (a, b); (a,b) : r; b ~:s |] ==> P"
shows  "P"
apply (rule surjective_pairing [THEN p2])
apply (rule surjective_pairing [THEN subst])
apply (rule ran_substrD1)
apply (rule p1)
apply (rule ran_substrD2) 
apply (rule p1)
done
declare ran_substrE [elim!]

lemma Dom_Anti_Restr : "(S <-: R) = (dom(R) - S) <: R"
apply auto
done

lemma dom_substr_Un_distribL [simp]: "(S <-: (A Un B)) = ((S <-: A) Un (S <-: B))"
apply auto
done

lemma dom_substr_Un_asso [simp]: "(A <-: (B <-: C)) = ((A Un B) <-: C)"
apply auto
done

lemma Ran_Anti_Restr [simp]:  "(R :-> T) = R :> (ran(R) - T)"
apply auto
done

lemma DomRestr_Un_DomSubstr [simp]:"(S <: R) Un (S <-: R) = R"
apply auto
done

lemma RanRestr_Un_RanSubstr [simp]: "(S :> R) Un (S :-> R) = S"
apply auto
done

lemma dom_anti_restr_single [simp]: "!! R. fst p ~: R ==> p : R <-: f = (p : f)"
apply auto
done

lemma dom_substr_empty [simp]: "(dom r <-: r) = {}"
apply auto
done


lemma equals0E: 
assumes p1: "Collect P = {}"
assumes p2:  "~ P x ==> Q"
shows "Q"
apply (rule p2)
apply (rule notI)
apply (rule_tac Q = "Collect P = {}" in impE)
prefer 2
apply (assumption)
apply (rule impI)
apply (rule p1)
apply auto
done


lemma dom_substr_subset : "((m <-: r) = {}) = ((dom r) <= m)"
apply auto
done

lemma dom_substr_subset_imp [simp]: "!! r. ((dom r) <= m) ==> ((m <-: r) = {})"
apply fast
done


(* **  RELATIONAL DISTRIBUTIVITY**  *)
subsection {* Relational Distributivity *}

lemma Rel_Union_Distr [simp]: "(r : (X <--> Y) & s : (X <--> Y)) = (r Un s : (X <--> Y))"
apply (unfold rel_def Pow_def)
apply fast
done

(* **  RELATIONAL COMPOSITION**  *)
subsection {* Relational Composition *}

lemma forw_comp_simp [simp]: "(r %; s) = (s %o r)"
apply (unfold forw_comp_def)
apply auto
done


lemma Compose_Rel [simp]: "(x,z):(R %; Q) = (? y. (x,y):R & (y,z):Q)"
apply auto
done

lemma Compose_Transitive : "(P %; (Q %; R)) = ((P %; Q) %; R)"
apply auto
done
(* Compose_Assoc *)


lemma Compose_Id_Left : "((idZ X) %;  P) = (X <: P)"
apply (unfold idZ_def)
apply auto
done
(*Addsimps [Compose_Id_Left];*)

lemma Compose_Id_Right [simp]: "(P %; idZ X) = (P :> X)"
apply (unfold idZ_def)
apply auto
done

lemma Compose_Refl_Trans [simp]: "!! R. (R %; R) <= R ==> ((R Un idZ(S)) %; (R Un idZ(S))) <= (R Un idZ(S))"
apply auto
done

(* **  RELATIONAL INVERSION**  *)
subsection {* Relational Inversion *}

lemma Inversion [simp]: "(y,x):(R %~) = ((x,y):R)"
apply auto
done

lemma Inverse_Comp [simp]: "((Q %; R) %~) = ((R %~) %; (Q %~))"
apply auto
done

lemma Inverse_Idem [simp]: "((R %~) %~) = R"
apply auto
done

lemma Inverse_Id [simp]: "((idZ X) %~) = idZ X"
apply (unfold idZ_def)
apply auto
done

lemma Inverse_Dom [simp]: "dom(R %~) = ran (R)"
apply auto
done

lemma Inverse_Ran [simp]: "ran(R %~) = dom (R)"
apply auto
done

lemma Dom_Anti_Restr_Int [simp]: "(((dom g) <-: f) Int g) = {}"
apply auto
done

lemma Dom_Dom_Anti_Restr_Int [simp]: "((dom ((dom g) <-: f)) Int (dom g)) = {}"
apply auto
done

lemma Rel_Dom_Restr [simp]: "!!f. [|f:(A<-->B); s: (Pow A) |] ==> ((s <: f) : (A <--> B))"
apply (unfold rel_def)
apply fast
done

(***** RELATIONAL IMAGE ****)
subsection {* Relational Image *}

lemma Image_Rel : "y:(R(|S|)) = (? x. {x} <= S & (x,y):R)"
apply auto
done
(*Addsimps [Image_Rel];*)

lemma Image_ran : "R(|S|) = ran (S <: R)"
apply auto
done
(*Addsimps [Image_ran];*)

lemma Image_dom_comp : "dom(Q %; R) = (Q %~) (|dom (R)|)"
apply auto
done
(*Addsimps [Image_dom_comp];*)

lemma Image_ran_comp : "ran(Q %; R) = R(|ran (Q)|)"
apply auto
done
(*Addsimps [Image_ran_comp];*)

lemma Image_union [simp]: "R(|(S Un T) |) = (R(|S|)) Un (R(|T|))"
apply auto
done
declare Image_union [simp]

lemma Image_inter [simp]: "R(|(S Int T)|) <= (R(|S|)) Int (R(|T|))"
apply auto
done

lemma Image_dom [simp]: "R(|dom (R)|) = ran(R)"
apply auto
done

(***** OVERRIDING  ****)
subsection {* Overriding *}

lemma overrideI1: "!!p. p : dom s <-: r ==> p : (r (+) s)"
apply (unfold override_def)
apply auto
done

lemma overrideI2: "!!p. p : s ==> p : (r (+) s)"
apply (unfold override_def)
apply auto
done

lemma overrideCI[intro!]:
assumes prem: "( p ~: s ==>  p : (dom s) <-: r)"
shows "p : (r (+) s)"
apply (unfold override_def)
apply (fast intro!: prem)
done

lemma overrideE[elim!]: "\<lbrakk> p:(r (+) s); p : (dom s) <-: r \<Longrightarrow> Q; p: s \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
apply (unfold override_def)
apply (rule UnE)
apply (auto)
done

lemma override_mt_left [simp]: "({} (+) R) = R"
apply auto
done

lemma override_mt_right [simp]: "(R (+) {}) = R"
apply auto
done


lemma override_idem [simp]: "(R(+)R) = R"
apply auto
done

lemma override_Domain [simp]: "dom(R(+)Q) = (dom (Q)) Un (dom (R))"
apply (unfold override_def)
apply auto
done

lemma override_assoc : "(P(+)(Q(+)R)) = ((P(+)Q)(+)R)"
apply auto
done


lemma override_left_idem [simp]: "(A (+) (A (+) B)) = (A (+) B)"
apply auto
done


lemma override_inter [simp]: "((dom(Q) Int dom(R)) = {}) ==> ((Q(+)R) = (Q Un R))"
apply auto
done

lemma override_res_left [simp]: "(V <: (Q(+)R)) = ((V<: Q) (+) (V <: R))"
apply auto
done

lemma override_res_right [simp]: "((Q(+)R):> W) <= ((Q:>W) (+) (R:>W))"
apply auto
done

lemma override_single [simp]: "{(x,y)} (+) {(x,z)} = {(x,z)}"
apply auto
done


(***** CLOSURE  ****)
subsection {* Closure *}

lemmas zrtrancl_def =  ref_trans_clos_def

lemma zrtrancl_fun_mono : "mono(%s. idZ(dom r Un ran r) Un (r %o s))"
apply (rule monoI)
apply auto
done

lemmas zrtrancl_unfold = zrtrancl_fun_mono [THEN zrtrancl_def [THEN def_lfp_unfold]] (* |> standard*)

lemma zrtrancl_refl0 : "!!x. [| x : dom r Un ran r |]  ==> (x,x) : (r %*)"
apply (subst zrtrancl_unfold)
apply auto
done

lemmas zrtrancl_refl = UnCI [THEN zrtrancl_refl0] (*|> standard*)

declare zrtrancl_refl [simp]
declare zrtrancl_refl [intro!]

lemma zrtrancl_into_zrtrancl : "!!r. [| (a,b) : r%*;  (b,c) : r |] ==> (a,c) : r%*"
apply (subst zrtrancl_unfold)
apply auto
done

(*rtrancl of r contains r *)
lemma r_into_zrtrancl [intro]: "!!p. p : r ==> p : r%*"
apply (simp (no_asm_simp) only: split_tupled_all)
apply (rule zrtrancl_refl [THEN zrtrancl_into_zrtrancl])
apply auto
done

(*
lemma id_into_zrtrancl1 [simp]: "!! r. (x,y) : r %* ==> (x,x) : r %*"
apply (drule DomainI)
apply auto
apply (erule zrtrancl_into_zrtrancl)
done*)



(*monotonicity of zrtrancl*)
lemma zrtrancl_mono: "!!r. r <= s ==> r%* <= s%*"
apply (unfold zrtrancl_def)
apply (rule lfp_mono Un_mono rel_comp_mono subset_refl)+
apply (auto)
done

(** standard induction rule **)

lemma zrtrancl_full_induct:
"\<lbrakk>(a,b) : r%*; !!x. x:dom r \<Longrightarrow> P(x,x); !!y. y:ran r \<Longrightarrow> P(y,y); !!x y z.\<lbrakk> P(x,y); (x,y): r%*; (y,z): r \<rbrakk> \<Longrightarrow> P(x,z)\<rbrakk> \<Longrightarrow> P(a,b)"
apply (rule def_lfp_induct [OF zrtrancl_def zrtrancl_fun_mono])
apply (assumption)
apply (blast)
done

lemma zrtrancl_full_induct2: 
assumes p1: "(a,b) : r%*" 
assumes p2: "!!x. x:dom r ==> P x x"  
assumes p3: "!!y. y:ran r ==> P y y"
assumes p4: "!!x y z.[| P x y; (x,y): r%*; (y,z): r |]  ==>  P x z" 
shows "P a b"
apply (subgoal_tac "P (fst (a,b)) (snd (a,b))")
apply (rule_tac [2] p1 [THEN zrtrancl_full_induct])
apply simp_all
apply (erule p2)
apply (erule p3)
apply (erule p4) 
apply (assumption) 
apply (assumption)
done


(*nice induction rule*)
lemma zrtrancl_induct:
    "[| (a::'a,b) : r%*;     
        a: dom r ==> P(a);  
        a: ran r ==> P(a);  
        !!y z.[| (a,y) : r%*;  (y,z) : r;  P(y) |] ==> P(z) |]   
      ==> P(b)"
(*by induction on this formula*)
apply (subgoal_tac "! y. (a::'a,b) = (a,y) --> P (y) ")
(*now solve first subgoal: this formula is sufficient*)
apply blast
(*now do the induction*)
apply (rule zrtrancl_full_induct)
apply (blast)+
done

(*
lemmas zrtrancl_induct2 = split_rule read_instantiate ["a","(ax,ay)", "b","(bx,by)"] zrtrancl_induct
*)


(*transitivity of transitive closure!! -- by induction.*)
lemma trans_zrtrancl: "trans(r%*)"
apply (unfold trans_def)
apply safe
apply (erule_tac b = "z" in zrtrancl_induct)
apply (blast intro: zrtrancl_into_zrtrancl)+
done

lemmas zrtrancl_trans = trans_zrtrancl [THEN transD, standard]

lemma zrtrancl_dom1 [simp]: "!!r .[| (a,b) : (r%*); a~:ran r |]  ==> a : dom r"
apply (erule zrtrancl_induct)
apply auto
done

lemma zrtrancl_ran0 : "!!r .(a,b) : (r%*) ==> b : dom r Un ran r"
apply (erule zrtrancl_induct)
apply auto
done

lemma zrtrancl_ran1 [simp]: "!!r .[| (a,b) : (r%*); b~:ran r |]  ==> b : dom r"
apply (drule zrtrancl_ran0)
apply auto
done

(*elimination of zrtrancl -- by induction on a special formula*)

lemma zrtranclE0: "[| (a,b) : r%*;  
        [| (a,b): (idZ (dom r Un ran r))|]  ==> P;         
        !!y.[| (a,y) : r%*; (y,b) : r |] ==> P   
     |] ==> P"
apply (subgoal_tac " (a,b) : idZ (dom r Un ran r) | (? y. (a,y) : (r%*) & (y,b) : r) ")
apply (erule asm_rl exE disjE conjE)+
apply blast
apply (erule exE)
apply blast
apply (rule_tac a = "a" in zrtrancl_induct)
apply (auto)
done

lemma zrtranclE:
assumes p1: "(a,b) : r%*"
assumes p2: "[| a:(dom r); a = b|]  ==> P"
assumes p3: "[| a:(ran r); a = b|]  ==> P"         
assumes p4: "!!y.[| (a,y) : r%*; (y,b) : r |] ==> P"   
shows  "P"
apply (rule p1 [THEN zrtranclE0])
apply (erule idZE) 
apply (erule UnE)
apply (rule p2)
apply (rule_tac [3] p3)
apply (rule_tac [5] p4)
apply auto
done


lemmas zrtrancl_into_zrtrancl2 = r_into_zrtrancl [THEN zrtrancl_trans, standard]

lemma reach_induct:
assumes p1: "q : (r%*) (| Q |)"
assumes p2: "!! x. x : Q ==> P x"
assumes p3: "!! y z. [| y : (r%*) (| Q |); (y, z) : r; P y |] ==> P z"
shows "P q "
apply (rule p1 [THEN ImageE])
apply (erule zrtrancl_induct)
apply (erule p2)
apply (erule p2)
apply (drule ImageI)
 apply (assumption)
apply (erule p3)
 apply (assumption)
 apply (assumption)
done


(*** More r%* equations and inclusions ***)

lemma dom_zrtrancl [simp]: "dom (r%*) = (dom r Un ran r)"
apply (auto elim: zrtrancl_induct)
done
 
lemma zrtrancl_ran_eq_dom [simp]: "!!r . ran(r%*) = dom(r%*)"
apply (rule iffI [THEN set_ext])
apply (erule RangeE)
apply (erule zrtrancl_induct)
apply auto
done

lemma dom_zrtrancl : "ran (r%*) = (dom r Un ran r)"
apply auto
done
(*Addsimps [ran_zrtrancl];*)

lemma zrtrancl_idemp [simp]: "(r%*)%* = r%*"
apply auto
apply (erule zrtrancl_induct)
apply (auto intro: zrtrancl_trans)
done

lemma zrtrancl_idemp_self_comp [simp]: "R%* O R%* = R%*"
apply (auto intro: zrtrancl_trans)
done

lemma zrtrancl_subset_zrtrancl : "!!r. r <= s%* ==> r%* <= s%*"
apply (drule zrtrancl_mono)
apply simp
done

lemma zrtrancl_subset :  "!! R. [| R <= S; S <= R%* |] ==> S%* = R%*"
apply (drule zrtrancl_mono)
apply (drule zrtrancl_mono)
apply simp
done

lemma zrtrancl_Un_zrtrancl : "(R%* Un S%*)%* = (R Un S)%*"
apply (blast intro!: zrtrancl_subset intro: r_into_zrtrancl zrtrancl_mono [THEN subsetD])
done

(*
Goal "(R%=)%* = R%*"
by (blast_tac (claset() addSIs [zrtrancl_subset] addIs [r_into_zrtrancl]) 1);
qed "zrtrancl_reflcl";
Addsimps [zrtrancl_reflcl];

Goal "(r - Id)%* = r%*";
by (rtac sym 1);
by (rtac zrtrancl_subset 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (rename_tac "a b" 1);
by (case_tac "a=b" 1);
 by (Blast_tac 1);
by (blast_tac (claset() addSIs [r_into_zrtrancl]) 1);
qed "zrtrancl_r_diff_Id";
*)

lemma zrtrancl_converseD : "!!r.(x,y) : (r%~)%* ==> (y,x) : r%*"
apply (erule zrtrancl_induct)
apply (auto intro: zrtrancl_trans)
done

lemma zrtrancl_converseI : "!!r.(y,x) : r%* ==> (x,y) : (r^-1)%*"
apply (erule zrtrancl_induct)
apply (auto intro: zrtrancl_trans)
done

lemma zrtrancl_converse : "((r%~)%*) = ((r%*)%~)"
(*blast_tac fails: the split_all_tac wrapper must be called to convert
  the set element to a pair*)
apply (rule set_ext)
apply (simp (no_asm_simp) only: split_tupled_all)
apply (safe dest!: zrtrancl_converseD intro!: zrtrancl_converseI)
done

lemma converse_zrtrancl_induct:
assumes major: "(a,b) : r%*"
assumes prem1: "b : dom r ==> P(b)"
assumes prem2: "b : ran r ==> P(b)"
assumes prem3: " !!y z.\<lbrakk> (y,z) : r;  (z,b) : r%*;  P(z) \<rbrakk> \<Longrightarrow> P(y)"
shows "P(a)"
apply (rule major [THEN zrtrancl_converseI [THEN zrtrancl_induct]])
apply (auto intro: prem1 prem2 prem3 dest!: zrtrancl_converseD)
done

lemmas converse_zrtrancl_induct2 = (*split_rule *) converse_zrtrancl_induct [where a = "(ax,ay)" and b = "(bx,by)"]

lemma converse_zrtranclE0:"\<lbrakk>(a,b) : r%*;(a,b): (idZ (dom r Un ran r))  ==>P;!!y.[| (a,y) : r; (y,b) : r%* |] ==> P\<rbrakk> \<Longrightarrow> P"
apply (subgoal_tac " (a,b) : idZ (dom r Un ran r) | (? y. (a,y) : r & (y,b) : r%*)")
apply (erule disjE)
apply blast+
apply (erule converse_zrtrancl_induct)
apply (auto)
done

lemma converse_zrtranclE:
assumes p1: "(x,z):r%*"
assumes p2: "[| z:(dom r); z = x|]  ==> P"
assumes p3: "[| z:(ran r); z = x|]  ==> P"        
assumes p4:  "!!y. [| (x,y):r; (y,z):r%* |] ==> P"  
shows "P"
apply (rule p1 [THEN converse_zrtranclE0])
apply (erule idZE)
 apply (erule UnE)
apply (rule p2)
apply (rule_tac [3] p3)
apply (rule_tac [5] p4)
apply auto
done

lemmas converse_zrtranclE2 = (*split_rule*) converse_zrtranclE [where x = "(xa,xb)" and z = "(za,zb)"] 

lemma r_comp_zrtrancl_eq :  "r O r%* = r%* O r"
apply (blast elim: zrtranclE converse_zrtranclE intro: zrtrancl_into_zrtrancl zrtrancl_into_zrtrancl2)
done


(**** The relation trancl ****)

subsection {* $^+$ *}

lemmas ztrancl_def = trans_clos_def

lemma ztrancl_mono:"!!r.[| p : r%+; r <= s |] ==> p : s%+"
apply (unfold ztrancl_def)
apply (blast intro: zrtrancl_mono [THEN subsetD])
done

(** Conversions between trancl and zrtrancl **)

lemma ztrancl_into_zrtrancl:"!!p. p : r%+ ==> p : r%*"
apply (unfold ztrancl_def)
apply (simp (no_asm_simp) only: split_tupled_all)
apply (erule rel_compEpair)
apply (rule zrtrancl_into_zrtrancl)
apply (assumption+)
done

(*r%+ contains r*)
lemma r_into_ztrancl[intro]:  "!!p. p : r ==> p : r%+"
apply (unfold ztrancl_def)
apply (simp (no_asm_simp) only: split_tupled_all)
apply auto
done

(*intro rule by definition: from zrtrancl and r*)
lemma zrtrancl_into_ztrancl1: "!!r. [| (a,b) : r%*;  (b,c) : r |]   ==>  (a,c) : r%+"
apply (unfold ztrancl_def)
apply auto
done

(*intro rule from r and zrtrancl*)
lemma zrtrancl_into_ztrancl2 :  "!!r. [| (a,b) : r;  (b,c) : r%* |]   ==>  (a,c) : r%+"
apply (erule zrtranclE)
apply blast
apply blast
apply (rule zrtrancl_trans [THEN zrtrancl_into_ztrancl1])
apply (rule r_into_zrtrancl)+
apply (assumption)+
done

(*Nice induction rule for ztrancl*)
lemma ztrancl_induct:
assumes major: "(a,b) : r%+"                                      
assumes prem1: "!!y.  [| (a,y) : r |] ==> P(y)"                  
assumes prem2: "!!y z.[| (a,y) : r%+;  (y,z) : r;  P(y) |] ==> P(z)"        
shows "P(b)"
apply (insert major)
apply (rule rel_compEpair)
apply (unfold ztrancl_def)
apply assumption
(*by induction on this formula*)
apply (subgoal_tac "ALL z. (y,z) : r --> P (z) ")
(*now solve first subgoal: this formula is sufficient*)
apply blast
apply (erule zrtrancl_induct)
apply (insert prem1 prem2)
apply (blast intro: zrtrancl_into_ztrancl1)+
done

(*Another induction rule for ztrancl, incorporating transitivity.*)
lemma ztrancl_trans_induct:
 "[| (x,y) : r%+;  
     !!x y. (x,y) : r ==> P x y;  
     !!x y z. [| (x,y) : r%+; P x y; (y,z) : r%+; P y z |] ==> P x z  
  |] ==> P x y"
apply (blast intro: ztrancl_induct)
done

(*elimination of r%+ -- NOT an induction rule*)

lemma ztranclE:
    "[| (a::'a,b) : r%+;   
        (a,b) : r ==> P;  
        !!y.[| (a,y) : r%+;  (y,b) : r |] ==> P   
     |] ==> P"
apply (subgoal_tac " (a::'a,b) : r | (? y. (a,y) : r%+ & (y,b) : r) ")
apply (erule disjE)
apply blast
apply (erule exE)
apply blast
apply (unfold ztrancl_def)
apply (erule rel_compEpair)
apply (erule zrtranclE)
apply blast+
done

(*Transitivity of r%+.
  Proved by unfolding since it uses transitivity of zrtrancl. *)
lemma trans_ztrancl: "trans(r%+)"
apply (unfold ztrancl_def)
apply (rule transI)
apply (erule rel_compEpair)+
apply (rule rel_compI)
apply (rule zrtrancl_trans)
apply (rule zrtrancl_into_zrtrancl)
apply (assumption)+
done

lemmas ztrancl_trans = trans_ztrancl [THEN transD, standard]

lemma zrtrancl_ztrancl_ztrancl: "!!r. [| (x,y):r%*; (y,z):r%+ |] ==> (x,z):r%+"
apply (unfold ztrancl_def)
apply (blast intro: zrtrancl_trans)
done

(* "[| (a,b) : r;  (b,c) : r%+ |]   ==>  (a,c) : r%+" *)

lemmas ztrancl_into_ztrancl2 = transD [OF trans_ztrancl r_into_ztrancl]



(* primitive recursion for ztrancl over finite relations: *)
(*
lemma ztrancl_insert: "(insert (y,x) r)%+ = r%+ Un {(a,b). (a,y):r%* & (x,b):r%}"
by (rtac equalityI 1);
 by (rtac subsetI 1);
 by (split_all_tac 1);
 by (etac ztrancl_induct 1);
  by (blast_tac (claset() addIs [r_into_ztrancl]) 1);
 by (blast_tac (claset() addIs
     [zrtrancl_into_ztrancl1,ztrancl_into_zrtrancl,r_into_ztrancl,ztrancl_trans]) 1);
by (rtac subsetI 1);
by (blast_tac (claset() addIs
     [zrtrancl_into_ztrancl2, zrtrancl_ztrancl_ztrancl,
      impOfSubs zrtrancl_mono, ztrancl_mono]) 1);
qed "ztrancl_insert";
*)

lemma ztrancl_converse: "(r^-1)%+ = (r%+)^-1"
apply (unfold ztrancl_def)
apply (simp (no_asm) add: zrtrancl_converse converse_rel_comp)
apply (simp (no_asm) add: zrtrancl_converse [symmetric] r_comp_zrtrancl_eq)
done


lemma ztrancl_converseI : "!! r. (x,y) : (r%+)^-1 ==> (x,y) : (r^-1)%+"
apply (simp add: ztrancl_converse)
done


lemma ztrancl_converseD : "!!r. (x,y) : (r^-1)%+ ==> (x,y) : (r%+)^-1"
apply (simp add: ztrancl_converse)
done

lemma converse_ztrancl_induct: 
assumes major: "(a,b) : r%+"
assumes prem1: "!!y. (y,b) : r ==> P(y)"  
assumes prem2: "!!y z.[| (y,z) : r;  (z,b) : r%+;  P(z) |] ==> P(y)"   
shows "P(a)"
apply (rule_tac P = "P" in ztrancl_induct)
apply (rule ztrancl_converseI)
apply (rule converseI)
apply (rule major)
apply (rule prem1)
apply (erule converseD)
apply (blast intro: prem1 prem2 dest!: ztrancl_converseD)
done

lemma ztranclD : "!!R. (x,y):R%+ ==> ? z. (x,z):R & (z,y):R%*"
apply (erule converse_ztrancl_induct)
apply auto
apply (blast intro: zrtrancl_trans) 
done

lemma lemma1:  "!!r. [| (a,b) : r%*;  r <= A %x A |] ==> a=b | a:A"
apply (erule zrtrancl_induct)
apply auto
done

lemma ztrancl_subset_Sigma: "!!r. r <= A %x A ==> r%+ <= A %x A"
apply (unfold ztrancl_def)
apply (blast dest!: lemma1)
done


(**********************************************************************)

lemma Closure_Trans_Inclusion [simp]: "R <= (R%+)"
apply fast
done

lemma Closure_Trans_Compose [simp]: 
"((R%+) %o (R%+)) <= (R%+)"
apply (blast intro: ztrancl_trans)
done

lemma Closure_Transitive : 
"!!R. [| R<=Q & Q %o Q <= Q |] ==> R%+ <= Q"
apply auto
apply (erule ztrancl_induct)
apply auto
done

lemma Closure_Ref_Inclusion [simp]: "idZ (dom R) <= R%*"
apply auto
done 

lemma Closure_RefTrans_Inclus [simp]: "R <= R%*"
apply auto
done

lemma Closure_Trans_RefTrans_Inclus [simp]: "R%+ <= R%* "
apply (rule subsetI) 
apply (erule ztrancl_into_zrtrancl)
done

(*: "R%* %o R%* <= R%*";*)

(*
lemmas Closure_RefTrans_Comp = zrtrancl_idemp_self_comp [THEN equalityD1] |> standard
*)
(*Addsimps [Closure_RefTrans_Comp];*)

lemma Closure_RefTransitive : 
"!!R. [| (idZ (dom R Un ran R) <= Q) ; (R<=Q) ; ((Q %o Q) <= Q) |] ==> ((R%* ) <= Q)"
apply auto
apply (erule zrtrancl_induct)
apply auto
done

lemma Closure_RefTrans_Id : "(R%* ) = ((R%+) Un (idZ (dom R Un ran R)))"
apply (rule set_ext)
apply (simp (no_asm_simp) only: split_tupled_all)
apply (blast elim: zrtranclE intro: zrtrancl_into_ztrancl1 ztrancl_into_zrtrancl)
done
(*Addsimps [Closure_RefTrans_Id];*)

lemma Closure_RefTrans_Id_Union : "R%* = (R Un idZ (dom R Un ran R))%+"
apply (rule equalityI)
apply (rule Closure_RefTransitive)
apply (rule_tac [4] Closure_Transitive)
apply auto
done
(*Addsimps [Closure_RefTrans_Id_Union];*)

(* add only here because it loops with dom_simp *)
(* Addsimps [dom_implies_ran];  *)

lemma isString [simp]: "x:String"
apply (unfold String_def)
apply auto
done

end
