(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * simpleRules.ML --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 2000-2003 University Freiburg, Germany
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
(* $Id: simpleRules.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* This file contains          *)
(* rules on a very low level   *)
(* Not all of them are really  *)
(* new but may be comfortable. *)


zgoal thy "(n,y):wc =+=> ~(wc={})";
auto();
qed "NemptyOneElem";

goal thy "!! x. [| x : dom f; f = {} |] ==> R";
auto();
qed"domExEmpty_any";

goal thy "S ~= {} =+=> (? x. x:S)";
auto();
qed"notEmpty_implies_example";

goal thy "!! f . [| f ~= {} ; f <= g |] ==> g ~= {}";
auto();
qed"notEmpty_subset";

goal thy "!! wc . wc = {} ==> ! n : dom wc . P n";
auto();
qed"empty_implies_Ball";


goal thy "!! x. [| A <= B; x ~: B |] ==> x ~: A";
auto();
qed"elem_contrapos";


goal thy "!! z. [| z : {(x,y). Q x y & P x y} |] ==> z : {(x,y). Q x y} & z : {(x,y). P x y}";
auto();
qed "elemSetConj";

goal thy "!! z. [| z : {(x,y). (x,y) : Q} |] ==> z : Q";
auto();
qed"doubleMember";


goal thy "!! a1 . [| a1 = b1 ; a2 = b2 |] ==> (a1, a2) = (b1, b2)";
auto();
qed"pairEq";

goal thy "!! a1 .  (a1, a2) = (b1, b2)==> (a1 = b1 /\\ a2 = b2 )";
auto();
qed"rev_pairEq";

(* lemma changeOverrid     *)
goal thy "!! x . a %^ x ~= (a (+) {u |--> p}) %^ x ==> x = u";

by(convert2hol_tac [maplet_def, rel_apply_def, func_overrid_def] 1);
auto();
qed"changeOverrid";


goal thy "!! x . {u |--> p} %^ u = p";
by(convert2hol_tac [maplet_def, rel_apply_def, func_overrid_def] 1);
auto();
qed"singleMaplet_appl";


goal thy "!! a . \
\ [| f = g (+) {a |--> b} ; a : dom g|] \
\ ==> dom f = dom g";
by(convert2hol_tac [maplet_def] 1);
auto();
qed"dom_inv_singleton";


goal thy "!! A . B = A (+) C ==> dom A <= dom B";
auto();
qed"oplDomSubset";

goal thy "!! x. x : dom A ==> x : dom (A (+) B) ";
auto();
qed"oplDomLeft";

goal thy "!! x. x : dom B ==> x : dom (A (+) B) ";
auto();
qed"oplDomRight";

(* allow d-res with associativity of (+) *)

goal thy "!! x. (D = (A (+) B) (+) C  ==> D = A (+) (B (+) C))";
auto();
qed"Overrid_Compose_D1";

(* lemmae which allow us to trace   *)
(* elements concerning relational   *)
(* override operation.              *)

goal thy "!! x . (x = uid) ==> \
\ (abs_passwd (+) {uid |--> passwd}) %^ x = passwd";
by(convert2hol_tac [maplet_def, rel_apply_def, func_overrid_def] 1);
auto();
qed"fapply_overrid";

goal thy "!! x . (x = uid) ==> \
\ (abs_passwd (+) {uid |--> (passwd uid)}) %^ x = (passwd uid)";
by(convert2hol_tac [maplet_def, rel_apply_def, func_overrid_def] 1);
auto();
qed"fapply_overrid_depend";


goal thy "!! x. [| A = B (+) C; x ~: dom C; x : dom A |] \
\  ==> x : dom B";
auto();
qed"dom_simple_trace_left";

(* legacy - lemma, better use next one! *)
goal thy "!! x. [| x : dom B ; x ~: dom A; B = A (+) C |] \
\  ==> x : dom C ";
auto();
qed"domTrace_Overrid";

(* This version matches easier with destruct resolution *)
(* because the first assumption determines the unifier  *)

goal thy "!! x. [| B = A (+) C; x : dom B ; x ~: dom A |] \
\  ==> x : dom C ";
auto();
qed"domDiff_trace_overrid";

goal thy "!! x. [| x : dom (A (+) C) ; x ~: dom A |] \
\  ==> x : dom C ";
auto();
qed"domTrace_Overrid_short";

goal thy "!! x. [| x : dom B ; x ~: dom A; B = A Un C |] \
\  ==> x : dom C ";
auto();
qed"dom_trace_un";

goal thy "!! f. f : dom (A <: B) ==> f : A";
auto();
qed"inRestrDom";

goal thy "!! f. [| f : dom B; f : A|]  ==> (f : dom (A <: B))";
auto();
qed"revRestrDom";

goal thy "!! f. f : dom (A <: B) ==> f : dom B";
auto();
qed"inDomRestr";

goal thy "!! x . f : dom C ==> (A (+) C) %^ f = C %^ f";
by(convert2hol_tac [func_overrid_def, dom_substr_def, rel_apply_def] 1);
qed"overridden_appl";

goal thy"!! x. B = A (+) C ==> \
\ ((B %^ f = A %^ f)\\/(B %^ f = C %^ f)) ";
by(hyp_subst_tac 1);
by(case_tac "f: dom C" 1);
by(convert2hol_tac [func_overrid_def, dom_substr_def, 
		    Domain_def, rel_apply_def] 2);
bd overridden_appl 1;
br disjI2 1;
ba 1;
qed"overrid_eitherOr";

goal thy "!! x. f : dom( A (+) B ) ==> f : (dom A) Un (dom B) ";
br mp 1;
by(res_inst_tac [("R", "A"), ("Q", "B")]  Overrid_Domain 2);
by(res_inst_tac [("t", "dom B Un dom A"), 
		 ("s", "dom A Un dom B")] subst 1);
auto();
(*
br UnKomm 1;
br impI 1;
be subst 1;
ba 1;
*)
qed"domDistr";


goal thy"!! x. [|B = A (+) C; (B %^ f ~= A %^ f) |] \
\    ==> (B %^ f = C %^ f)  ";
be (make_elim overrid_eitherOr) 1;
be disjE 1;
ba 2;
br notE 1;
ba 1;
ba 1;
qed"neqAppl_trace_overrid";

(* legacy - lemma, better use next one. *)
goal thy "!! x. [| f:dom C; C = (A (+) B); \
\  C %^ f ~= A %^ f |]                     \
\ ==> f : dom B";
by(convert2hol_tac [Domain_def, func_overrid_def, 
		    dom_substr_def, rel_apply_def] 1);
auto();
qed"neqAppl_domTrace_overrid";

goal thy "!! x. [| C = (A (+) B); f:dom C; \
\  C %^ f ~= A %^ f |]                     \
\ ==> f : dom B";
by(convert2hol_tac [Domain_def, func_overrid_def, 
		    dom_substr_def, rel_apply_def] 1);
auto();
qed"fneq_domTrace_overrid";


goal thy "!! x. [| C = (A (+) B); f:dom C; \
\                    C %^ f ~= A %^ f |]   \
\  ==> (f : dom B)  /\\ (B %^ f = C %^ f)";
br conjI 1;
br neqAppl_domTrace_overrid 1;
ba 1;
ba 1;
ba 1;
bd neqAppl_trace_overrid 1;
ba 1;
br sym 1;
ba 1;
qed"domTrace_overrid_comb";

goal thy "!! x. [| f:dom B; C = (A (+) B)|] \
\  ==> C %^ f = B %^ f ";
by(convert2hol_tac [func_overrid_def, dom_substr_def, rel_apply_def] 1);
qed"overriden_relAppl";

goal thy "!! x. [| C = (A (+) B); f:dom B |] \
\ ==> f : dom C ";
by(convert2hol_tac [func_overrid_def, dom_substr_def, rel_apply_def] 1);
auto();
qed"overriden_relApplDom";

goal thy "!! x. [| f ~:dom A ; f : dom B |] ==> (A(+)B)%^f = B %^ f";
by(convert2hol_tac [func_overrid_def, dom_substr_def, rel_apply_def] 1);
qed"overrid_choose_rel_apply";

goal thy "!! A . \
\ [| C = (A (+) B); f ~:dom A ; f : dom C|] ==> C %^f = B %^ f";
by(res_inst_tac [("s","A(+)B") ,
		 ("t","C")] subst 1);
br sym 1;
ba 1;
br overrid_choose_rel_apply 1;
br domTrace_Overrid 2;
by(AtomizePremSolveAll);
qed"domTrace_Overrid_apply";

(* the following rule combines *)
(* the lemma above with a      *)
(* definedness lemma.          *)
(* It allows to combine the two*)
(* steps on the assumptions    *)
(* using dtac.                 *)

goal thy "!! A . \
\ [| C = (A (+) B); f ~:dom A ; f : dom C|] \
\ ==> C %^f = B %^ f /\\ f : dom B";
br conjI 1;
br domTrace_Overrid_apply 1;
ba 1;
ba 1;
ba 1;
br domTrace_Overrid 1;
ba 1;
ba 1;
ba 1;
qed"domTrace_Overrid_comb";

goal thy "!! x. [| f :dom A ;f ~: dom B |] ==> (A(+)B)%^f = A %^ f";
by(convert2hol_tac [func_overrid_def, dom_substr_def, rel_apply_def, Domain_def] 1);
qed"rev_overrid_choose_rel_apply";

goal thy "!! x. [| f ~:dom A ; f : dom B |] ==> (A Un B)%^f = B %^ f";
by(convert2hol_tac [Domain_def, Un_def, rel_apply_def] 1);
qed"un_choose_rel_apply";


(* these lemmata are useful *)
(* for reasoning about the  *)
(* HOL-Z-Representation of  *)
(* the Z-Set Comprehension. *)

goal thy "!! a. a : ((%n. n) `` asSet(%n. P n)) ==> P a";
by(convert2hol_tac [image_def] 1);
auto();
qed"id_img_prop";

goal thy "!! a. a : dom ((%n. n |--> Q n) `` asSet(%n. P n)) ==> P a";
by(convert2hol_tac [image_def, maplet_def] 1);
auto();
qed"dom_id_img_prop";

goal thy "!! a. (P a)==> a : dom ((%n. n |--> Q n) `` asSet(%n. P n))";
by(convert2hol_tac [image_def, maplet_def] 1);
auto();
qed"rev_dom_id_img_prop";

goal thy "!! f . (P f) ==> (((%n. n |--> Q n) `` asSet(%n. P n))%^ f) = Q f";
by(convert2hol_tac [image_def, maplet_def, rel_apply_def] 1);
auto();
qed"yields_prop";

goal thy "!! f . [| (P f);  (f : (%n. n) `` asSet(%n. Q n) ) |] \
\  ==> (f : (%n. n) `` asSet(%n. P n /\\ Q n) )";
by(convert2hol_tac [image_def, maplet_def, rel_apply_def] 1);
auto();
qed"singleProps";


goal thy "!! f . P f  ==> (f : (%n. n) `` asSet(%n. P n))";
by(convert2hol_tac [image_def, maplet_def, rel_apply_def] 1);
auto();
qed"simpleGetProp";

(* some simple lemmata for *)
(* the users comfort       *)

goal thy "!! f . [| f <= Abs_Name;      \
\                         (f ~: (%P Abs_Name)) |]  \
\                          ==> p";
auto();
qed"f_absNameContr";

goal thy "!!P. P ==> ~ (~ P)";
auto();
qed"notnotI";

goal thy "!! x . ~ x ~: A ==> x : A";
auto();
qed"notNotinD";

(* fits well to Relation.Domain *)

goal thy "!! x z. x ~: dom g ==> (x,z) ~: g ";
auto();
qed"DomNotE";

goal thy "!! x. x ~= y ==> y ~= x";
auto();
qed"nsym";

goal thy "!! x .                \
\            [| f = g;          \
\                f ~= h |]      \
\                ==> g ~= h     ";
 auto();
qed "nTrans";

goal thy "!! f. ? x . f %^ x ~= g %^ x ==> f ~= g";
auto();
qed"oneNeqFunc";

(* transformation lemma *)

goal thy "!! x . [|  (x /\\ y =+=> z) |] ==> (x =+=> y =+=> z)";
auto();
qed"and_imp";

goal thy "!! x . [|  (y =+=> x =+=> z) |] ==> (x =+=> y =+=> z)";
auto();
qed"imp_change";

goal thy " !! x . [| x : dom f; x ~: dom g |] \
\ ==> f ~= g  ";
auto();
qed"chDom_implies_chFunc";

goal thy " !! x . [| x : dom f; x ~: dom g |] \
\ ==> (f %^ x) ~= (g %^x) ";
auto();

goal thy "!! f . dom f ~= {} ==> f ~= {}";
auto();
qed"f_dom_f_emptyD";

zgoal thy " f: B =+=> \
\ ((%n. n |--> A) ``(%n. n : B )) %^ f = A";
by(convert2hol_tac [maplet_def, image_def, rel_apply_def] 1);
auto();
qed"f_apply_maplet";


goal thy " f (+) {x} ~= {}";
by(convert2hol_tac [func_overrid_def] 1);
qed"elem_notEmpty";

goal thy "!! x. fst (a, b) : C ==> a : C";
auto();
qed"fst_PairIn";


(* some lemmata which make *)
(* Definedness -proofs     *)
(* easier.                 *)


goal thy "!! x. [| x : dom A ; A : (T <--> S)|] ==> x : T";
by(convert2hol_tac [rel_def, Pow_def] 1);
auto();
qed"Type_inDom_Rel";


goalw thy [partial_func_def,rel_def]
" !!y. [| f : A -|-> B; x : dom f |]  ==> x : A";
auto();
qed"dom_pfun";

goalw thy [partial_func_def,rel_def]
" !!y. [| f : A -|-> B; x : ran f |]  ==> x : B";
auto();
qed"ran_pfun";


goalw thy [rel_def]
" !!y. [| f : A -|-> B ; (x,y) : f |]  ==> y : B";
by(convert2hol_tac [partial_func_def, rel_def] 1);
auto();
qed"pfun_snd";

goalw thy [rel_def]
" !!y. [| f : A -|-> B ; x : dom f |]  ==> f%^ x : B";
auto();
qed"pfun_appl";

goal thy "!! a. [| (a,b) : f ; f : A-|-> B|] ==> f %^ a = b";
by(convert2hol_tac [partial_func_def, rel_apply_def] 1);
auto();
qed"tuple_yields_ifPartial";



(* some HOL - Properties.     *)
(* They are used e.g. to      *)
(* prove (x,absPwd x):Aknows. *)



goal thy "S ~= {} =+=> (? a . ? b . (a,b) : S)";
by(stripS_tac 1);
zbd notEmpty_implies_example 1;
be exE 1;
by(pair_tac "x" 1);
br exI 1;
br exI 1;
ba 1;
qed"notEmpty_implies_examplePair";


(* version for abs_add *)

goal thy "(a,b) : S =+=> (@ x. x : dom S) : dom S";
br impI 1;
br selectI2 1;
ba 2;
br DomainI 1;
ba 1;
qed"eps_from_example";

(* more common version *)
(* for abs_up.         *)

goal thy "(a,b) : S =+=> P a =+=> (@ x. x : dom S /\\ P x) : dom S";
by( stripS_tac 1);
br selectI2 1;
be conjE 2;
ba 2;
br conjI 1;
ba 2;
by(convert2hol_tac [Domain_def] 1);
br exI 1;
ba 1;
qed"eps_from_example_pred";

goal thy " (? a . ? b . (a,b) : S) =+=> (@ x. x : dom S) : dom S";
by(stripS_tac 1);
by(atomizePrem_ex 1);
zbr eps_from_example 1;
ba 1;
qed"eps_from_exists_example";

(* more common version *)
(* for abs_up.         *)

goal thy " (? a . ? b . (a,b) : S /\\ P a) =+=> (@ x. x : dom S /\\ P x) : dom S";
by(stripS_tac 1);
by(atomizePrem_ex 1);
zbr eps_from_example_pred 1;
ba 1;
ba 1;
qed"eps_from_exists_example_pred";


goal thy "!!x . x : dom f ==> (x, (f %^ x)) : f";
by(convert2hol_tac [rel_apply_def, Domain_def] 1);
auto();
by(eres_inst_tac [("P","%y. (x,y):f")] selectI 1);
qed"relAppl_refl_example";


