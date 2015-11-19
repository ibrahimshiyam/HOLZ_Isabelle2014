(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * BB.ML ---
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
(* $Id: BB.ML 6739 2007-08-03 06:16:18Z brucker $ *)

open BB;
toToplevel schemes;
toToplevel axdefs;


(* ***************************************************************** *)
(*                                                                   *)
(* Elementary proving examples for equational reasoning on schemas   *)
(*                                                                   *)
(* ***************************************************************** *)

zgoalw thy []
"(+.. birthday:(Name -|-> Date); \
\     known : Pow Name           \ 
\ |--                           \
\      known = dom(birthday)     \
\ -..) = ?X";
by(UNFOLD "% known birthday. known = dom(birthday)" [symmetry] 1);
br refl 1;
back();
qed"Test1";

zgoalw thy []
"+.. dummy : {dummy}                         \
\ |--                                        \
\   (A : (%N -|-> %P(%Z))&                   \
\   (B : (%Z ---> Report))&                  \        
\   (! x. (A %^ x) = {}))                    \
\ -.. ";(* Just a test for axiomatic definitions *)
(* dummy  -  Hack just to produce a trivial signature for a goal 
   (the embedding for |- assumes that there is always a signature) *) 

by(intro_schema_tac 1);
by(cut_facts_tac [A_axdef] 1);
by(convert2hol_tac [] 1);
qed"Test2";

(* For the moment, this is a paradigmatic proof scheme:
   - intro turnstyle,
   - convert to hol
   - blow it away . . . (or not)

*)



zgoalw thy [] " %Delta BirthdayBook";
by(UNFOLD "% known birthday known' birthday'. \
\          ?X known birthday known' birthday'&\
\          ?Y known birthday known' birthday'" [conj_commute] 1);



zgoal thy 
"{. FindBirthday @ (%theta BirthdayBook, %theta BirthdayBook') .} = ?Z";


(* ***************************************************************** *)
(*                                                                   *)
(* Paradigmatical proof examples for refinement proofs               *)
(*                                                                   *)
(* ***************************************************************** *)


(* Spivey gives the following simplified version of the first refinement
   condition (see below). HOL-Z reduces this goal via "auto()". *)
zgoal thy 
"(%A BirthdayBook @ (%A BirthdayBook1 @  \
\    (%A name? %: Name@ %A date? %: Date@ \
\      ((name? ~: known /\\  known =  {n. ? i : #1..hwm. n = (names%^i)}) \
\      =+=>                                                               \
\      (!i : #1..hwm. name? ~= (names %^ i)))                             \
\ )))";
by(stripS_tac 1);
auto();
qed"PO_refine_1_AddBirthday_simple";



(* In the following, we introduce three lemmas that allow the reduction
   of the first refinement condition to simplified version above.

   First: syntactic precondition over leagal states implies semantic
   precondition for AddBirthday1: *)
zgoal thy 
"BirthdayBook1 /\\(!i: #1..hwm. name? ~= (names %^ i)) =+=> pre AddBirthday1";
(* elementary Z-logical massage *)
by(stripS_tac 1);
by(intro_pre_tac [AddBirthday1_def] 1);
by(asm_simp_tac (simpset() addsimps [DECL_def, DELTA_def]) 1);
(* split declarations from boby ... *)
br conjI 1;
(* take the prescribed successor state and propagate it in proof *)
by(REPEAT (rtac conjI 2 ORELSE rtac refl 2));

(* prove that the successor state fulfills state invariant *)
by(full_expand_schema_tac BirthdayBook1_def 1);
auto(); (*do your best to make it simpler *)
(* auto reduces the proof to a "proof by contradiction" scheme ...
   Mostly, it has to do with 

          (names (+) {(hwm + #1, name?)}) %^ i =
          (names (+) {(hwm + #1, name?)}) %^ j;
 
   while we know that names %^ i ~= names %^ j.
   We bring this goal in the end of the assumption list: *)   
by(rotate_tac 1 1);
(* ... and birng away "+ #1" clauses since the library is more
  tuned towards zsuc than to its alternative formulation ... *)
by(asm_full_simp_tac (HOL_ss addsimps [zsuc_simp RS sym]) 1);

(* Now comes the proof idea: We split up a case-distinction tree
   for the cases that i and j refer to the new element ... 
   rotate brings these clauses in front in the assumption list
   and makes them most visible for the rewriter. *)
by(case_tac "i=zsuc hwm" 1);
by(case_tac "j=zsuc hwm" 1);
by(case_tac "j=zsuc hwm" 3);
by(ALLGOALS (rotate_tac ~2));
(* Since we know already that i~=j or
    ! i: #1 .. hwm. name? ~= names %^ i, 
  these four cases can be reduced ad absurdum. *)
auto();
qed "lemma1";


(* Second: Semantic Precondition (abstract operation) implies
   syntactic precondition *)
zgoal thy 
"pre AddBirthday =+=> name? ~: known";
by(stripS_tac 1);
by(elim_pre_tac 1);
by(full_expand_schema_tac AddBirthday_def 1);
auto();
qed "lemma2";


(* Third: Abs-predicate implies this fact over the structure of the state: *) 
(* This is a semantic projector into the predicate part of schema Abs ...  *)
(* (see ZProofUtil) *)

bind_thm("lemma3",get_conj thy "Abs" 1);

(* here comes a structural proof for the first main goal: 
   use the above three Z-lemmas in order to reduce the main goal
   to the simplified version of it above. The technique
   applies the stripS converter to bring Z-lemmas on-thy-fly
   into HOL form and introduce them into the proof by Isabelle
   standard tactics. *)
zgoal thy 
"(%A BirthdayBook @ (%A BirthdayBook1 @(%A name? %: Name@(%A date? %: Date@ \
\      ((pre AddBirthday /\\ Abs)                                           \
\      =+=>                                                                 \
\      (pre AddBirthday1))))                                                \
\ ))";
(* structural normalization *)
by (stripS_tac 1);
by (Step_tac 1);
(* building together lemmas by weakening assumptions
   and reducing conclusions *)
br (stripS lemma1) 1;
br conjI 1;
by (convert2hol_tac [] 1); 
   (* atac should do, but stripS_tac is a bit too hasty... *)
bd (stripS lemma2) 1;
bd (stripS lemma3) 1;
(* simple version achieved; now automation takes over *)
auto();
qed"PO_refine_1_AddBirthday";



zgoal thy 
" (AddBirthday /\\ Abs /\\ AddBirthday1)             \
\ =+=>                                               \
\ (known' = {n. ? i: #1 .. hwm'. n = names' %^ i})";
(* structural normalization ... *)
by(stripS_tac 1);
by (convert2hol_tac [AddBirthday_def,AddBirthday1_def,
                     BirthdayBook_def,BirthdayBook1_def,
                     Abs_def] 1);
by(REPEAT(etac conjE 1));
by(asm_full_simp_tac (HOL_ss addsimps 
                      [Dom_Union,zsuc_simp RS sym]) 1);
(* idea: reason via set extensionality and split equivalence ... *)
br set_ext 1;
by(Simp_tac 1);
br iffI 1;

(* case I: "<=" *)
be disjE 1;
be bexE 2;
by(res_inst_tac [("x","i")] bexI 2);
by(res_inst_tac [("x","zsuc hwm")] bexI 1);
br numb_range_mem 2;
br numb_range_mem_subset2 5; ba 6;
by(ALLGOALS(asm_simp_tac (simpset() addsimps 
                          [in_naturals])));
by(stac override_apply2 1);
(* case I: "=>" *)
be bexE 3;
by(case_tac "i=zsuc hwm" 3);
by(ALLGOALS (rotate_tac ~1));
auto();
qed"lemma4";

zgoal thy 
" (AddBirthday /\\ Abs /\\ AddBirthday1)             \
\ =+=>                                               \
\ (! i: #1 .. hwm'. birthday' %^ (names' %^ i) = dates' %^ i)";
by(stripS_tac 1);
by (convert2hol_tac [AddBirthday_def,AddBirthday1_def,
                     BirthdayBook_def,BirthdayBook1_def,
                     Abs_def] 1);
by(REPEAT(etac conjE 1));
by(asm_full_simp_tac (HOL_ss addsimps 
                      [Dom_Union,zsuc_simp RS sym]) 1);
by(case_tac "i=zsuc hwm" 1);
auto();
by(stac dom_insert_apply 1);
auto();
qed"lemma5";


zgoal thy 
"(%A BirthdayBook @ (%A BirthdayBook1 @  (%A BirthdayBook1' @  \
\  (%A name? %: Name @ (%A date? %: Date @                     \
\      ((pre AddBirthday /\\ Abs /\\ AddBirthday1)             \
\       =+=>                                                   \
\      (%E BirthdayBook' @ Abs' /\\ AddBirthday))              \
\ )))))";

by(stripS_tac 1);
by(Step_tac 1);
by(elim_pre_tac 1);
by(intro_sch_ex_tac 1);
br refl 2;
by(HINT "BirthdayBook(birthday',known')" (K all_tac) 2); ba 2;back();
by(full_expand_schema_tac AddBirthday_def 2);
bd DECL_D1 2;
by (convert2hol_tac [] 2);
br conjI 1;
ba 2;
by(expand_schema_tac Abs_def 1);
br DECL_I 1;

by(full_expand_schema_tac Abs_def 1);
by(full_expand_schema_tac AddBirthday_def 1);
bd DECL_D1 1;back();
by (convert2hol_tac [] 1);

br conjI 1;
br (stripS lemma4) 1;
br ballI 2;
br (stripS lemma5) 2;
auto();

qed"PO_refine_2_AddBirthday";

(* This concludes the refinement proof based on Forward Simulation
   in the style of Spivey for the standard example Birthdaybook. *)
