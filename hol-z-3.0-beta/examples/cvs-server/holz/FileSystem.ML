(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * FileSystem.ML --- 
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
(* $Id: FileSystem.ML 6746 2007-08-03 07:25:55Z brucker $ *)

open FileSystem;

toToplevel axdefs;
toToplevel schemes;

(* abbreviations *)
val isin_def     = X_isdirin__axdef4;
val isdirin_def  = X_isdirin__axdef5;
val isfilein_def = X_isdirin__axdef6;


(* ******************************************************************** *)
(*  									*)
(* 	Miscellaneous   						*)
(*  									*)
(*  ******************************************************************* *)


goalw thy [rel_def]
" !!y. [| f : A <--> B; x : dom f |]  ==> x : A";
auto();
qed"dom_rel";
goalw thy [rel_def]
" !!y. [| f : A <--> B; x : ran f |]  ==> x : B";
auto();
qed"ran_rel";


goalw thy [partial_func_def,rel_def]
" !!y. [| f : A -|-> B; x : dom f |]  ==> x : A";
auto();
qed"dom_pfun";
goalw thy [partial_func_def,rel_def]
" !!y. [| f : A -|-> B; x : ran f |]  ==> x : B";
auto();
qed"ran_pfun";


(* lemmas on dom                           *)
(* especcially good for Definedness Proofs *)


goalw thy []
" !!x. [| f : A ---> B ; x : A |]  ==> x : dom f";
auto();
qed"tfun_dom";

goalw thy []
" !!x y. [| g : A ---> B ; (x,y) : g |]  ==> y : B";
by(convert2hol_tac [total_func_def, partial_func_def, rel_def] 1);
auto();
qed"tfun_snd";

goalw thy [rel_def]
" !!y. [| f : A -|-> B ; (x,y) : f |]  ==> y : B";
by(convert2hol_tac [partial_func_def, rel_def] 1);
auto();
qed"pfun_snd";

goalw thy [rel_def]
" !!y. [| f : A -|-> B ; x : f |]  ==> snd x : B";
by(convert2hol_tac [partial_func_def, rel_def] 1);
auto();
qed"pfun_snd_expl";


goalw thy [] "!! f x. [| f : A ---> B; x : A |] ==> (f %^ x) : B";
br Rel_Apply_in_Partial_Ran2 1;
by(res_inst_tac [("t","dom f"), ("s","A")] subst 2);
ba 3;
by(convert2hol_tac [total_func_def]1); 
be conjE 1;
ba 1;
by(convert2hol_tac [total_func_def]1); 
qed "totalApplDom";


goalw thy [] "!! f x y. [| f : A ---> B ---> C; x : A; y : B |] ==> f %^ x %^ y : C";
by(res_inst_tac [("f","f %^ x"),("A","B")] totalApplDom 1);
ba 2;
br totalApplDom 1;
ba 1;
ba 1;
qed "totalApplDom2Levels";

goalw thy [] "!! f x y. [| f : A ---> B ---> C; x : A; y : B ; q = (f %^ x %^ y)|] ==> q : C";
by(res_inst_tac [("t","q"), ("s","f %^ x %^ y")] subst 1);
br sym 1;
ba 1;
br totalApplDom2Levels 1;
auto();
qed "totalApplDom2Levels2";



goalw thy [] "!! f x y. [| f : A ---> B ---> %P C; x : A; y : B |] ==> f %^ x %^ y <= C";
br PowD 1;
br totalApplDom2Levels 1;
auto();
qed "PowTotalApplDom2Levels";


goalw thy [] "!! a b. [| f: A ---> B ---> C ; a : A; b : B |] ==> b: dom (f %^ a)";
br tfun_dom 1;
br totalApplDom 1;
ba 1;
ba 1;
ba 1;
qed"tfun_ApplDom";


(* ******************************************************************** *)
(*  									*)
(* 	Basic Rules on Path						*)
(*  									*)
(*  ******************************************************************* *)

goal thy "%< x::Name %> : seq Name";
auto();
qed "single_is_path";

goal thy "%< x::Name,y %> : seq Name";
auto();
qed "double_is_path";

goalw thy [Path_def]"!!f. f : Path ==> f : seq Name";
ba 1;
qed "Path_rule";

goalw thy [Path_def]" %<%> : seq Name";
auto();
qed "mt_is_path";

goalw thy [Path_def,FILESYS_TAB_def,partial_func_def]
"!!f.[| s : FILESYS_TAB; x:dom s |]==> x : seq Name";
by(Asm_full_simp_tac 1);
br dom_rel 1;
auto();
qed "dom_FILESYSTAB_is_seq_Name";

Addsimps[mt_is_path,single_is_path,double_is_path,
         Path_rule,dom_FILESYSTAB_is_seq_Name];

goalw thy [Path_def]"!!f g . [|f : Path; g : Path |] ==> f %&^ g : Path";
auto();
qed"cat_path";

goalw thy [Path_def]"!! x. x : Name ==> %< x %> : Path";
auto();
qed "elem_path";



(* lemmas on Path*)

val [k] = goalw thy [] "x : Name ==> ((%< x, y %>) =  (%< x %> %&^ %< y %>))";
(* by(HINT "x : Name" (K all_tac) 1); *)
by(stac (k RS insertseq_concat) 1);
by(stac concatseq_emptyseq 3);
auto();
by(res_inst_tac [("Y","Name")] Seq_Subset 1);
auto();
qed"twoElemPath";

goalw thy [] "!!x. [| x : Name; y : Name |] ==> ((%< x, y %>) =  (%< x %> %&^ %< y %>))";
by(asm_simp_tac (simpset() addsimps [insertseq_concat,single_is_path RS concatseq_emptyseq]) 1);
qed"twoElemPathAssum";

goalw thy [] "!!x y.[| x: Name ; y : Name |] ==> (%<x%> %&^ %<y%>) : seq Name";
auto();

goalw thy [] "!!x y. (%<x%> %&^ %<y%>) : seq Name";
auto();
qed "catName";


goalw thy [] "!!p y. [| p : seq Name |] ==> (p %&^ %<y%>) : seq Name";
auto();
qed"catPathName";

goalw thy [] "!!p. (%<p%>) : seq Name";
auto();
qed"NameSeqName";



(* lemma also for concat *)
bind_thm("sharpSameConcatseqEq",(same_concatseq_eq RS mp));



(* ******************************************************************** *)
(*  									*)
(* 	Relations between isin, isfilein, isdirin			*)
(*  									*)
(*  ******************************************************************* *)

bind_thm("isin_if_isdirin", (isdirin_def RS iffD1) RS conjunct1);
bind_thm("isin_if_isfilein", (isfilein_def RS iffD1) RS conjunct1);
bind_thm("not_isdirin_if_isfilein",(isfilein_def RS iffD1) RS conjunct2);

goal thy 
"!!p. [| f : Path -|-> Data %+ Unit; p : Path; ?X p |] ==> \
\  p : dom f";
br (isin_if_isdirin RSN (3, isin_def RS iffD1)) 1; ba 5;
auto();
qed "in_dom_if_isdirin";
(* warum klappt 
    asm_full_simplify (HOL_ss addsimps [isin_def]) 
                      (isin_if_isdirin RSN (3, isin_def RS iffD1));

   ???  Vermutlich wg. meta-variablen.
 *)


goal thy 
"!!p. [| f : Path -|-> Data %+ Unit; p : Path; ?X p |] ==> \
\  p : dom f";
by(res_inst_tac [("s","?Y"),("t","p : dom f")] subst 1);
br isin_def 1;ba 1;ba 1;
ba 1;
qed"in_dom_if_isin";


goal thy 
"!!p. [| f : Path -|-> Data %+ Unit; p : Path; ?X p |] ==> \
\  p : dom f";
br (isin_if_isfilein RSN (3, isin_def RS iffD1)) 1; ba 5;
auto();
qed "in_dom_if_isfilein";

(*Nuetzlich : ein splitter: wenn's im FileSystem ist, ist es
  entweder ein Directory oder ein File *)



(* ******************************************************************** *)
(*  									*)
(* 	Lemmas over prefix-closedness in FileSystems			*)
(*  									*)
(*  ******************************************************************* *)


zgoalw FileSystem.thy [Path_def] 
"FileSystem /\\ (p:Path) /\\ (p %&^ %<x%> : dom files) =+=> p : dom files";
by (intro_schema_tac 1);
by (step_tac HOL_cs 1);
by (forward_tac [stripS (get_conj thy "FileSystem" 1)] 1); ba 1;

by (HINT "p %&^ %< x %> ~= %<%>" (K all_tac) 1);
by (stac concatseq_is_empty 2); ba 2;by(rtac single_is_path 2);
by (Simp_tac 2);

by (rotate_tac ~1 1);by (Asm_full_simp_tac 1);
(*be conjE 1;*)

by (forward_tac [stripS (get_decl thy "FileSystem" 1)] 1); 
by (asm_full_simp_tac (HOL_ss addsimps [FILESYS_TAB_def]) 1);

be in_dom_if_isdirin 1;

by (asm_simp_tac (HOL_ss addsimps [Path_def]) 1);
by (res_inst_tac [("t","p")] subst 1);ba 2;
br refl 1;
qed "prefix_closedness";

(* fehlt: front_snoc mp, 
   a^&b : seq M = (a : seq M & b : seq M)
 *)


goal Arith.thy "(A ~= {}) = (? x. x : A)";
auto();
val neqset_exists = result();


zgoalw FileSystem.thy [] 
"FileSystem /\\ (dom files ~= {}) =+=> %<%> : dom files";
by (stripS_tac 1);
by (asm_full_simp_tac (HOL_ss addsimps [neqset_exists]) 1);
be conjE 1; be exE 1;
br mp 1; ba 2;back(); (* back(); *)
by (forward_tac[stripS(get_decl thy "FileSystem" 1)]1);
bd dom_FILESYSTAB_is_seq_Name 1;ba 1;
by (eres_inst_tac [("s","x")] seq_snocinduct 1);
auto();
by (forward_tac[stripS(get_conj thy "FileSystem" 1)]1);
br pair_rel_dom 1; ba 1; back();
auto();
by (HINT "s : dom files" (K all_tac) 1);
by (Fast_tac 1);
by (forward_tac[stripS(get_decl thy "FileSystem" 1)]1);
br (isin_def RS iffD1) 1;
br ((isdirin_def RS iffD1) RS conjunct1) 3;
by (fold_goals_tac [Path_def,FILESYS_TAB_def]);
by (ALLGOALS(Asm_simp_tac ));
qed "nonempty_FileSystem_contains_root";


(*
zgoalw thy [] "p: Path =+=> p = %<%> \\/ (front p) : Path";
by (stripS_tac 1);
by (rewrite_goals_tac [Path_def]);
by (eres_inst_tac [("s","p")] seq_snocinduct 1);
auto();
qed "front_p_is_path";
*)

zgoalw thy [] "p: Path /\\ p ~= %<%> =+=> (front p) : Path";
by (stripS_tac 1);
by (rewrite_goals_tac [Path_def]);
auto();
qed "front_p_is_path";

(* we keep this for historical reasons... *)
zgoalw thy [] "FileSystem /\\ Q:FILESYS_TAB /\\  p: dom (files (+) Q) =+=> p : Path";
by (stripS_tac 1);
by (full_expand_schema_tac FileSystem_def 1);
auto();
by (rewrite_goals_tac [FILESYS_TAB_def]);
br dom_pfun 1;
by (res_inst_tac [("f","files")] dom_pfun 3);
by (thin_tac "dom files = dom attributes" 4);
auto();
qed "path_in_files_override";

(* lemmas about prefixes and cutPath *)
goalw thy [prefixseq_def] "!!x. x : seq X ==> x prefix x";
auto();
by (res_inst_tac [("x","%<%>")] bexI 1);
auto();
qed"prefix_refl";

goalw thy [prefixseq_def] 
"!!x. [| x : seq X; y : seq X; z : seq X; x prefix y |] ==> (z %&^ x) prefix (z %&^ y)";
auto();
by (res_inst_tac [("x","v")] bexI 1);
by (auto_tac (claset(), simpset() addsimps [ concatseq_assoc]));
qed"prefix_left_concat";

goalw thy [prefixseq_def] 
"!!x. [| x : seq X; y : seq X |] ==> x prefix (x %&^ y)";
by(Simp_tac 1);
br bexI 1;
auto();
qed"prefix_right_concat";
Addsimps[prefix_refl,prefix_left_concat,prefix_right_concat];

goalw thy [] 
"!!x. x : seq X ==> (front x) prefix x";
by(res_inst_tac [("s","x")] seq_snocinduct 1);
auto();
qed"front_prefix";


goalw thy [prefixseq_def] "!!x. [| x:Path; y:Path; \
			  \ (cutPath %^ (x, y)): Path |] ==>  y prefix x";
by (Step_tac 1);
br bexI 1;
br ((cutPath_axdef2 RS iffD1) RS sym) 1;
by (ALLGOALS (asm_full_simp_tac (HOL_ss addsimps [Path_def])));
by (Asm_simp_tac 1);
qed "cutPath_prefix";



(* ******************************************************************** *)
(*  									*)
(* 	Lemmas especcially good for Definedness Proofs  		*)
(*  									*)
(*  ******************************************************************* *)

(* lemma on FileSystem-files - dom*)

zgoalw FileSystem.thy []  "(FileSystem /\\ p : dom files) =+=> p : dom attributes";
by(convert2hol_tac [FileSystem_def] 1);
auto();
by(res_inst_tac [("s","dom aa"),("t","dom a")] subst 1);
ba 1;
br pair_rel_dom 1;ba 1;
qed "domAttr_domFiles";



zgoalw FileSystem.thy [Path_def] 
"FileSystem /\\ (p:Path) /\\ (x : Name) /\\ (y : Name) /\\ (p %&^ %<x, y%> : dom files) =+=> p : dom files";
by (intro_schema_tac 1);
by (step_tac HOL_cs 1);
by (forward_tac [stripS (get_conj thy "FileSystem" 1)] 1); ba 1;
br (stripS prefix_closedness) 1;
br conjI 1;br conjI 1;
ba 1;by(convert2hol_tac [Path_def] 1);
br (stripS prefix_closedness) 1;
br conjI 1;br conjI 1;
ba 1;
by(res_inst_tac [("t","?A %&^ ?B")] subst 2);
ba 3;
by(res_inst_tac [("t","p %&^ ?A %&^ ?B"),("s","p %&^ (?A %&^ ?B)")] subst 2);
by(asm_simp_tac (simpset() addsimps [concatseq_assoc]) 2);
by(res_inst_tac [("t","?Y")] subst 2);
br sym 2;
br sharpSameConcatseqEq 2;
ba 2;
br twoElemPath 4;
ba 4;

br insertseq_seq_pred 2;
ba 3;
br catName 3;
by(rewrite_goals_tac[Path_def]);
br catPathName 1;
ba 1;
br NameSeqName 1;
qed"FSminus2Path";

