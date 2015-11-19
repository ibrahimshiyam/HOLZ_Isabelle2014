(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * Prelude.ML --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 2003-2007 ETH Zurich, Switzerland
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
(* $Id: Prelude.ML 6743 2007-08-03 06:39:08Z brucker $ *)

(*
(* TODO: move to library. *)


(* Why the Heck did no one prove this so far ?!?!                                *)
(* This is a foundational rule for core HOL constructs, and no one proved it ... *)

goal HOL.thy "!!P. [| if A then B else C; [|A;B|] ==> P; [|~A;C|] ==> P |] ==> P";
by(case_tac "A" 1);
auto();
qed"ifE";

goal HOL.thy "!!P. [| x = (if A then B else C); [|A;x=B|] ==> P; [|~A;x=C|] ==> P |] ==> P";
by(case_tac "A" 1);
auto();
qed"if_eqL_E";

goal HOL.thy "!!P. [| (if A then B else C) = x; [|A;B=x|] ==> P; [|~A;C=x|] ==> P |] ==> P";
by(case_tac "A" 1);
auto();
qed"if_eqR_E";

goal HOL.thy "!!P. [| Q(if A then B else C); [|A;Q B|] ==> P; [|~A;Q C|] ==> P |] ==> P";
by(case_tac "A" 1);
by(ALLGOALS(rotate_tac ~1));
by(ALLGOALS(Asm_full_simp_tac));
qed"if_general_E";

goal HOL.thy "!!A. [| A; B |] ==> if A then B else C";
auto();
qed"ifI1";

goal HOL.thy "!!A. [| ~A; C |] ==> if A then B else C";
auto();
qed"ifI2";

goal HOL.thy "!!A. [| A; x = B |] ==> x = (if A then B else C)";
auto();
qed"if_eqL_I1";

goal HOL.thy "!!A. [| A; B = x |] ==> (if A then B else C) = x";
auto();
qed"if_eqR_I1";

goal HOL.thy "!!A. [| ~A; x = C |] ==> x = (if A then B else C)";
auto();
qed"if_eqL_I2";

goal HOL.thy "!!A. [| ~A; C = x |] ==> (if A then B else C) = x";
auto();
qed"if_eqR_I2";

goal HOL.thy "!!A. [| A; P B |] ==> P (if A then B else C)";
auto();
qed"if_general_I1";

goal HOL.thy "!!A. [| ~A; P C |] ==> P (if A then B else C)";
auto();
qed"if_general_I2";


(* renaming table ... *)
val oplus_def       = func_overrid_def;
val oplus_I2= overridI2;
val oplus_I1= overridI1;
val oplus_CI= overridCI;
val oplus_single   = func_overrid_singleton;
val oplus_res_right= Overrid_Restr_right;
val oplus_res_left = Overrid_Restr_left;
val oplus_Inter    = Overrid_Inter;
val oplus_idem     = Overrid_Idempotent;
val oplus_mt_right = Overrid_Empty_right;
val oplus_mt_left  = Overrid_Empty_left;
val oplus_Domain   = Overrid_Domain;
val oplus_comp     = Overrid_Compose;
val oplus_fpfun    = fin_part_fun_override;
val oplus_pfunI    = Partial_Func_overrid_Distr;

goalw Z.thy [total_func_def,partial_func_def,rel_def]
"!!z. [| x:A;y:B |] ==> {(x,y)} : A -|-> B";
auto();
qed"pair_pfunI";


goalw Z.thy [oplus_def,dom_substr_def,rel_apply_def]
"!!z. z : dom S ==> (R (+) S) %^ z = S %^ z";
auto();
qed"oplus_apply1";
val oplus_apply2    = override_apply2;
val oplus_non_apply = override_non_apply;
val oplus_apply     = override_apply;

Addsimps[oplus_apply1,oplus_apply2,pair_pfunI];


goalw Z.thy [oplus_def,dom_substr_def,rel_apply_def]
"!!z. x = z ==> (R (+) {(z, y)}) %^ x = y";
auto();
qed"oplus_by_pair_apply1";

val oplus_by_pair_apply2 = override_non_apply;
Addsimps[oplus_by_pair_apply1,oplus_by_pair_apply2];


val tfun_implies_pfun = total_func_implies_Pfun;
val beta_apply_pfun   = pair_mem_apply RS mp RS mp;
val beta_apply_tfun   = tfun_implies_pfun RS beta_apply_pfun;

val pfun_apply = Rel_Apply_in_Partial_Ran2;

goal Z.thy "!!F. [| F : X ---> Y; x : X |] ==> F %^ x : Y";
by(asm_full_simp_tac (HOL_ss addsimps [total_func_simp])1);
be conjE 1;
br pfun_apply 1;
auto();
qed"tfun_apply";
Addsimps [tfun_apply];

val Rel_Apply_in_total_range = tfun_apply;
val pfun_def = partial_func_def;
val tfun_def = total_func_def;


goalw Z.thy [] "!!f. [| x: B %x C |] ==> EX y z. x = (y,z)";
auto();
qed "pair_exhaust";


goalw Z.thy [] "!!f. [| f : A ---> B %x C; x : A |] ==> fst(f %^ x) : B";
bd tfun_apply 1; ba 1;
by (forward_tac  [pair_exhaust] 1);
be exE 1; be exE 1;
by(rotate_tac ~1 1);
by(Asm_full_simp_tac 1);
qed"tfun_apply_fst";


goalw Z.thy [] "!!f. [| f : A ---> B %x C; x : A |] ==> snd(f %^ x) : C";
bd tfun_apply 1; ba 1;
by (forward_tac  [pair_exhaust] 1);
be exE 1; be exE 1;
by(rotate_tac ~1 1);
by(Asm_full_simp_tac 1);
qed"tfun_apply_snd";


goalw Z.thy [] "!!f. [| f : A -|-> B %x C; x : dom f |] ==> fst(f %^ x) : B";
bd pfun_apply 1; ba 1;
by (forward_tac  [pair_exhaust] 1);
be exE 1; be exE 1;
by(rotate_tac ~1 1);
by(Asm_full_simp_tac 1);
qed"pfun_apply_fst";


goalw Z.thy [] "!!f. [| f : A -|-> B %x C; x : dom f |] ==> snd(f %^ x) : C";
bd pfun_apply 1; ba 1;
by (forward_tac  [pair_exhaust] 1);
be exE 1; be exE 1;
by(rotate_tac ~1 1);
by(Asm_full_simp_tac 1);
qed"pfun_apply_snd";



val prems = goalw ZFun.thy [Pow_def]
"!!f. [| f : %P (a %x b); b <= c |] ==> f : %P (a %x c)";
auto();
qed"Pow_right_subset";

val prems = goalw ZFun.thy [Pow_def]
"!!f. [| f : %P (a %x b); a <= c |] ==> f : %P (c %x b)";
auto();
qed"Pow_left_subset";
Addsimps[Pow_right_subset,Pow_left_subset]; (* really *)
AddSEs[Pow_right_subset,Pow_left_subset]; (* really *)


val prems = goalw ZFun.thy [rel_def]
"!!f. [| f : a <--> b; b <= c |] ==> f : a <--> c";
auto();
qed"rel_ran_subset";

val prems = goalw ZFun.thy [rel_def]
"!!f. [| f : a <--> c; a <= b |] ==> f : b <--> c";
auto();
qed"rel_dom_subset";
AddSEs[rel_ran_subset,rel_dom_subset];

val partial_fun_dom_subset = Partial_Func_Subset;

val prems = goalw ZFun.thy [pfun_def]
"!!f. [| f : a -|-> b; b <= c |] ==> f : a -|-> c";
auto();
qed"partial_fun_ran_subset";
AddSEs[partial_fun_dom_subset,partial_fun_ran_subset];



val [prem1,prem2,prem3] = goal ZInteg.thy
"[|x : %N ; !! x.[| x:%N; P(x) |] ==> P(x + $#1) ; P($#0)|] ==> P(x)";
by(cut_facts_tac [prem1] 1);
bd (nat2naturals RS iffD2) 1;
be exE 1;
by(hyp_subst_tac 1);
by(induct_tac "xnat" 1);
br prem3 1;
by(res_inst_tac [("P","P")] subst 1);
br prem2 2; ba 3;
by(res_inst_tac [("s","$# (xnat + 1)"),("t","$# xnat + $# 1")] subst 1);
br znat_add 1;
by (ALLGOALS Simp_tac);
qed "naturals_induct";


val prems = goalw Z.thy []
"!!n. [| n : %N ; n~= #0 |] ==> EX m. (m : %N & n = m + #1)";
by(asm_full_simp_tac (HOL_ss addsimps [nat2naturals RS sym]) 1);
auto();
by(HINT "$i #0 = 0" (K all_tac) 1);
by(rotate_tac ~1 1);
auto();
bd less_eq_Suc_add 1;
by(Asm_full_simp_tac 1);
be exE 1;
by(hyp_subst_tac 1);
by(res_inst_tac [("x","$# k")] exI 1);
auto();
by(HINT "#1 = $# 1" (K all_tac) 1);
by(res_inst_tac [("t","#1")] subst 1);
by(stac ((zsuc_def RS meta_eq_to_obj_eq) RS sym) 2);
auto();
by(res_inst_tac [("t","#0")] subst 1);
by(stac zint_inverse  2);
br refl 2;
auto();
qed"naturals_shift";


(* <<<<<<<<<<<<<<<<<<<<<<<< TODO: move to library. *)

(* Must be exported in HOL-Z !!! *)

val bla' = prove_goalw ZPure.thy [split_def,SB_def]
"!!f . (SBinder a f) x ==>  (? y z. f y z)"
(fn _ => [auto_tac(claset(),simpset())]);

val bla0' = prove_goalw ZPure.thy [SB0_def]
"!!f. (SBinder0 a f) x ==> f x"
(fn _ => [auto_tac(claset(),simpset())]);


val exE1 = read_instantiate_sg (sign_of ZPure.thy)
                               [("P","%y. ? z. SBinder0 ?a (?f y) z")] exE;
val exE2 = read_instantiate_sg (sign_of ZPure.thy)
                               [("P","%y. SBinder0 ?a ?f y")] exE;
val exE3 = read_instantiate_sg (sign_of ZPure.thy)
                               [("P","%y. ? z. SBinder ?a (?f y) z")] exE;
val exE4 = read_instantiate_sg (sign_of ZPure.thy)
                               [("P","%y. SBinder ?a ?f y")] exE;


fun bind_elim_tac i = (STATE (fn top =>
    let val termS = Logic.strip_assums_hyp(nth_elem(i-1,prems_of top));
        fun b str = EVERY[dtac bla' i,prune_params_tac,
                          (etac exE1 i) ORELSE (etac exE3 i),
                          rename_tac str i,
                          (etac exE2 i) ORELSE (etac exE4 i)]
        fun b0 str= EVERY[dtac bla0' i, rename_tac str i]
        fun ex (x::R) =  case x of
            Const("Trueprop",_) $ (Const ("ZPure.SBinder",_) $S$_$_)
                => (b(String2string S)) THEN (bind_elim_tac i)
           |Const("Trueprop",_) $ (Const ("ZPure.SBinder0",_)$S$_$_)
                => b0(String2string S)
           | _ => ex R;
    in  ex termS
    end));


val elim_sch_ex_tac    = ((etac sbexE2) ORELSE' (etac sbexE1)) THEN' bind_elim_tac;




(* move to library ... *)

val TC = ref ([]:thm list);


goal Z.thy "!!s. s == UNIV ==> x : s";
auto();
qed"def_UNIV";


fun Add_Univdef_TC tc = (TC:= tc @ (!TC));
fun Add_Univrule_TC tc = (TC := (map (fn h => h RS def_UNIV) tc) @ (!TC));


Add_Univdef_TC[UNIV_I];
Add_Univrule_TC[get_thm ZSeqtoList.thy "extraction_def"];



goalw Z.thy [] "!!x. [|x:dom X; x:dom Y|] ==> x : dom (X (+) Y)";
by(asm_simp_tac (simpset() addsimps [Overrid_Domain]) 1);
qed"dom_oplus_I";

goalw Z.thy [] "!!x. [|x:dom X; x:dom Y|] ==> x : dom (X Un Y)";
by(asm_simp_tac (simpset() addsimps [Dom_Union]) 1);
qed"dom_Un_I";(* not analytic ! *)

goalw Z.thy [] "!!x. [|x = fst a|] ==> x : dom (insert a Y)";
by(asm_simp_tac (simpset() addsimps [Dom_Insert]) 1);
qed"dom_insert_I1";

goalw Z.thy [] "!!x. [|x:dom Y|] ==> x : dom (insert a Y)";
by(asm_simp_tac (simpset() addsimps [Dom_Insert]) 1);
qed"dom_insert_I2";

goalw Z.thy [] "!!x. [|x:X; x:dom Y|] ==> x : dom (X <: Y)";
by(asm_simp_tac (simpset() addsimps [Dom_Restrict]) 1);
qed"dom_dres_I";

goalw Z.thy [] "!!x. [|x:A|] ==> x : dom (Lambda A f)";
by(asm_simp_tac (simpset() addsimps [Lambda_dom]) 1);
qed"dom_LambdaI";

goalw Z.thy [] "!!x. [|x = a|] ==> x : dom (%[ a %])";
by(asm_simp_tac (simpset() addsimps [DomBagSingleton]) 1);
qed"dom_BagSingleton_I";



val dom_infers  = [dom_oplus_I,dom_Un_I,dom_insert_I1,dom_insert_I2,
                   dom_dres_I,dom_BagSingleton_I];


val type_infers = [SigmaI,subsetI RS PowI,
                   pair_rel_dom_fst,pair_rel_dom];

val unsafe_type_infers = [];

TC:= dom_infers @ type_infers @ (!TC);


fun fun_type_infers axdefs =
    (mapfilter (fn x => Some(x RS tfun_apply_fst) handle THM _ => None) axdefs) @
    (mapfilter (fn x => Some(x RS tfun_apply_snd) handle THM _ => None) axdefs) @
    (mapfilter (fn x => Some(x RS tfun_apply) handle THM _ => None) axdefs) @
    (mapfilter (fn x => Some(x RS Dom_Partial_Fin) handle THM _ => None) axdefs) @
    (mapfilter (fn x => Some(x RS pfun_apply_fst) handle THM _ => None) axdefs) @
    (mapfilter (fn x => Some(x RS pfun_apply_snd) handle THM _ => None) axdefs) @
    (mapfilter (fn x => Some(x RS pfun_apply) handle THM _ => None) axdefs);




fun Add_axdefs_TC axdef =
    let fun flat_conj m = flat (mapfilter (
                                fn x            =>Some(flat_conj[x RS conjunct1,
                                                                 x RS conjunct2])
                                   handle THM _ =>Some[x]) m)
        fun closure m   = m @ (fun_type_infers m)
    in  TC := (flat(mapfilter(fn x => Some(closure(flat_conj[x RS DECL_D1]))
                              handle THM _ => None)
                              axdef))
               @ (!TC)
    end;

(*
fun Add_schemadefs_TC schdef = ???
 *)





fun tc_tac n = asm_simp_tac (prod_ss addsimps !TC) n;
fun unsafe_tc_tac n = fast_tac (HOL_cs addSIs (!TC)) n; (* untested ! *)


(* new short-cuts corresponding to rtac, dtac, etac, stac:
   perform the Z-specific stripping of quantifiers and
   try to eliminate resulting type-constraints.
   (does not unify, i.e. preserves meta-variables); *)

fun zstac S n = let val thm = stripS S;
                    val m = length(prems_of thm)
                    val TC_tac = foldr (op THEN)
                                 (map tc_tac ((n+m-1) downto n), all_tac)
                in  (stac thm n) THEN TC_tac end;


fun zftac S n = let val thm = stripS S;
                    val m = length(prems_of thm)
                    val TC_tac = foldr (op THEN)
                                 (map tc_tac ((n+m-1) downto n), all_tac)
                in  (forward_tac [thm] n) THEN TC_tac end;


fun zrtac S n = let val thm = stripS S;
                    val m = length(prems_of thm)
                    val TC_tac = foldr (op THEN)
                                 (map tc_tac ((n+m-1) downto n), all_tac)
                in  (rtac thm n) THEN TC_tac end;

fun zetac S n = let val thm = stripS S;
                    val m = length(prems_of thm)
                    val TC_tac = foldr (op THEN)
                                 (map tc_tac ((n+m-1) downto n), all_tac)
                in  (etac thm n) THEN TC_tac end;

fun zdtac S n = let val thm = stripS S;
                    val m = length(prems_of thm)
                    val TC_tac = foldr (op THEN)
                                 (map tc_tac ((n+m-1) downto n), all_tac)
                in  (dtac thm n) THEN TC_tac end;


(* <<<<<<<<<<<<<<<<<<<<<<<<< Must be exported in HOL-Z !!! *)

*)
