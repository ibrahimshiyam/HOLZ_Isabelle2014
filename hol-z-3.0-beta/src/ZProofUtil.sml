(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ZProofUtil.sml --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 1998-2000 University Bremen, Germany
 *               2000-2003 University Freiburg, Germany
 *               2003-2007 ETH Zurich, Switzerland
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
(* $Id: ZProofUtil.sml 6729 2007-08-03 05:25:17Z brucker $ *)

infix ZRS;
structure ZProofUtil 
(*
:
  sig
    val toToplevel     : (string * thm) list -> unit
    (* enters the scheme list of a theory into a collection
       of definitions in the SML-toplevel. Works for axdefs too. *)
    val open_schemes   : (string * thm) list -> unit
    (* outdated ! same as toToplevel *)

    type zproof
    val restore_zproof : zproof -> thm list
    val save_zproof    : unit -> zproof

    val zgoal          : ZTheory.ztheory -> string -> thm list
    val zgoalw         : ZTheory.ztheory -> thm list -> string -> thm list
    val prove_zgoalw   : ZTheory.ztheory -> thm list
                          -> string -> (thm list -> tactic list) -> thm


    (* ******************************************************************* *)
    (* Forward Proof                                                       *)
    (* ******************************************************************* *)
    val lift               : thm -> int -> thm
    (* converts a boolean equivalence into an equivalence over
       schemas built over this boolean equivalence *)

    val strip_turnstyle    : thm -> thm
    (* erases topmost turnstyle *)

    val strip_sch_ball     : thm -> thm
    (* erases topmost schema quantifier %A x: A @ P x*)

    val strip_ball         : thm -> thm
    (* erases topmost bounded quantifier ! x: A. P x *)

    val strip_imp          : thm -> thm
    (* erases topmost implication *)

    val stripS             : thm -> thm
    (* erases topmost combination of operators as above *)

    val Z2HOL_ss           : simpset 
    (* blows away all semantic markups of Z - and converts
       a thm or proofstate into pure HOL. This may help
       Isabelles decision procedures, but at the price of a
       blow-up of the pretty-printed presentation. *)

    val atomize_Z          : thm -> thm list
    (* decomposes a Z-expression --- such as axdefs ---
       into all its parts and strips off Z-qunatifiers. *)
       
    val prep_axdefs        : string * thm -> unit
    (* atomizes an axdef and prepares a setup for the
       theory database. Attempts to add all rules in global
       simpset. *)


    (* ******************************************************************* *)
    (* Backward Proof                                                      *)
    (* ******************************************************************* *)
    val intro_schema_tac   : int -> tactic
    (* pseudo introduction rule of a schema-turnstyle or
       a schema equality; in backwards reasoning, it eliminates
       all topmost schema-binders in equalities and turnsyles
       and replaces them by paramaters, that were suitably renamed *)
    val intro_sch_all_tac  : int -> tactic
    (* pseudo introduction rule of a schema-univ. quantifier %A S @ P;
       in backwards reasoning, it eliminates a topmost schema-quantor
       and replaces them by paramaters, that were suitably renamed *)
    val intro_sch_ex_tac   : int -> tactic
    (* pseudo introduction rule of a schema-univ. quantifier %E S @ P;
       in backwards reasoning, it eliminates a topmost schema-quantor
       and replaces them by paramaters, that were suitably renamed *)
    val intro_pre_tac      : thm list -> int -> tactic
    (* pseudo introduction rule of a schema-univ. quantifier pre S;
       analogously to intro_sch_ex_tac. The list is used to provide
       the definition of S. *)
    val intro_sch_ex1_tac  : int -> tactic
    (* pseudo introduction rule of a schema-univ. quantifier %E1 S @ P;
       in backwards reasoning, it eliminates a topmost schema-quantor
       and replaces them by paramaters, that were suitably renamed *)

    val elim_sch_ex_tac  : int -> tactic
    (* pseudo elimination rule of a schema-univ. quantifier %E1 S @ P;
       in backwards reasoning, it eliminates a topmost schema-quantor
       and replaces them by paramaters, that were suitably renamed 
       --- known Bug : unfortunately not completely. *)

    val elim_pre_tac       : int -> tactic
    (* pseudo elimination tactic for pre schema. Corresponds to
       an ex-elimination. *)

    val stripS_tac         : int -> tactic
    (* generalization of HOL's strip_tac - removes leading turnstyles, 
       universal schema, bounded and unbounded quantifiers and 
       implications ... *)

    val expand_schema_tac  : thm list -> int -> tactic
    (* expands a schema definition within a proof goal *)
    val full_expand_schema_tac  : thm list -> int -> tactic
    (* expands a schema definition within a proof goal 
       (assumptions inclusive) *)
    val convert2hol_tac    : thm list -> int -> tactic
    (* converts a goal into plain HOL - i.e. eliminates
       all ZPure-related operators establishing schema semantics *)


    (* ******************************************************************* *)
    (* Generators for semantic projection lemmas  	         	   *)
    (* ******************************************************************* *)

    val get_decl  : theory -> string -> int -> thm
    (* get_decl thy name n : generates from definition of schema <name>
       (which must be defined in theory <thy> a projection theorem
       of the form "|- name =+=> D", where <D> is the n-th declaration
       in the declaration part of a schema. *)
    val get_conj  : theory -> string -> int -> thm
    (* get_conj thy name n : generates from definition of schema <name>
       (which must be defined in theory <thy> a projection theorem
       of the form "|- name =+=> C", where <C> is the n-th conjunct
       in the body part of a schema. *)

    val tc_tac    : int -> tactic
    (* tactic related to type-checking *)


    val zstac : thm -> int -> tactic
    val zftac : thm -> int -> tactic
    val zrtac : thm -> int -> tactic
    val zetac : thm -> int -> tactic
    val zetac : thm -> int -> tactic

    val ZRS       : thm * thm  -> thm


    (* ******************************************************************* *)
    (* Tactical Combinators for proof-structuring			   *)
    (* ******************************************************************* *)

    val CASE_DIST : string -> int -> tactic
    val FOLD      : string -> thm list -> int -> tactic
    val FOLD_AT   : string -> thm list -> int -> tactic
    val GEN_ALL   : string -> int -> tactic
    val HINT      : string -> (int -> tactic) -> int -> tactic
    val UNFOLD    : string -> thm list -> int -> tactic
    val UNFOLD_AT : string -> thm list -> int -> tactic

    (* ******************************************************************* *)
    (* Z-specific Abbreviations:					   *)
    (* ******************************************************************* *)

    val zbr       : thm -> int -> unit
    val zbd       : thm -> int -> unit
    val zbe       : thm -> int -> unit


    val removeTheta: thm -> thm
    val removeTheta_tac : int -> tactic

    (* ******************************************************************* *)
    (* Tracing and pretty-printing auxilliaries:			   *)
    (* ******************************************************************* *)

    val off       : unit   -> unit
    val on        : unit   -> unit
    val remove_hyps : int  -> tactic

    (* ******************************************************************* *)
    (* Obscure stuff:							   *)
    (* ******************************************************************* *)

    val reset_basezenv : unit -> unit
    val set_basezenv_to_zthy : ZTheory.ztheory -> unit
    
  end 
*)
= struct

local open ZPrelude ZEnv ZTheory in
 
fun set_basezenv_to_zthy zthy = (ZEncoder.ZENV:=get_zenv zthy);
fun reset_basezenv ()         = (ZEncoder.ZENV:=mt_zenv);


fun toIsaName st = 
    let val str' = String.translate 
                    (fn x => if Symbol.is_letdig (str x) 
                             then str x 
                             else "_"^Int.toString(ord(str x))) st
    in if String.isPrefix "_" str' then "X"^str'
       else  str'
    end;




fun toToplevel S = (map (fn (x,y) => bind_thm(toIsaName x, y)) S; ())
val open_schemes = toToplevel (* outdated *)

fun zgoalw thy rths agoal = 
    (let val zenv = !ZEncoder.ZENV
         val _ = (ZEncoder.ZENV:=get_zenv thy)
         val t = goalw_cterm rths (cterm_of(sign_of thy) 
	                             (ZEncoder.schema_read thy agoal))
                 handle ERROR => error(*from type_assign, 
		                         etc via prepare_proof*)
	                          ("The error above occurred for " 
				   ^ quote agoal);
	 val _ = ZEncoder.ZENV:=zenv
     in  t
     end
    );

fun prove_zgoalw thy rths agoal tcl =
    (let val zenv = !ZEncoder.ZENV;
         val _ = ZEncoder.ZENV:=get_zenv thy;
         val t = prove_goalw_cterm rths 
                       (cterm_of(sign_of thy)
     				(ZEncoder.schema_read thy agoal))
		       (tcl)
                 handle ERROR => error (*from type_assign, 
		                         etc via prepare_proof*)
	                          ("The error above occurred for " 
				   ^ quote agoal);
	 val _ =ZEncoder.ZENV:=zenv
     in  t
     end
     );
   
fun zgoal zthy gl = (zgoalw zthy [] gl);
    
(* Genauso push_proof, pop_proof, zQED ... *)

datatype zproof = mk_zproof of ZEnv.Zenv * proof;

fun save_zproof () = mk_zproof(!ZEncoder.ZENV, save_proof());

fun restore_zproof (mk_zproof(zenv,prf)) = 
    (ZEncoder.ZENV:=zenv; restore_proof prf);
     
(*  ******************************************************************* *)
(*  									*)
(*   Basic Proving Infrastructure			 		*)
(*  									*)
(*  ******************************************************************* *)

fun lift th 0 = th
   |lift th 1 = th RS SB0_ext
   |lift th n = (lift th (n-1)) RS SB_ext;

	
(* Known BUG: does too much. simpset_of Prod.thy includes
   already set theory, and this leads to the destruction
   of the body to be selected. *)
	
fun full_expand_schema_tac thmS n = 
    let val prod_ss = simpset_of (theory"Product_Type")
        fun H0 thm  = thm RS conv_sname0
        fun H  thm  = thm RS conv_sname
    in
	(asm_full_simp_tac (prod_ss addsimps ((map H0 thmS) @ (map H thmS))) n)
        THEN
        (asm_full_simp_tac (HOL_ss addsimps SB0_eq::SB_pair_eq::thmS) n)
    end;

fun expand_schema_tac thmS n = 
    let val prod_ss = simpset_of (theory"Product_Type")
        fun H0 thm  = thm RS conv_sname0
        fun H  thm  = thm RS conv_sname
    in
	(simp_tac (prod_ss addsimps ((map H0 thmS) @ (map H thmS))) n)
        THEN
        (simp_tac (HOL_ss addsimps SB0_eq::SB_pair_eq::thmS) n)
    end;



(*---------------------------------------------------------------------------*)
(* Die SBs werden aufgeloest, wobei die entstehenden Meta-quantifizierten 
   Variablen gemaess den Strings im SB-Teil der Schemadefinition benannt
   werden. Dadurch erhoeht sich die Lesbarkeit! *)


fun STATE tacfun st = tacfun st st;

fun getgoal_new top i =
      (case  Library.drop (i-1, prems_of top) of
            [] => error"getgoal: Goal number out of range"
          | Q::_ => Q);

fun goal_params_new top i =
  let val gi = getgoal_new top i
      val frees = map Free (Logic.strip_params gi)
  in (gi,frees) end;

fun concl_of_goal_new top i =
  let val (gi,frees) = goal_params_new top i
      val B = Logic.strip_assums_concl gi
  in subst_bounds(frees,B) end;


fun SB_tac i = (STATE (fn top => 
    let val term = (concl_of_goal_new top i);  
        val (Const ("Trueprop",_)) $ term = term
    in case term of 
         Const ("ZPure.turnstyle",_) $ term => 
               (case term of
                  (Const ("ZPure.SBinder0",_) $ str $ _ ) =>
                             ((rtac turnstyle_SB0 i) 
                              THEN
                              (rename_tac (toIsaName(dest_string str)) i))
                | (Const ("ZPure.SBinder",_) $ str $ _ ) =>
                             ((rtac turnstyle_SB i) 
                              THEN
                              (rename_tac (toIsaName(dest_string str)) i)
                              THEN (SB_tac i))
                | _ => all_tac)
       | _ => no_tac
    end));


val intro_schema_tac = SB_tac 

fun bind_intro_tac i = (STATE (fn top => 
    let val term = (concl_of_goal_new top i);  
        val (Const ("Trueprop",_)) $ term = term
    in  case term of
           (Const ("ZPure.SBinder0",_) $ str $ _ $ _) =>
                   ((rtac bla0 i) THEN
                    (rename_tac (toIsaName(dest_string str)) i) THEN
                    (hyp_subst_tac i) THEN
                    (prune_params_tac))
         | (Const ("ZPure.SBinder",_) $ str $ _ $ _) =>
                   ((rtac bla i) THEN
                    (rename_tac (toIsaName(dest_string str)) i) THEN
                    (hyp_subst_tac i ) THEN
                    (prune_params_tac) THEN (bind_intro_tac i))
         | _ => all_tac
    end));


local
val exE1 = read_instantiate_sg (sign_of ZPure.thy) 
                               [("P","%y. ? z. SBinder0 ?a (?f y) z")] exE;
val exE2 = read_instantiate_sg (sign_of ZPure.thy) 
                               [("P","%y. SBinder0 ?a ?f y")] exE;
val exE3 = read_instantiate_sg (sign_of ZPure.thy) 
                               [("P","%y. ? z. SBinder ?a (?f y) z")] exE;
val exE4 = read_instantiate_sg (sign_of ZPure.thy) 
                               [("P","%y. SBinder ?a ?f y")] exE;
in

fun bind_elim_tac i = (STATE (fn top => 
    let val termS = Logic.strip_assums_hyp(Library.nth_elem(i-1,prems_of top));  
        fun b str = EVERY[dtac bla' i,prune_params_tac,
                          (etac exE1 i) ORELSE (etac exE3 i),
                          rename_tac (toIsaName str) i,
                          (etac exE2 i) ORELSE (etac exE4 i)]
        fun b0 str= EVERY[dtac bla0' i, rename_tac (toIsaName str) i]
        fun ex (x::R) =  case x of
            Const("Trueprop",_) $ (Const ("ZPure.SBinder",_) $S$_$_) 
                => (b(dest_string S)) THEN (bind_elim_tac i)
           |Const("Trueprop",_) $ (Const ("ZPure.SBinder0",_)$S$_$_) 
                => b0(dest_string S)
           | _ => ex R;
    in  ex termS
    end));

end

fun elim_pre_tac i     = (etac preE i) THEN (bind_elim_tac i);

val elim_sch_ex_tac    = ((etac sbexE2) ORELSE' (etac sbexE1)) THEN' bind_elim_tac
(* known problem : does not eliminate the x in the A x. *)

fun elim_sch_ex1_tac i = no_tac; (* not yet implemented *)

val intro_sch_all_tac  = EVERY'[rtac SBall_I2,bind_intro_tac];


fun split_schema_args n = (STATE (fn top => 
    let val term = (concl_of_goal_new top n);  
        val (Const ("Trueprop",_)) $ term = term
    in  case term of
           (Const ("ZPure.SBinder0",_) $ str $ _ $ _) =>
                          (rtac bla0E n)
         | (Const ("ZPure.SBinder",_) $ str $ _ $ _) =>
                          ((rtac blaE n) THEN  (rtac exI n) THEN
                           (rtac exI n) THEN  (rtac conjI n) THEN 
                           split_schema_args n )                   
         | _ => all_tac
    end));


val intro_sch_ex_tac = ((rtac sbexI2) ORELSE' (rtac sbexI1))
                       THEN' split_schema_args
               (*        THEN' (K(ALLGOALS (simp_tac HOL_ss))) *)

fun intro_sch_ex1_tac _= no_tac; (* not yet implemented *)
fun intro_pre_tac []   = (rtac preI)
   |intro_pre_tac tt   = (rtac preI)
                         THEN' (expand_schema_tac tt)
                         THEN' (split_schema_args)
                         THEN' (K(ALLGOALS (simp_tac HOL_ss)))


fun stripS_tac i = REPEAT((intro_sch_all_tac i) ORELSE
                          (intro_schema_tac i)  ORELSE 
                          resolve_tac [impI,allI,ballI] i);


(* *********************************************************************** *)
(*									   *)
(* Generators for semantic projection lemmas  		         	   *)
(*									   *)
(* *********************************************************************** *)

fun get_conjoint proj thy name n =
    let val zenv = schemas_of(get_zenv thy);
        val zsig = schemasig_of(the(ZEnv.lookup(zenv,name)));
    in  
        prove_zgoalw thy []  (name^" =+=> ?X")
           (fn _ =>  [expand_schema_tac [get_thm thy (Name(name^"_def"))] 1,
                      intro_schema_tac 1,
                      rtac impI 1,
                      dtac proj 1,
                      REPEAT(etac conjE 1),
                      rotate_tac (n-1) 1,
                      atac 1])
    end;


val get_decl = get_conjoint DECL_D1;
val get_conj = get_conjoint DECL_D2;

fun get_conjoint2 proj thm n =
    let val thy  = theory_of_thm thm
        fun drop_def x = String.substring(x,0,(size x) - 4)
        val name = drop_def(NameSpace.base(Thm.name_of_thm thm))
    in  
        prove_zgoalw thy []  (name ^" =+=> ?X")
           (fn _ =>  [expand_schema_tac [thm] 1,
                      intro_schema_tac 1,
                      rtac impI 1,
                      dtac proj 1,
                      REPEAT(etac conjE 1),
                      rotate_tac (n-1) 1,
                      atac 1])
    end;


val get_decl2 = get_conjoint2 DECL_D1;
val get_conj2 = get_conjoint2 DECL_D2;


(* *********************************************************************** *)
(*									   *)
(* Forward Reasoning:			   		         	   *)
(*									   *)
(* *********************************************************************** *)

(* old running code
fun get_tuple_arity tt =
    let fun ct (Term.Type("*",[_,tt as Term.Type("*",[_,_])])) =1+ct(tt)
               |ct (Term.Type("*",[_,_])) = 2
	       |ct _ = 1
    in  ct tt end; 
*)
(* new code ... untested *) 
fun get_tuple_arity tt = length(HOLogic.prodT_factors tt)

fun get_sch_arity tt = 
    if is_funtype tt then get_tuple_arity (domain_type tt) else 0


fun mk_sch_tuple n =
    let fun f 0 = ")"
           |f 1 = "?X01)"
           |f n = "?X0"^(Int.toString(n))^","^(f (n-1))
    in  "("^(f n) end;

local
val b2 = SB_pair_eq RS iffD1;
val b3 = SB0_eq RS iffD1;
in
fun strip_binder thm = 
    (strip_binder(thm RS b2))
    handle THM _ => thm RS b3;
end;


fun get_sch_typ_turnstyle(Const ("Trueprop",_) 
                          $ (Const("turnstyle",tt) $ D)) = domain_type tt
   |get_sch_typ_turnstyle(Const ("Trueprop",_) 
                          $ (Const("ZPure.turnstyle",tt) $ D)) = domain_type tt
   |get_sch_typ_turnstyle _ = raise THM("get_sch_typ_turnstyle",0,[]);



fun strip_op get_sch_typ res thm = 
(* precondition: free variable inside resolvent res must be "x" *)
    let val sch_typ = (get_sch_typ (concl_of thm))
                      handle Match 
                          => raise THM("strip_op: type mis match",0,[])
        val inst    = mk_sch_tuple(get_sch_arity sch_typ)
        val res     = read_instantiate_sg (sign_of (theory_of_thm res))
                         [("x",inst)] res
        val h1      = thm RS res
    in  strip_binder h1 end;


val strip_turnstyle = strip_op get_sch_typ_turnstyle turnstyleE;

val strip_ball = fn X => X RS bspec;

fun get_sch_typ_sball(Const ("Trueprop",_) 
                          $ (Const("SBall",tt) $ A $ B)) =
        HOLogic.dest_setT (domain_type tt)
   |get_sch_typ_sball(Const ("Trueprop",_) 
                          $ (Const("ZPure.SBall",tt) $ A $ B)) =
        HOLogic.dest_setT(domain_type tt) 
   |get_sch_typ_sball _ = raise THM("get_sch_typ_ball",0,[]);

val strip_sch_ball = strip_op get_sch_typ_sball SBallE;

val strip_imp   = fn X => X RS mp;

fun strip_one_op thm = 
    (strip_imp thm)
    handle THM _ =>((strip_ball thm)
                    handle THM _ =>((strip_sch_ball thm)
                                    handle THM _ => strip_turnstyle thm));

fun stripS thm =
    (stripS(strip_one_op thm))
    handle THM _ => thm;


val Z2HOL_ss = prod_ss addsimps 
	       [SNAME0_def,SNAME_def,SB0_def,SB_def,turnstyle_def,
		asSet_def,asPred_def,DECL_def,theta_def,PROJ_def,
                DELTA_def,XI_def,PRE_def,SBall_def,SBex_def,SBex1_def];


fun convert2hol_tac thms i = 
    asm_full_simp_tac (Z2HOL_ss addsimps thms) i



fun atomize_Z thm =
    let val thm = simplify (HOL_ss addsimps [DECL_def,conj_assoc]) thm
        fun deconj thm = ((thm RS conjunct1):: (deconj (thm RS conjunct2)))
                         handle THM _=> [thm]
    in  map stripS (deconj thm) end


fun prep_axdefs (str,thm) =
    let val thmS = atomize_Z thm;
        val namS = map (fn x=> (toIsaName str)^(Int.toString x))
	               (1 upto (length thmS))
    in  map2 bind_thm (namS, thmS);
        Addsimps thmS
    end        

val _ = ZEncoder.init_axprep prep_axdefs; 
        (* set axdef-preparator *)



(* *********************************************************************** *)
(*									   *)
(* New schema-calculus stripping tactics				   *)
(*									   *)
(* *********************************************************************** *)

local 
val def_UNIV = prove_goal 
          (the_context())
          "!!s. s == UNIV ==> x : s"
          (fn _ => [auto_tac (claset_of(the_context()),
                              simpset_of(the_context()))])

in

fun Add_Univrule_TC tc =
    Add_TC(Library.mapfilter (fn h => (SOME(h RS def_UNIV)
                                      handle _ => NONE))
                             (tc));
end


fun tc_tac n thm =
    let val ss = ZEnv.tc_simps_of
                    (ZTheory.get_zenv
                        (theory_of_thm thm))
    in  asm_simp_tac ss n thm
    end;

(* new short-cuts corresponding to rtac, dtac, etac, stac:
   perform the Z-specific stripping of quantifiers and
   try to eliminate resulting type-constraints.
   (does not unify, i.e. preserves meta-variables); *)

fun gen_z_tac tac S n =
    let val thm = stripS S;
        val m = length(prems_of thm)
        val TC_tac = Library.foldr (op THEN)
                           (map tc_tac ((n+m-1) downto n), all_tac)
    in  (tac thm n) THEN TC_tac end;

val zstac = gen_z_tac stac
val zftac = gen_z_tac (fn x => forward_tac [x])
val zrtac = gen_z_tac rtac
val zetac = gen_z_tac etac
val zdtac = gen_z_tac dtac




(* *********************************************************************** *)
(*									   *)
(* Tracing auxilliaries:						   *)
(*									   *)
(* *********************************************************************** *)


fun on  () = (show_types:=true; show_sorts:=true);
fun off () = (show_types:=false;show_sorts:= false);
fun remove_hyps x = (REPEAT (etac thin_rl x));

(* *********************************************************************** *)
(*									   *)
(* Tactical Combinators for proof-structuring:				   *)
(*									   *)
(* *********************************************************************** *)

(* Diese Datei ist ausschliesslich fuer Isabelle - Kommandos	*)
(* Kommandos fuer eine Beweisausgabeumgebung gehoeren nach      *)
(* PROOF_PRINT, Beweiskombinatoren (darauf aufsetzend) gehoeren *)
(* nach TRAFO.ML *)

fun CASE_DIST s n =
(* CASE DISTINCTION in n over "i=nat" *)
(* Precondition: s does not contain variables 
   that were locally bound in subgoal*)
EVERY[	res_inst_tac [("P",s)] case_split_thm n,
	asm_simp_tac (HOL_ss addsimps [if_P]) (n+1), 		
	asm_simp_tac (HOL_ss addsimps [if_not_P]) n]; 

fun FOLD s t n = 
EVERY[	res_inst_tac [("t",s)] subst n,
	REPEAT (rtac ext n),
      	if null(t) then (atac n) else ( rtac (hd t) n) ];

fun FOLD_AT s t n = 
EVERY[	res_inst_tac [("P",s)] subst n,
	REPEAT (rtac ext n),
      	if null(t) then (atac n) else ( rtac (hd t) n) ];


fun UNFOLD s t n = 
EVERY[  res_inst_tac [("t",s)] ssubst n,
	REPEAT (rtac ext n),
	if null(t) then (atac n) else (rtac (hd t)) n];

fun UNFOLD_AT s t n = 
EVERY[  res_inst_tac [("P",s)] ssubst n,
	REPEAT (rtac ext n),
	if null(t) then (atac n) else (rtac (hd t)) n];


fun HINT s tac n   = 
EVERY[	subgoals_tac [s] n, tac (n+1)];

fun GEN_ALL name n = 
EVERY[	res_inst_tac [("x",name)] spec n];

(* *********************************************************************** *)
(*									   *)
(* Z-Abbreviations:			 				   *)
(*									   *)
(* *********************************************************************** *)

fun zbr tac = br (stripS tac);
fun zbe tac = be (stripS tac);
fun zbd tac = bd (stripS tac);


fun (a ZRS b) = ((stripS a)RS(stripS b));
(* for simplicity of usage, the *)
(* removeTheta-Functions        *)
(* incorporate stripS.          *)

fun removeTheta x = (asm_full_simplify (HOL_ss addsimps[theta_def])
                                       (stripS x));

val removeTheta_tac = (fn i => (stripS_tac i) THEN
                               (asm_full_simp_tac (HOL_ss addsimps[theta_def]) i));


end					 	
end



