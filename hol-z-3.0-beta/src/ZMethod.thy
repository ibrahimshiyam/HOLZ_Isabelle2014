(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ZMethod.thy --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 1998-1999 GMD First, Germany
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
(* $Id: ZMethod.thy 6729 2007-08-03 05:25:17Z brucker $ *)


header {* Method Package for Z Representation and Z Refinement *}

theory  ZMethod
imports ZPure
uses    "kernel_ext/ProofObligationMgr.sml" 
begin


section {* Configuring the Generic PO Manager *}

ML{* 

structure FMethod (*: FMETHOD*) =
  struct 
     open POKind    

     val PO_classifier = Symtab.make[("tcc",                   repr),
                                     ("axdefConservative",     lethal),
                                     ("ccState",               wff), 
                                     ("ccOp",                  wff), 
                                     ("fwRefinementFunctional",meth),
                                     ("fwRefinementInit",      meth),
                                     ("fwRefinementOp",        meth)]

     datatype content = Mk of {abs : (string*string*string) option,
                               functional_refinement : bool} 

     val  init    = Mk{abs = NONE,functional_refinement=false}
     val  merge   = fn (x,y) => init
     fun  boolToString x    = if x then "true" else "false"
     fun  print (Mk{abs,functional_refinement}) = 
              (writeln ("Method Package State:");
               writeln ("=====================");
               writeln ("abstraction relation: "^
                           (case abs of NONE => "---" | SOME (x,y,z) => x)); 
               writeln ("functional refinemt : "^
                           (boolToString functional_refinement))) 
  end

structure ZPO_Mgr = PO_Manager (FMethod);

*}

   text{* Initialize Environment *}

   setup "ZPO_Mgr.PO_state_setup "  

section{* The Z Method Package *}

text{* On top of the generic PO Manager, which has now been
  imported and instantiated, we define a number of Method-
  specific PO generation methods. In our case, we implement
  support for classical forward data refinement (with an
  optimizing option for functional abstraction relations)
  following the lines described in the Spivey-Book also
  described in the Woodcock/Davis Book "Using Z".

  There is a general configuration operation \verb+set_abs+
  that sets the underlying abstration relation and
  concepts such as abstract or concrete state.

  PO generators are in particular:

  \begin{enumerate}
  \item \verb+gen_state_cc+ for checking that state schemas 
        (representing system invariants) are in fact satisfyable.
  \item \verb+gen_op_cc+ for checking that operation schemas 
        are "implementable" or "non-blocking", i.e. there exists a function
        that maps inputs and state to outputs and successor state.
        (Note that this function is \textbf{not} necessarily
        computable). 
  \item \verb+gen_thm_tcc+ extracts from an arbitrary definition
        or axiom the side-conditions for type-constraint-consistency.
        (a representational side-condition of HOL-Z).
  \item \verb+declare_abs+ allows for setting the
        abstraction relation (per schema definition).
        An additional option \verb+[functional]+ specifies
        the relation to be functional, which results in different
        (usually simpler) proof obligations.      
  \item \verb+refine_init+ for generating a PO assuring
        compatibility of Init schemas (in forward simulation)
  \item \verb+refine_op+ for generating two PO's establishing
        refinement of operation schemas.
  \end{enumerate}

*}

ML{* 

signature ZMETHOD_PACKAGE =
   sig
      type schema_name = string

      val gen_tcc_from : string -> theory -> theory
       (* PRE string denotes thm which is schema_def or axdef.
          POST add PO for each C(F%^E): CONT(C, F : Domain E)    
        *)
  
      val gen_cc_state : schema_name -> theory -> theory
       (* PRE stateschema is schema without x?, x!, x' variables.
          POST add PO  : \<exists> x. x : stateschema *)

      val gen_cc_op    : schema_name -> theory -> theory
       (* PRE opschema is schema with x and x' variables.
          POST add PO  : \<Sforall> state.\<forall> in.\<Sexists> state.
                                                         \<exists> out. op 
        *)
  
      val declare_abs  : bool -> schema_name -> theory -> theory
       (* PRE  absname must denote Z schema,
               which imports exactly two schemas.
               The first is used as abstract state,
               the second as concrete state.
          POST if functional, 
                  add PO: "\<Sforall> state_conc. \<Sexists1> abs_state. abs"
               else SKIP 
        *)

      val refine_init  : schema_name * schema_name -> theory -> theory
       (* PRE  abs relation must be set.
               init_abs init_conc must be schema names.
          POST if functional:
                    add PO:"\<Sforall> state_abs state_conc. 
                                       conc_init & abs \implies abs_init"  
               else add PO:"\<Sforall> state_conc. init_conc 
                                             \implies (\<Sexists> state_abs. 
                                                       init_abs & abs)"
        *)
      val refine_ops   : schema_name * schema_name -> theory -> theory
       (* PRE  abs relation must be set.
               op_abs op_conc must be schema names.
          POST if functional:
                 add PO: \<Sforall> state_abs state_conc. \<forall> in. 
                                     pre op_abs \<and> abs \<longrightarrow> pre op_conc
                 add PO: \<Sforall> state_abs state_conc. \<forall> in out. 
                                     pre op_abs \<and> abs \<and> op_conc \<and> abs' 
                                         \<longrightarrow> op_abs
               else
                 add PO: \<Sforall> state_abs state_conc. \<forall> in. pre op_abs  
                                                           & abs \<longrightarrow> pre op_conc
                 add PO: \<Sforall> abs_state conc_state. \<forall> in out. 
                                     pre op_abs \<and> abs \<and> op_conc  \<longrightarrow> 
                                         \<Sexists> state_abs'. abs' \<and> op_abs
        *)

   end

*}

ML{*

structure ZMethod_Package  : ZMETHOD_PACKAGE  =
struct 
   open ZPrelude;

   val DEBUG = ref([]: string list)

   type schema_name = string

   fun gen_tcc_from name thy               = error("NOT YET IMPLEMENTED")

   fun is_schema name thy =
       ZEnv.is_def(ZEnv.schemas_of (ZTheory.get_zenv thy),name)


   fun gen_cc_state stateschema thy         = 
   let val _ = if is_schema stateschema thy then ()
               else error("Must be schema name: "^stateschema)
       val zsig_opt= ZEnv.lookup (schemas_of(ZTheory.get_zenv thy),stateschema)
       val nn= map fst (filter(fn (x,_) => ZPrelude.is_in_name x orelse
                                           ZPrelude.is_out_name x orelse
                                           ZPrelude.is_stroke_name x)
                              (schemasig_of(the zsig_opt)))
       val _ = if null nn then ()
               else error("state schema should contain only \
                          \undecorated variables: "^(String.concat nn))
       val _    = (ZEncoder.ZENV:=ZTheory.get_zenv thy)

       val agoal= "%E "^ stateschema^" @ True";
       val cf   =  cterm_of(sign_of thy)
                         (ZEncoder.schema_read thy agoal)
       val thy' = ZPO_Mgr.declare_PO 
                            (SOME(Context.theory_name thy),
                             "ccState",stateschema) 
                             cf thy
       val _    = writeln("PO declared: "^(the
                                (ZPO_Mgr.get_name_of_PO cf thy')))

    in thy'  
    end     


   fun gen_cc_op opschema thy               = 
   let val _ = if is_schema opschema thy then ()
               else error("Must be schema name: "^opschema)
       val zsig_opt= ZEnv.lookup (schemas_of(ZTheory.get_zenv thy),opschema)
       val nn   = map fst (filter(fn (x,_) => ZPrelude.is_stroke_name x)
                                 (schemasig_of(the zsig_opt)))
       val _    = if not(null nn) then ()
                  else error("op schema should contain  \
                            \post state (i.e. 'stroked') components. ")
       val _    = (ZEncoder.ZENV:=ZTheory.get_zenv thy)

       val agoal= "pre "^ opschema;
       val cf   = cterm_of(sign_of thy)
                         (ZEncoder.schema_read thy agoal)
       val thy' = ZPO_Mgr.declare_PO 
                            (SOME(Context.theory_name thy),
                             "ccOp",opschema) 
                             cf thy
       val _    = writeln("PO declared: "^(the
                                (ZPO_Mgr.get_name_of_PO cf thy')))

    in thy'  
    end     

 
   fun declare_abs functional abs thy = 
   let
       val _ = if is_schema abs thy then ()
               else error("Must be schema name: "^abs)
       val abs_term = concl_of (get_thm thy (Name(abs^"_def"))) 

       val schema = ZEncoder.strip_Binder
                    (case abs_term of
                       Const("==",_) $ _ $ t => t
                     | _ => error("name must denote schema!"))
       val decl   = (case schema of
                     Const("ZPure.DECL",_) $ H $ _ => H
                    |_ => error("name must denote schema!"))
       fun strip_sname (Const("ZPure.SNAME",_)$(Const(s,_))$_) = s
          |strip_sname  _ = error("declaration part must consist of \
                              \two schema names only!")
       val (state_abs,state_conc) = (case decl of 
                           Const ("op &", _)$H$H' => (strip_sname H,
                                                      strip_sname H')
                         | _ => error("declaration part must consist of \
                                    \two schema names only!"))
       val cont = FMethod.Mk{abs=SOME(abs,
                                     (NameSpace.base state_abs),
                                     (NameSpace.base state_conc)),
                         functional_refinement=functional}                 
       val thy' = ZPO_Mgr.set_content cont thy
   
       val _    = (ZEncoder.ZENV:=ZTheory.get_zenv thy');

       val agoal= "%A "^(NameSpace.base state_conc)^" @ (%E1 "^
                   (NameSpace.base state_abs)^" @ "^(NameSpace.base abs)^")";
       val cf   =  cterm_of(sign_of thy')
                         (ZEncoder.schema_read thy' agoal)

       val thy''=  if functional 
                   then ZPO_Mgr.declare_PO 
                            (SOME(Context.theory_name thy'),
                             "fwRefinementFunctional",abs) 
                            cf thy'
                   else thy'
       val _ =     if functional
                   then writeln("PO declared: "^(the
                                (ZPO_Mgr.get_name_of_PO cf thy'')))
                   else ()
 
   in  thy'' end

   fun refine_init(init_abs, init_conc)(thy) =
       let val _ = if is_schema init_abs thy then ()
                   else error("Must be schema name: "^init_abs)
           val _ = if is_schema init_conc thy then ()
                   else error("Must be schema name: "^init_conc)
           val FMethod.Mk{abs,functional_refinement}  = ZPO_Mgr.get_content thy
           val (abs, state_abs, state_conc)= case abs of 
	                                       NONE => error"no abstraction relation set!"
					     | SOME x => x
           val term_abs  = concl_of (get_thm thy (Name(init_abs^"_def"))) 
           val term_conc = concl_of (get_thm thy (Name(init_conc^"_def"))) 
           val term_abs  = ZEncoder.strip_Binder
                          (case term_abs of
                             Const("==",_) $ _ $ t => t
                           | _ => error(init_abs^"must denote init schema!"))
           val term_conc = ZEncoder.strip_Binder
                          (case term_conc of
                             Const("==",_) $ _ $ t => t
                           | _ => error(init_conc^"must denote init schema!"))
           fun test m (Const("ZPure.DECL",_)  
                         $ (Const("ZPure.SNAME",_) $ Const(s,_) $_) 
			 $ _) = 
                           if (NameSpace.base s) = m then ()
                           else error("imported schema must be :"^m)
	      |test m _ = error"illegal pattern of import schema"
           val _ = test state_abs  term_abs
           val _ = test state_conc term_conc
           val goal = if functional_refinement 
                      then "%A "^state_abs^" @ (%A "^state_conc^" @ ("
                           ^ init_conc ^" & "^abs^" --> "^init_abs^"))"
                      else "%A "^state_conc^" @ ("^ init_conc ^" --> "^
                           "(%E "^state_abs^" @ ("^abs^" & "^init_abs^")))"
           val cf   =  cterm_of(sign_of thy)
                           (ZEncoder.schema_read thy goal)
           val thy' =  ZPO_Mgr.declare_PO 
                            (SOME(Context.theory_name thy),
                             "fwRefinementInit",state_abs) 
                            cf thy
           val _    = writeln("PO declared: "^(the
                                (ZPO_Mgr.get_name_of_PO cf thy')))
       in  thy' end



   fun refine_ops (op_abs, op_conc)     thy = 
       let (* checking syntactic side-conditions ... *)
           val _ = if is_schema op_abs thy then ()
                   else error("Must be schema name: "^op_abs)
           val _ = if is_schema op_conc thy then ()
                   else error("Must be schema name: "^op_conc)
           val FMethod.Mk{abs,functional_refinement}  = ZPO_Mgr.get_content thy
           val SOME(abs, state_abs, state_conc)=abs
           val term_abs  = concl_of (get_thm thy (Name(op_abs^"_def"))) 
           val term_conc = concl_of (get_thm thy (Name(op_conc^"_def"))) 
           val term_abs  = ZEncoder.strip_Binder
                          (case term_abs of
                             Const("==",_) $ _ $ t => t
                           | _ => error(op_abs^"must denote op schema!"))
           val term_conc = ZEncoder.strip_Binder
                          (case term_conc of
                             Const("==",_) $ _ $ t => t
                           | _ => error(op_conc^"must denote op schema!"))
           fun test m (Const("ZPure.DECL",_) $
                        (Const ("op &",_)  
                          $ (Const ("ZPure.DELTA",_) 
                             $ (Const("ZPure.SNAME",_)$(Const(s,_))$_) 
                             $ _)
                          $ _) $ _) = 
                          (if (NameSpace.base s) = m then ()
                           else error("imported schema must be :"^m))
              |test m (Const("ZPure.DECL",_) $
                        (Const ("op &",_)  
                          $ (Const ("ZPure.DELTA",_)
                             $ (Const ("ZPure.DELTA",_) 
                                $ (Const("ZPure.SNAME",_)$(Const(s,_))$_) 
                                $ _)
                             $ _ $ _)
                          $ _) $ _) = 
                          (if (NameSpace.base s) = m then ()
                           else error("imported schema must be :"^m))
              |test m _  = error("illegal pattern of schema:"^m) 
           val _ = test state_abs  term_abs
           val _ = test state_conc term_conc

           fun zsig_of name =  schemasig_of(the(ZEnv.lookup 
                                (schemas_of(ZTheory.get_zenv thy),name)))
           fun get_params test name = filter test
                                      (map fst (zsig_of name))
           val in_parms  = get_params ZPrelude.is_in_name op_abs
           val in_parms' = get_params ZPrelude.is_in_name op_conc
           val _         = if in_parms = in_parms' then ()
                           else error("Input parameters must agree !")
           val out_parms = get_params ZPrelude.is_out_name op_abs
           val out_parms'= get_params ZPrelude.is_out_name op_conc
           val _         = if out_parms = out_parms' then ()
                           else error("Output parameters must agree !")
 
           (* generating proof obligations ... *)
           fun ALL [] b  = "("^b^")"
              |ALL S  b  = "(ALL "^(String.concat 
                                    (map(fn x => x^" ")S))^". "^b^")"

           val goal1 = "%A "^state_abs^" @ (%A "^state_conc^" @ "^
                       (ALL in_parms                       
                            ("pre "^op_abs^" \<and> "^abs^
                             " \<longrightarrow> pre "^op_conc))^")"
           val goal2c= if functional_refinement 
                       then " \<and> "^abs^stroke_sym^" \<longrightarrow> "^op_abs
                       else " \<longrightarrow> (%E "^state_abs^stroke_sym^" @ "
                            ^abs^stroke_sym^" \<and> "^op_abs^")"
           val goal2a= "%A "^state_abs^" @ (%A "^state_conc^" @ "^
                       "(%A "^state_conc^stroke_sym^" @ "^
                       (ALL in_parms                       
                            (ALL out_parms ("pre "^op_abs^" \<and> "^abs^
                                            " \<and> "^op_conc^ 
                                            " \<longrightarrow> (%E "
                                            ^state_abs^stroke_sym^" @ "^abs^stroke_sym^
                                            " \<and> "^op_abs^")")))^"))"
           val goal2b= "%A "^state_abs^" @ (%A "^state_abs^stroke_sym^
                       " @ (%A "^state_conc^" @ "^ "(%A "^state_conc^stroke_sym^" @ "^
                       (ALL in_parms                       
                            (ALL out_parms ("pre "^op_abs^" \<and> "^abs^
                                            " \<and> "^op_conc^ 
                                            " \<and> "^abs^stroke_sym^
                                            " \<longrightarrow> "^op_abs
                                            )))^")))" 
           val goal2 = if functional_refinement then goal2b else goal2a
           val cf1   = cterm_of(sign_of thy)
                           (ZEncoder.schema_read thy goal1)
           val cf2   = cterm_of(sign_of thy)
                           (ZEncoder.schema_read thy goal2)
           val thy'  = ZPO_Mgr.declare_PO 
                            (SOME(Context.theory_name thy),
                             "fwRefinementOp",op_abs) 
                            cf1 thy
           val thy'' = ZPO_Mgr.declare_PO 
                            (SOME(Context.theory_name thy),
                             "fwRefinementOp",op_abs) 
                            cf2 thy'
           val _     = writeln("PO declared: "^(the
                                (ZPO_Mgr.get_name_of_PO cf1 thy''))) 
           val _     = writeln("PO declared: "^(the
                                (ZPO_Mgr.get_name_of_PO cf2 thy''))) 
       in  thy'' end




structure P = OuterParse and K = OuterKeyword;

val declare_absP =
    let fun declare_abs'(name,X) = declare_abs (isSome X) name 
    in OuterSyntax.command "set_abs" "set abstraction relation" 
			OuterKeyword.thy_script
			((P.name) -- (Scan.option (P.$$$ "[" |-- P.$$$ "functional" --| P.$$$ "]"))
                        >> (Toplevel.theory o declare_abs'))
    end;
val _ =  OuterSyntax.add_parsers [declare_absP];
val _ = OuterSyntax.add_keywords ["functional"];

val gen_tcc_fromP =
    OuterSyntax.command "gen_thm_tcc" "generate type constraint side conditions" 
			OuterKeyword.thy_script
			((P.name)  >> (Toplevel.theory o gen_tcc_from));
val _ =  OuterSyntax.add_parsers [gen_tcc_fromP];


val gen_cc_stateP =
    OuterSyntax.command "gen_state_cc" "generate state consistency conditions" 
			OuterKeyword.thy_script
			((P.name)  >> (Toplevel.theory o gen_cc_state));
val _ =  OuterSyntax.add_parsers [gen_cc_stateP];


val gen_cc_opP =
    OuterSyntax.command "gen_op_cc" "generate operation consistency relation" 
			OuterKeyword.thy_script
			((P.name)  >> (Toplevel.theory o gen_cc_op));
val _ =  OuterSyntax.add_parsers [gen_cc_opP];


val refine_opsP =
    OuterSyntax.command "refine_op" "generate forward refinement proof obligations" 
			OuterKeyword.thy_script
			((P.name)  -- (P.name) >> (Toplevel.theory o refine_ops));
val _ =  OuterSyntax.add_parsers [refine_opsP];

val refine_initP =
    OuterSyntax.command "refine_init" "generate forward refinement proof obligations for init schemas" 
			OuterKeyword.thy_script
			((P.name)  -- (P.name) >> (Toplevel.theory o refine_init));
val _ =  OuterSyntax.add_parsers [refine_initP];




end

*}

end
