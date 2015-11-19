(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ZPure.thy--- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 1998-1999 University Bremen, Germany
 *               2000-2003 University Freiburg, Germany
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
(* $Id: ZPure.thy 8132 2008-06-16 12:25:34Z wolff $ *)


header {* Definitions of Syntax and Core-Combinators of Z *}

theory  ZPure
imports "contrib/ProdContrib"
uses   "ZPrelude.sml"      (* General term api *)
        "ZAbsy.sml"        (* holz format (export ZETA) *)
        "ZEnv.sml"         (* Z environment, keeping schema information *)
        "ZTheory.sml"      (* Z Theory Data Setup *)
       ("ZEncoder.sml")    (* parse & encode Z constructs into Isabelle/HOL *)
       ("ZConversion.sml") (* conversions for holz format *)
       ("ZProofUtil.sml")  (* Declaration of dependency on the proof package *) 
        
begin
(* ML{* use "ZEnv.sml" *} *)

section{* Initialize Z-Environment, provide Access *}

   setup "ZTheory.ZEnv_setup"  (* actually from ZTheory.sml*)


ML{* ZTheory.print_TC (the_context()) *}
ML{* print_ss empty_ss *}

ML_setup {*
local
    fun change_global f (thy, th) = (f [th] thy, th);
    val tc_simp_attr = (Attrib.add_del_args (change_global ZTheory.Add_TC) 
                                            (change_global ZTheory.Del_TC),
                        Attrib.add_del_args (fn _ => error ("no local tc's!"))
                                            (fn _ => error ("no local tc's!")));
in
val _ = Context.add_setup
           [Attrib.add_attributes
                   [("tc_simp", 
                    tc_simp_attr, 
                    "declaration of type checking simplification rule")]]

end;
*}


setup "Context.setup ()"


section{* Syntax *}

types Zschema = bool        (* schemas are HOL-predicates by default *)

(*  ******************************************************************* *)
(*  									*)
(*  basic schema (name) decorations					*)
(*  									*)
(*  ******************************************************************* *)

(* The overall principle of the representation of Z in HOL is 
   - to provide e-mail-format syntax for Schema-Decorations like
     STROKE,IN,OUT,Delta,Xi,theta
   - to provide a system of semantic operators that represents 
     them in HOL like DELTA, XI, ... and the schema operators
   - and 4 phases of conversion between these two, designed to
     be revertible in a pretty-printing process.
     These are:
     - STROKE, IN, OUT, Delta, XI, 
         => expansion by ast-rewriting and as parse-translations
     - expand_schema (marking schema names with SNAME and expanding theta)
     - bind_schema (generating schema-binders for all schema quantifier,
       for pre etc, and for schema-as-sets)
     - expand_projections (generating PROJ on a heuristic basis;
       this expansion may produce ambiguous or even false code due
       to lack of type-information in the HOL-representation)
 *)
 

syntax

  (* syntax constants to generate lexical Z conventions in a pre-conversion
     phase - see parse-translations below. Note that SSTROKE, _IN, _OUT were
     copied directly into the strings of the underlying constant symbols
     in the print-process during parse-translations.*)
  SSTROKE   :: "idt => idt"          ("_'`") (* transcribing ` *)
  "_IN"	    :: "idt => idt"	     ("_?")
  "_OUT"    :: "idt => idt"	     ("_!")
  SSTROKE   :: "idt => logic"        ("_'`") (* transcribing ' *)
  "_IN"     :: "idt => logic"        ("_?")
  "_OUT"    :: "idt => logic"        ("_!")


  "%Delta"  :: "idt => Zschema"      ("(%Delta _)" [100]5) 
  "%Xi"	    :: "idt => Zschema"      ("(%Xi _)"    [100]5)
  "%theta"  :: "'a  => Zschema"      ("(%theta _)" [100]5)

 syntax (xsymbols)
  "%Delta"  :: "idt => Zschema"      ("(\<Delta> _)" [100]5) 
  "%Xi"	    :: "idt => Zschema"      ("(\<Xi> _)" [100]5)
  "%theta"  :: "'a  => Zschema"      ("(\<theta> _)" [100]5)

 
(*  ******************************************************************* *)
(*  									*)
(*  schema expression operators						*)
(*  									*)
(*  ******************************************************************* *)

nonterminals
  rnm
  rnms


syntax
  "_rnm"    :: "[idt , idt] => rnm"               ("(_ '/ _)" )
  ""        :: "rnm => rnms"                      ("_")
  "_rnms"   :: "[rnm, rnms] => rnms"              ("_,/ _")  
 "%not"     :: "Zschema => Zschema"               ("%not (_)//" [40]40)      
  "\\'/"    :: "[Zschema, Zschema]    => Zschema" (infixl 30) 
  "'/\\"    :: "[Zschema, Zschema]    => Zschema" (infixl 35) 
  "=+=>"    :: "[Zschema, Zschema]    => Zschema" (infixr 25) 
  "<=+=>"   :: "[Zschema, Zschema]    => Zschema" (infixr 25) 
  pre       :: "Zschema               => Zschema"
  "%E"      :: "[Zschema, Zschema]    => Zschema" ("%E (2_) @ (_)"    [30,31]30)
  "%E1"	    :: "[Zschema, Zschema]    => Zschema" ("%E1 (3_) @ (_)"   [30,31]30)
  "%A"      :: "[Zschema, Zschema]    => Zschema" ("%A (2_) @ (_)"    [30,31]30)
  "_hiding" :: "[Zschema, args]       => Zschema" ("(_)\\[(_)]"    [80,81]80)
  "_geninst":: "[idt, args]           => Zschema" ("(_)[(_)]"      [80,81]80)
  "_rename" :: "[idt, rnms]           => Zschema" ("(_)\\[(_)]"    [80,81]80)
  "_schset" :: "[idt, 'a]             => 'b set"  ("(1{.(_) @ (_).})")
  "_select" :: "['a,idt]              => 'c"      ("_._" [200,201]200)   
  "|\\"     :: "[Zschema, Zschema]    => Zschema" (infixl 80)
  "%%;"	    :: "[Zschema, Zschema]    => Zschema" (infixl 80)
  ">>"	    :: "[Zschema, Zschema]    => Zschema" (infixl 80)


syntax (xsymbols)
  "%E"      :: "[Zschema, Zschema]    => Zschema" ("\<Sexists> (2_) \<spot> (_)"    [30,31]30)
  "%E1"	    :: "[Zschema, Zschema]    => Zschema" ("\<Sexistsone> (3_) \<spot> (_)"   [30,31]30)
  "%A"      :: "[Zschema, Zschema]    => Zschema" ("\<Sforall> (2_) \<spot> (_)"    [30,31]30)
 

translations

  "%not P"         => "~ P" 
  "A \\/ B"        => "A | B" 
  "A /\\ B"        => "A & B" 
  "A =+=> B"       => "A --> B" 
  "A <=+=> B"      => "A = B" 



(*  ******************************************************************* *)
(*  									*)
(*  Syntax for schema notation						*)
(*  									*)
(*  ******************************************************************* *)
 

types   Predicate = bool
        DeclPart  = bool
        
nonterminals
        DeclParts  
        SchemaName 
 
syntax
  ""              :: "DeclPart              => DeclParts" ("_")
  "_combdecls"    :: "[DeclPart, DeclParts] => DeclParts" ("_;/ _")  
  
consts
  SCHEMA          ::  "[bool, bool]         => Zschema "

translations
  "_combdecls D D1" => "D & D1"

syntax
  "_AXIOM0"     ::  "Zschema"  
  		   ("+.. //-..") 
  "_AXIOM1"     :: "DeclParts => Zschema"  
  		   ("+..//(2 _)//-..") 
  "_AXIOM2"     :: "Predicate => Zschema"  
  		   ("+.. //|-- //(2 _)//-..") 
  "_AXIOM3"     :: "[DeclParts, Predicate] => Zschema"  
  		   ("+..//(2 _)//|--//(2 _)//-..") 

translations
  "_AXIOM0" 	== "SCHEMA True True" 
  "_AXIOM1 D" 	== "SCHEMA D True " 
  "_AXIOM2 P"	== "SCHEMA True P"  
  "_AXIOM3 D P"	== "SCHEMA D P"
	
syntax

 "_GEN0" :: "args => Zschema"  
 				("+== [(_)] ===//-==") 
 "_GEN1" :: "[args, DeclParts]=> Zschema " 
 				("+== [(_)] ===//(2 _) //-==") 
 "_GEN2" :: "[args, Predicate]=> Zschema"  
 				("+== [(_)] ===//|--//(2 _)//-==") 
 "_GEN3" :: "[args, DeclParts, Predicate] => Zschema" 
 				("+== [(_)] ===//(2 _)//|--//(2 _)//-==")
 

translations

  "_GEN0 M" == "%M. (_AXIOM0)" 
  "_GEN1 M D" == "%M. (_AXIOM1 D)"
  "_GEN2 M P" == "%M. (_AXIOM2 P)" 
  "_GEN3 M D P" == "%M. (_AXIOM3 D P)"


syntax
  "_SCHEME0":: "SchemaName => Zschema"                    ("+-- _ --- //---" ) 
  "_SCHEME1"::"[SchemaName, args] => Zschema"             ("+-- _ [_] ---//---") 
  "_SCHEME2"::"[SchemaName, DeclParts] => Zschema"        ("+-- _ ---//(2 _)//---")
  "_SCHEME3"::"[SchemaName, Predicate] => Zschema "       ("+-- _ ---//|--//(2 _)//---" )
  "_SCHEME4"::"[SchemaName, args, DeclPart] => Zschema"   ("+-- _ [_] ---//(2 _)//---")
  "_SCHEME5"::"[SchemaName, args, Predicate]=> Zschema"   ("+-- _ [_] ---//|--//(2 _)//---")
  "_SCHEME6"::"[SchemaName, DeclParts,Predicate]=>Zschema"("+-- _ ---//(2 _)//|--//(2 _)//---")
  "_SCHEME7"::"[SchemaName, args, DeclParts, Predicate]=>Zschema" ("+-- _ [_] ---//(2 _)//|--//(2 _)//---") 

translations
  "_SCHEME0 N"        == ("prop") "N == _AXIOM0" 
  "_SCHEME1 N M"      == ("prop") "N == (_GEN0 M)"  
  "_SCHEME2 N D"      == ("prop") "N == (_AXIOM1 D)"
  "_SCHEME3 N P"      == ("prop") "N == (_AXIOM2 P)"
  "_SCHEME4 N M D"    == ("prop") "N == (_GEN1 M D)" 
  "_SCHEME5 N M P"    == ("prop") "N == (_GEN2 M P)" 
  "_SCHEME6 N D P"    == ("prop") "N == (_AXIOM3 D P)"
  "_SCHEME7 N M D P"  == ("prop") "N == (_GEN3 M D P)" 


section{* Semantic Representation *}


consts

  SNAME0       :: "'a  => 'a"         (* name for schema with empty sign.*)
  SNAME        :: "['a=>'b,'a] => 'b" (* name for schema with nonempty sign.*)
  SBinder0     :: "['a, 'b => 'd] => ('b => 'd)"           
  SBinder      :: "['a,['b,'c] => 'd] => (('b*'c)=>'d)" 
  
  (* These two constants control the conversion of "Schemas as Sets"
     and "Schemas as Predicates" (default). This is necessary since
     these two views are *isomorphic*, but not identical for the
     Isabelle/HOL typechecking...*) 
  asSet        :: "['a => bool] => 'a set" (* converts schemas into sets *)
  asPred       :: "['a set] => 'a => bool" (* converts sets into schemas *)
  turnstyle    :: "('a => bool)  => bool " ("|- (3_)" ) 
  theta        :: "[string,'a]   => 'a"
  DELTA        :: "[bool,bool]   => bool"
  XI           :: "[bool,'a,'a]  => bool"
  PROJ         :: "['a,'a=>'b,'c]=>'b"
  DECL         :: "[bool,bool]   => bool"  ("(0_/ |----/ _)" [15,14]14)
  PRE          :: "['a => bool]  => bool"
  SBall        :: "['a set, 'a => bool] => bool"
  SBex         :: "['a set, 'a => bool] => bool"
  SBex1        :: "['a set, 'a => bool] => bool"
  SSet         :: "['a set, 'a => 'b]   => 'b set"



defs
  SNAME0_def:   "SNAME0 x == x"
  SNAME_def:    "SNAME f args  == f args"
  SBinder0_def: "SBinder0 An P == P"
  SBinder_def:  "SBinder An P  == (% (x,y). (P x y))"
  asSet_def:    "asSet         == Collect"
  asPred_def:   "asPred        == (%X. %x. x : X)"
  turnstyle_def:"|- P          == All P" 
  PROJ_def:     "PROJ X F ide  == F X" 
  DELTA_def:    "DELTA s t     == s & t"     
  XI_def:       "XI s t t'     == s & t=t'"     
  theta_def:    "theta s t     == t"     
  DECL_def:     "DECL P Q      == P & Q"
  PRE_def:      "PRE           == Ex"
  SBall_def:    "SBall         == Ball"
  SBex_def:     "SBex          == Bex"
  SBex1_def:    "SBex1 A P     == ?! x. x : A & P x"
  SSet_def:     "SSet A f      == f ` A"
  


nonterminals
  sbind
  sbinds

syntax
  "_sbind"  :: "['a , 'b] => sbind"          ("(2_ ~~> _)" 10)
  ""        :: "sbind => sbinds"             ("_")
  "_sbinds" :: "[sbind, sbinds] => sbinds"   ("_,/ _")  
  "_SB"     :: "[sbinds,'a] => 'a"           ("(4SB (_). (_))" 10)
(* deprecated
  "%EN"     :: "['a,'b, Zschema] => Zschema" ("%E (_ %: _) @ (_)" [30,31]30)
  "%E1N"    :: "['a,'b, Zschema] => Zschema" ("%E1 (_ %: _) @ (_)"[30,31]30)
  "%AN"     :: "['a,'b, Zschema] => Zschema" ("%A (_ %: _) @ (_)" [30,31]30)
 *)

translations
(* STROKE is handled by parse-translation, while
   %theta is handled internally in the ZEncoder, namely the 
   exp_binding phase ... *) 
  "%Delta S"  => "DELTA S (SSTROKE S)"
  "%Delta S"  <= "DELTA S T"
  "%Xi    S"  => "XI (%Delta S) (%theta S) (%theta (SSTROKE S))"
  "%Xi    S"  <= "XI (%Delta S) (T) (U)"

(* deprecated 
  "%E x %: S @ T" == "Bex S (%x. T)"  
  "%E1 x %: S@ T" == "SBex1 S (%x. T)"
  "%A x %: S @ T" == "Ball S(%x. T)" 
 *) 
  "_SB (_sbinds (_sbind x y) sbds) e" == "SBinder x (%y. _SB sbds e)"
  "_SB (_sbind x y) e"                == "SBinder0 x (%y. e)"

(* For the following cases, the parsing is done internally in the 
   ZEncoder, more precisely, the exp_binding phase ... *)
  "pre S"     <= "PRE S"
  "%E S @ T"  <= "SBex  S T"  
  "%E1 S @ T" <= "SBex1 S T"
  "%A S @ T"  <= "SBall S T" 
  "{.S @ T.}" <= "SSet  S T" 



section {* Syntax: The parse-translation setup *}

ML{*
val show_full_sem = ref false; 
val SAVE = ref([]:term list)

(* switch to shut off the pretty printing to email format *)

local

local open Ast ZPrelude ZEnv in

(* ************************************************************* *)
(* absolute pre-parsing ... runs before ZEncoder.schema_conv !!! *)
(* ************************************************************* *)
fun parse_SSTROKE [Free(x,t)] =  Free(stroke (x,t))
   |parse_SSTROKE [Const(x,t)]=  Const(stroke(x,t))
   |parse_SSTROKE _ = error ("Illegal STROKE-Term: must be identifier.");

fun parse_IN [Free(x,t)] =  Free(x^ZPrelude.in_sym,t)
   |parse_IN _ = error ("Illegal IN-Term: must be identifier.");

fun parse_OUT [Free(x,t)] =  Free(x^ZPrelude.out_sym,t)
   |parse_OUT _ = error ("Illegal OUT-Term: must be identifier.");

fun parse_SCHEMA [decl,pred] = Const("DECL",dummyT) $ decl $ pred
   |parse_SCHEMA _ = error ("Illegal Schema Term.");
    (* why as parse translation ??? *)


(* *************** *)
(* pretty-printing *)
(* *************** *)


fun print_decls (Const ("op &",t) $ T $ T') = 
			Const ("_combdecls",t) $ T $ (print_decls T')
   |print_decls T = T;

fun print_Proto [decl, preds] = 
(* Introduces the root-symbol for pretty-printing schemata in Zproto *) 
	if !show_full_sem then raise Match
	else Const("SCHEMA",dummyT) $ (print_decls decl) $ preds
   |print_Proto _  = raise Match;

fun TR s h = (writeln s; h)

fun print_SB0 [anno, Abs(_,t,body)] = 
      if !show_full_sem then (raise Match) 
      else (subst_bounds([Free(dest_string anno,t)],body))
   |print_SB0 _ = raise Match;



fun print_SB (anno:: Abs(_,t,body)::R)  = 
      if !show_full_sem then raise Match
      else (list_comb(subst_bounds
                       ([Free(dest_string anno,t)],body),R))
   |print_SB _ = raise Match

fun print_SCH_name0 [x] =
      if !show_full_sem then raise Match else x
   |print_SCH_name0 _ = raise Match


fun print_SCH_name [f as Const(s,_),arg] =
(* delifting all applications marked as a schema-names applied to argument
   tuple. It is checked that 1. arg forms a tuple, 2. components of arg
   are just Free's, 3. all names in the free's match to the signature sign
   of s modulo a unique number d of strokes '.  
   
   USES ZENV FROM ENCODER (parser . . .)
   *)
      if !show_full_sem then raise Match 
      else (let val _ = (SAVE:=[f,arg]@(!SAVE)) 
               fun  stripFree (Free(s,t) :: R) = s :: (stripFree R)
                  | stripFree((Const("_bound",_) $ Free(s,t))::R) = 
                                                 s :: (stripFree R)
                    (* this case captures variables bound by other
                       quantifiers than just schema quantifiers ...*)
      		  | stripFree (_ :: R) = raise Match
      		  | stripFree []     = [];
	       val x::R = stripFree (strip_tuple arg);
	       val sign = (case lookup (schemas_of(!ZEnv.ZENV),s) of
                             NONE => raise Match 
                            |SOME n => map fst (schemasig_of n));
	       val y    = case sign of a::_ => a | _ => raise Match;
	       val d    = (size x) - (size y);
	       fun cm [] [] = true
	          |cm (a::r)(a'::r') = if (size a) + d = size a' andalso
	                                  a = (substring(a',0,size a' - d))
	                               then cm r r'
	                               else raise Match
	          |cm _ _ =  raise Match
      	   in  if d >= 0 andalso cm sign (x::R)
      	       then genstrokeN d f  
               else raise Match
           end)
   |print_SCH_name _ = (raise Match);  
    
fun print_theta [s,e] =
         if !show_full_sem then raise Match 
         else let val t = dest_string s;
                  val n = strokes t;
              in   Const("%theta",dummyT)$
                        (genstrokeN n (Free(destroke t,dummyT))) 
              end
   |print_theta _ = raise Match
    
fun print_asSet [a] = if !show_full_sem then raise Match else a
   |print_asSet _ = raise Match;

fun print_asPred [a] =  if !show_full_sem then raise Match else a
   |print_asPred _ = raise Match

fun print_PROJ [X,F,str] =
         if !show_full_sem then raise Match
         else Const("_select",dummyT)$ X $
              Const(dest_string str,dummyT)
   |print_PROJ _ = raise Match
  
end (* local open *) 

in

val parse_translation = [("SSTROKE", parse_SSTROKE),
			 ("_IN", parse_IN),
			 ("_OUT", parse_OUT),
			 ("SCHEMA", parse_SCHEMA)];
val print_translation = [("SBinder0", print_SB0),
	 	         ("SBinder", print_SB),
			 ("DECL", print_Proto),
			 ("SNAME0",print_SCH_name0), 
			 ("SNAME",print_SCH_name),
 			 ("theta",print_theta),
			 ("asSet",print_asSet),
			 ("asPred",print_asPred),
			 ("PROJ",print_PROJ) 
			];
 
end
*}

parse_translation {* parse_translation *}
print_translation {* print_translation *}


section{* Derived Rules *}

subsection {* Schema Binders*}

lemma SB0_ext: "(\<And>x. f x = g x) \<Longrightarrow> SBinder0 a f = SBinder0 b g"
by (rule ext, simp add: SBinder0_def)

lemma SB_ext: "(\<And>x. f x = g x) \<Longrightarrow> SBinder a f = SBinder b g"
by(simp add: SBinder_def)


lemma conv_sname0 : "f\<equiv>g \<Longrightarrow> SNAME0 f = g"
by(simp add: SNAME0_def)

lemma conv_sname :  "f\<equiv>g \<Longrightarrow> SNAME f args = g args"
by(simp add: SNAME_def)

lemma turnstyle_SB0: "(\<And>x. f x) \<Longrightarrow> |- SBinder0 a f"
by(auto simp: SBinder0_def turnstyle_def)

lemma turnstyle_SB: "(\<And>x. |- f x) \<Longrightarrow> |- SBinder a f"
by(simp add: SBinder_def turnstyle_def)

lemma SB0_ext_id: "(\<And>x. f x = g x) \<Longrightarrow> SBinder0 a f = SBinder0 a g"
by(rule ext, simp add: SBinder0_def)

lemma SB_ext_id: "(\<And>x. f x = g x) \<Longrightarrow> SBinder a f = SBinder a g"
by(simp add: SBinder_def)

lemma SB0_extL: "(\<And>x. f x = g x) \<Longrightarrow> SBinder0 a f = g"
by(rule ext, simp add: SBinder0_def)

lemma SB_extL: "(\<And>x y. f x y = g (x, y)) \<Longrightarrow> SBinder a f = g"
by(simp add: SBinder_def split_eta)


lemmas Zexts = ext SB0_ext SB_ext

lemma SB0_eq: "SBinder0 a P x = P x"
by(simp add: SBinder0_def)

lemma SB_eq: "SBinder a P z = (P (fst z) (snd z))"
apply(simp add: SBinder_def)
apply (rule  surjective_pairing [THEN ssubst])
apply (safe+, simp)
done

lemma SB_pair_eq: "SBinder a P (x,y) = (P x y)"
by (simp add: SBinder_def)

lemma EX_SBinder0: "(\<exists> x. (SBinder0 a P) x) = (\<exists> x. P x)"
by (simp add: SBinder0_def)

lemma EX_SBinder: "(\<exists> x. (SBinder a P) x) = (\<exists> x y. P x y)"
by (simp add: SBinder_def)

declare SB0_eq SB_eq EX_SBinder0 EX_SBinder[simp]
(* Addsimps [SB0_eq,SB_eq,EX_SBinder0,EX_SBinder]; *)



subsection {*DECL*}

lemma DECL_I : "\<lbrakk>A; A \<Longrightarrow> B\<rbrakk> \<Longrightarrow> A |---- B"
by (auto simp: DECL_def)

lemma DECL_D1 : "A |---- B \<Longrightarrow> A"
by (auto simp: DECL_def)

lemma DECL_D2 : "A |---- B \<Longrightarrow> B"
by (auto simp: DECL_def)

lemma DECL_E: "\<lbrakk>P |---- Q; \<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by (auto simp: DECL_def)

lemma DECL_cong:
"\<lbrakk>P = P'; P' \<Longrightarrow> Q = Q'\<rbrakk> \<Longrightarrow> (P |---- Q) = (P' |---- Q')"
by (auto simp: DECL_def)


declare DECL_I [intro!]
declare DECL_E [elim!]
declare DECL_cong [cong]
(* AddSIs [DECL_I]; AddSEs [DECL_E]; Addcongs [DECL_cong]; *)

text{* Tests: *}
ML{*
(* Syntax-Checks... *)
goalw (the_context()) [] "(SB x  ~~> y, a  ~~> b. DECL A B ) = ?X";
goalw (the_context()) [] "fgh'' = ?X "
*}

lemma SBall_I : "(\<And>x. x \<in> A \<Longrightarrow> P x) \<Longrightarrow> SBall A P"
by(auto simp: SBall_def)

lemma SBall_I2 : "(\<And>x. A x ==> P x) ==> SBall (asSet A) P"
by(auto simp: asSet_def SBall_def)

lemma bla : "(\<And>z y . x=(y,z) \<Longrightarrow> f y z) \<Longrightarrow> (SBinder a f) x"
by(auto simp: split_def SBinder_def)

lemma bla0 : "(\<And>y. x=y \<Longrightarrow> f y) \<Longrightarrow> (SBinder0 a f) x"
by(auto simp: split_def SBinder0_def)

lemma bla' : "(SBinder a f) x \<Longrightarrow>  (\<exists> y z. f y z)" 
by(auto simp: split_def SBinder_def)

lemma bla0': "(SBinder0 a f) x \<Longrightarrow> f x"
by(auto simp: split_def SBinder0_def)

lemma blaE : "(\<exists> y z. f y z \<and> x=(y,z)) \<Longrightarrow> (SBinder a f) x"
by(auto simp: split_def SBinder_def)

lemma bla0E: "(f x) \<Longrightarrow> (SBinder0 a f) x"
by(auto simp: split_def SBinder0_def)

  
lemma PRE_I : "\<lbrakk> P x \<rbrakk> \<Longrightarrow> PRE P"
by(auto simp: PRE_def)

lemma PRE_E : "\<lbrakk> PRE P; \<And> x.  P x \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by(auto simp: PRE_def)


lemma SBex_E1 : "\<lbrakk> SBex A P; \<And>x. \<lbrakk> x : A; P x \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by(auto simp: SBex_def asSet_def)

lemma SBex_E2 : "\<lbrakk> SBex (asSet A) P; \<And>x. \<lbrakk> A x; P x \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by(auto simp: SBex_def asSet_def)


lemma SBex_I1 : "\<lbrakk> P x; x : A \<rbrakk> \<Longrightarrow> SBex A P"
by(auto simp: SBex_def asSet_def)

lemma SBex_I2 : "\<lbrakk> P x; A x \<rbrakk> \<Longrightarrow> SBex (asSet A) P"
by(auto simp: SBex_def asSet_def)


lemma turnstyle_E: "|- P  \<Longrightarrow> P x"
by(auto simp: turnstyle_def)

lemma SBall_E : "\<lbrakk> SBall A P; x : A \<rbrakk> \<Longrightarrow> P x"
by(auto simp: SBall_def)

section {* Proof Support: Z-tactics *}

lemmas Z2HOL = SNAME0_def SNAME_def SBinder0_def SBinder_def turnstyle_def 
               asSet_def asPred_def DECL_def theta_def PROJ_def 
               DELTA_def XI_def PRE_def SBall_def SBex_def SBex1_def

(* bas should be:

   val set_ss =
  HOL_ss addsimps mem_simps
         addcongs [ball_cong,bex_cong]
         setmksimps (mksimps mksimps_pairs);
 *)

lemmas set_simps = insert_subset 
               insert_not_empty empty_not_insert 
               Int_absorb Int_empty_left Int_empty_right
               Un_absorb Un_empty_left Un_empty_right Un_empty
               UN_empty UN_insert image_empty
               Compl_disjoint double_complement
               Union_empty Union_insert empty_subsetI subset_refl
               Diff_cancel empty_Diff Diff_empty Diff_disjoint

lemmas prod_simps = fst_conv snd_conv split Pair_eq


subsection{* ML Code *}

ML{*
(* compatibility: *)
structure ZPure = 
struct 
   val thy = the_context()
end


val SB0_def      = thm"SBinder0_def"  val SB_def      = thm"SBinder_def"
val SNAME0_def   = thm"SNAME0_def"    val SNAME_def   = thm"SNAME_def"
val SBall_def    = thm"SBall_def"     val SBex_def    = thm"SBex_def"
val SBex1_def    = thm"SBex1_def"     val asSet_def   = thm"asSet_def"
val PRE_def      = thm"PRE_def"       val DECL_def    = thm"DECL_def"
val theta_def    = thm"theta_def"     val asPred_def  = thm"asPred_def"
val turnstyle_def= thm"turnstyle_def" val PROJ_def    = thm"PROJ_def"
val DELTA_def    = thm"DELTA_def"     val XI_def      = thm"XI_def"

val empty_not_insert = thm "empty_not_insert";

val SB0_ext      = thm"SB0_ext"      val SB_ext       = thm"SB_ext"
val turnstyle_SB0= thm"turnstyle_SB0"val turnstyle_SB = thm"turnstyle_SB"
val SB0_ext_id   = thm"SB0_ext_id"   val SB_ext_id    = thm"SB_ext_id"
val SB0_extL     = thm"SB0_extL"     val SB_extL      = thm"SB_extL"
val SB0_eq       = thm"SB0_eq"       val SB_eq        = thm"SB_eq"
val SB_pair_eq   = thm"SB_pair_eq"   val EX_SBinder0  = thm"EX_SBinder0"
val EX_SBinder   = thm"EX_SBinder"   val DECL_I       = thm"DECL_I"
val DECL_D1      = thm"DECL_D1"      val DECL_D2      = thm"DECL_D2"
val DECL_E       = thm"DECL_E"       val DECL_cong    = thm"DECL_cong"

val conv_sname0  = thm"conv_sname0"  val conv_sname   = thm"conv_sname"
val SBall_I      = thm"SBall_I"      val SBall_I2 = thm"SBall_I2" 
val SBallE       = thm"SBall_E"

val sbexE1       = thm"SBex_E1"      val sbexE2   =thm"SBex_E2" 
val sbexI1       = thm"SBex_I1"      val sbexI2   =thm"SBex_I2"
val preI         = thm"PRE_I"        val preE = thm"PRE_E" 
val bla          = thm"bla"          val bla0 = thm"bla0"
val bla'         = thm"bla'"         val bla0'= thm"bla0'"
val blaE         = thm"blaE"         val bla0E=thm"bla0E"
val turnstyleE   = thm"turnstyle_E" 

val set_ss =
  HOL_ss addsimps mem_simps
         addcongs [ball_cong,bex_cong]
         setmksimps (mksimps mksimps_pairs);

val set_ss = set_ss addsimps
  [insert_subset,
   insert_not_empty,empty_not_insert,
   Int_absorb,Int_empty_left,Int_empty_right,
   Un_absorb,Un_empty_left,Un_empty_right,Un_empty,
   UN_empty, UN_insert,image_empty,
   Compl_disjoint,double_complement,
   Union_empty,Union_insert,empty_subsetI,subset_refl,
   Diff_cancel,empty_Diff,Diff_empty,Diff_disjoint];

val prod_ss = set_ss addsimps [fst_conv, snd_conv, split, Pair_eq];

fun prover s = prove_goal HOL.thy s (fn _ => [fast_tac HOL_cs 1]);

*}


ML{*
use "ZEncoder.sml";
use "ZConversion.sml";

use "ZProofUtil.sml";        
open ZProofUtil;

(* Test *)
ZProofUtil.lift conj_commute 5; 
(*val it =  "(SB ?A ~~> x, ?A1 x ~~> xa, ?A2 x xa ~~> xb,
                 ?A3 x xa xb ~~> xc, ?A4 x xa xb xc ~~> xd. 
                       ?P5 x xa xb xc xd /\\\\ ?Q5 x xa xb xc xd) =
             (SB ?A ~~> x, ?A1 x ~~> xa, ?A2 x xa ~~> xb,
                 ?A3 x xa xb ~~> xc,  ?A4 x xa xb xc ~~> xd. 
                       ?Q5 x xa xb xc xd /\\\\ ?P5 x xa xb xc xd)" *)
*}

ML_setup{* 

fun nat_arg f = (f) oo
 (#2 oo Method.syntax(Scan.lift (Scan.optional (Args.parens Args.nat) 1)));

fun nat_thms_args f = uncurry f oo
  (#2 oo Method.syntax (Scan.lift (Scan.optional (Args.parens Args.nat) 1) -- Attrib.local_thmss));


fun tac2meth_unary tac n = Method.SIMPLE_METHOD (tac n);
fun tac2meth_binary tac thmS n = Method.SIMPLE_METHOD (tac thmS n);
fun tac2meth tac n ths = let fun multitac tac thms n = FIRST(map (fn thm => tac thm n) thms)
                         in  Method.SIMPLE_METHOD 
                                    (CHANGED_PROP (multitac tac ths n))
                         end;

val zsubst_meth  = tac2meth zstac;
val zrule_meth   = tac2meth zrtac;
val zdrule_meth  = tac2meth zdtac;
val zerule_meth  = tac2meth zetac;
val zfrule_meth  = tac2meth zftac;
val tc_meth      = tac2meth_unary tc_tac;
val zstrip_meth  = tac2meth_unary stripS_tac;
val zunfold_meth = tac2meth_binary (fn x => fn y => if x = 0 
                                                  then expand_schema_tac y 1
                                                  else full_expand_schema_tac y 1)
                   (* ^^^^^^^^^^^^^^^^^^^ HACK *) 

val zintro_schema_meth  = tac2meth_unary  intro_schema_tac;
val zintro_sch_all_meth = tac2meth_unary  intro_sch_all_tac
val zintro_sch_ex_meth  = tac2meth_unary  intro_sch_ex_tac
val zintro_pre_meth     = tac2meth_binary (fn x => fn y => intro_pre_tac y x) 
val zintro_sch_ex1_meth = tac2meth_unary  intro_sch_ex1_tac
val zelim_sch_ex_meth   = tac2meth_unary  elim_sch_ex_tac
val zelim_pre_meth      = tac2meth_unary  elim_pre_tac

*}


ML{*

val zmethods = [
  ("zsubst", nat_thms_args zsubst_meth, 
             "apply Z-rule as rewrite (improper)"),
  ("zrule", nat_thms_args zrule_meth, 
             "apply Z-rule in resolution manner (improper)"),
  ("zerule", nat_thms_args zerule_meth, 
             "apply Z-rule in elimination manner (improper)"),
  ("zdrule", nat_thms_args zdrule_meth, 
             "apply Z-rule in destruction resolution manner (improper)"),
  ("zfrule", nat_thms_args zfrule_meth, 
             "apply Z-rule in forward resolution manner (improper)"),
  ("zintro_pre", nat_thms_args zintro_pre_meth (*zfrule_meth should be:  zintro_pre_meth *), 
             "apply Z-rule in resolution manner (improper)"),
  ("tc",     nat_arg tc_meth, 
             "apply solver for typing conditions (improper)"),
  ("zstrip", nat_arg zstrip_meth, 
             "strip schema calculus operators (improper)"),
  ("zunfold", nat_thms_args zunfold_meth, 
             "unfold schema definition (improper)"),
  ("zintro_schema", nat_arg zintro_schema_meth,"intro schema expression"),
  ("zintro_sch_all",nat_arg zintro_sch_all_meth,"intro schema all quantifier"),
  ("zintro_sch_ex",nat_arg zintro_sch_ex_meth,"intro schema ex quantifier"),
  ("zintro_sch_ex1",nat_arg (tac2meth_unary intro_sch_ex1_tac),
                    "intro schema ex1 quantifier"),
  ("zelim_sch_ex",nat_arg zelim_sch_ex_meth,"eliminate schema ex quantifier"),
  ("zelim_pre",nat_arg zelim_pre_meth,"eliminate schema pre") 

 ]

val _ = Context.add_setup [Method.add_methods zmethods];

   *}

ML{* 

local
fun gen_GET thmP comb = 
    let fun apply f B (x, A) = (x, f(A,B)) 
    in Attrib.syntax ( Scan.lift (Scan.optional (Args.bracks Args.nat) 1) >> 
                       (apply (uncurry comb)))
    end;
val GET_global = gen_GET Attrib.global_thm (get_decl2);
val GET_local  = gen_GET Attrib.local_thm;
fun zstrip x = Attrib.no_args (Drule.rule_attribute (K (stripS))) x;

in

val _ = 
let val z_attributes = 
    [("zstrip",  (zstrip,zstrip),"strip schema operators"),
     ("zdecl",(gen_GET Attrib.global_thm get_decl2,
                  gen_GET Attrib.local_thm get_decl2),"get conjunct from declaration part"),
     ("zpred",(gen_GET Attrib.global_thm get_conj2,
                  gen_GET Attrib.local_thm get_conj2),"get conjunct from predicative part")]
in Context.add_setup [Attrib.add_attributes z_attributes] end;

end;
*}

setup "Context.setup ()"

end
 
