(*****************************************************************************
 * HOL-OCL --- an interactive theorem-prover for for UML/OCL
 *             http://www.brucker.ch/projects/hol-ocl/
 *                                                                            
 * ProofObligationsMgr.sml --- a generic proof obligation manager
 * This file is part of HOL-OCL.
 *
 * Copyright (c) 2006-2007, ETH Zurich, Switzerland
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)
(* $Id: ProofObligationMgr.sml 6711 2007-07-24 05:26:43Z brucker $ *)


(* A Generic Proof-Obligation(PO)Manager for Isabelle. It allows introduction 
 * and bookkeeping of PO's. The package also defines the generic part of
 * the ISAR syntax, i.e. po, discharge, list_po, show_po, etc.  Some hack 
 * prevents the easy use of sorry or done. *)



structure POKind =
  struct

    datatype kind = wff | repr | meth | lethal 
                    (* classes of proof obligations, e.g.
		       well-formedness-constraint, 
		       representational-constraint,
		       methodological-constraint
                       (resulting from analytical statements),
		       lethal-side-condition ... 
		       As "lethal side condition" we consider
		       deep logical inconsistencies that are
		       *tolerated* on the object logical level
		       (such as False on axdef in Z) *)


  end 

signature FMETHOD =
  sig
    val  PO_classifier : POKind.kind Symtab.table
                        (* data requirement: keys in symtab
			   must neither contain "_" nor "." *)
    type content        (* state of the method package *)
    val  init          : content
    val  merge         : content * content -> content
    val  print         : content -> unit
  end


signature PO_MGR =
  sig
    val  PO_state_setup   : (theory -> theory) list 
                            (* making isar initilizing
                               this component *)

    type path
    type state

    val  get_state        : theory -> state   
    val  mt_state         : state
    val  print_state      : 'a -> state -> unit

    structure FMethod     : FMETHOD
    val  get_content      : theory -> FMethod.content
    val  set_content      : FMethod.content -> theory -> theory

    val  get_path         : theory -> path
    val  set_path         : path -> theory -> theory

    val  get_prover_tab   : theory -> tactic Symtab.table
    val  set_prover_tab   : tactic Symtab.table -> theory -> theory

    type PO_name
    (* A PO_name is :  a) a path  b) a classifier c) a core name
       d) an index. (PO Management makes sure that  PO_names are unique. *)

    val  mk_PO_name       : path * string * string * int -> PO_name
    val  dest_PO_name     : PO_name -> (path * string * string * int) option

    val  declare_PO       : path option * string * string
                            -> cterm -> theory -> theory
			    
    val  prove_i_PO       : bool -> string -> theory -> theory
    (* essential discharge mechanism (classical goal package)
       PRE string must be declared PO name
       POST proof state opened in goal package.
            if bool true, then also automatic proof attempt.
       NOT ISAR READY.
     *)
    val  prove_PO     : string -> theory -> Proof.state
    (* essential discharge mechanism (ISAR version)
       PRE string must be declared PO name
       POST proof state opened in goal package.
     *)
    
    (* NOT EXPORTED:
    val  set_status_of_PO : cterm -> string -> theory -> theory
    would allow to discharge PO's. *)

    val  get_status_of_PO : cterm -> theory -> string option option

    val  get_name_of_PO   : cterm -> theory -> PO_name option

    val  get_PO_from_name : string -> theory -> cterm

    val  list_POs         : string list -> theory -> string list

    val  check_statistics : string list -> theory -> unit
  end



functor PO_Manager (FMethod : FMETHOD) : PO_MGR =
struct
    open POKind
    structure FMethod = FMethod
    val DEBUG = ref([]:string list)

    type PO_name = string

    fun isClassifier x = x mem (map fst (Symtab.dest FMethod.PO_classifier)) 

    fun mk_PO_name (path, classifier,corename,index) =
        if isClassifier classifier 
        then path^NameSpace.separator^classifier^"_"
             ^corename^"_"^(Int.toString index)
        else error "mk_PO_name"

    fun dest_PO_name name =
        let val path = NameSpace.drop_base name
        in case String.tokens (fn c => c= #"_") (NameSpace.base name) of
           [cl,co,instr] => case Int.fromString instr of 
                               SOME i => if isClassifier cl 
                                         then SOME (path,cl,co,i)
                                         else NONE
                             | NONE   => NONE
            | _ => NONE
        end

    fun mk_PO_name_base (path, classifier,corename) = 
        if isClassifier classifier 
        then path^NameSpace.separator^classifier^"_"^corename 
        else error "mk_PO_name_base"


    fun fast_cterm_ord (ct1,ct2) =
        prod_ord string_ord Term.fast_term_ord
            ((Context.theory_name (theory_of_cterm ct1), term_of ct1),
             (Context.theory_name (theory_of_cterm ct2), term_of ct2)) 

    structure Ctermtab = TableFun(type key = cterm val ord = fast_cterm_ord);

    type path  = string

    datatype state = MkState of 
                      {act_path      : path,
                       method_state  : FMethod.content,
                       PO_prover_tab : tactic Symtab.table,
				       (* PO_classifier to tactic *)
                       PO_tab        : (cterm*string option) list Symtab.table,
                                       (* PO_name without index to PO reprs *)
		       ran_PO_tab    : path Ctermtab.table
                      }

    val mt_state = MkState{act_path = "",
                           method_state = FMethod.init,
                           PO_prover_tab=Symtab.make 
                                         (map (fn (n,_)=> (n,no_tac))
                                              (Symtab.dest FMethod.PO_classifier)),
                           PO_tab = Symtab.empty,
                           ran_PO_tab = Ctermtab.empty
                          }

   fun merge_state pp (MkState state1, MkState state2) =
       let val {act_path = ap1,method_state=ms1,PO_prover_tab= pt1, 
                PO_tab = t1, ran_PO_tab = rpt1} = state1
           val {act_path = ap2,method_state=ms2,PO_prover_tab= pt2, 
                PO_tab = t2, ran_PO_tab = rpt2} = state1
       in  MkState{act_path = "",
                   method_state = FMethod.merge(ms1,ms2),
                   PO_prover_tab = pt2,
                   PO_tab = Symtab.merge(op =)(t1,t2),
                   ran_PO_tab = Ctermtab.merge(op =)(rpt1,rpt2)
                  }
       end


   fun pr1 str =(writeln""; 
                 case the(Symtab.lookup FMethod.PO_classifier str) of
                       wff   => (writeln("well-formedness proof-obligations:"^str))
                     | repr  => (writeln("representational proof-obligations:"^str))
                     | meth  => (writeln("methodological proof-obligations:"^str))
                     | lethal=> (writeln("lethal proof-obligations:"^str)));


   fun print_state thy (MkState{PO_tab, method_state, ...}) =
       let fun pr_po (name, []) = (NameSpace.base name)^" "
              |pr_po (name, S)  = String.concat
                                  (map (fn (m,n) =>(NameSpace.base name)^"_"^
                                                   (Int.toString n)^" ")
                                       (S ~~ (1 upto (length S))))   
           val dom = map pr_po (Symtab.dest PO_tab)
           fun is str = Library.mapfilter (fn x => if String.isPrefix str x
                                           then SOME(String.substring(str,size str,
                                                                         (size x) - 
                                                                         size str)) 
                                           else NONE) 
                                dom
           fun pr2 str = (let val H = is str 
                          in  if null H then ()
                              else (pr1 str; writeln (String.concat H))
                          end)
    in  Library.seq (pr2 o fst) (Symtab.dest FMethod.PO_classifier);
        writeln ("FMethod Package Content:"); FMethod.print method_state  
    end


   structure PO_Data : THEORY_DATA_ARGS =
   struct
     val name = "PO-mgr-state"
     type T = state
     val empty = mt_state
     fun copy T = T
     fun prep_ext T = T
     fun extend T = T
     val merge  = merge_state
     val print  = print_state
   end;

   structure PO_state_management = TheoryDataFun(PO_Data);
   val PO_state_setup = [PO_state_management.init]

   val get_state = PO_state_management.get

   fun set_path path = 
       let fun f (MkState{act_path,method_state,PO_prover_tab,PO_tab,ran_PO_tab}) =  
                 (MkState{act_path=path,method_state=method_state,PO_prover_tab=PO_prover_tab,
                          PO_tab=PO_tab,ran_PO_tab=ran_PO_tab})
       in  PO_state_management.map f end

   fun get_path thy =
       let val MkState{act_path, ...} = PO_state_management.get thy
       in  act_path end


   fun set_content ct = 
       let fun f (MkState{act_path,method_state,PO_prover_tab,PO_tab,ran_PO_tab}) =  
                 (MkState{act_path=act_path,method_state=ct,PO_prover_tab=PO_prover_tab,
                          PO_tab=PO_tab,ran_PO_tab=ran_PO_tab})
       in  PO_state_management.map f end
  
   fun get_content thy =
       let val MkState{method_state, ...} = PO_state_management.get thy
       in  method_state end
 
   fun set_prover_tab tab = 
       let fun f (MkState{act_path,method_state,PO_prover_tab,PO_tab,ran_PO_tab}) =  
                 (MkState{act_path=act_path,method_state=method_state,PO_prover_tab=tab,
                          PO_tab=PO_tab,ran_PO_tab=ran_PO_tab})
       in  PO_state_management.map f end


   fun get_prover_tab thy =
       let val MkState{PO_prover_tab, ...} = PO_state_management.get thy
       in  PO_prover_tab end

   fun get_name_of_PO ct thy = 
       let val MkState{act_path,method_state,PO_prover_tab,PO_tab,ran_PO_tab} = 
                       PO_state_management.get thy 
       in  Ctermtab.lookup ran_PO_tab ct
       end 


   fun get_status_of_PO  ct thy =
       (* PRE: ct is a declared PO *)
       let val p = the(get_name_of_PO ct thy)
           val SOME(path,class,core,n) = dest_PO_name p
           val MkState{act_path,method_state,PO_prover_tab,PO_tab,ran_PO_tab} = 
                                PO_state_management.get thy 
           val SOME ll = Symtab.lookup PO_tab (mk_PO_name_base(path,class,core))
           val (_,status) = List.nth(ll,n-1)
       in  SOME status end;


   fun get_PO_from_name name thy = 
       let val (path,class,core,n) = case dest_PO_name name of
                                       NONE => error("illegal name format:" ^ name)
				     | SOME x => x
           val MkState{act_path,method_state,PO_prover_tab,PO_tab,ran_PO_tab} = 
                                PO_state_management.get thy 
           val ll = Symtab.lookup PO_tab (mk_PO_name_base(path,class,core))
       in  case ll of 
             SOME ll => if n <= length ll then (fst(List.nth(ll,n-1)))
                        else error"get_PO_from_name: undeclared PO name (index)"
           | NONE    => error"get_PO_from_name: undeclared PO name"
       end


   fun set_status_of_PO ct po_attempt thy =
         (* PRE: ct is a declared PO *)
       let val p = case (get_name_of_PO ct thy) of
                     NONE =>  error("unknown proof obligation:" ^ 
		                    (Sign.string_of_term thy (term_of ct)))
                   | SOME p => p
           val SOME(path,class,core,n) = dest_PO_name p
           val poname_base = mk_PO_name_base(path,class,core) 
           val MkState{act_path,method_state,PO_prover_tab,PO_tab,ran_PO_tab} = 
                               PO_state_management.get thy 
           val SOME ll = Symtab.lookup PO_tab poname_base
           val ll'     = map_nth_elem (n-1) 
                                      (fn (ct,_) => (ct, SOME po_attempt))
                                      (ll)
           val PO_tab' = Symtab.update(poname_base,ll')(PO_tab)
           val state'  = MkState{act_path=act_path,method_state=method_state,
                                 PO_prover_tab=PO_prover_tab,
                                 PO_tab=PO_tab',ran_PO_tab=ran_PO_tab} 
       in  PO_state_management.put state' thy
       end




   fun declare_PO (path_O, class, core) (ct) (thy) =
                           (* PRE : path_0 must be path, class a classifier.
			            cterm must be of type prop.
				    It can contain free vars and
				    free typevars.
			      POST: Generates unique name
			            (cterm decides !!!) and 
				    entry in PO_tab *)
       let val _  = if isClassifier class 
                    then ()
                    else error "declare_PO: not leagal classifier"
           val MkState{act_path,method_state,PO_prover_tab,PO_tab,ran_PO_tab} = 
                       PO_state_management.get thy 
           val path =(case path_O of
                        SOME(p) => p
                      | NONE    => act_path)
       in case Ctermtab.lookup ran_PO_tab ct of
           SOME _ => thy (* PO exists already *)
         | NONE   =>(let val poname_base = mk_PO_name_base(path,class,core) 
                         val po_s   = case Symtab.lookup PO_tab poname_base of
                                        NONE => []
                                       |SOME p => p
                         val poname = poname_base^"_"^
                                      (Int.toString (length po_s + 1))
                         val ran_PO_tab' = Ctermtab.update(ct,poname)
                                                          (ran_PO_tab)
                         val PO_tab' = Symtab.update(poname_base,
                                                     po_s@[(ct,NONE)])
                                                    (PO_tab) 
                     in  PO_state_management.put 
                         (MkState{act_path=act_path,method_state=method_state,
                                  PO_prover_tab=PO_prover_tab,
                                  PO_tab=PO_tab',ran_PO_tab=ran_PO_tab'}) thy
                     end)
      end  


    fun prove_i_PO discharge_automatic name thy =
    let val MkState{act_path,method_state,PO_prover_tab,PO_tab,ran_PO_tab} = 
                       PO_state_management.get thy 
        val (path,class,core,n) = case dest_PO_name name of
	                            SOME x => x
			          | NONE => error"illegal format of PO name"
        val poname_base = mk_PO_name_base(path,class,core)
        val ll = case Symtab.lookup PO_tab poname_base of 
                   NONE => error("undeclared proof obligation: "^name)
                 | SOME ll => ll
        val (po,_) = List.nth(ll,n-1)
	val name' = mk_PO_name(Context.theory_name thy, class,core,n)
        val thy' = set_status_of_PO po name' thy 
        val tac = case Symtab.lookup PO_prover_tab class of
                    NONE => no_tac
                  | SOME tac => tac
        fun nthm () = prove_goalw_cterm [] po (fn prems => [cut_facts_tac prems 1,tac]) 
    in  if discharge_automatic 
	then (bind_thm(name',nthm()); thy')
        else (goalw_cterm [] (po);thy')
    end


    fun prove_PO name thy =
    let val ct = get_PO_from_name name thy
        val y' = ("",[])
        val w' = [(((* NameSpace.base *) name,[]),[(term_of ct,([],[]))])]
    in  (Proof.theorem_i Drule.lemmaK (K (K I)) (SOME "") y' w' o 
         ProofContext.init) thy 
    end

    fun gen_store_PO_attempt opt_lemmaname name thy =
    let val ct = get_PO_from_name name thy
        val (path,class,core,n) = case dest_PO_name name of
	                            SOME x => x
			          | NONE => error"illegal format of PO name"
	val name'  = case opt_lemmaname of
                      NONE => mk_PO_name(Context.theory_name thy,class,core,n)
                              (* generic name *)
                     |SOME x=>(Context.theory_name thy^NameSpace.separator^x)
                              (* user controlled name *)   
    in  set_status_of_PO ct name' thy end 


   fun list_POs filtr thy =
       let val _ = if forall isClassifier filtr then ()
                   else error"not a classifier"
           val MkState{act_path,method_state,PO_prover_tab,PO_tab,ran_PO_tab} = 
                               PO_state_management.get thy
           fun isExcluded name_base = let val (_,class,_,_)=
                                              the(dest_PO_name(name_base^"_1"))
                                      in class mem filtr end 
           fun expand (nb,S) = if isExcluded nb
                               then []
                               else map (fn ((_,stat),x)=>
                                             (nb^"_"^(Int.toString x)^" ",stat)) 
                                        (S ~~ (1 upto length S))
           val cc = Library.flat (map expand (Symtab.dest PO_tab))
       in  (map fst cc) end


   fun check_statistics ignore_class_list thy =  
       let val MkState{act_path,method_state,PO_prover_tab,PO_tab,ran_PO_tab} = 
                               PO_state_management.get thy
           fun expand (nb,S) = map (fn ((_,stat),x)=>(nb^"_"^(Int.toString x),stat)) 
                                   (S ~~ (1 upto length S))
           val cc = Library.flat (map expand (Symtab.dest PO_tab))
           fun check (name,status) = case status of
                                      NONE => true (* no proof attempt *)
                                    | SOME p => ((Goals.get_thm thy p; false)  
                                                (* Has theorem really been
                                                   proven, i.e. has the proof
                                                   been completed? 
                                                   At the moment, there is no
                                                   check for sorry ... *)
                                                 handle _ => true)
           val not_discharged = filter check cc
           val _ = let val classes = (map fst (Symtab.dest FMethod.PO_classifier)) 
                   in  if forall(fn x => x mem classes) ignore_class_list
                       then ()
                       else error"Undefined PO class!"
                   end
           fun is_name_of_class class n = let val (_,cl,_,_)=the(dest_PO_name n)
                                          in cl = class end
           fun is_PO_in_class class = (class, 
                                       filter ((is_name_of_class class) o fst) 
                                              not_discharged)
           val class_nds = map is_PO_in_class ignore_class_list
           fun sum [] = 0 | sum (a::R) = a + (sum R)
           val no_ignored_nd  = sum (map (length o snd) class_nds) 
           val no_nd = (length not_discharged) - no_ignored_nd  
           fun pr3 (class, []) = ()
              |pr3 (class, S) = (pr1 class; Library.seq (fn (n,_) => writeln n) S)  
       in  writeln("Statistics of Proof-Obligations:");
           writeln("================================");
           if no_ignored_nd > 0 
           then writeln("There are "^(Int.toString no_ignored_nd)^
                        " unproven proof-obligations (ignored due to filtering). ")
           else ();
           if no_nd > 0
           then error("There are "^(Int.toString no_nd)^
                      " unproven proof-obligations (can not ignore!). \n"^ 
                      "Check failed.")
           else ();
           if  no_ignored_nd <= 0 andalso no_nd <= 0
           then (writeln ("There have been "^Int.toString(length cc)^
                          " proof obligations.");
                 if length cc > 0 
                 then writeln ("All of them have been discharged.")
                 else ())
           else ()
       end     



structure P = OuterParse and K = OuterKeyword;

val show_poP =
  let val xname1 = Scan.repeat1 P.xname
      fun show_pos S state = let val thy = Toplevel.theory_of state 
                                 fun H x = writeln (Sign.string_of_term thy (term_of
                                                     (get_PO_from_name x thy)));
                             in  List.app H S end
  in  OuterSyntax.improper_command "show_po" "print proof obligation" K.diag
      (xname1 >> (fn str =>  Toplevel.keep(show_pos str)))
  end;
val _ =  OuterSyntax.add_parsers [show_poP];


val poP =
  let fun store name  =  gen_store_PO_attempt NONE name
  in  OuterSyntax.command "po" 
                          "prove proof obligation" 
                          K.thy_goal
      (P.xname >> (fn x => (Toplevel.print 
                            o (Toplevel.theory_to_proof(prove_PO x)))))
  end;
val _ =  OuterSyntax.add_parsers [poP];


fun dischargedT prf =
    let
        val prt_md_S  = (!print_mode)
        val _         = (print_mode:=["ProofGeneral","PGASCII"]);
        val prf_state = ProofHistory.current prf;
        val thy       = Proof.theory_of prf_state;
        val name      = let
                           val goal = hd(filter(fn x=>String.isPrefix"goal" x)
                                               (map Pretty.string_of 
                                                    (Proof.pretty_state 0 
                                                             prf_state)))
                           val _::_::name::_ = if (goal = "")
                                               then ["","",""]
                                               else String.tokens 
                                                   (fn x => x = #"(" orelse 
                                                            x = #")") 
                                                    goal
                         in
                           name
                         end
        val _          = writeln (name^" discharged.");
        val top_thm    = snd(snd(Proof.get_goal(prf_state)));
        val thy        = fst(PureThy.add_thms 
                              [((NameSpace.base name,top_thm),[])] 
                              (thy));
        val thy        = gen_store_PO_attempt NONE name thy
    in
        print_mode:=prt_md_S;
        thy
    end


val dischargedP =
    OuterSyntax.command "discharged" 
                        "proof obligation discharged (and theorem stated)"
                        OuterKeyword.qed_global
                        (Scan.succeed (Toplevel.print3 o 
                                       (Toplevel.proof_to_theory dischargedT)));
val _ =  OuterSyntax.add_parsers [dischargedP];


val list_poP =
  let val xname1 =  Scan.optional (P.$$$ "except" |-- (Scan.repeat1 P.xname)) []
      fun list_PO S state = List.app writeln (list_POs S (Toplevel.theory_of state))
  in  OuterSyntax.improper_command "list_po" "list impending proof obligations" 
      K.diag (xname1 >> (fn str => Toplevel.keep (list_PO str)))
  end;
val _ = OuterSyntax.add_parsers  [list_poP];
val _ = OuterSyntax.add_keywords ["except"];


val check_poP =
  let val xname1 =  Scan.optional (P.$$$ "except" |-- (Scan.repeat1 P.xname)) []
      fun check_po S state = check_statistics S (Toplevel.theory_of state)
  in  OuterSyntax.improper_command "check_po" "check proof obligation" K.diag
      (xname1 >> (fn str => Toplevel.keep (check_po str)))
  end;   
val _ =  OuterSyntax.add_parsers [check_poP];


end (*struct*)

