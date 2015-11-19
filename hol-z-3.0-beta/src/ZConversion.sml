(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ZConversion.sml --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 2000-2003, University Freiburg, Germany
 *               2003-2007, ETH Zurich, Switzerland
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
(* $Id: ZConversion.sml 6729 2007-08-03 05:25:17Z brucker $ *)

structure ZConversion =
    struct 
	
        open ZPrelude HOLogic ZAbsy;
	    
(* ******************************************************************* *)
(*                                                                     *)
(* General term operations                                             *)
(*                                                                     *)
(* ******************************************************************* *)

(* fun list_comb term * term list => term -- as usual *)

	fun k_tr (*"_K"*) t = Abs ("uu", dummyT, incr_boundvars 1 t)
	fun foldr_term_K(term,termS) = foldr1 (fn(x,y) => term $ x $ (k_tr y)) termS;
 
	fun stripName n = n;

	fun foldl_term(term,termS) = Library.foldl  (fn(x,y) => term $ x $ y) 
					    (hd termS,tl termS);
					   
        fun foldr_term(term,termS) = Library.foldr1 (fn(x,y) => term $ x $ y) termS;

	fun last l = hd(rev l);

	fun front l = Library.take(length(l)-1,l);

	fun build_split(names, term) = 
	    let val la = last names
	    	fun cv(n,t) = 
		    Const("split",dummyT) $ 
			 Abs((stripName n),dummyT,
			     abstract_over1(Free((stripName n),dummyT), t)) 
	    in List.foldr cv 
			      (Abs((stripName la), dummyT,
				   abstract_over1(Free((stripName la),dummyT), 
								     term)))
			      (front names)
	    end;

	fun build_tlist(names, T) = 
	    let	fun cv(n,t) = Const("op &",dummyT) $ t $ 
				   (Const("op :",dummyT) $
					 Free((stripName n),dummyT) $ T) 
	    in List.foldr cv 
			      (Const("op :",dummyT) $ 
				    Free(stripName(hd names),dummyT) $ T)
			      (tl names)
	    end;


(* ******************************************************************* *)
(*                                                                     *)
(* Types                                                               *)
(*                                                                     *)
(* ******************************************************************* *)
(* here is the coding scheme for Z types to HOL types represented.
   Note that schemas (having type P (| x1 :-> t1, ..., xn :-> tn|)
   were represented as predicates, and bindings(or "signatures" or 
   "records") as sorted cartesian products. *)

   fun mk_sumT (T1, T2) = Term.Type ("+", [T1, T2]);



        fun conv2typ (Type(t)) = conv2typ t
	   |conv2typ (NameAppl("baseNum",[])) = Term.Type("int",[])
	   |conv2typ (NameAppl("denotation",[])) = Term.Type("string",[])
	   |conv2typ (NameAppl(str,[])) = Term.Type(str,[])
	   |conv2typ (Unary(Power, m as Signature(sgs))) = 
	                           (conv2typ m) --> HOLogic.boolT
	   |conv2typ (Unary(Power, s)) = Term.Type("set", [conv2typ s])
	   |conv2typ (Signature sgs) = ZPrelude.gen_bindingT
	                                        (map(fn(s,t)=>
						       (s,conv2typ t))
					            sgs)
	   |conv2typ (Product[NameAppl("Prelude_SUM",[]),
                              Unary(Power,S), Unary(Power,T)]) 
                      = Term.Type("+",[conv2typ S, conv2typ T])
       	   |conv2typ (Product S) = foldr1 HOLogic.mk_prodT (map conv2typ S)



	fun convTjdmt(Type(Unary(Power, Signature sgr))) =
	                           SOME(map(fn(s,t)=>(s,conv2typ t)) sgr)
 	   |convTjdmt _ = NONE 

(* ******************************************************************* *)
(*                                                                     *)
(* Expressions                                                         *)
(*                                                                     *)
(* ******************************************************************* *)

	(* val Number : string -> Expr *)
        fun convNumber(str) = case Int.fromString(str) of
                                SOME n => mk_int(IntInf.fromInt( n ))
                              | NONE   => error"convNumber: No integer string!"
             

	(* val Denotation : string -> Expr *)  
        and convDenotation(str) = mk_string str

	
	(* val NameAppl : string * Expr list -> Expr (* variables *) *)
        and convNameAppl("nat",[]) = Const ("ZMathTool.Naturals",dummyT)
	  | convNameAppl("num",[]) = Const ("ZMathTool.Integers",dummyT)
	  | convNameAppl("finset_",[expr]) = Const ("ZMathTool.Fin",dummyT) 
					       $ (convExpr expr)
	  | convNameAppl("seq_",[expr]) = Const ("ZSeq.seq",dummyT) 
					       $ (convExpr expr)
	  | convNameAppl("seq_1_",[expr]) = Const ("ZSeq.seq1",dummyT) 
					       $ (convExpr expr)
	  | convNameAppl("iseq_",[expr]) = Const ("ZSeq.iseq",dummyT) 
					       $ (convExpr expr)
          | convNameAppl("_in_",[]) = Const("op :", dummyT)
          | convNameAppl("_=_",[]) = Const("op =",dummyT)
          | convNameAppl("_<_",[]) = Const("op <",dummyT)
          | convNameAppl("_leq_",[]) = Const("op <=",dummyT)
          | convNameAppl("_>_",[]) = error ">: NOT YET IMPLEMENTED !"
          | convNameAppl("_geq_",[]) = error "geq: NOT YET IMPLEMENTED !"
	  | convNameAppl("_pfun_",S) = 
	    list_comb (Const("ZMathTool.partial_func",dummyT), map convExpr S)
	  | convNameAppl("_fun_",S) = 
	    list_comb (Const("ZMathTool.total_func",dummyT), map convExpr S)
	  | convNameAppl("_pinj_",S) = 
	    list_comb (Const("ZMathTool.partial_inj",dummyT), map convExpr S)
	  | convNameAppl("_inj_",S) = 
	    list_comb (Const("ZMathTool.total_inj",dummyT), map convExpr S)
	  | convNameAppl("_psurj_",S) = 
	    list_comb (Const("ZMathTool.partial_surj",dummyT), map convExpr S)
	  | convNameAppl("_surj_",S) = 
	    list_comb (Const("ZMathTool.total_surj",dummyT), map convExpr S)
	  | convNameAppl("_bij_",S) = 
	    list_comb (Const("ZMathTool.biject",dummyT), map convExpr S)
	  | convNameAppl("_finj_",S) = 
	    list_comb (Const("ZMathTool.fin_part_inj",dummyT), map convExpr S)
	  | convNameAppl("_ffun_",S) = 
	    list_comb (Const("ZMathTool.fin_part_func",dummyT), map convExpr S)
	  | convNameAppl("_rel_",[e1,e2]) = Const("ZMathTool.rel",dummyT) $
						 (convExpr e1) $ (convExpr e2)
	  | convNameAppl("dom",[])   = Const("Domain",dummyT)
	  | convNameAppl("front",[]) = Const("frontseq",dummyT)
	  | convNameAppl("last",[])  = Const("lastseq",dummyT)
	  | convNameAppl("head",[])  = Const("headseq",dummyT)
	  | convNameAppl("tail",[])  = Const("tailseq",dummyT)
	  | convNameAppl("_cat_",[]) = Const("concatseq",dummyT)
	  | convNameAppl("rev",[])   = Const("revseqseq",dummyT)
	  | convNameAppl("_extract_",[])  = Const("extraction",dummyT)
	  | convNameAppl("_filter_",[])   = Const("filtering",dummyT)
	  | convNameAppl("_prefix_",[])   = Const("prefixseq",dummyT)
	  | convNameAppl("_suffix_",[])   = Const("suffixseq",dummyT)
	  | convNameAppl("_inseq_",[])    = Const("inseq",dummyT)
	  | convNameAppl("emptyset",[])   = Const("{}",dummyT)
	  | convNameAppl("denotation",[]) = Const("String",dummyT)
	  | convNameAppl("id_",[expr]) = Const("idZ",dummyT) $ (convExpr expr)
          (* handling of generics by catchall.
             Exceptions: Inr and Inl that were coded inline *)
          | convNameAppl("Inr",S) = Const("Inr",dummyT)
          | convNameAppl("Inl",S) = Const("Inl",dummyT)
          | convNameAppl(name,S) = 
            list_comb (Free((stripName name),dummyT), map convExpr S)   
            (* generic catch-all *)

	

	(* val Tuple : Expr list -> Expr *)
        and convTuple(exprS) = 
            foldr_term(Const("Pair",dummyT), map convExpr exprS)
	

	(* val Product : Expr list -> Expr *)
        and convProduct(exprS) =
            foldr_term_K(Const("Sigma", dummyT), map convExpr exprS)


	(* val Binding : Expr list -> Expr *)
        and convBinding(exprS) = 
            gen_binding (map (fn Eqn(a,e,t) => (a,convExpr e)) exprS)	

	(* val Signature : (string * Expr) list -> Expr *)
        and convSignature(bdS) = 
            error "Signature: NOT YET IMPLEMENTED !"
	

	(* val Display : Expr list -> Expr *)
        and convDisplay(exprS)= 
	    foldr_term(Const("insert",dummyT), 
		       (map convExpr exprS) @ [Const("{}",dummyT)])


	(* val Cond : Expr * Expr * Expr -> Expr *)
        and convCond(cond,thenB,elseB) =
            Const("If",dummyT) $ (convExpr cond)
                               $ (convExpr thenB) 
                               $ (convExpr elseB) 
	

	and prodz_list names = 
	    let fun getT T n = convExpr T
		fun vars (Direct(ns,T)) = map (getT T) ns
		  | vars _ = error("*** prodz_list called with wrong args...\n")
		val ts = List.concat (map vars names)
		fun cv (t1,t2) = Const("prodZ",dummyT) $ t1 $ t2
	    in 
		List.foldr cv (last ts) (front ts)
	    end


	(* val Quantor : QuantorKind * Expr list * Expr list * Expr -> Expr *)
	and convQuantor(Forall,decls,[],pred) = 
	    let fun cc (Direct(names,E), t) = 
		    let fun cv(n,trm) = 
			    Const("Ball",dummyT) $ convExpr E $
				 Abs((stripName n),dummyT,  
				     abstract_over1
					 (Free((stripName n),dummyT), trm))
		    in  List.foldr cv t names end
		  | cc (SchemaName(n,_,[]), t) = 
		    Const ("%A",dummyT) $ Free(n,dummyT) $ t
	    in List.foldr cc (convExpr pred) decls end
	  | convQuantor(Forall,decls,[pred],expr) = 
	    let fun cc (Direct(names,E), t) = 
		    let fun cv(n,trm) = 
			    Const("Ball",dummyT) $ convExpr E $
				 Abs((stripName n),dummyT,  
				     abstract_over1
					 (Free((stripName n),dummyT), trm))
		    in  List.foldr cv t names end
		  | cc (SchemaName(n,_,[]), t) = 
		    Const ("%A",dummyT) $ Free(n,dummyT) $ t
	    in List.foldr 
		   cc 
		   (Const ("op -->",dummyT) $ (convExpr pred) $ 
			  (convExpr expr))
		   decls 
	    end
	  | convQuantor(Forall,decls,preds,expr) = 
 	    let val pred = list_comb(Const("op &",dummyT), 
				     map convExpr preds) 
		fun cc (Direct(names,E), t) = 
		    let fun cv(n,trm) = 
			    Const("Ball",dummyT) $ convExpr E $
				 Abs((stripName n),dummyT,  
				     abstract_over1
					 (Free((stripName n),dummyT), trm))
		    in  List.foldr cv t names end
		  | cc (SchemaName(n,_,[]), t) = 
		    Const ("%A",dummyT) $ Free(n,dummyT) $ t
	    in  List.foldr 
		    cc 
		    (Const ("op -->",dummyT) $ pred $ (convExpr expr))
		    decls
	    end
	  | convQuantor(Exists,decls,[],pred) = 
	    let fun cc (Direct(names,E), t) = 
		    let fun cv(n,trm) = 
			    Const("Bex",dummyT) $ convExpr E $
				 Abs((stripName n),dummyT,  
				     abstract_over1
					 (Free((stripName n),dummyT), trm))
		    in  List.foldr cv t names end
		  | cc (SchemaName(n,_,[]), t) = 
		    Const ("%E",dummyT) $ Free(n,dummyT) $ t
	    in List.foldr cc (convExpr pred) decls end
	  | convQuantor(Exists,decls,[pred],expr) = 
	    let fun cc (Direct(names,E), t) = 
		    let fun cv(n,trm) = 
			    Const("Bex",dummyT) $ convExpr E $
				 Abs((stripName n),dummyT,  
				     abstract_over1
					 (Free((stripName n),dummyT), trm))
		    in  List.foldr cv t names end
		  | cc (SchemaName(n,_,[]), t) = 
		    Const ("%E",dummyT) $ Free(n,dummyT) $ t
	    in List.foldr 
		   cc 
		   (Const ("op &",dummyT) $ (convExpr pred) $ (convExpr expr))
		   decls 
	    end
	  | convQuantor(Exists,decls,preds,expr) = 
	    let val pred = list_comb(Const("op &",dummyT), 
				     map convExpr preds) 
		fun cc (Direct(names,E), t) = 
		    let fun cv(n,trm) = 
			    Const("Bex",dummyT) $ convExpr E $
				 Abs((stripName n),dummyT,  
				     abstract_over1
					 (Free((stripName n),dummyT), trm))
		    in  List.foldr cv t names end
		  | cc (SchemaName(n,_,[]), t) = 
		    Const ("%E",dummyT) $ Free(n,dummyT) $ t
	    in  List.foldr 
		    cc 
		    (Const ("op &",dummyT) $ pred $ (convExpr expr))
		    decls
	    end
	  | convQuantor(Set,[Direct(names,E)],[pred],expr) =
	    Const("image",dummyT) $ (build_split(names,(convExpr expr))) $
		 (Const("asSet",dummyT) $ 
		       build_split(names,(Const("op &", dummyT) $
					       (build_tlist(names, 
							    (convExpr E))) $
					       (convExpr pred))))
	 (* special handling of set comprehension, when we quantify over
	    schemas. Done inside ZEncoder analogously to 
	    schema-quantifiers ... *)
	  | convQuantor(Set,[SchemaName(n,_, [])], [],expr) =
	    Const("_schset",dummyT) $ (Free(n,dummyT)) $ (convExpr expr)
	  | convQuantor(Set,decls,[],expr) =
	    let fun decl_names (Direct(ns,e)) = ns 
		val names = List.foldr op@ [] (map decl_names decls)
		val t_const = 
		    let fun bs (Direct(ns,E), t) = 
			    Const("op &",dummyT) $ 
				 build_tlist(ns,(convExpr E)) $ t
			fun t_last (Direct(ns,E)) = build_tlist(ns,(convExpr E))
		    in
			List.foldr bs (t_last(hd decls)) (tl decls)
		    end
 	    in Const("image",dummyT) $ (build_split(names,(convExpr expr))) $
		    (Const("asSet",dummyT) $ 
			  build_split(names, t_const))
	    end
	  | convQuantor(Set,decls,[pred],expr) =
	    let fun decl_names (Direct(ns,e)) = ns 
		val names = List.foldr op@ [] (map decl_names decls)
		val t_const = 
		    let fun bs (Direct(ns,E), t) = 
			    Const("op &",dummyT) $ 
				 build_tlist(ns,(convExpr E)) $ t
		    in
			List.foldr bs (convExpr pred) decls
		    end
 	    in Const("image",dummyT) $ (build_split(names,(convExpr expr))) $
		    (Const("asSet",dummyT) $ 
			  build_split(names, t_const))
	    end
          | convQuantor(Set,decls,preds,expr) =
	    let val pred = list_comb(Const("op &",dummyT), 
				     map convExpr preds) 
		fun decl_names (Direct(ns,e)) = ns 
		val names = List.foldr op@ [] (map decl_names decls)
		val t_const = 
		    let fun bs (Direct(ns,E), t) = 
			    Const("op &",dummyT) $ 
				 build_tlist(ns,(convExpr E)) $ t
		    in
			List.foldr bs pred decls
		    end
 	    in Const("image",dummyT) $ (build_split(names,(convExpr expr))) $
		    (Const("asSet",dummyT) $ 
			  build_split(names, t_const))
	    end
	  | convQuantor(Lambda,decls,[],expr) = 
	    let fun decl_names (Direct(ns,e)) = ns 
		val names = List.foldr op@ [] (map decl_names decls)
		val prod = prodz_list decls
 	    in 
		Const("Lambda",dummyT) $ 
		     prod $ (build_split(names,(convExpr expr)))
	    end
          | convQuantor(Lambda,decls,preds,expr) =
	    error "Lambda with predicates: NOT YET IMPLEMENTED !"	    
	  | convQuantor(Mu,decls,[pred],expr) = 
	    let fun decl_names (Direct(ns,e)) = ns 
		val names = List.foldr op@ [] (map decl_names decls)
		val prod = prodz_list decls
 	    in 
		build_split(names, (convExpr expr)) $ 
			   (Const("Mu",dummyT) $ prod $ 
				 (build_split(names, (convExpr pred))))
	    end
          | convQuantor(Mu,decls,preds,expr) =
	    let fun decl_names (Direct(ns,e)) = ns 
	        val pred = list_comb(Const("op &",dummyT), 
				     map convExpr preds) 
		val names = List.foldr op@ [] (map decl_names decls)
		val prod = prodz_list decls
 	    in 
		build_split(names, (convExpr expr)) $ 
			   (Const("Mu",dummyT) $ prod $ 
				 (build_split(names, pred)))
	    end
          | convQuantor(Let,[Eqn(name,E,t)],[],body) = 
	    Const("Let",dummyT) $ convExpr E $
		 Abs((stripName name),dummyT,  
		     abstract_over1
			 (Free((stripName name),dummyT), convExpr body))
          | convQuantor(Let,eqns,preds,body) = 
	    error "Let with multiple eqns: NO YET IMPLEMENTED!"
          | convQuantor(qK,args,projs,pred) = 
	    error "Quantor: NOT YET IMPLEMENTED !"
		  
	(* val SchemaText : Expr list * Expr list -> Expr *)
	(* schema with empty predicate part *)
        and convSchemaText(e1,[]) = 
            let fun convDecl (Direct(nameS, tt)) =
                    let val et = convExpr tt
                        fun cv x = Const("op :",dummyT) $
					Free((stripName x),dummyT) $ et
                    in  foldr_term(Const("op &",dummyT), 
                                   map cv  nameS) 
                    end
		  | convDecl (NameAppl(s,[])) = Free((stripName s),dummyT)
		  | convDecl (Unary(S,T)) = convUnary(S, T)
		  | convDecl (SchemaName(s,_,[])) = Free((stripName s),dummyT)
            in  Const("ZPure.DECL", dummyT) 
                $ (foldr_term(Const("op &",dummyT), map convDecl e1))
                $ (Const("True",dummyT))
            end	
          | convSchemaText(e1,e2) = 
            let fun convDecl (Direct(nameS, tt)) =
                    let val et = convExpr tt
                        fun cv x = Const("op :",dummyT) $
					Free((stripName x),dummyT) $ et
                    in  foldr_term(Const("op &",dummyT), 
                                   map cv  nameS) 
                    end
		  | convDecl (NameAppl(s,[])) = Free((stripName s),dummyT)
		  | convDecl (Unary(S,T)) = convUnary(S, T)
		  | convDecl (SchemaName(s,_,[])) = Free((stripName s),dummyT)
            in  Const("ZPure.DECL", dummyT) 
                $ (foldr_term(Const("op &",dummyT), map convDecl e1))
                $ (foldr_term(Const("op &",dummyT), map convExpr e2))
            end	

	(* val Select : Expr * Expr * Expr -> Expr *)
        and convSelect(E,NameAppl(x,[]),Type(Signature S)) = 
            let val e = convExpr E
                val tagS = map fst S
		val strippedTagS = map stripName tagS
            in  gen_projection (stripName x) e strippedTagS end
           |convSelect(_,_,_) = 
               error "Select: NOT YET IMPLEMENTED !"
           
	(* val Unary : UnaryKind * Expr -> Expr *)
        and convUnary(Power,expr) = 
                      Const("Pow",dummyT) $ (convExpr expr)
           |convUnary(Not,expr)   = 
                      Const("Not",dummyT) $ (convExpr expr)
           |convUnary(Theta,SchemaName(n,t,[])) = 
                      Const("%theta", dummyT) $ (Free (n, dummyT) $
						      (convSchemaType t))
           |convUnary(Theta,NameAppl(n,[])) = 
                      Const("%theta", dummyT) $ Free (n, dummyT)
           |convUnary(Delta,NameAppl(str,[])) = 
                      Const("DELTA",dummyT) 
                      $ Free ((stripName str),dummyT)
                      $ Free (ZPrelude.stroke ((stripName str),dummyT))
           |convUnary(Delta,_) = error "Unary: illegal DELTA expression !"
           |convUnary(Xi,NameAppl(str,[]))    = 
                      Const("XI",dummyT) $
                        (Const("DELTA",dummyT) 
                         $ Free ((stripName str),dummyT)
                         $ Free (ZPrelude.stroke ((stripName str),dummyT)))
                      $ (Const("%theta",dummyT)$Free((stripName str),dummyT))
                      $ (Const("%theta",dummyT)
                         $ Free(ZPrelude.stroke ((stripName str),dummyT)))
           |convUnary(Xi,_)    = error "Unary: illegal Xi expression !"
                      
           |convUnary(Pre,expr)   = Free("pre",dummyT) $ (convExpr expr)

           |convUnary(Hide,expr)  = error "Unary: NOT YET IMPLEMENTED !"
           (* We only support decorated schema names, not
              general schema expressions. *)
           |convUnary(Decorate,NameAppl(name,[])) = 
		      Free (ZPrelude.stroke ((stripName name),dummyT))
           |convUnary(Decorate,expr) = 
                      error "Decorate with schema expression: NOT YET IMPLEMENTED !"

	(* val Binary : BinaryKind * Expr * Expr -> Expr *)
        and convBinary(And,expr1,expr2) =
                       Const("op &",dummyT) $ (convExpr expr1)
                                            $ (convExpr expr2) 
	  |convBinary(Or,expr1,expr2) =
                       Const("op |",dummyT) $ (convExpr expr1)
		       $ (convExpr expr2) 
	  |convBinary(Iff,expr1,expr2) =
                       Const("op =",dummyT) $ (convExpr expr1)
		       $ (convExpr expr2) 
	  |convBinary(Implies,expr1,expr2) =
                       Const("op -->",dummyT) $ (convExpr expr1)
		       $ (convExpr expr2) 
          (* We must distinguish the Z apply and the HOL apply operator here: 
             for HOL-Z internals (e.g. dom, ran) we use $ for efficiency. For 
	     arbitrary expressions we use the HOL-Z apply operator. *)
	  |convBinary(Apply, Binary(Apply, NameAppl("iter",[]),nexpr), rexpr)=
	               Const("iter",dummyT) $ (convExpr rexpr) 
                                            $ (convExpr nexpr)
	  |convBinary(Apply,NameAppl("dom",[]),expr2) = 
	  (* special treatment for inline (= as function) coded relations
	     of the library; such functions are Inr, Inl, most of Seq and Bag*)
	               let val C = Const("Lambda",dummyT) $ 
		                   Const("UNIV",  dummyT)
			   fun Fl[a,b]= [a] ---> mk_sumT(a,b)
			   fun Fr[a,b]= [b] ---> mk_sumT(a,b)
		           fun T F [a,b] = (F(map conv2typ [a,b])
			                    handle Match => error ("Error: \
					    \Can not convert Type Instance: \
					    \Not a ground type !"))
			      |T F [] = dummyT
		           val m = case expr2 of
		               NameAppl("Inr",t) => C $ Const("Inr",T Fr t)
                              |NameAppl("Inl",t) => C $ Const("Inl",T Fl t)
                              |_ => convExpr expr2 
		       in  Const("Domain",dummyT) $ m end
	  |convBinary(Apply,NameAppl("ran",[]),expr2) =
	  (* special treatment for inline (= as function) coded relations
	     of the library; such functions are Inr, Inl, most of Seq and Bag*)
	               let val C = Const("Lambda",dummyT) $ 
		                   Const("UNIV",  dummyT)
			   fun Fl[a,b]= [a] ---> mk_sumT(a,b)
			   fun Fr[a,b]= [b] ---> mk_sumT(a,b)
		           fun T F [a,b] = (F(map conv2typ [a,b])
			                    handle Match => error ("Error: \
					    \Can not convert Type Instance: \
					    \Not a ground type !"))
			      |T F [] = dummyT
		           val m = case expr2 of
		               NameAppl("Inr",t) => C $ Const("Inr",T Fr t)
                              |NameAppl("Inl",t) => C $ Const("Inl",T Fl t)
                              |_ => convExpr expr2 		       
		       in  Const("Range",dummyT) $ m end
	  |convBinary(Apply,NameAppl("_cup_",[]),Tuple([expr1,expr2])) = 
                       Const("op Un",dummyT) 
		       $ (convExpr expr1) $ (convExpr expr2)
	  |convBinary(Apply,NameAppl("_cap_",[]),Tuple([expr1,expr2])) = 
                       Const("op Int",dummyT) 
		       $ (convExpr expr1) $ (convExpr expr2)
	  |convBinary(Apply,NameAppl("bigcup",[]),expr) = 
                       Const("Union",dummyT) $ (convExpr expr)
	  |convBinary(Apply,NameAppl("bigcap",[]),expr) = 
                       Const("Inter",dummyT) $ (convExpr expr)
	  |convBinary(Apply,NameAppl("_mapsto_",[]),Tuple([expr1,expr2])) = 
                       Const("ZMathTool.maplet",dummyT) $ 
		       (convExpr expr1) $ (convExpr expr2)
	  |convBinary(Apply,NameAppl("_dres_",[]),Tuple([expr1,expr2])) = 
                       Const("ZMathTool.dom_restr",dummyT) $ 
		       (convExpr expr1) $ (convExpr expr2)
	  |convBinary(Apply,NameAppl("_rres_",[]),Tuple([expr1,expr2])) = 
                       Const("ZMathTool.ran_restr",dummyT) $ 
		       (convExpr expr1) $ (convExpr expr2)
	  |convBinary(Apply,NameAppl("_ndres_",[]),Tuple([expr1,expr2])) = 
                       Const("ZMathTool.dom_substr",dummyT) $ 
		       (convExpr expr1) $ (convExpr expr2)
	  |convBinary(Apply,NameAppl("_nrres_",[]),Tuple([expr1,expr2])) = 
                       Const("ZMathTool.ran_substr",dummyT) $ 
		       (convExpr expr1) $ (convExpr expr2)
	  |convBinary(Apply,NameAppl("_oplus_",[]),Tuple([expr1,expr2])) = 
                       Const("ZMathTool.override",dummyT) 
                       $ (convExpr expr1)
                       $ (convExpr expr2)
	  |convBinary(Apply,NameAppl("_setminus_",[]),Tuple([expr1,expr2])) = 
                       Const("op -",dummyT) $ 
		       (convExpr expr1) $ (convExpr expr2)
	  |convBinary(Apply,NameAppl("_limg_rimg",[]),Tuple([expr1,expr2])) = 
                       Const("Image",dummyT) $ (convExpr expr1) $ (convExpr expr2)
	  |convBinary(Apply,NameAppl("_upto_",[]),Tuple([expr1,expr2])) = 
                       Const("ZMathTool.numb_range",dummyT) 
		       $ (convExpr expr1) $ (convExpr expr2) 
	  |convBinary(Apply,NameAppl("_circ_",[]),Tuple([expr1,expr2])) = 
                       Const("op O",dummyT) 
		       $ (convExpr expr1) $ (convExpr expr2) 
	  |convBinary(Apply,NameAppl("_comp_",[]),Tuple([expr1,expr2])) = 
                       Const("ZMathTool.forw_comp",dummyT) 
		       $ (convExpr expr1) $ (convExpr expr2) 
          | convBinary(Apply,NameAppl("_inv",[]),expr) = 
                       Const("converse",dummyT) $ (convExpr expr)
	  |convBinary(Apply,NameAppl("#",[]),expr) = 
                       Const("ZMathTool.zsize",dummyT) $ (convExpr expr)
	  |convBinary(Apply,NameAppl("_star",[]),expr) = 
                       Const("ZMathTool.ref_trans_clos",dummyT) 
                       $ (convExpr expr)
	  |convBinary(Apply,NameAppl("_plus",[]),expr) = 
                       Const("ZMathTool.trans_clos",dummyT) $ (convExpr expr)
          |convBinary(Apply,NameAppl("_+_",[]),Tuple([expr1,expr2])) = 
                      Const("op +",dummyT) 
                       $ (convExpr expr1) 
                       $ (convExpr expr2)
          |convBinary(Apply,NameAppl("_-_",[]),Tuple([expr1,expr2])) = 
                      Const("op -",dummyT) 
                       $ (convExpr expr1) $ (convExpr expr2)
          |convBinary(Apply,NameAppl("_*_",[]),Tuple([expr1,expr2])) = 
                      Const("op *",dummyT) 
                       $ (convExpr expr1) 
                       $ (convExpr expr2)
	  |convBinary(Apply,NameAppl("langle,,rangle",[]),Display([])) = 
		       Const("emptyseq",dummyT)
	  |convBinary(Apply,NameAppl("langle,,rangle",[]),Display(pairs)) = 
		       let fun cv (Tuple([x,y]),s) = Const("insertseq",dummyT)$
							(convExpr y) $ s
		       in
			   List.foldr cv (Const("emptyseq",dummyT)) pairs
		       end
          |convBinary(Apply,NameAppl("_cat_",[]),Tuple([expr1,expr2])) = 
            Const("ZMathTool.rel_appl",dummyT) $ 
		 Const("ZSeqtoList.concatseq",dummyT) 
                 $ (Const("Pair",dummyT) 
                 $ (convExpr expr1) 
                 $ (convExpr expr2))
          | convBinary(Apply,NameAppl("rev",[]),expr) = 
            Const("ZMathTool.rel_appl",dummyT) $ 
		 Const("ZSeqtoList.revseqseq",dummyT) $ (convExpr expr)
          | convBinary(Apply,NameAppl("head",[]),expr) = 
            Const("ZMathTool.rel_appl",dummyT) $ 
		 Const("ZSeqtoList.headseq",dummyT) $ (convExpr expr)
          | convBinary(Apply,NameAppl("last",[]),expr) = 
            Const("ZMathTool.rel_appl",dummyT) $ 
		 Const("ZSeqtoList.lastseq",dummyT) $ (convExpr expr)
          | convBinary(Apply,NameAppl("tail",[]),expr) = 
            Const("ZMathTool.rel_appl",dummyT) $ 
		 Const("ZSeqtoList.tailseq",dummyT) $ (convExpr expr)
          | convBinary(Apply,NameAppl("front",[]),expr) = 
            Const("ZMathTool.rel_appl",dummyT) $ 
		 Const("ZSeqtoList.frontseq",dummyT) $ (convExpr expr)
          | convBinary(Apply,NameAppl("_extract_",[]),Tuple([expr1,expr2])) = 
            Const("ZMathTool.rel_appl",dummyT) $ 
		 Const("ZSeqtoList.extraction",dummyT) 
                 $ (Const("Pair",dummyT) 
                 $ (convExpr expr1) 
                 $ (convExpr expr2))
          | convBinary(Apply,NameAppl("_filter_",[]),Tuple([expr1,expr2])) = 
            Const("ZMathTool.rel_appl",dummyT) $ 
		 Const("ZSeqtoList.filtering",dummyT) 
                 $ (Const("Pair",dummyT) 
                 $ (convExpr expr1) 
                 $ (convExpr expr2))
          | convBinary(Apply,NameAppl("_pplus_",[]),Tuple([expr1,expr2])) = 
	    Const("Plus",dummyT) 
                 $ (convExpr expr1) 
                 $ (convExpr expr2)
	  |convBinary(Apply,NameAppl("Inr",_),expr) = 
	    Const("Inr",dummyT) $ (convExpr expr)
	  |convBinary(Apply,NameAppl("Inl",_),expr) = 
                       Const("Inl",dummyT) $ (convExpr expr)
	  |convBinary(Apply,NameAppl("first",[]),expr) = 
                       Const("fst",dummyT) $ (convExpr expr)
	  |convBinary(Apply,NameAppl("second",[]),expr) = 
                       Const("snd",dummyT) $ (convExpr expr)
	  |convBinary(Apply,expr1,expr2) = 
                       Const("ZMathTool.rel_appl",dummyT) 
		       $ (convExpr expr1) $ (convExpr expr2) 
	  |convBinary(Compose,expr1,expr2) = 
		       error "Compose (semi): Pipe NOT YET IMPLEMENTED !"
	  |convBinary(Pipe,expr1,expr2) =
		       error "Binary: Pipe NOT YET IMPLEMENTED !"
	  |convBinary(Project,expr1,expr2) =
		       error "Binary: Project NOT YET IMPLEMENTED !"
	
	(* val Test : Expr * Expr -> Expr *)
        and convTest(Tuple args,NameAppl("_notin_",[])) =
            Const("Not",dummyT) $
            (list_comb(Const("op :",dummyT), map convExpr args))
          | convTest(Tuple([expr1,expr2]), NameAppl("_neq_",[])) =
	    Const("Not",dummyT) $ 
		 (Const("op =",dummyT) $ (convExpr expr1)
		       $ (convExpr expr2))
          | convTest(Tuple([expr1,expr2]), NameAppl("_=_",[])) =
	    Const("op =",dummyT) $ (convExpr expr1) $ (convExpr expr2)
          | convTest(Tuple([expr1,expr2]), NameAppl("_in_",[])) =
	    Const("op :",dummyT) $ (convExpr expr1) $ (convExpr expr2)
          | convTest(Tuple([expr1,expr2]), NameAppl("_subset_",[])) =
	    Const("op <",dummyT) $ (convExpr expr1) $ (convExpr expr2)
          | convTest(Tuple([expr1,expr2]), NameAppl("_subseteq_",[])) =
	    Const("op <=",dummyT) $ (convExpr expr1) $ (convExpr expr2)
          | convTest(Tuple([expr1,expr2]), NameAppl("_<_",[])) =
	    Const("op <",dummyT) $ (convExpr expr1) $ (convExpr expr2)
          | convTest(Tuple([expr1,expr2]), NameAppl("_leq_",[])) =
	    Const("op <=",dummyT) $ (convExpr expr1) $ (convExpr expr2)
          | convTest(Tuple([expr1,expr2]), NameAppl("_geq_",[])) =
	    Const("op <=",dummyT) $ (convExpr expr2) $ (convExpr expr1)
          | convTest(Tuple([expr1,expr2]), NameAppl("_>_",[])) =
	    Const("op <",dummyT) $ (convExpr expr2) $ (convExpr expr1)
          | convTest(Tuple([expr1,expr2]), NameAppl("_suffix_",[])) =
	    Const("op :",dummyT) $ 
		 (Const("Pair",dummyT) $ (convExpr expr1) $ (convExpr expr2))
		 $ Const("ZSeqtoList.suffixseq",dummyT)
          | convTest(Tuple([expr1,expr2]), NameAppl("_prefix_",[])) =
	    Const("op :",dummyT) $ 
		 (Const("Pair",dummyT) $ (convExpr expr1) $ (convExpr expr2))
		 $ Const("ZSeqtoList.prefixseq",dummyT)
          | convTest(Tuple([expr1,expr2]), NameAppl("_inseq_",[])) =
	    Const("op :",dummyT) $ 
		 (Const("Pair",dummyT) $ (convExpr expr1) $ (convExpr expr2))
		 $ Const("ZSeqtoList.inseq",dummyT)
          | convTest(Tuple([expr1,expr2]), pred) =
	    Const("op :", dummyT) $ (Const("Pair",dummyT) $ (convExpr expr1) $
					  (convExpr expr2)) $ (convExpr pred)
          | convTest(Tuple args,pred) = 
	    Const("op :", dummyT) 
                 $ ZPrelude.mk_tuple(map convExpr args) 
                 $ (convExpr pred)
	  | convTest(expr1,expr2) = 
	    Const("op :", dummyT) $ (convExpr expr1) $ (convExpr expr2)
(*           | convTest(Tuple args,pred) = 
            list_comb(convExpr pred, map convExpr args) *)

	(* val Fact : FactKind -> Expr *)
        and convFact(True) = Const("True",dummyT)
	  | convFact(False) = Const("False",dummyT)
	
	and convSchemaType (Type(Unary(Power, Signature(vars)))) = 
	    let fun mk_pairs(E::b::R) = Const("Pair",dummyT) $ Free(E,dummyT) $
					     (mk_pairs (b::R))
		  | mk_pairs (E::[]) = Free(E,dummyT)
	    in
		mk_pairs (map fst vars)
	    end

	(* val Type : Expr -> Expr *)
        and convType(expr) = 
            error "Type: NOT YET IMPLEMENTED !"

	and convRenaming (expr, rns) = gen_rename expr rns

        and convExpr (Number     str) = convNumber str
           |convExpr (Denotation str) = convDenotation str
	   |convExpr (NameAppl   H)   = convNameAppl H
	   |convExpr (Tuple      H)   = convTuple H
	   |convExpr (Product    H)   = convProduct H
	   |convExpr (Binding    H)   = convBinding H
	   |convExpr (Signature  H)   = convSignature H
	   |convExpr (Display    H)   = convDisplay H
	   |convExpr (Cond       H)   = convCond H
	   |convExpr (Quantor    H)   = convQuantor H
	   |convExpr (SchemaText H)   = convSchemaText H
	   |convExpr (Select     H)   = convSelect H
	   |convExpr (Unary      H)   = convUnary H
	   |convExpr (Binary     H)   = convBinary H
	   |convExpr (GivenType  str) = 
                     error "convExpr: GivenType not allowed inside expression!"
	   |convExpr (FreeType   H)   = 
                     error "convExpr: FreeType not allowed inside expression!"
	   |convExpr (Test       H)   = convTest H
	   |convExpr (Fact       H)   = convFact H
	   |convExpr (Eqn        H)   = 
                     error "convExpr: Eqn not allowed inside expression!"
	   |convExpr (Direct     H)   = 
                     error "convExpr: Direct not allowed inside expression!"
	   |convExpr (Gen        H)   = 
                     error "convExpr: Gen not allowed inside expression!"
	   |convExpr (Type       H)   = convType H
	   |convExpr (Renaming   H)   = convRenaming H  


(* Unfortunately, Zeta uses ' to denote strokes on the lexical level, 
   HOL-Z uses ´. The following code performs the translation. *)
fun trans_stroke str = 
    let val stroke = hd(String.explode ZPrelude.stroke_sym)
        fun H [] = []
           |H (a::R) = if a= #"'" then stroke::H(R) else a::R;
    in   String.implode(rev(H(rev(String.explode str))))
    end

fun trans_stroke_term (Free(s,t)) = Free(trans_stroke s,t)
   |trans_stroke_term (Abs(s,t,e)) = Abs(trans_stroke s,t,trans_stroke_term e)
   |trans_stroke_term (e$e') = (trans_stroke_term e)$(trans_stroke_term e')
   |trans_stroke_term e = e

val convExpr = trans_stroke_term o convExpr 
val convTjdmt=(fn x => case convTjdmt x of
                         SOME y => SOME(map (fn(s,t)=>(trans_stroke s,t)) y)
                       | NONE   => NONE)

(* ******************************************************************* *)
(*                                                                     *)
(* Items . . .                                                         *)
(*                                                                     *)
(* ******************************************************************* *)
	
	(* val FreeType : string * Branch list -> Expr *)
        fun convFreeType(name,brS) =
            let fun cv(Constant str) = ((stripName str),[],NoSyn)
	          | cv(Function (str,expr)) = 
                    error "FreeType with non-constant: NOT YET IMPLEMENTED !"
            in  ([],(stripName name), map cv brS) end;
 


        fun convItem tn ((Eqn(name,e1,t)),thy) =
                     (* constdefs, schemadefs *)
                     (* (writeln ("Loading definition " ^ name ^" ..."); *)
                      ZEncoder.add_schemes_i tn 
                        [([Const  ("==", dummyT) 
                           $ Free ((stripName name),dummyT) 
                           $ (convExpr e1)],
			   convTjdmt t)] thy
          | convItem tn ((GivenType(name)),thy) =
                     (* abstract type definitions *)
                     (writeln ("Loading abstract type " ^ name ^" ...");
                      ZEncoder.add_abs_type (stripName name) thy)
          | convItem tn ((FreeType(name,varS)),thy) =
                     (* free data types *)
                     (writeln ("Loading free type " ^ name ^" ...");
                     ZEncoder.add_free_type (convFreeType(name,varS)) thy)
          | convItem tn ((e1 as SchemaText([],[pred])),thy) =
                     (* conjectures *)
                     (writeln ("Loading concjecture ...");
                     ZEncoder.add_conjecture_i tn (convExpr pred) thy)
          | convItem tn ((e1 as SchemaText(name,Vars)),thy) =
                     (* axiomatic definitions *)
                     (* (writeln ("Loading axiomatic definition ..."); *)
                     ZEncoder.add_schemes_i tn
                        [([Const ("Trueprop",dummyT)$(convExpr e1)],NONE)]thy
          | convItem tn ((Gen(parmS,SchemaText(name,Vars))),thy) =
                     (* generic axiomatic definitions *)
                     error "convItem: GAD : NOT YET IMPLEMENTED !"
          | convItem tn ((Gen(parmS,Eqn(name,e1,t))),thy) =
                     (* generic schema definitions *)
                     error "convItem: GD : NOT YET IMPLEMENTED !"
          | convItem tn ((EmbeddedText(str)),thy) = thy
		     (* (writeln "EmbeddedText is ignored.";thy) *)
	  | convItem tn ((ZedFixity(str)),thy) = thy
		     (* (writeln "ZedFixity is ignored.";thy) *)
          | convItem tn ((_),thy) =
                     (* generic schema definitions *)
                     error "convItem: Unknown Z-construction !"

 
(* ******************************************************************* *)
(*                                                                     *)
(* Top Structures . . .                                                *)
(*                                                                     *)
(* ******************************************************************* *)

	fun unitName s = 
            let val ComSep = #":"
                val OrigSeq = #"#"
                fun t x = (x = ComSep) orelse (x = OrigSeq)
                val [a,b,c] = String.tokens t s
            in  {adaptorName=a,Name=b,adaptorData=c} end;

        (* val ZSection : string * string list * Item list -> Section *)

	fun printSec (ZSection(aName,aImportS,_)) = 
		writeln ("*** Loading Z section: " ^ aName);

end
