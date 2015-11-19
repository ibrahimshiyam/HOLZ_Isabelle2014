(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ZEncoder.sml --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 2000-2003, University Freiburg, Germany
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
(* $Id: ZEncoder.sml 6729 2007-08-03 05:25:17Z brucker $ *)

signature ZENCODER =
  sig

    type bindings      = (string*typ) list 

    val init           : unit -> unit
    (*  internal debugging states *)
    val init_axprep    : (string * thm -> bool) -> unit
    (*  set post-processor for axiomatic definitions *)


    val schema_read    : ZTheory.ztheory -> string -> term


    val string_of_zthm : ZTheory.ztheory -> thm -> string


    val add_abs_type   : string -> ZTheory.ztheory -> ZTheory.ztheory 
    (* NOT YET PORTED *)
    val add_free_type  : (* dt_type *) string list * string * 
                         (string * (* dt_type *) string list * mixfix) list
                                 -> ZTheory.ztheory 
                                 -> ZTheory.ztheory
    (* will become: (string list * bstring * mixfix
           * (bstring * string list * mixfix) list) list ... *)

    val TYPE_INFERS    : thm list ref

    val add_schemes    : string  -> string list -> 
                                    ZTheory.ztheory -> 
                                    ZTheory.ztheory
    val add_schemes_i  : string  -> (term list * bindings option) list -> 
                                    ZTheory.ztheory -> 
                                    ZTheory.ztheory

    val add_conjecture : string  -> string ->
                                    ZTheory.ztheory -> 
                                    ZTheory.ztheory
 
    val add_conjecture_i:string  -> term  -> 
                                    ZTheory.ztheory -> 
                                    ZTheory.ztheory
 
    val get_schemes    : ZTheory.ztheory -> (string * thm) list
    val get_axdefs     : ZTheory.ztheory -> (string * thm) list
    val get_conjectures: ZTheory.ztheory -> (string * thm) list

  end;





structure ZEncoder (* : ZENCODER *) = (* for debugging *)
struct
 
type bindings      = (string*typ) list 

open ZPrelude ZEnv ZTheory Sign Term HOLogic;
(*drop the first n elements from a list*)
fun drop (n, []) = []
  | drop (n, x :: xs) =
      if n > 0 then drop (n - 1, xs) else x :: xs;


(* parametric case ?! *)
(*
-- rough approximation of the type of a term;
   uses the fact that HOL-Z operators are constants
   and hence have known types, and schema names are variables
   and have hence known types. Sufficient to recognize correct
   schema expressions without schema variables.
*)

(* *********************************************************************** *)
(*									   *)
(* type handling                                                           *)
(*									   *)
(* *********************************************************************** *)
(* constructs type approximations for constant-head lifter, i.e
   expressions of the form %x1 ... xn. C E1 ... Em. The underlying
   assumption of the encoder is that this is sufficient for
   deciding whether schemas (must have been defined in the
   Z-section before, are thus constants) are imported 
   "asSet", "asPredicate" or "asBool". *)

val ZschemaT = boolT

fun type_of_appl l ty = if ty = dummyT then ty
                        else let val (argty,rty)= strip_type ty
                             in if l < length(argty)
                                then drop(l, argty) ---> rty
                                else rty
                             end

fun type_of_doms tS ty = if ty = dummyT then (map (K dummyT) tS,tS)
                         else let val (argty,rty)= strip_type ty
                                  fun fill([],[]) = ([],[])
                                     |fill([],a::R) = let val (c,t)=fill([],R)
                                                      in  (dummyT::c,a::t)end
                                     |fill(a::R,[]) = ([],[]) 
                                     |fill(b::S,a::R) = let val (c,t)=fill(S,R)
                                                        in  (b::c, a::t)end
                              in fill(argty,tS) end;


(* a raw type approximation taking Z constructs into account *)
fun type_of sg (Free (n,ty))  = if n="pre" then ZschemaT --> ZschemaT else
                                if not(ty = dummyT) then ty
                                else (case const_type sg 
                                        (intern_const sg 
                                           (destroke n)) of 
                                        SOME t => t
                                      | NONE   => dummyT)
   |type_of sg (Const("DELTA",_))   = ZschemaT --> ZschemaT
   |type_of sg (Const("XI",_))      = ZschemaT --> ZschemaT 
   |type_of sg (Const("PRE",_))     = ZschemaT --> ZschemaT
   |type_of sg (Const("%E",_))      = [ZschemaT,ZschemaT] ---> ZschemaT
   |type_of sg (Const("%E1",_))     = [ZschemaT,ZschemaT] ---> ZschemaT
   |type_of sg (Const("%A",_))      = [ZschemaT,ZschemaT] ---> ZschemaT
   |type_of sg (Const("_schset",_)) = [dummyT,dummyT] ---> (HOLogic.mk_setT dummyT)
   |type_of sg (Const("_hiding",_)) = error "no hiding yet"
   |type_of sg (Const("_rename",_)) = error "no renaming yet"
   |type_of sg (Const("op |\\",_))  = error "no projection yet"
   |type_of sg (Const("op %%;",_))  = error "no composition yet"
   |type_of sg (Const("op >>",_))   = error "no piping yet"

   |type_of sg (Const(n,ty))  = if not(ty = dummyT) then ty
                                else (case const_type sg 
                                        (intern_const sg 
                                           (destroke n)) of 
                                        SOME t => t
                                      | NONE   => dummyT)
   |type_of sg (t as _ $ _)   = let val (hd,args) = strip_comb t
                                    val l = length args
                                    val ty = type_of sg hd
                                in  type_of_appl l ty end
   |type_of sg (Bound _)      = dummyT
   |type_of sg (Var(_,t))     = t
   |type_of sg (Abs(_,T,body))= T --> (type_of sg body);




fun type_of_appl l ty = if ty = dummyT then ty
                        else let val (argty,rty)= strip_type ty
                             in if l < length(argty)
                                then drop(l, argty) ---> rty
                                else rty
                             end

fun type_of_doms tS ty = if ty = dummyT then (map (K dummyT) tS,tS)
                         else let val (argty,rty)= strip_type ty
                                  fun fill([],[])    = ([],[])
                                     |fill([],a::R)  = let val (c,t)=fill([],R)
                                                       in  (dummyT::c,a::t)end
                                     |fill(a::R,[])  = ([],[]) 
                                     |fill(b::S,a::R)= let val (c,t)=fill(S,R)
                                                       in  (b::c, a::t) end
                              in fill(argty,tS) end;

(* alias "boolfun" *)
fun is_pred (ty as Type("fun", _)) = (snd(strip_type ty) = boolT)   
   |is_pred _ = false;

fun is_set (Type ("set", [T])) = true
   |is_set _ = false;

fun is_setfun (ty as Type("fun", _)) = (is_set (snd(strip_type ty)))
   |is_setfun _ = false;

datatype tyclass = Bool | Other | Pred | Prop | Set | Setfun

fun tycl ty = if      ty = boolT   then Bool
              else if ty = propT   then Prop
              else if is_pred ty   then Pred 
              else if is_set ty    then Set
              else if is_setfun ty then Setfun
              else Other 

fun tycl2string Bool  = "Bool"
   |tycl2string Other = "Other"
   |tycl2string Pred  = "Pred"
   |tycl2string Prop  = "Prop"
   |tycl2string Set   = "Set"
   |tycl2string Setfun= "Setfun"


fun zSchemaSign e (Const ("DECL",_) $ decl $ pred) = 
	            zSchemaSign e decl (* append_zsig zSchemaSign e pred *)
   |zSchemaSign e (Const ("ZPure.DECL",_) $ decl $ pred) = 
	            zSchemaSign e decl (* append_zsig zSchemaSign e pred *)
   |zSchemaSign e (Const("True",_)) = mt_zsig
   |zSchemaSign e (Const("False",_)) = mt_zsig
   |zSchemaSign e (Const("op :",_)$Free(s,t)$e2) = insert_zsig (s,t) mt_zsig
   |zSchemaSign e (Const ("op &",T2) $ S $ T)    = (zSchemaSign e S) union_zsig 
   						     (zSchemaSign e T)
   |zSchemaSign e (Const ("op |",T2) $ S $ T)    = (zSchemaSign e S) union_zsig 
   						     (zSchemaSign e T)
   |zSchemaSign e (Const ("op -->",T2) $ S $ T)  = (zSchemaSign e S) union_zsig 
   						     (zSchemaSign e T)
   |zSchemaSign e (Const ("op =",_) $
                   (Const ("theta",_) $ _ $ S) $
                   (Const ("theta",_) $ _ $ T)) = 
                    let fun H (Free s,e) = insert_zsig s e
                        val S' = foldl H mt_zsig (strip_tuple S)
                        val T' = foldl H mt_zsig (strip_tuple T) 
                    in  S' union_zsig T' end
   |zSchemaSign e (Const("SNAME",_) $ _ $ T) =
                    let fun H (Free s,e) = insert_zsig s e
                    in  foldl H (mt_zsig) (strip_tuple T) end
   |zSchemaSign e (Const("DELTA",_) $ S $ T) = (zSchemaSign e S) union_zsig 
   						     (zSchemaSign e T)
   |zSchemaSign e (Const("XI",_) $ S $ T $ U) = (zSchemaSign e S)
   |zSchemaSign e (Const("PRE",_) $ T)     = 
       filter_zsig (fn (x,_) => not(is_stroke_name x orelse is_out_name x))
                   (zSchemaSign e T)
   |zSchemaSign e (Free("pre",_) $ T)     = 
       filter_zsig (fn (x,_) => not(is_stroke_name x orelse is_out_name x))
                   (zSchemaSign e T)
   |zSchemaSign e (Const("Bex",_)$ S $ (Abs(s,ty,T))) =
       (zSchemaSign e S) union_zsig  (delete_zsig (s,ty) (zSchemaSign e T))
   |zSchemaSign e (Const("Ball",_)$ S $ (Abs(s,ty,T))) =
       (zSchemaSign e S) union_zsig  (delete_zsig (s,ty) (zSchemaSign e T))
   |zSchemaSign e (Const("All",_)$ (Abs(s,ty,T))) =
       (delete_zsig (s,ty) (zSchemaSign e T))
   |zSchemaSign e (Const("Ex",_)$ (Abs(s,ty,T))) =
       (delete_zsig (s,ty) (zSchemaSign e T))
   |zSchemaSign e (Const("%E",_) $ S $ T)  =
       (zSchemaSign e T) diff_zsig  (zSchemaSign e S)
   |zSchemaSign e (Const("%E1",_) $ S $ T) =
       (zSchemaSign e T) diff_zsig  (zSchemaSign e S)
   |zSchemaSign e (Const("%A",_) $ S $ T)  =
       (zSchemaSign e T) diff_zsig  (zSchemaSign e S)
   |zSchemaSign e (Const("_schset",_) $ S $ T)  =
       (zSchemaSign e T) diff_zsig  (zSchemaSign e S)
   |zSchemaSign e (Const("_hiding",_) $ S $ T) = error "no hiding yet"
   |zSchemaSign e (Const("_rename",_) $ S $ T) = error "no renaming yet"
   |zSchemaSign e (Const("op |\\",_)  $ S $ T) = error "no projection yet"
   |zSchemaSign e (Const("op %%;",_)  $ S $ T) = error "no composition yet"
   |zSchemaSign e (Const("op >>",_)   $ S $ T) = error "no piping yet"
   |zSchemaSign e (t as _ $ _)   = 
                    let val (hd,args) = strip_comb t
                        fun H(ty,t) = if ty = boolT 
                                      then zSchemaSign e t 
                                      else mt_zsig 
                        val ty = type_of e t
                    in  if type_of_appl (length args) ty = boolT 
                        then foldl (fn (s1,s2) => s2 union_zsig s1) 
                                mt_zsig (map2 H (type_of_doms args ty))
                        else mt_zsig
                    end
   |zSchemaSign e _   =  mt_zsig (* veeery liberal, but we admit e.g.
                                    meta-variables, what makes the machinery
                                    quite heuristic. But this is handy
                                    in most cases like "schema = ?X" *)
   
             



(* *********************************************************************** *)
(*									   *)
(* lifting: marking schema names, converting theta                         *)
(*									   *)
(* *********************************************************************** *)

fun mk_tuple tS = let val a::R = rev tS 
                  in  foldl mk_prod a R end

(* lifting expands elementary schema references and handles 
   theta-expressions over (expanded) schema references *)

(* Riddle: where the heck were the free's stroked?
   Well, in the lookup. bu *)
fun lift zsig (Free (s,t)) = 
         (case lookup (zsig,s) of
   	     NONE   => Free(s,t)
     	   | SOME n => if null(schemasig_of n) 
  	   	       then (Const("SNAME0",dummyT)$ Const(destroke s,t))
	               else  Const("SNAME",dummyT) $ Const(destroke s,t) $  
			          (mk_tuple(map Free (schemasig_of n))))
   |lift zsig (Const("%theta",_) $ (Free(s,t))) =
         (case lookup (zsig,s) of
             NONE   => error ("illegal schema reference: %theta "^s)
            |SOME n => Const ("theta",dummyT) $(mk_string s) $ 
                             (mk_tuple (map Free (schemasig_of n)))) 
   |lift zsig (Abs(s,ty,t)) = Abs(s,ty, lift zsig t)
   |lift zsig (s $ t)       = (lift zsig s) $ (lift zsig t)
   |lift zsig s = s


(* *********************************************************************** *)
(*									   *)
(* making Z-Binding Structure explicit                                     *)
(*									   *)
(* *********************************************************************** *)

(* Schemas can be used "asBoolean" (which is the default in our encoding),
   "asSet" or "asPredicate". The function mk_context_adaptor generates 
   conversions between these three, according to their need in the context
   of a term t. This need is expressed by the "expected type" of a term
   which is compared to its "result type". The types were represented by
   type classes as defined above.
 *)


fun add_store_defs S thy =
    let val (thy',thms) = PureThy.add_defs true S thy
        val H = map (fn((s,_),_) => s) S
        val _ = map2 bind_thm (H,thms)
    in  thy' end;

fun add_store_defs_i S thy =
    let val (thy',thms) = PureThy.add_defs_i true S thy
        val H = map (fn((s,_),_) => s) S
        val _ = map2 bind_thm (H,thms)
    in  thy' end;

fun add_store_axioms_i S thy =
    let val (thy',thms) = PureThy.add_axioms_i S thy
        val H = map (fn((s,_),_) => s) S
        val _ = map2 bind_thm (H,thms)
    in  thy' end;


fun top_sg() = #sign(rep_thm(topthm()));

fun pp t = Sign.string_of_term (top_sg()) t;

fun mk_context_adapter sg t0 (expected_type,result_type) t = 
   let fun sgn t0 = schemasig_of(zSchemaSign sg t0) in
       (* delayed for efficency reasons *)
   (case (expected_type, result_type) of
         (* |- A  with A a schema name *)
         (Prop,Pred) => Const("ZPure.turnstyle",dummyT)$t
        |(Prop,Bool) =>(let val bds = sgn t0
                        in  case bds of
                             [] => t
                            | _ => Const("ZPure.turnstyle",dummyT) $ 
                                   (gen_binder bds t)
                        end)
        |(Prop,x)    => error ("internal error: context_adapter 1 "^
                               (tycl2string x)^" "^(pp t))

         (* standard case: convert a rhs to a predicate over signature *)
        |(Pred,Bool) => (gen_binder (sgn t0) t)
        |(Pred,Other)=> (gen_binder (sgn t0) t)
        |(Pred,_)    => t
(*      |(Pred,x)    => error ("internal error: context_adapter 2"^
                               (tycl2string x)^(pp t)) 
        adapter generator must be admissive - whenever you detect 
        a context gap, generate a bridge; but since you do not know
        the types exactly, do nothing whenever something weird occurs ... *)

         (* predicate application: P(x1,...,xn)  |-> (x1,...,xn) : P *)
        |(Bool,Bool) =>  t
        |(Bool,_)    =>  (case t of 
                             e1 $ e2 => if is_setfun(type_of sg e1) 
                                        then Const("asPred",dummyT) $ e1 $ e2
                                        else t
                           | _ => t)
                         (* HO predicate applications not supported*)
         (* seq (A /\ B) etc. *)
        |(Set,Bool)  =>  Const("asSet",dummyT) $ 
                            (gen_binder (sgn t0) t )
         (* seq A *)
        |(Set,Pred)  =>  Const("asSet",dummyT) $ t
        |(Set,Set)   =>  t
        |(Set,_)     => (case t of 
                           Const("SNAME",_)$f$args => Const("asSet",dummyT)$f
                         | Const("SNAME0",_)$f     => Const("asSet",dummyT)$f
                           (* produces rubbish, but is rubbish anyway *)
                         | _                       => t)
        |(Setfun,x)  => let fun skip_abs f (Abs(a,ty,t)) = Abs(a,ty, skip_abs f t)
                               |skip_abs f x = f x
                        in  skip_abs (mk_context_adapter sg t0 (Set,x)) t end
(*      |(Set,x)     =>  error ("internal error: context_adapter 3"^
                                (tycl2string x)^(pp t)) *)
        | _ => t)

    end



fun exp_binding sg zenv (exp_ty,t) =
       let val rty = type_of sg t
       in  mk_context_adapter sg t (exp_ty,tycl rty)
           (case t of 
             Free("pre",_) $ S =>
                           let val sgm = filter_zsig (fn (x,_)=> is_stroke_name x 
                                                                 orelse 
                                                                 is_out_name x) 
                                         (zSchemaSign sg S)
                           in  Const("PRE",dummyT) $ 
                                  (gen_binder (schemasig_of sgm) 
                                      (exp_binding sg zenv (Bool,S)))
                           end 
            |Const("Ball",_)$S$(Abs(s,ty,T)) =>
                           Const("Ball",dummyT)$
                           (exp_binding sg zenv (Set, S))$
                           (Abs(s,ty,abstract_over1(Free(s,ty),
                                      exp_binding sg zenv (Bool,(T)))))
            |Const("Bex",_)$S$(Abs(s,ty,T)) =>
                           Const("Bex",dummyT)$
                           (exp_binding sg zenv (Set, S))$
                           (Abs(s,ty,abstract_over1(Free(s,ty),
                                      exp_binding sg zenv (Bool,(T)))))
            |Const("All",_)$(Abs(s,ty,T)) =>
                           Const("All",dummyT)$
                           (Abs(s,ty,abstract_over1(Free(s,ty),
                                      exp_binding sg zenv (Bool,(T)))))
            |Const("Ex",_)$(Abs(s,ty,T)) =>
                           Const("Ex",dummyT)$
                           (Abs(s,ty,abstract_over1(Free(s,ty),
                                      exp_binding sg zenv (Bool,(T)))))
            |Const("%A",_)$S$T =>
                           let val sgm = (zSchemaSign sg S)
                               val S'  = exp_binding sg zenv (Set, S)
                               val T'  = exp_binding sg zenv (Bool, T)
                                         (* should be Pred since type signature
                                            of SBall requires `a => bool for this 
                                            argument.  However, since the context
                                            adaption is done here and not outermost
                                            as in the default, the expected type is set 
                                            to bool in order to avoid an own adaption ...*)
                           in  Const("SBall",dummyT) $ S' $ 
                               (gen_binder (schemasig_of sgm) T') 
                           end
            |Const("%E",_)$S$T =>
                           let val sgm = (zSchemaSign sg S)
                               val S'  = exp_binding sg zenv (Set, S)
                               val T'  = exp_binding sg zenv (Bool, T)
                               (* see %A above ... *)
                           in  Const("SBex",dummyT) $ S' $ 
                               (gen_binder (schemasig_of sgm) T') 
                           end
            |Const("%E1",_)$S$T =>
                           let val sgm = (zSchemaSign sg S)
                               val S'  = exp_binding sg zenv (Set, S)
                               val T'  = exp_binding sg zenv (Bool, T)
                               (* see %A above ... *)
                           in  Const("SBex1",dummyT) $ S' $ 
                               (gen_binder (schemasig_of sgm) T') 
                           end
            |Const("_schset",_) $ S $ T =>
                           let val sgm = (zSchemaSign sg S)
                               val S'  = exp_binding sg zenv (Set, S)
                               val T'  = exp_binding sg zenv (Bool, T)
                           in  Const("SSet",dummyT) $ S' $ 
                               (gen_binder (schemasig_of sgm) T') 
                           end
            |e $ e' => let val (hd,args) = strip_comb t
                           val ty        = type_of sg hd
                           val hd'       = exp_binding sg zenv (tycl ty,hd)
                           val (A,B)     = (type_of_doms args ty)
                           val args'     = map2 (exp_binding sg zenv)
                                                (map tycl A,B)
                       in  list_comb(hd',args') end 
            |Abs(x,t,e) => 
                       let val ty = if t = dummyT then type_of_appl 1 rty
                                    else type_of_appl 1 t  
                       in  Abs(x,t, exp_binding sg zenv (tycl ty,e)) end
            |t      => t)
    end;




fun exp_binding_in_item sg zenv (t as (Const("==",_) $ lhs $ rhs)) =
                        (* == generated by translations _SCHEME *)
                        Const("==",dummyT) 
			$ lhs 
			$ (exp_binding sg zenv (Pred,rhs))
  | exp_binding_in_item sg zenv (Const("op =",_) $ lhs $ rhs) =
                        (* A <=> B *)
                        Const("op =",dummyT) $ 
			 (exp_binding sg zenv (Pred,lhs)) $ 
			 (exp_binding sg zenv (Pred,rhs))
  | exp_binding_in_item sg zenv tt =   
                        (* case in goals *)
		        exp_binding sg zenv (Prop, tt)


(* *********************************************************************** *)
(*									   *)
(* projection expansion ...                                                *)
(*									   *)
(* *********************************************************************** *)

fun flat (ls: 'c list list) : 'c list = foldr (op @) [] ls;


fun expand_select zenv ns (Const("_select",_) $ e1 $ (Const(x,_))) =
           let val selS = lookup_selectors zenv x  
           in  map (gen_proj x e1)(selS) end
  | expand_select zenv ns (Const("_select",_) $ e1 $ (Free(x,_))) = 
           let val selS = lookup_selectors zenv x  
           in  map (gen_proj x e1)(selS) end
  | expand_select zenv ns (Const("_select",_) $ e1 $ (Bound x)) = 
           let val x = List.nth(ns,x)
               val selS = lookup_selectors zenv x  
           in  map (gen_proj x e1)(selS) end
  | expand_select zenv ns (A $ B) =
           let val A' = expand_select zenv ns A
               val B' = expand_select zenv ns B
           in  flat(map (fn a => map (fn b => a $ b) B') A') end
  | expand_select zenv ns (Abs(x,t,e)) = map (fn y => Abs(x,t,y))
                                          (expand_select zenv (x::ns) e)
  | expand_select zenv ns X = [X];
                          

(* the overall structure of the conversion:
   - translate ' notation into `
     (the former appears in ZETA, the latter is 
      required for HOL-Z)
   - lifting
   - binding expansion
   - selection expansion *)
fun schema_conv sg zenv t =
    let fun dest_Trueprop' (Const ("Trueprop", _) $ P) = P
          | dest_Trueprop' t = t;
        val t = dest_Trueprop' t
        fun mk_Trueprop'(P as (Const ("==", _) $ _ $ _)) = P
          | mk_Trueprop' P = mk_Trueprop P
    in  expand_select zenv []
           (mk_Trueprop'
                (exp_binding_in_item sg zenv 
                     (lift (schemas_of zenv) 
                           (dest_Trueprop' t))))
    end






(* *********************************************************************** *)
(*									   *)
(* parsing ...                                                             *)
(*									   *)
(* *********************************************************************** *)   


(* parsing and printing of schemes depends on the internal variable 
   ZENV. Since this is necessarily updated during interactive 
   proving, both routines protect the content of this global variable *)
fun schema_parser thy zenv scheme = 
    let val h = !ZENV;
        val t = (ZENV:=zenv;
                 Syntax.read thy (Sign.is_logtype thy) (syn_of thy) propT (scheme)
                 (* generates list of raw-term-parses. *)
                );
    in (ZENV:=h; t) end;
    
fun string_of_zthm thy zenv thm = 
    let val h = !ZENV;
        val t = (ZENV:=zenv;string_of_thm thm);
    in (ZENV:=h; t) end;
    

(* *********************************************************************** *)
(*									   *)
(* add operations (main interface) ...                                     *)
(*									   *)
(* *********************************************************************** *)


fun strip_Zsig (Const("ZPure.SBinder",_)  $ _ $ Abs (n,t,T))
       = insert_zsig (n,t) (strip_Zsig T)
   |strip_Zsig (Const("ZPure.SBinder0",_) $ _ $ Abs (n,t,T))
       = insert_zsig (n,t) mt_zsig
   |strip_Zsig _ = mt_zsig;

fun strip_Binder (Const("ZPure.SBinder",_)  $ _ $ Abs (n,t,T))
       = strip_Binder T
   |strip_Binder (Const("ZPure.SBinder0",_) $ _ $ Abs (n,t,T))
       = T
   |strip_Binder T = T
	
val SCHEMANAMES = ref([]:string list)
val AXDEFS      = ref([]:string list)
val CONJECTURES = ref([]:string list)
val FREEDEFS    = ref([]:string list)
val PARSES      = ref([]:term list);
val PARSES1     = ref([]:term list);
val PARSES2     = ref([]:term list);
fun init ()     = (SCHEMANAMES := []; AXDEFS :=[];
                   CONJECTURES:=[]; FREEDEFS:=[];
                   PARSES := []; PARSES1 := []; PARSES2:= [])
val AXPREP      = ref(NONE:((string * thm)->unit) option);
fun init_axprep p = (AXPREP:=SOME p);
fun do_axprep thy (n,thm) = case !AXPREP of
                              SOME p  => (context thy;p(n,thm))
		     	    | NONE    => ();

val TYPE_INFERS = ref([]: thm list)


fun Add_axdefs_TC axdef =
    let fun RS'' y x = SOME(x RS y) handle THM _ => NONE
        fun type_infers axdefs =
                          Library.flat (map (fn X => Library.mapfilter (RS'' X) 
                                                                        axdefs) 
                                       (!TYPE_INFERS))
        fun flat_conj m = Library.flat (Library.mapfilter (
                                fn x            =>SOME(flat_conj[x RS conjunct1,
                                                                 x RS conjunct2])
                                   handle THM _ =>SOME[x]) m)
        fun closure m   = m @ (type_infers m)
    in  Add_TC (Library.flat(Library.mapfilter
                    (fn x => SOME(closure(flat_conj[x RS DECL_D1]))
                              handle THM _ => NONE)
                              axdef))

    end;



fun gen_abs_type_thm str thy =
    let val nthm = prove_goalw thy [get_thm thy (Name (str^"_def"))] 
                                   ("x : "^str) 
                                   (K [asm_simp_tac (simpset_of thy) 1])
        val thy  = fst(PureThy.add_thms [((str^"_simp",nthm),[Simplifier.simp_add_global])] thy)
    in  Add_TC [nthm] thy
    end

fun add_abs_type ztype thy= 
(thy 
  |> Theory.add_types       [(ztype, 0, NoSyn)] 
  |> Theory.add_arities     [(ztype, [], "type")] 
  |> Theory.add_consts      [(ztype, ztype^" set", NoSyn)] 
  |> add_store_defs         [((ztype^"_def",ztype^" == UNIV"),[])] )
  |> gen_abs_type_thm       ztype;


(* functions for processing free datatype declarations, e.g.: 
   Report ::= ok| allready_known 
   KNOWN LIMITATION: DOES ONLY WORK FOR ENUMERATIONS
 *)
fun add_free_type (dt_types, tname, cons) thy = 
  let val (thy,{case_thms,distinct,exhaustion,induction,
                rec_thms,inject, simps,size, split_thms}) 
                                 =  DatatypePackage.add_datatype 
                                        false [tname]
                                        [(dt_types,tname,NoSyn,cons)] 
                                        thy 
(* TODO: Korrektes Verbuchen all dieser Fakten. --- Scheint uz klappen, steckt offenbar in thy.*)
  in    thy
     |> Theory.add_consts    [(tname, tname^" set", NoSyn)]
     |> add_store_defs       [((tname^"_def",tname^" == UNIV"),[])]
     |> gen_abs_type_thm     tname 
  end



(* FOR DEBUGGING : Global Vars containing the input,
   the input after binding expansion, the input after typewchecking *)

fun add_scheme_i thy_name (schemaS,bindsOpt) thy = 
    let val _          = (PARSES := schemaS @ (!PARSES) );
        val zenv       = ZTheory.get_zenv thy 
        (* AND NOW: structural conversion ! ! ! *)
        val schemaS    = flat(map (schema_conv (sign_of thy) zenv) schemaS)   
        val _          = (PARSES1 := schemaS);
        (* AND NOW: typechecking ! ! ! *)
        val (schema,_) = Sign.infer_types (Sign.pp thy) thy 
				(K NONE) (K NONE) [] true (schemaS,propT)
        val _          = (PARSES2:=[schema]);
        (* AND NOW: conversion into Isabelle-Definitions ! ! ! *)
    in  case schema of
        (* schema definition >>> *)
        (Const  ("==", T) $ Free (name,typ) $ D) =>
         (let val ()    = writeln("Converting schema definition "^name^".")
              val(typ,D)= case bindsOpt of
                           SOME _ => if is_set(typ) (* a set expression 
                                                       denotes a schema *)
                                     then let val tt = (dest_setT typ)-->boolT
                                          in (tt,
                                              Const("ZPure.asPred",typ-->tt)$D)
                                          end (* convert it into predicate
                                                 (the default represenation)*)
                                     else (typ,D)
                          |_ => (typ,D)
              val thy1  = Theory.add_consts_i  [(name, typ, NoSyn)](thy); 
         (*   This worked in Isabelle98:
	      val term  = Const("==", typ --> typ --> propT)
                          $ Const (thy_name^"."^name,typ) $ D; *)
	 (*   Now this seems to be more appropriate: *)		  
	      val thy_name'= NameSpace.path_of(Sign.naming_of thy1)
              val term  = Const("==", typ --> typ --> propT)
                          $ Const (thy_name'^"."^name,typ) $ D; 	  
              val thy2  = add_store_defs_i [((name^"_def", term),[])] thy1;
              val mm    = case bindsOpt of (* if ZETA-type available *)
	                    SOME x => update_zsig(K x)(mt_zsig) (*take it *)
			   |NONE   => strip_Zsig D       (* help yourself *)
              val zsig1 = if not(null(schemasig_of mm)) 
	                                   (* is it really a schema ? *)
                          then ZEnv.insert ((name,mm), schemas_of zenv)
                          else (schemas_of zenv)
	      val _     = (ZENV_test := update_Zenv_by_Zsig zenv zsig1)
              val _     = (SCHEMANAMES:= (name^"_def")::(!SCHEMANAMES))
          in  ZTheory.put_zenv (update_Zenv_by_Zsig zenv zsig1) (thy2) 
          end) 
      |(Const  ("==", T) $ Const (name,typ) $ D) => 
                           error("add_scheme_i: "^ name ^
                                 " was already defined!")
      | (* axiomatic definition >>> *)
        (Const ("Trueprop",ty) $
         (Const ("ZPure.turnstyle", _) $ S)) =>
        (let val Zsig{schemasig,...} = strip_Zsig S
             val name= (fst(hd schemasig) ^ "_axdef")
             val ()  = (writeln ("Parsing axiomatic definition "^name^"."))
             fun cast E = (map (fn (x,y) => (x,y,NoSyn)) E) 
             val thy = Theory.add_consts_i (cast schemasig) (thy);
             val ()  = (AXDEFS:=(name)::(!AXDEFS))
             fun cast2 E = map (fn (x,y) => Const(thy_name^"."^x,y)) E
             val S'  = subst_bounds(List.rev(cast2 schemasig),
                                    strip_Binder S);
             val S'' = Const ("Trueprop",ty) $ S';
             val thy = add_store_axioms_i [((name,S''),[])] thy
	     val thy = Add_axdefs_TC [get_axiom thy name] thy
         in  thy end)
    end;



fun add_scheme thy_name schema thy = 
    let val zenv = ZTheory.get_zenv thy 
    in add_scheme_i thy_name ((schema_parser thy zenv schema),NONE) thy end

(* val add_schemes : string list -> ztheory -> ztheory *)
fun add_schemes thy_name S zthy = 
    foldl (fn(m,zthy) => add_scheme thy_name m zthy) zthy  S ;    

fun add_schemes_i thy_name S zthy = 
    foldl (fn(m,zthy) => add_scheme_i thy_name m zthy) zthy  S ;    



fun add_conjecture_i thy_name conj thy =
     let val _          = (PARSES := (!PARSES) @ [conj]);
         val zenv       = ZTheory.get_zenv thy
         (* AND NOW: structural conversion ! ! ! *)
         fun dest_Trueprop (Const ("Trueprop", _) $ P) = P
           | dest_Trueprop t = t;
         val conjS      = map dest_Trueprop 
                              (schema_conv (sign_of thy) zenv conj)   
         val _          = (PARSES1 := conjS);
         (* AND NOW: typechecking ! ! ! *)
         val name       = "conjecture_"^(Int.toString(length(!CONJECTURES)))
         val thy_name'  = NameSpace.path_of(Sign.naming_of thy)
         val ()         = writeln("Converting conjecture "^name^".")
         val thy1       = Theory.add_consts_i  [(name, boolT, NoSyn)](thy); 
         val conjS      = map (fn conj => (Const  ("==", boolT --> boolT --> propT) $ 
                                           Const (thy_name'^"."^name,boolT) $ conj)) conjS
         val (conj',_)  = Sign.infer_types  (Sign.pp thy) thy1
				 (K NONE) (K NONE) [] true (conjS,propT)
         val _          = (PARSES2:=[conj']);
         (* AND NOW: conversion into Isabelle-Definitions ! ! ! *)
         val thy2       = add_store_defs_i     [((name^"_def", conj'),[])] thy1;
         val _          = (CONJECTURES:= (name^"_def")::(!CONJECTURES))
      in thy2 end


fun add_conjecture thy_name S thy =
    let val zenv = ZTheory.get_zenv thy
    in add_conjecture_i thy_name (hd(schema_parser thy zenv S)) thy end


(* *********************************************************************** *)
(*									   *)
(* OLD STYLE DECLARATIONS ...                                              *)
(*									   *)
(* *********************************************************************** *)


fun get_schemes thy     = map (fn x => (x, get_axiom thy x))(!SCHEMANAMES);
fun get_axdefs thy      = map (fn x => (x, get_axiom thy x))(!AXDEFS);
fun get_conjectures thy = map (fn x => (x, get_axiom thy x))(!CONJECTURES);


val string_of_zthm = fn zthy => let val zenv = ZTheory.get_zenv thy 
                                in  string_of_zthm thy zenv end

fun schema_read thy zenv  schema = 
    let val ts = schema_parser thy zenv schema;
        val _  = (PARSES := ts @ (!PARSES) );
        val ts = flat(map (schema_conv (sign_of thy) zenv) ts);
        val _  = (PARSES1 := ts @ (!PARSES1) );
        val (anno_semterm,_) = Sign.infer_types (Sign.pp thy) thy 
				(K NONE) (K NONE) [] true (ts,propT)
        val _  = (PARSES2 := [anno_semterm] @ (!PARSES2) );
    in  anno_semterm end;

val schema_read= fn thy => let val zenv = ZTheory.get_zenv thy
                           in schema_read thy zenv end

end;
