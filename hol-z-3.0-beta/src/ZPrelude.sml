(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ZPrelude.sml --- 1999-2000 University Bremen, Germany
 *                  2000-2003 University Freiburg, Germany
 *                  2004-2007 ETH Zurich, Switzerland
 *
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
(* $Id: ZPrelude.sml 8082 2008-06-06 10:39:53Z wolff $ *)

structure ZPrelude	=
struct

fun stripName str = hd(rev (String.fields (fn x => x = #".") str))

fun stripTerm (Const(str,ty)) = Const(stripName str,ty)
   |stripTerm (s $ t)         = (stripTerm s) $(stripTerm t)
   |stripTerm (Abs(s,ty,t))   = Abs(s,ty,stripTerm t)
   |stripTerm t               = t

val stroke_sym = "'";
val in_sym     = "?";
val out_sym    = "!";

fun destroke str = 
    let fun cut (a :: S) = if a = stroke_sym then cut S else (a :: S)
           |cut []       = [];
    in  implode (rev (cut (rev (explode str)))) end;


fun is_in_name str =  (case rev(explode str) of
                          x ::_ => in_sym = x
                        | _ => false);

fun is_out_name str = (case rev(explode str) of
                           x ::_ => out_sym = x
                        | _ => false);

fun is_stroke_name str = (case rev(explode str) of
                           x ::_ => stroke_sym = x
                        | _ => false);

fun copy str n = if n = 0 then "" else str ^ copy str (n-1) ;
   	                      
fun strokeN n str = str ^ (copy stroke_sym n);

fun strokes str = (size str) - (size (destroke str));

fun stroke (a,t) = (strokeN 1 a,t);

fun genstrokeN n t = if n=0 then t
      	             else Const("SSTROKE",dummyT) $ (genstrokeN(n-1)t);     

fun sharevars  [] e1 = []
  | sharevars l [] = l
  | sharevars ((n,t)::ll) ((n1,t1)::e) =  if ((n,t)  = (n1,t1)) 
  				  then (sharevars ll e) 
  				  else ((n1,t1)::(sharevars ll e));

(* Diese Funktionen sind das verbliebene Erbe des Afrikaners ... *)

fun diffvars  [] e1 = []
  | diffvars l [] = l
  | diffvars ((n,t)::ll) ((n1,t1)::e)  = if ((n,t)  = (n1,t1))  
  				 then (diffvars ll e) 
  				 else ((n1,t1)::(diffvars ll e));

 val compare = (op <= : string * string -> bool);  
 fun insert ((l, ll), e) = if ((l, ll) mem e) 
 			   then e 
 			   else ((l,ll)::e);

fun sortmerge e e1 =  
    let fun  firstsort ([],e1) 		 	  = e1
  	    |firstsort (e,[]) 		 	  = e
  	    |firstsort (((ll,t)::al), ((ll1,t1)::al1)) =
  		       if compare(ll,ll1) 
  		       then (ll,t)::(firstsort (al, (ll1,t1)::al1))
  		       else (ll1,t1)::(firstsort(((ll,t)::al), al1));
  	 fun sndsort [] = []
  	    |sndsort ((aa,aaa)::al)=firstsort(((aa,aaa)::al), sndsort al)
    in distinct((sndsort (firstsort (e, e1))) @(sndsort (firstsort (e, e1)))) 
    end;

fun sortmerge [] S = 
     gen_distinct (fn ((x,_),(y,_))=> x = y)
        (sort(fn ((x,_),(y,_)) => string_ord(x,y)) S);
    


fun mk_tuple (E :: b :: R) = Const("Pair",dummyT) $ E $ (mk_tuple (b::R))
   |mk_tuple (E::[])       = E;
   
fun strip_tuple (Const ("Pair",_) $ a $ b) = a :: (strip_tuple b)
   |strip_tuple x = [x];



val zero = ord "0";
val ten = ord "A" - 10;
val List_nibble_prefix="List.nibble."
val List_nibble_prefix_length = size List_nibble_prefix
val Nibble_prefix= "Nibble";
val Nibble_prefix_length= size Nibble_prefix;


(* Problem : The following code for dest_{char,string} must run in
   terms where all constant names are fully qualified as well of
   terms where there are not. This explains part of the complexity. *)

fun mk_nib n =
    Syntax.const (Nibble_prefix ^ chr (n + (if n <= 9 then zero else ten)));

fun dest_nib (Const (c, _)) =
    let val norm   = if String.isPrefix List_nibble_prefix c
	                 then String.substring(c,List_nibble_prefix_length,(size c) -
			                         List_nibble_prefix_length) 
			 else c
        val norm   = if String.isPrefix Nibble_prefix norm
                         then String.substring(norm,Nibble_prefix_length,(size norm) -
			                            Nibble_prefix_length) 
			 else error("dest_nib: wrong format:"^c)
    in  (case explode (norm) of
            [h] => (if "0" <= h andalso h <= "9" 
	            then ord h - ord "0"
		    else if "A" <= h andalso h <= "F" 
		         then ord h - ord "A" + 10
			 else raise Match)
            | _ => raise Match)
	end
    | dest_nib _ = raise Match;


fun dest_nibs t1 t2 = chr (dest_nib t1 * 16 + dest_nib t2);


fun mk_char c =
      Syntax.const "List.Char" $ mk_nib (ord c div 16) 
                               $ mk_nib (ord c mod 16);

fun dest_char (Const ("Char", _) $ t1 $ t2) = dest_nibs t1 t2
  | dest_char (Const ("List.char.Char", _) $ t1 $ t2) = dest_nibs t1 t2
  | dest_char _ = raise Match;


(*
fun mk_string [] = Syntax.const Syntax.constrainC $ Syntax.const "[]" 
                                                  $ Syntax.const "string"
    | mk_string (t :: ts) = Syntax.const "op #" $ t $ mk_string ts;
 *)

val charT = Type ("List.char", []);

fun mk_string st = HOLogic.mk_list(mk_char) (charT) (explode st)


fun dest_string x = 
    let fun dest_string0 (Const ("List.list.Nil", _)) = []
          | dest_string0 (Const ("Nil", _)) = []
          | dest_string0 (Const ("List.list.Cons", _) $ c $ cs) = 
                           dest_char c :: dest_string0 cs
          | dest_string0 (Const ("Cons", _) $ c $ cs) = 
                           dest_char c :: dest_string0 cs
          | dest_string0 _ = raise Match;
    in implode(dest_string0 x) end


      
exception IllegalSchema;
exception IllegalType;
exception IllegalSemTerm;
exception IllegalSyntax;
exception SchemaNotDefined;

(*Form an abstraction over a free Zschema variable.*)

fun tconv _ _ = true;

fun abstract_over1 (Free(t,T),body) =
  let fun abst (lev,u) = 
      (case u of
          Free(s,S)  => if (t = s) andalso tconv S T then (Bound lev) 
		        else Free(s,S)
        | Abs(a,T,t) => Abs(a, T, abst(lev+1, t))
	| f$rand => abst(lev,f) $ abst(lev,rand)
	| _ => u)
  in  abst(0,body)  end;


(********* For an old version of schema binders SB x. SB0 y.  A *******)

fun sb0_absfree (a,T,body) = (Const("ZPure.SBinder0",dummyT) $ 
			     	(mk_string a) $ Abs(a, T, 
			     	    abstract_over1 (Free(a,T), body)));

fun sb_absfree (a,T,body) = (Const("ZPure.SBinder",dummyT) $ 
				(mk_string a) $ Abs(a, T, 
				abstract_over1 (Free(a,T), body)));

(*Abstraction over a list of free Zschema variables*)
fun sb_list_abs_free ([] ,     t) = t
  | sb_list_abs_free ((a,T)::[], t) = 
      sb0_absfree(a, T, t)
  | sb_list_abs_free ((a,T)::vars, t) = 
      sb_absfree(a, T, sb_list_abs_free(vars,t));



fun lift_mvars (Var x) i k = list_comb ((Var x) ,
                                        (map Bound (i upto (i+k))))
   |lift_mvars (S $ T) i k = (lift_mvars S i k) $
                             (lift_mvars T i k)
   |lift_mvars (Abs(s,t,tt)) i k = Abs(s,t,lift_mvars tt (i+1) k)
   |lift_mvars tt i k = tt

fun gen_binder freeNames trm =
    let val sortedNames= sortmerge [] freeNames;
          (* May be problematic in connection with type-variables as
             a consequence of Generic Structures *)
        val trm2 = lift_mvars trm 0 ((length sortedNames) - 1)
          (* lifting of internal Var's over the sch-binder
             increases usability of during proofs *)
    in  sb_list_abs_free(sortedNames, trm2) end;


fun gen_binding taggedExprS =
    let val sorted = sortmerge [] taggedExprS 
    in  mk_tuple (map snd sorted) end;
	
fun gen_proj x e (no,num) = 
    let fun gen_pr x = let fun gp 0 = Bound 0
                             | gp x = Const("snd",dummyT) $ (gp (x-1))
                           fun lastProj E= if num = 0 then Bound 0
					   else if no=num 
					        then E
					        else Const("fst",dummyT) $ E
		       in  Abs("x",dummyT, lastProj(gp x)) end
    in  Const("ZPure.PROJ",dummyT) $ e $ (gen_pr no) $ (mk_string x)
    end

fun gen_projection x e tagS =
    let val tagNo      = (length tagS)-1
        val numTagS    = ListPair.zip(tagS, 0 upto tagNo)
        val sortedTags = sortmerge [] numTagS
        val SOME(_,no) = List.find (fn (a,_) => a = x)(sortedTags)
    in  gen_proj x e (no,tagNo) end

fun gen_bindingT bdg = foldr1 HOLogic.mk_prodT (map snd (sortmerge [] bdg))

(* tt: Term in which we want to rename,
rn: list of pairs of strings *)
fun gen_rename tt rn = Free("xxx", dummyT)



end;
