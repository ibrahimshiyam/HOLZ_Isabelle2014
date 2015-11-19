(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * pruningTactics.ML --- 
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
(* $Id: pruningTactics.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* Tactics to prune assumptions of isabelle*)
(* subgoals using strings.                 *)
(* The functions still have experimental   *)
(* status. Use them as heuristic functions *)
(* for pruning.                            *)
(* GPL open source software - usage on     *)
(* own danger                              *)
(*   written by  Harald Hiss.              *)
(*                                         *)


signature PRUNING_TACTICS =
sig 

    (* These are the default functions.  *)

    val filterPrems_keep : string list -> int -> Tactical.tactic
    val filterPrems_drop : string list -> int -> Tactical.tactic
    val filterPrems_drop_nth  : string list -> int -> int -> Tactical.tactic
    val filterPrems_drop_fst : string list -> int -> Tactical.tactic 

    (* These are tactics which provide   *)
    (* more parameters.                  *)
    (* The selection mode can be either  *)
    (* chosen from and/or mode or a self *)
    (* made function which decides for a *)
    (* given premise string and the      *)
    (* arguments string list, wether to  *)
    (* keep the corresponding premise or *)
    (* not.                              *)

    val filterPrems_keep_and : string list -> int -> Tactical.tactic
    val filterPrems_keep_or : string list -> int -> Tactical.tactic
    val filterPrems_keep_abs : 
	(string -> string list -> bool) -> string list -> int -> Tactical.tactic
    val filterPrems_drop_and : string list -> int -> Tactical.tactic
    val filterPrems_drop_or : string list -> int -> Tactical.tactic
    val filterPrems_drop_abs : 
	(string -> string list -> bool) -> string list -> int -> Tactical.tactic
    val filterPrems_drop_nth_or : string list -> int -> int -> Tactical.tactic
    val filterPrems_drop_nth_and : string list -> int -> int -> Tactical.tactic
    val filterPrems_drop_nth_abs :
	(string -> string list -> bool) -> string list -> int -> int -> Tactical.tactic
									
   (* The following functions allow to  *)
   (* make assumptions guided by a      *)
   (* search string (or several/using   *)
   (* and/or mode) to use assume_tac on *)
   (* the first matching assumption.    *)

   (* default, simple version *)
    val guidedAssumption : string list -> int -> Tactical.tactic

   (* versions having more parameters *)
    val guidedAssumption_abs : 
	(string -> string list -> bool) -> string list -> int -> Tactical.tactic
    val guidedAssumption_and : string list -> int -> Tactical.tactic
    val guidedAssumption_or : string list -> int -> Tactical.tactic

(* The following set of functions allows to *)
(* rotate the first matching assumption to  *)
(* the front of the assumption list. The    *)
(* Tactics etac, dtac, ... which operate    *)
(* directly on the assumptions can be guided*)
(* to use the desired operator.             *)

(* The following Tactics still have experimental *)
(* status.                                       *)

   (* default, simple version *)
    val move2Head : string list -> int -> Tactical.tactic

   (* versions having more parameters *)
    val move2Head_abs : 
	(string -> string list -> bool) -> string list -> int -> Tactical.tactic
    val move2Head_and : string list -> int -> Tactical.tactic
    val move2Head_or : string list -> int -> Tactical.tactic

(* the following functions directly   *)
(* combine the move2Head tactics with *)
(* etac, dtac.                        *)
    val guided_etac : string list -> Thm.thm -> int -> Tactical.tactic
    val guided_dtac : string list -> Thm.thm -> int -> Tactical.tactic
    val bge : string list -> Thm.thm -> int -> unit
    val bgd : string list -> Thm.thm -> int -> unit

   (* default, simple version *)
    val move2End : string list -> int -> Tactical.tactic

   (* versions having more parameters *)
    val move2End_abs : 
	(string -> string list -> bool) -> string list -> int -> Tactical.tactic
    val move2End_and : string list -> int -> Tactical.tactic
    val move2End_or : string list -> int -> Tactical.tactic

(* a function which i use frequently  *)
(* isSubstringOf smallString largeString *)
    val isSubstringOf : string -> string -> bool

end;



structure pruningTactics : PRUNING_TACTICS=
struct 


(* get the nth subgoal *)

fun nth_subgoal n pST= nth_elem ((n-1), (prems_of (pST)));


(* compute a list containing the meta-all-       *)
(* quantified variables (read all outer sequences*)
(* of all Lam () ...                             *)

fun mQuantVarList 
    ((Const("all", ty1)) $ (Abs (varName, ty2, tm)))
       = [varName]@(mQuantVarList tm)
  | mQuantVarList _ = [];

(* convert list of terms to list of strings. *)

(* critical point here:      *)
(* not sure wether theory of *)
(* topthm() makes sense/     *)
(* usage of Sign.string_of_term*)
(* if Z syntax is   known,   *)
(* the constants will not be *)
(* expanded (e.g.:           *)
(* ZMathTool.rel_appl will   *)
(* appear instead of %^ )    *)


fun term_toString aTerm aPrfState = 
    (Sign.string_of_term 
         (sign_of (theory_of_thm(aPrfState))) 
	 aTerm);
(**)
fun terms_toString aTermList aPrfState = 
    map 
	(fn x =>
	    (term_toString  
		 x 
		 aPrfState))
	aTermList;


(* ================== *)

(* some functions to do basic operations *)
(* on terms.                             *)


fun drop_fst  (t1 $ t2) = t2;

fun drop_snd (t1 $ t2) = t1;

fun getConstStr (Const(str, ty)) = str;

fun getConstTy (Const(str, ty)) = ty;

fun getAbsStr (Abs(str, ty, tm)) = str;

(* drop All $ Lam x. and keep t *)

fun drop_ConstAbs ((Const(str, ty)) $ Abs(stra, tya, tm)) 
    = tm;

(* retrieve new freeVar string  *)

fun getBStr_ConstAbs ((Const(str, ty)) $ Abs(stra, tya, tm)) 
  = stra;

(* retrieve type of new freeVar *)

fun getBTy_ConstAbs ((Const(str, ty)) $ Abs(stra, tya, tm)) 
  = tya;


(* ================== *)

(* a substitution function which replaces a *)
(* bound with a free variable.              *)

(* subst_free_in_b n aTerm (str, ty) *)
(* uses str and ty for replacing     *)
(* the B.n variable hole with a Free.*)
(*                                   *)
(* Be careful, its use only makes    *)
(* sense for globally declared B-Vars*)
(* , no care is taken of internal re-*)
(* numbering on recursive descending *)

fun subst_free_in_b n (Bound i) (str, ty)= 
    if (i=n) 
    then (Free(str, ty))
    else (Bound i)
  | subst_free_in_b n 
		    (Abs(strr, 
			 tyy, 
			 tmm)) 
		    (str, ty) = (Abs(strr, 
				     tyy, 
				     (subst_free_in_b n tmm (str, ty))))
  | subst_free_in_b n 
		    (t1 $ t2) 
		    (str, ty) = ((subst_free_in_b n t1 (str, ty)) 
				       $ (subst_free_in_b n t2 (str, ty)))
  | subst_free_in_b n x (str, ty) = x;



(*==========================================*)

(* now repeat #metavars times :   *)
(* strip first meta-allquantor    *)
(* and replace bound i with       *)
(* the renamed (using variant_abs)*)
(* and now free variable.         *)
(* (continue, i--)                *)

(*==========================================*)


fun rip_bound_n j n aTerm 
  = 
  let 
      val newName = if (not(j = n))
		    then fst(variant_abs ((getAbsStr(drop_fst aTerm)), 
					  (getConstTy (drop_snd aTerm)), 
					  (drop_fst aTerm)))
		    else "";
	  val cutAbsTerm = if (not(j = n))
			   then (drop_ConstAbs aTerm)
			   else aTerm;
	      val pairStrTy = if (not(j = n))
			      then ( newName, 
				     (getBTy_ConstAbs aTerm))
			      else ("", (fastype_of aTerm));
  in
      if(j = n)
      then aTerm 
      else rip_bound_n
	       (j-1)
	       n
	       (subst_free_in_b 
		    (j-1)
		    cutAbsTerm
		    pairStrTy)
  end;

(* combine correct counting of bruijn indices *)

fun rip_bound aTerm 
  = 
  let 
      val jInt = ((length (mQuantVarList aTerm)))
  in
      rip_bound_n jInt 0 aTerm
  end;

(*==========================================*)

(* need some String Processing functions here *)


(* fun is_Prefix smallString mainString *)

fun is_Prefix_e [] x = true
  | is_Prefix_e x [] = false
  | is_Prefix_e (x::xs) (y::ys) = 
    if (x=y)
    then (is_Prefix_e xs ys)
    else false;

(* exploding strings *)

fun is_Prefix smallString mainString
  = is_Prefix_e 
	(explode smallString) 
	(explode mainString);
  
  

(* processing strings: *)

fun isSubstringOf (smallString:string) (mainString:string) =
    if (Int.<((size mainString), (size smallString)))
    then false
    else
        if(is_Prefix smallString mainString)
        then true
        else (isSubstringOf 
		  smallString 
		  (substring(mainString,
                             1,
                             (size(mainString)-1))));
    
   
(*==========================================*)

(* these functions encapsulate the different*)
(* modes (and/or)                           *)
 
fun contains_one mainString aStringList
    = (exists (fn y 
		  => (isSubstringOf 
			  y 
			  mainString)) 
	      aStringList);
 
fun contains_all mainString aStringList
    = (forall (fn y 
		  => (isSubstringOf 
			  y 
			  mainString)) 
	      aStringList);
   
(*==========================================*)

(* These are the basic operations which     *)
(* allow pruning - rotate or drop           *)
(* assumption (combined with a recursive    *)
(* function call)                           *)


fun rotate_step recfun i  =
    THEN (( rotate_tac 1 i),
	  recfun);

fun drop_step recfun i =
    THEN ((thin_tac "?a" i),
	  recfun);


(*==========================================*)

(* This is the abstract body for the main   *)
(* pruning tactics using -keep- strategy.   *)

fun prunePrems_keep modeFun i [] aStringList  = all_tac
  | prunePrems_keep modeFun i (x::xs) aStringList 
    = 
    let
	val recFun = (prunePrems_keep modeFun i xs aStringList) 
    in
	if(modeFun x aStringList)
	then
            (rotate_step recFun i)
	else 
	    (drop_step recFun i)
    end;
    

(* This is the abstract body for the main   *)
(* pruning tactics using -drop- strategy.   *)

fun prunePrems_drop modeFun i [] aStringList  = all_tac
  | prunePrems_drop modeFun i (x::xs) aStringList 
    = 
    let
	val recFun = (prunePrems_drop modeFun i xs aStringList) 
    in
	if(modeFun x aStringList)
	then
            (drop_step recFun i)
	else 
	    (rotate_step recFun i)
    end;
    

(*---------------------------------*)
(* combine    correctly to make    *)
(* the procedures                  *)
(* work as Tacticals.              *)
(*---------------------------------*)

(* This function takes a pruning   *)
(* function and a selection mode   *)
(* function, a String List and a   *)
(* subgoal number and returns a    *)
(* tactic.                         *)

fun ((filterPrems_abs pruneFun modeFun aStringList i):Tactical.tactic)
  = 

  (fn pSt => 
      ( 
       let
	   val assums_strings = (terms_toString 
				     (Logic.strip_assums_hyp 
					  (rip_bound (nth_subgoal i pSt)))
				     pSt)
       in
	   (
	    (pruneFun
		 modeFun
		 i
		 assums_strings
		 aStringList) pSt
	    )
       end));

(* This version also provides an argument for *)
(* the pruning function.                      *)

fun ((filterPrems_abs_args pruneFun modeFun aStringList i args):Tactical.tactic)
  = 

  (fn pSt => 
      ( 
       let
	   val assums_strings = 
	       (terms_toString 
		    (Logic.strip_assums_hyp 
			 (rip_bound (nth_subgoal i pSt)))
		    pSt)
       in
	   (
	    (pruneFun
		 modeFun
		 i
		 args
		 assums_strings
		 aStringList) pSt
	    )
       end));  

(* concrete pruning Tactics *)
(* using the keep strategy. *)

(* abstract version, may be extended *)
(* using an own selection mode.      *)

val filterPrems_keep_abs =
    (filterPrems_abs prunePrems_keep);

(* and - selection mode *)
val filterPrems_keep_and =
    (filterPrems_keep_abs contains_all); 


(* or - selection mode. *)
val filterPrems_keep_or =
    (filterPrems_keep_abs contains_one); 

(* or - mode is default *)
val filterPrems_keep = filterPrems_keep_or;


(* concrete pruning Tactics *)
(* using the drop strategy. *)

(* abstract version, may be extended *)
(* using an own selection mode.      *)

val filterPrems_drop_abs =
    (filterPrems_abs prunePrems_drop);

(* and - selection mode *)
val filterPrems_drop_and =
    (filterPrems_drop_abs contains_all); 


(* or - selection mode. *)
val filterPrems_drop_or =
    (filterPrems_drop_abs contains_one); 

(* or - mode is default *)
val filterPrems_drop = filterPrems_drop_or;


(* a similiar tactic which drops  *)
(* the nth assumption which has a *)
(* match relative to the given    *)
(* string list                    *)
(* (if it exists)                 *)


fun prunePrems_drop_nth modeFun i n [] (aStringList: (string list))  = all_tac
  | prunePrems_drop_nth modeFun i n (x::xs) aStringList 
    = 
    let 
	val recFun_pn = (prunePrems_drop_nth modeFun i (n-1) xs aStringList )
	val recFun_n = (prunePrems_drop_nth modeFun i (n) xs aStringList )
    in
	if(modeFun x aStringList)
	then
	    if (n = 1)
	    then (drop_step recFun_pn i)
	    else (rotate_step recFun_pn i)
	else 
	    (rotate_step recFun_n i)
    end;



(* concrete pruning Tactics     *)
(* using the drop_nth strategy .*)

(* abstract version, may be extended *)
(* using an own selection mode.      *)

val filterPrems_drop_nth_abs =
    (filterPrems_abs_args prunePrems_drop_nth);

(* and - selection mode *)
val filterPrems_drop_nth_and =
    (filterPrems_drop_nth_abs contains_all); 


(* or - selection mode. *)
val filterPrems_drop_nth_or =
    (filterPrems_drop_nth_abs contains_one); 

(* or - mode is default *)
val filterPrems_drop_nth = filterPrems_drop_nth_or;



(* a simple variant of the previous tactic    *)
(* which drops the first matching assumption. *)
(* It uses the or - selection mode.           *)

fun filterPrems_drop_fst strList i = 
    (filterPrems_drop_nth_or strList i 1);


(*==========================================*)

(* The following function shall allow you to*)
(* choose a matching assumption controlled  *)
(* by a modeFunction and a matching string  *)
(* list. Metavariables for example can be   *)
(* automatically guided to match on the     *)
(* desired assumption.                      *)

(* This is the abstract body for the main   *)
(* guided assumption tactics.               *)
(* [fail if no match  found!]               *)
(* emulate -do nothing- using the TRY       *)
(* Tactical.                                *)

fun guidedAssums_abs modeFun i [] aStringList  = no_tac
  | guidedAssums_abs modeFun i (x::xs) (aStringList: (string list)) 
    = 
    let
	val recFun = (guidedAssums_abs modeFun i xs aStringList) 
    in
	if(modeFun x aStringList)
	then
            (assume_tac i)
	else 
	    (rotate_step recFun i)
    end;
    
(* use abstraction function from before    *)
(* abstract version: *)
val guidedAssumption_abs = 
    (filterPrems_abs guidedAssums_abs);

(* and version (also default)*)
val guidedAssumption_and = 
    (guidedAssumption_abs contains_all);
val guidedAssumption = guidedAssumption_and;
    
(* or  version               *)
val guidedAssumption_or = 
    (guidedAssumption_abs contains_one);

(*==========================================*)

(* The following set of functions allows to *)
(* rotate the first matching assumption to  *)
(* the front of the assumption list. The    *)
(* Tactics etac, dtac, ... which operate    *)
(* directly on the assumptions can be guided*)
(* to use the desired operator.             *)

(* This is the abstract body for the main   *)
(* move2Head Tactics.                       *)

(* raise exception if no match occured -    *)
(* can be ignored afterwards using TRY.     *)

fun moveTOHead_abs modeFun i [] aStringList  = no_tac
  | moveTOHead_abs modeFun i (x::xs) aStringList 
    = 
    let
	val recFun = (moveTOHead_abs modeFun i xs aStringList) 
    in
	if(modeFun x aStringList)
	then
            (all_tac)
	else 
	    (rotate_step recFun i)
    end;
     
(* use abstraction function from before    *)
(* abstract version: *)
val move2Head_abs = 
    (filterPrems_abs moveTOHead_abs);

(* and version (also default)*)
val move2Head_and = 
    (move2Head_abs contains_all);
val move2Head = move2Head_and;
    
(* or  version               *)
val move2Head_or = 
    (move2Head_abs contains_one);

(* the following functions directly   *)
(* combine the move2Head tactics with *)
(* etac, dtac.                        *)

(* etac - version/be: *)

fun guided_etac aStringList aThm i = 
    ((move2Head aStringList i) 
	 THEN 
	 (etac aThm i));

(* dtac - version:/bd *)

fun guided_dtac aStringList aThm i = 
    ((move2Head aStringList i) 
	 THEN 
	 (dtac aThm i));

(* shorthand (like be) *)
fun bge aStringList aThm i = by(guided_etac aStringList aThm i);

(* shorthand (like bd) *)
fun bgd aStringList aThm i = by(guided_dtac aStringList aThm i);


(*==========================================*)

(* The following set of functions allows to *)
(* rotate the first matching assumption to  *)
(* the back  of the assumption list. The    *)
(* Tactics etac, dtac, ... which operate    *)
(* directly on the assumptions can be guided*)
(* to use the desired operator.             *)

(* This is the abstract body for the main   *)
(* move2Head Tactics.                       *)

(* raise exception if no match occured -    *)
(* can be ignored afterwards using TRY.     *)

fun moveTOEnd_abs modeFun i [] aStringList  = no_tac
  | moveTOEnd_abs modeFun i (x::xs) aStringList 
    = 
    let
	val recFun = (moveTOEnd_abs modeFun i xs aStringList) 
    in
	if(modeFun x aStringList)
	then
            (rotate_tac 1 i)
	else 
	    (rotate_step recFun i)
    end;
     
(* use abstraction function from before    *)
(* abstract version: *)
val move2End_abs = 
    (filterPrems_abs moveTOEnd_abs);

(* and version (also default)*)
val move2End_and = 
    (move2End_abs contains_all);
val move2End = move2End_and;
    
(* or  version               *)
val move2End_or = 
    (move2End_abs contains_one);


end; 

(* end struct pruningTactics *)

(* SAMPLE SESSION *)

(*
...starting at level 20 of proof of loginAknows.

Level 20
((abs_passwd, rep, rep_permtab, wc, wc_uidtab, wfiles), abs_passwdS, repS,
 rep_permtabS, wcS, wc_uidtabS, wfilesS)
: Areachable3 =+=>
abs_passwd %^ x ~= abs_passwdS %^ x =+=> (x, abs_passwdS %^ x) : Aknows
 1. !!xa y z.
       [| fst xa %^ x ~= fst y %^ x =+=> (x, fst y %^ x) : Aknows;
          (xa, y) : {.AService @ (%theta AbsState, %theta AbsState').} %*;
          (y, z) : {.AService @ (%theta AbsState, %theta AbsState').};
          fst xa %^ x ~= fst z %^ x; fst xa %^ x = fst y %^ x |]
       ==> (x, fst z %^ x) : Aknows
 2. !!xa y z.
       [| (xa, y) : {.AService @ (%theta AbsState, %theta AbsState').} %*;
          (y, z) : {.AService @ (%theta AbsState, %theta AbsState').};
          fst xa %^ x ~= fst z %^ x; fst xa %^ x ~= fst y %^ x;
          (x, fst y %^ x) : Aknows |]
       ==> (x, fst z %^ x) : Aknows
val it = () : unit
> by(filterPrems_drop_fst ["%^ x"] 1);
Level 21
((abs_passwd, rep, rep_permtab, wc, wc_uidtab, wfiles), abs_passwdS, repS,
 rep_permtabS, wcS, wc_uidtabS, wfilesS)
: Areachable3 =+=>
abs_passwd %^ x ~= abs_passwdS %^ x =+=> (x, abs_passwdS %^ x) : Aknows
 1. !!xa y z.
       [| (xa, y) : {.AService @ (%theta AbsState, %theta AbsState').} %*;
          (y, z) : {.AService @ (%theta AbsState, %theta AbsState').};
          fst xa %^ x ~= fst z %^ x; fst xa %^ x = fst y %^ x |]
       ==> (x, fst z %^ x) : Aknows
 2. !!xa y z.
       [| (xa, y) : {.AService @ (%theta AbsState, %theta AbsState').} %*;
          (y, z) : {.AService @ (%theta AbsState, %theta AbsState').};
          fst xa %^ x ~= fst z %^ x; fst xa %^ x ~= fst y %^ x;
          (x, fst y %^ x) : Aknows |]
       ==> (x, fst z %^ x) : Aknows
val it = () : unit
> by(filterPrems_drop_nth ["xa"] 3 1);
Level 22
((abs_passwd, rep, rep_permtab, wc, wc_uidtab, wfiles), abs_passwdS, repS,
 rep_permtabS, wcS, wc_uidtabS, wfilesS)
: Areachable3 =+=>
abs_passwd %^ x ~= abs_passwdS %^ x =+=> (x, abs_passwdS %^ x) : Aknows
 1. !!xa y z.
       [| (xa, y) : {.AService @ (%theta AbsState, %theta AbsState').} %*;
          (y, z) : {.AService @ (%theta AbsState, %theta AbsState').};
          fst xa %^ x ~= fst z %^ x |]
       ==> (x, fst z %^ x) : Aknows
 2. !!xa y z.
       [| (xa, y) : {.AService @ (%theta AbsState, %theta AbsState').} %*;
          (y, z) : {.AService @ (%theta AbsState, %theta AbsState').};
          fst xa %^ x ~= fst z %^ x; fst xa %^ x ~= fst y %^ x;
          (x, fst y %^ x) : Aknows |]
       ==> (x, fst z %^ x) : Aknows
val it = () : unit
> by(filterPrems_keep ["AService"] 2);
Level 23
((abs_passwd, rep, rep_permtab, wc, wc_uidtab, wfiles), abs_passwdS, repS,
 rep_permtabS, wcS, wc_uidtabS, wfilesS)
: Areachable3 =+=>
abs_passwd %^ x ~= abs_passwdS %^ x =+=> (x, abs_passwdS %^ x) : Aknows
 1. !!xa y z.
       [| (xa, y) : {.AService @ (%theta AbsState, %theta AbsState').} %*;
          (y, z) : {.AService @ (%theta AbsState, %theta AbsState').};
          fst xa %^ x ~= fst z %^ x |]
       ==> (x, fst z %^ x) : Aknows
 2. !!xa y z.
       [| (xa, y) : {.AService @ (%theta AbsState, %theta AbsState').} %*;
          (y, z) : {.AService @ (%theta AbsState, %theta AbsState').} |]
       ==> (x, fst z %^ x) : Aknows
val it = () : unit
> by(filterPrems_drop ["y"] 1);
Level 24
((abs_passwd, rep, rep_permtab, wc, wc_uidtab, wfiles), abs_passwdS, repS,
 rep_permtabS, wcS, wc_uidtabS, wfilesS)
: Areachable3 =+=>
abs_passwd %^ x ~= abs_passwdS %^ x =+=> (x, abs_passwdS %^ x) : Aknows
 1. !!xa y z. fst xa %^ x ~= fst z %^ x ==> (x, fst z %^ x) : Aknows
 2. !!xa y z.
       [| (xa, y) : {.AService @ (%theta AbsState, %theta AbsState').} %*;
          (y, z) : {.AService @ (%theta AbsState, %theta AbsState').} |]
       ==> (x, fst z %^ x) : Aknows

==========================================================

sample session for the guidedAssumption - tactic family:

> goal thy "!! a. [| a; b; ba; c; da|] ==> ?A";
Level 0
!!a. [| a; b; ba; c; da |] ==> ?A
 1. !!a. [| a; b; ba; c; da |] ==> ?A
val it = [] : Thm.thm list
> by(guidedAssumption ["b", "a"] 1);
Level 1
!!a. [| a; b; ba; c; da |] ==> ba
No subgoals!
val it = () : unit
> undo();
Level 0
!!a. [| a; b; ba; c; da |] ==> ?A
 1. !!a. [| a; b; ba; c; da |] ==> ?A
val it = () : unit
> by(guidedAssumption_or ["b", "a"] 1);
Level 1
!!a. [| a; b; ba; c; da |] ==> b
No subgoals!
val it = () : unit
> 

*)
