(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ZEnv.sml --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 2000-2003 University Freiburg, Germany
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
(* $Id: ZEnv.sml 6729 2007-08-03 05:25:17Z brucker $ *)


infixr union_zsig  diff_zsig;

(*
  TODO: Renaming
  Zsig -> Schtyp
  zsig -> schtyp

  ZsigTable -> Schtyp_tab
  schemas_of -> schtyp_tab_of

 *) 

structure ZEnv 		:
 sig datatype Zsig      = Zsig of {schemasig : (string * typ) list}
     val eq_zsig        : Zsig * Zsig -> bool
     val schemasig_of   : Zsig -> (string * typ) list

     val mt_zsig        : Zsig
     val insert_zsig    : string * typ -> Zsig -> Zsig
     val delete_zsig    : string * typ -> Zsig -> Zsig
     val union_zsig     : Zsig * Zsig -> Zsig
     val diff_zsig      : Zsig * Zsig -> Zsig
     val update_zsig    : ((string * typ) list -> (string * typ) list)
                          -> Zsig -> Zsig
     val filter_zsig    : (string * typ -> bool) -> Zsig -> Zsig 

     type ZsigTable     = Zsig Symtab.table
     type Zenv;

     val ZENV           : Zenv ref
     val ZENV_test      : Zenv ref
     val protect_zenv   : ('a -> 'b) -> 'a -> 'b

     val mt_zenv        : Zenv
     val update_Zenv_by_Zsig: Zenv -> ZsigTable -> Zenv 
     val update_Zenv_by_Imports: Zenv -> string list -> Zenv
     val update_Zenv_by_Unit: Zenv -> (string * ZAbsy.Section) -> Zenv 
     val update_Zenv_by_tc_simps : Zenv -> simpset -> Zenv
 
     val lookup         : ZsigTable * string -> Zsig option
     val lookup_selectors: Zenv -> string -> (int*int) list
     val insert 	: (string * Zsig) * ZsigTable -> ZsigTable     
     val merge          : Zenv * Zenv -> Zenv
     val is_def 	: ZsigTable * string  -> bool

     val schemas_of     : Zenv -> ZsigTable 
     val tc_simps_of    : Zenv -> simpset
     val imports_of     : Zenv -> string list

     val prinzenv       : Zenv -> unit

end = 
struct

local open ZPrelude in


datatype Zsig = Zsig of {schemasig : (string * typ) list}

val mt_zsig = Zsig{schemasig=[]};


fun eq_zsig (Zsig{schemasig=s1},Zsig{schemasig=s2}) = (s1 = s2);

fun update_zsig f (Zsig{schemasig})
      = Zsig{schemasig = f schemasig};

fun insert_zsig x (Zsig{schemasig})
      = Zsig{schemasig = x::schemasig};

fun delete_zsig x (Zsig{schemasig})
      = Zsig{schemasig = filter_out (fn(a,b)=>a=(fst x))schemasig};

fun filter_zsig f (Zsig{schemasig})
      = Zsig{schemasig = filter f schemasig};

fun (Zsig{schemasig=s1}) union_zsig
    (Zsig{schemasig=s2}) = 
  let fun max (a,b) = if (a < b) then b else a;
  in Zsig{schemasig = s1@s2}
  end;

fun (Zsig{schemasig=s1}) diff_zsig
    (Zsig{schemasig=s2}) = 
  let fun max (a,b) = if (a < b) then b else a;
  in  Zsig{schemasig = filter_out (fn(a,_)=>exists(fn(b,_)=>a=b) s2) s1}
  end;

fun schemasig_of (Zsig{schemasig,...}) = schemasig;


type ZsigTable = Zsig Symtab.table;
type UnitTable = ZAbsy.Section Symtab.table;

datatype Zenv = Zenv of {schemas  : ZsigTable,
                         units    : UnitTable,
                         imports  : string list,
                         tc_simps : simpset}




fun schemas_of (Zenv{schemas,...}) = schemas;

fun units_of (Zenv{units,...})     = units;

fun imports_of (Zenv{imports,...}) = imports;

fun tc_simps_of (Zenv{tc_simps,...}) = tc_simps;

val mt_zenv = Zenv {schemas = (Symtab.empty:ZsigTable),
                    units   = (Symtab.empty:UnitTable),
                    imports=["Toolkit"], 
                    tc_simps = HOL_ss 
                               (* OR: simpset_of (theory ("Product_Type"))  *) };


val ZENV = ref mt_zenv;
val ZENV_test = ref mt_zenv;

fun protect_zenv f x = let val h = !ZENV 
                           val g = f x
                       in  (ZENV := h; g) end;


fun update_Zenv_by_Zsig (Zenv{schemas,units,imports,tc_simps}) zsig 
    = 
    Zenv {schemas  = zsig,
          units    = units,
          imports  = imports,
          tc_simps = tc_simps};

fun update_Zenv_by_Imports (Zenv{schemas,units,imports,tc_simps}) imprt 
    = 
    Zenv {schemas  = schemas,
          units    = units,
          imports  = imprt,
          tc_simps = tc_simps};

fun update_Zenv_by_Unit (Zenv{schemas,units,imports,tc_simps})
                        (name,sec) = 
    Zenv {schemas  = schemas,
          units    = Symtab.update (name,sec) units,
          imports  = imports,
          tc_simps = tc_simps};

fun update_Zenv_by_tc_simps (Zenv{schemas,units,imports,tc_simps})
                        ss = 
    Zenv {schemas  = schemas,
          units    = units,
          imports  = imports,
          tc_simps = ss};


fun lookup (e, n)  = 
    let val k = strokes n  
        fun m (a,b)=(strokeN k a,b)
    in  case Symtab.lookup e  (ZPrelude.destroke n) of
          NONE    => NONE
        | SOME sg => SOME(update_zsig (map m) sg)
    end

fun insert (l, e) =
    let val zs = (fst l, 
                  Zsig {schemasig = (schemasig_of (snd l))});
    in Symtab.update zs e end;

fun cons_entry ((key, entry), tab) =
    Symtab.update (key, entry :: (Symtab.lookup_multi tab key))  tab;

fun merge (z1,z2)  = 
    Zenv {schemas  = Symtab.merge (eq_zsig) (schemas_of z1,schemas_of z2)
                     handle Symtab.DUPS strS =>(writeln("ZEnv.merge ERROR:"^
	                                        (String.concat strS)^"\n");
			                       raise Symtab.DUPS strS ),
          units    = Symtab.merge (op =)(units_of z1,units_of z2),
          imports  = distinct(imports_of z1 @ imports_of z2),
          tc_simps = merge_ss(tc_simps_of z1, tc_simps_of z1)};

fun is_def (e,n) = 
    case Symtab.lookup e  (ZPrelude.destroke n) of
          NONE   => false
        | SOME n => true;
    
fun lookup_selectors zenv nm = 
    let 
	fun mapfilter (f: 'a -> 'b option) ([]: 'a list) = [] : 'b list
	  | mapfilter f (x :: xs) =
	    (case f x of
		 NONE => mapfilter f xs
	       | SOME y => y :: mapfilter f xs);
	val cont = map (fn(k,e) => schemasig_of e) 
                   (Symtab.dest(schemas_of zenv))
        fun H x  = let val k = find_index (fn (x,_) => x = nm) x
                   in  if k= ~1 then NONE
                       else SOME(k,(length x) -1) (* SOME(((length x) - k) - 1) *)
                   end
        val selS = mapfilter H cont
    in  distinct selS
    end; 

fun get_name_and_rhs th =
    let fun parseeq (Const("==",_)$Const(n,_)$t) = (n,t)
          | parseeq (Const("op =",_)$Const(n,_)$t) = (n,t)
          | parseeq (Const ("Trueprop",_)$t) = parseeq t
          | parseeq _                  = raise ERROR;
    in parseeq (concl_of th) end;


(* gibt zenv in lesbarer Form aus *)
fun prinzenv zenv =
  let fun constructstring sep (s::[]) = s
        | constructstring sep (s::sl) = s^sep^constructstring sep sl
        | constructstring sep [] = "";
      fun sig2string s = constructstring "," (map fst s);
      fun makestring d =
        let fun decimal_shift s 0 = s
              | decimal_shift s x = decimal_shift ((chr(48+(x mod 10)))^s)
                                                  (x div 10);
        in if (d < 0) then "~" ^ decimal_shift "" (~d) else decimal_shift "" d
        end;
      fun zprint (n,Zsig{schemasig=s})
                   = writeln 
                     ("--------------------------------------------------\n\n"
                      ^n^" sig=["^(sig2string s)
                      ^"])\n\n");
  in map zprint (Symtab.dest (schemas_of zenv));
     writeln ("--------------------------------------------------\n\n");
     writeln ("imports: "^(concat (imports_of zenv)));
     writeln ("--------------------------------------------------\n\n");
     writeln ("tc_simps: "); print_ss(tc_simps_of zenv)
  end;


end;
end;

open ZEnv;

