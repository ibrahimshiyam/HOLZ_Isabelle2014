(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * CVSServer.ML --- 
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
(* $Id: CVSServer.ML 6746 2007-08-03 07:25:55Z brucker $ *)


open CVSServer;

toToplevel axdefs;
toToplevel schemes;

(* Show that rep_access only selects paths that are valid paths in the
 * file system. 
 *)
zgoalw CVSServer.thy [] "(Cvs_FileSystem /\\ x: Path) =+=> \
			\ (!p: (rep_access %^ (%theta Cvs_FileSystem) %^ (x)). \
			\ ( ? q : Path . q %&^ p : dom files))";
by (intro_schema_tac 1); 
by (step_tac HOL_cs 1); 
by (forward_tac [stripS (get_decl thy "Cvs_FileSystem" 1)] 1); 
by (stac rep_access_axdef2 1);
br ballI 3; 
by (ALLGOALS (asm_full_simp_tac (Z2HOL_ss addsimps [image_def,asSet_def,prefixseq_def])));
auto();
qed "rep_access_is_in_dom_files";


(* a basic lemma that's missing in Set *)
goalw Fun.thy [] "!!A. (A = B) ==> (x:A) = (x:B)";
auto();
qed "set_cong";

(* , another one: *)

goalw thy [] "!! x. [| x : B ; A=B |] ==> x:A";
auto();
qed"eqSetMem";


(* *)
zgoalw CVSServer.thy [theta_def] "Cvs_FileSystem /\\ x: Path /\\ \
			\ p: (rep_access %^ (%theta Cvs_FileSystem) %^ (x)) \
			\ =+=> (x prefix p)";
by (stripS_tac 1);
by (Step_tac 1);
br (((simplify (simpset()addsimps [image_def,asSet_def]) 
	       ((rep_access_axdef2 RS set_cong) RS iffD1)) 
	 RS conjunct2) RS conjunct1) 1;
auto();
by (asm_full_simp_tac Z2HOL_ss 1);
qed "rep_access_prefix";


(*
(* *)
zgoalw CVSServer.thy [theta_def] 
"p: (rep_access %^ (%theta Cvs_FileSystem) %^ (x)) /\\ Cvs_FileSystem \
				  \ /\\ x: Path /\\ p ~= x \
				  \ =+=> (front p):(rep_access %^ (%theta Cvs_FileSystem) %^ (x))";
by (stripS_tac 1);
be conjE 1;be conjE 1;be conjE 1;
by (stac rep_access_axdef2 1);

by (asm_full_simp_tac Z2HOL_ss 1);
ba 1;

by (asm_full_simp_tac (Z2HOL_ss addsimps [image_def]) 1);
br bexI 1;

*)


zgoalw CVSServer.thy [] 
"(files : FILESYS_TAB /\\ ( pf : ((%q. q) ``                 \
\                 {q. q : Path /\\                          \
\                     ( p prefix q /\\                      \
\                      ( cvs_rep %&^ q : dom files /\\ ?Y))})))  \
\ =+=>                                                      \
\ (cvs_rep %&^ pf) : dom files";
by(stripS_tac 1);
auto();
qed"complSetDomFiles";


(* files with rep_access are reachable in 'files' *)
(* weaker version                                 *)
zgoalw CVSServer.thy [] 
"Cvs_FileSystem /\\                                    \
\ (q : (rep_access %^ (%theta Cvs_FileSystem)  %^ p))  \
\ /\\ (p:Path)                                         \
\ =+=>                                                 \
\ cvs_rep %&^ q : dom files";
by(stripS_tac 1);
by(cut_facts_tac [rep_access_axdef] 1);
by(convert2hol_tac [] 1);
by(REPEAT (etac conjE 1));
by(eres_inst_tac [("x","(attributes, cvs_passwd, files,wcs_attributes)")] ballE 1);
by(eres_inst_tac [("x","p")] ballE 1);
auto();
qed"rep_accessPathInDomRepFiles";
