(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * ROOT.ML  --- Root file to load Z in Isabelle/HOL            
 * This file is part of HOL-Z.
 *
 * Copyright (c) 2000-2002 University Freiburg, Germany
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
(* $Id: ROOT.ML 6729 2007-08-03 05:25:17Z brucker $ *)

path_add "./lib"; 

use_thy "Z";


(* *********************************************************************** *)
(* Finish setup                                                            *)
(* *********************************************************************** *)

show_full_sem:=false;       (* pretty - printing off *)


(* *********************************************************************** *)
(* Check HOL-Z in documentation generation mode                            *)
(* *********************************************************************** *)
(*
if !make_html=true then (use_dir "examples")
else ();
*)

(*********************************************************************)
(* misc                                                              *)
(*********************************************************************)
ProofGeneral.write_keywords "HOL-Z";
print_depth 10;

