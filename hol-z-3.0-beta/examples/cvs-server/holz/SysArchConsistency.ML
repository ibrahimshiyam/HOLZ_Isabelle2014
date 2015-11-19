(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * SysArchConsistency.ML --- 
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
(* $Id: SysArchConsistency.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* Instructions for usage of this file:   *)
(* (also view README.txt)                 *)
(*                                        *)
(* - in the directory above, enter in the *)
(*   file zetarc.template the line        *)
(*   holz -u LTX:SysArchConsistency#arch  *)
(* - start isabelle holz                  *)
(* - enter use_holz"SysArchConsistency";  *)
(*                                        *)

(* the following imports are   *)
(* from SysArchSec. They shall *)
(* allow for more flexibility  *)
(* at migrating the proofs     *)
(* at version changes.         *)

(* use the pruningTactics   *)
use"pruningTactics";
open pruningTactics;
(* use extensions for HOL-Z *)
use"ext_Z_fun";
(* import Rules *)
use"simpleRules";
use"specificRules";

(* the actual Consistency theory *)

open SysArchConsistency;
toToplevel SysArchConsistency.axdefs;
toToplevel SysArchConsistency.schemes;

use"AbstractStateCons";
(* AbsOperationsCons contains the *)
(* deadlock-free proof for the    *)
(* operation abs_ci as it can be  *)
(* found in the file arch.pdf     *)
(* in Chapter 6.                  *)
use"AbsOperationsCons";
use"FileSystemCons";
use"CVSServerCons";

