(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * SysArchSec.ML --- 
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
(* $Id: SysArchSec.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* Instructions for usage of this file:   *)
(* (also view README.txt)                 *)
(*                                        *)
(* - in the directory above, enter in the *)
(*   file zetarc.template the line        *)
(*   holz -u LTX:SysArchSec#arch          *)
(* - start isabelle holz                  *)
(* - enter use_holz"SysArchSec";          *)
(*                                        *)


open SysArchSec;

toToplevel axdefs;
toToplevel schemes;
(*use_holz "SysArchSec";*)


(* This file provides an environment for   *)
(* theorem proving for security properties *)
(* of the cvs server case study.           *)


(* use the pruningTactics   *)
use"pruningTactics";
open pruningTactics;
(* use extensions for HOL-Z *)
use"ext_Z_fun";

(* import the lemmata      *)
(* avoiding conflicts from *)
(* dependencies.           *)

(* import Rules *)
use"simpleRules";
use"specificRules";
(* import implications of  *)
(* operations and schemata *)
use"SimpleAbsOpsImpls";
use"BasicAbsServiceStateImpls";
(* implications from axdef-environments *)
use"cvs_adminAx_impls";
use"has_access_impls";
use"abs_authAx_impls";
use"secAx_impls";
use"aInventsAx_impls.ML";
use"mergeHull_impls";
(* state/operation - implications *)
use"repState_impls";
use"clientState_impls";
use"abs_add_impls";
use"abs_login_impls";
use"abs_up_impls";
use"abs_ci_repPtab_inv";
use"abs_ci_impls";
use"abs_init_impls";
use"modify_impls";
use"abs_readProp_impls";
use"AService_impls";
(* more complicated lemmata *)
use"LoginAknows";
use"abs_Passwd_dom";
use"abs_Passwd_add";
use"abs_Passwd_up";
use"abs_Passwd_zrtrancl";
use"permAdmin_abs_ci_impls";
use"initial_permAdmin";
use"abs_repModify_lemmata";
use"abs_writeSec";(* <-- Proof of AWriteSec from arch.pdf *)
use"wc_Ainvents";
use"owner_Or_invented";
use"domUtb_implies_domWc";
use"owner_inRep_Lemmas";
use"owner_inRep_implies_perm";
use"abs_read_lemmata";
use"abs_read_ci_lemmata";
use"abs_read_up_lemmata";
use"abs_readSec";  (* <-- Proof of AReadSec from arch.pdf   *)


