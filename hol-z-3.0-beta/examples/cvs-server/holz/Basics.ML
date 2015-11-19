(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * Basics.ML --- 
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
(* $Id: Basics.ML 6746 2007-08-03 07:25:55Z brucker $ *)

open Basics;

toToplevel axdefs; 
toToplevel schemes;

(* thms_of thy;      -- checking the automatic setup of ax_defs. *)


goalw thy [AUTH_TAB_def] 
"!!f. f : AUTH_TAB ==> (dom f) <= (Cvs_Uid %x Cvs_Passwd)";
br Rel_Dom_subset 1;
br Pfun_Rel 1;
ba 1;
qed "AUTH_TAB_dom";


