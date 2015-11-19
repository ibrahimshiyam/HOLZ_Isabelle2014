(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * aInventsAx_impls.ML --- 
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
(* $Id: aInventsAx_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)

zgoal thy "Ainvents = MH %^ Ainvents_Base";
br ((Ainvents_axdef RS DECL_D2) RS conjunct2) 1; 
qed"Ainvents_MH";

zgoal thy "?Ainvents : %P (Abs_Name %x Abs_Data)";
by(stripS_tac 1);
br ((Ainvents_axdef RS DECL_D1) RS conjunct2 RS conjunct2) 1;
qed"type_Ainvents";

zgoal thy "?Ainvents_base : %P (Abs_Name %x Abs_Data)";
by(stripS_tac 1);
br ((Ainvents_axdef RS DECL_D1) RS conjunct2 RS conjunct1) 1;
qed"type_Ainvents_base";

