(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_readProp_impls.ML --- 
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
(* $Id: abs_readProp_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)

val instantiateARead_def 
  = 
  (AReadProp__axdef 
       RS 
       DECL_D2 
       RS 
       bspec 
       RS 
       bspec 
       RS 
       bspec);


zgoal SysArchSec.thy "         \
\ (wc, rep, rep_permtab) : AReadProp_ \
\ =+=>                         \
\ wc:ABS_DATATAB  =+=>         \
\ rep:ABS_DATATAB =+=>         \
\ rep_permtab:ABS_PERMTAB =+=> \
\ (! n:dom wc.                                           \
\                     (n, wc %^ n) : Ainvents \\/        \
\                     ((? m:Aknows.                      \
\                          ((rep_permtab %^ n), (authtab %^ rep %^ m))  \
\                          : cvs_perm_order)))";
by(stripS_tac 1);
br mp 1;
by(guidedAssumption [": AReadProp"] 2);
by(res_inst_tac [("t", 
		  "(wc, rep, rep_permtab) : AReadProp_")] 
		subst 1);
br sym 1;
br instantiateARead_def 1;
by(Asm_simp_tac 4);
by(AtomizePremSolveAll);
qed"revExchange_AReadProp";




zgoal SysArchSec.thy "         \
\ wc:ABS_DATATAB  =+=>         \
\ rep:ABS_DATATAB =+=>         \
\ rep_permtab:ABS_PERMTAB =+=> \
\ (! n:dom wc.                                           \
\                     (n, wc %^ n) : Ainvents \\/        \
\                     ((? m:Aknows.                      \
\                          ((rep_permtab %^ n), (authtab %^ rep %^ m))  \
\                          : cvs_perm_order))) \
\ =+=>                                         \           
\ (wc, rep, rep_permtab) : AReadProp_ ";
by(stripS_tac 1);
by(res_inst_tac [("t", 
		  "(wc, rep, rep_permtab) : AReadProp_")] 
		subst 1);
br sym 1;
br instantiateARead_def 1;
by(AtomizePremSolveAll);
qed"replace_AReadProp";



zgoal SysArchSec.thy "InitAbsState =+=> \
\ (wc, rep, rep_permtab) : AReadProp_";
by(stripS_tac 1);
zbr replace_AReadProp 1;
zbd (InitAbsState_implies_AbsState
     ZRS
     AbsState_implies_ClientState
     ZRS
     type_wc) 1;
ba 1;
zbd (InitAbsState_implies_AbsState
     ZRS
     AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_rep) 1;
ba 1;
zbd (InitAbsState_implies_AbsState
     ZRS
     AbsState_implies_RepositoryState
     ZRS
     RepState_implies_type_repPtb) 1;
ba 1;
by(full_expand_schema_tac InitAbsState_def 1);
be conjE 1;
bd DECL_D2 1;
by(atomizePrem 1);
br empty_implies_Ball 1;
ba 1;
qed"InitAbsState_implies_AReadProp";


