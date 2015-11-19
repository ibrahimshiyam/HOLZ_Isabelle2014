(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_init_impls.ML --- 
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
(* $Id: abs_init_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)


(* specific implications of InitAbsState *)


zgoal thy "((%theta AbsState):  InitAbsState) =+=> \
\  x : abs_passwd =+=> x : Aknows";
by(stripS_tac 1);
by(convert2hol_tac [InitAbsState_def] 1);
qed"InitAbs_implies_Aknows";


zgoal SysArchSec.thy "InitAbsState =+=> abs_passwd ~= {}";
by(stripS_tac 1);
by(convert2hol_tac [InitAbsState_def] 1);
qed"InitAbsState_implies_nemptyAbsPwd";

zgoal SysArchSec.thy "InitAbsState =+=> wc = {}";
by(stripS_tac 1);
by(convert2hol_tac [InitAbsState_def] 1);
qed"InitAbsState_implies_wc_empty";

zgoal SysArchSec.thy "InitAbsState =+=> wc_uidtab = {}";
by(stripS_tac 1);
by(convert2hol_tac [InitAbsState_def] 1);
qed"InitAbsState_implies_wcUtb_empty";

zgoal SysArchSec.thy "InitAbsState =+=> \
\ (! x:Aknows. authtab %^ rep %^ x ~= cvs_admin)";
by(stripS_tac 1);
by(convert2hol_tac [InitAbsState_def] 1);
qed"InitAbsState_implies_noPermAdmin";
