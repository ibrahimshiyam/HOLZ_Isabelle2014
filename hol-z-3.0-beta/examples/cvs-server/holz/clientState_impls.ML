(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * clientState_impls.ML ---
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
(* $Id: clientState_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)

(* implications of the schema ClientState  *)

zgoal thy "ClientState =+=> wc : ABS_DATATAB";
by(stripS_tac 1);
by(convert2hol_tac [ClientState_def] 1);
qed"type_wc";

zgoal thy "ClientState =+=> wc_uidtab : ABS_UIDTAB";
by(stripS_tac 1);
by(convert2hol_tac [ClientState_def] 1);
qed"type_wcUidtab";

zgoal thy "ClientState =+=> abs_passwd : PASSWD_TAB";
by(stripS_tac 1);
by(convert2hol_tac [ClientState_def] 1);
qed"type_absPwd";

zgoal thy "ClientState =+=> abs_passwd : Cvs_Uid <--> Cvs_Passwd";
by(stripS_tac 1);
by(fold_goals_tac [PASSWD_TAB_def]);
zbr type_absPwd 1;
ba 1;
qed"type_absPwd_unfold";

zgoal thy "ClientState =+=> wc_uidtab : Abs_Name -|-> Cvs_Uid";
by(stripS_tac 1);
by(fold_goals_tac [ABS_UIDTAB_def]);
zbr type_wcUidtab 1;
ba 1;
qed"type_wcUidtab_unfold";
