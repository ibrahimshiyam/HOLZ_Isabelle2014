(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * has_access_impls.ML --- 
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
(* $Id: has_access_impls.ML 6746 2007-08-03 07:25:55Z brucker $ *)


goal thy "(rep_permtab, rep, abs_passwd, file, role) : has_access_ \
\ =+=> rep_permtab:ABS_PERMTAB =+=> rep:ABS_DATATAB \
\ =+=> abs_passwd :PASSWD_TAB  =+=> file:Abs_Name =+=> role:Cvs_Uid \
\ =+=> ((rep_permtab %^ file), \
\                         (authtab %^ rep %^ (role, (abs_passwd %^ role)))) \
\                        : cvs_perm_order";
by(stripS_tac 1);
by(cut_facts_tac [has_access__axdef] 1);
bd DECL_D2 1;
by( REPEAT ((dtac bspec 1)
		THEN
		(assume_tac 1)));
br conjunct2 1;
br subst 1;
ba 1;
ba 1;
qed"has_access_implies_inPermOrder";



goal thy "  \
\ (rep_permtab, rep, abs_passwd, file, role) : has_access_ \
\ =+=> rep_permtab:ABS_PERMTAB =+=> rep:ABS_DATATAB        \
\ =+=> abs_passwd :PASSWD_TAB  =+=> file:Abs_Name =+=>     \ 
\ (role) : Cvs_Uid                               \
\ =+=>                                                     \
\ ((role),                                       \
\ (abs_passwd %^ (role) ))                       \
\ : dom (authtab %^ rep)  ";
by(stripS_tac 1);
by(cut_facts_tac [has_access__axdef] 1);
bd DECL_D2 1;
by( REPEAT ((dtac bspec 1)
		THEN
		(assume_tac 1)));
br conjunct1 1;
br subst 1;
ba 1;
ba 1;
qed"has_access_implies_up_inDom_auth";

