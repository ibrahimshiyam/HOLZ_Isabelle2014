(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * abs_ci_repPtab_inv.ML ---
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
(* $Id: abs_ci_repPtab_inv.ML 6746 2007-08-03 07:25:55Z brucker $ *)


(* These lemmata allow to conclude: *)
(*                                  *)
(* f:dom rep, abs_ci implies that   *)
(* rep_permtab stays invariant.     *)



zgoal SysArchSec.thy"    \
\ f : dom rep            \
\  =+=>                  \
\ ~(f : dom ((%n.                   \
\  n |-->                           \
\    authtab %^ rep %^ (wc_uidtab %^ n, abs_passwd %^ (wc_uidtab %^ n))) ``   \
\                                    {n. n : wfiles /\\   \
\  (n : files_63 /\\                \
\   (n ~: dom rep /\\               \
\    (n : dom wc_uidtab /\\         \
\     (wc_uidtab %^ n, abs_passwd %^ (wc_uidtab %^ n))    \
\     : dom (authtab %^ rep))))})) \
\  ";
by(stripS_tac 1);
by(convert2hol_tac [maplet_def] 1);
auto();
qed"f_notin_repPtab_new";



zgoal SysArchSec.thy"    \
\ f : dom rep            \
\  =+=>                  \
\  (rep_permtab' =       \
\                    rep_permtab (+) (%n.   \
\  n |-->                           \
\    authtab %^ rep %^ (wc_uidtab %^ n, abs_passwd %^ (wc_uidtab %^ n))) ``   \
\                                    {n. n : wfiles /\\   \
\  (n : files_63 /\\                \
\   (n ~: dom rep /\\               \
\    (n : dom wc_uidtab /\\         \
\     (wc_uidtab %^ n, abs_passwd %^ (wc_uidtab %^ n))    \
\     : dom (authtab %^ rep))))})   \
\ =+=>                              \
\ rep_permtab %^ f = rep_permtab' %^ f";
by(stripS_tac 1);
by(res_inst_tac [("t", "rep_permtab'")] subst 1);
br sym 1;
ba 1;
br sym 1;
zbr applOpl 1;
zbr f_notin_repPtab_new 1;
ba 1;
qed"rep_ptab_invariant";




zgoal SysArchSec.thy "   \
\  f : dom rep           \
\ =+=>                   \
\ abs_ci                 \
\ =+=>                   \
\ rep_permtab %^ f =     \
\ rep_permtab' %^ f      \
\ ";
by(stripS_tac 1);
by(full_expand_schema_tac abs_ci_def 1) ;
bd DECL_D2 1;
by(atomizePrem 1);
by(filterPrems_keep_or ["f : dom rep", "rep_permtab (+)"] 1);

zbr rep_ptab_invariant 1;
ba 1;
by(convert2hol_tac [] 1);
qed"abs_ci_repPtab_invariant";

