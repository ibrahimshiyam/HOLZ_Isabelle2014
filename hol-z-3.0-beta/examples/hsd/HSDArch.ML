(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * HSDArch.ML --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 2003-2007 ETH Zurich, Switzerland
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
(* $Id: HSDArch.ML 6743 2007-08-03 06:39:08Z brucker $ *)


(* cd "holz";
   use_holz "HSDArch";
 *)
(*
toToplevel HSDArch.axdefs;
toToplevel HSDArch.schemes;

Add_axdefs_TC (map snd HSDArch.axdefs);



(* Architectural decomposition theorem - If the combined system makes a step,
   then it must have one of the following 4 forms:
*)

zgoal HSDArch.thy
"System =+=>  ((%E DARMA @   AuthenticateUserW & AuthenticateUserL)   |  \
\              (%E DARMA @   GenerateSignatureW & NopOperationL)      |  \
\              (%E DARMA @   GenerateSignatureW & GenerateSignatureL) |  \
\              (%E DARMA @   LogoutW & LogoutL))";
by(stripS_tac 1);
by(full_expand_schema_tac System_def 1);
by(elim_sch_ex_tac 1);
be conjE 1;
by(full_expand_schema_tac ClientOperation_def 1);

(* Case-Distinction over Client Operations ... *)
be disjE 1;
be disjE 2;

(* Throw away superfluous disjoints in order to
   make proof state smaller ... *)
br disjI1 1;
br disjI2 2;
br disjI2 3;
br disjI2 3;
br disjI2 3;

(* Now we extract the commands the user sends ... *)
by(forward_tac [stripS (get_conj HSD.thy "AuthenticateUserW" 3)] 1);
by(forward_tac [stripS (get_conj HSD.thy "GenerateSignatureW" 3)] 2);
by(forward_tac [stripS (get_conj HSD.thy "LogoutW" 1)] 3);
(* for the case GenerateSignatureW, we make a case distinction over
   hash-Failure. *)
by(case_tac "message_63 : hashFailure_" 2);
by(rotate_tac ~1 2);
by(rotate_tac ~1 3);
by(ALLGOALS Asm_full_simp_tac);

(* Throw away superfluous disjoints in order to
   make proof state smaller ... *)
br disjI1 2;
br disjI2 3;
br disjI1 3;

(* Now, unfold the server and produce all cases ... *)
by(ALLGOALS (full_expand_schema_tac ServerOperation_def));
by(Safe_tac);
(* ... produces 16 cases. We extract the commands the
   Server may go and lead 12 cases to contradictions
   with what the Client wanted. *)
by(forward_tac [stripS (get_conj HSD.thy "GenerateSignatureL" 1)] 2);
by(forward_tac [stripS (get_conj HSD.thy "LogoutL" 1)] 3);
by(forward_tac [stripS (get_conj HSD.thy "NopOperationL" 1)] 4);

by(forward_tac [stripS (get_conj HSD.thy "AuthenticateUserL" 1)] 5);
by(forward_tac [stripS (get_conj HSD.thy "GenerateSignatureL" 1)] 6);
by(forward_tac [stripS (get_conj HSD.thy "LogoutL" 1)] 7);

by(forward_tac [stripS (get_conj HSD.thy "AuthenticateUserL" 1)] 9);
by(ALLGOALS Asm_full_simp_tac); (* Just exploit contradictions *)

by(forward_tac [stripS (get_conj HSD.thy "LogoutL" 1)] 4);
by(forward_tac [stripS (get_conj HSD.thy "NopOperationL" 1)] 5);
by(forward_tac [stripS (get_conj HSD.thy "AuthenticateUserL" 1)] 6);
by(forward_tac [stripS (get_conj HSD.thy "GenerateSignatureL" 1)] 7);
by(forward_tac [stripS (get_conj HSD.thy "NopOperationL" 1)] 9);
by(ALLGOALS Asm_full_simp_tac); (* Just exploit contradictions *)

(*
by(forward_tac [stripS (get_conj HSD.thy "NopOperationL" 1)] 4);
by(forward_tac [stripS (get_conj HSD.thy "NopOperationL" 1)] 6);
by(ALLGOALS Asm_full_simp_tac); (* Just exploit contradictions *)

does not work due to bug in get_conj (resp. expand_schema_tac.
which does simplification with prod_ss which already includes
set simplification - i.e. too much.

Workaround: use the results of the internal simplification ...

*)
by(forward_tac [stripS (get_conj HSD.thy "NopOperationL" 2)] 4);
by(forward_tac [stripS (get_conj HSD.thy "NopOperationL" 3)] 6);
by(ALLGOALS Asm_full_simp_tac); (* Just exploit contradictions *)

by(intro_sch_ex_tac 1);
br conjI 1; ba 1; ba 1;
by(ALLGOALS (fn x => TRY(rtac refl x)));
bd(stripS (get_decl HSD.thy "AuthenticateUserW" 4)) 1;
by (convert2hol_tac [] 1);

by(intro_sch_ex_tac 1);
br conjI 1; ba 1; ba 1;
by(ALLGOALS (fn x => TRY(rtac refl x)));
bd(stripS (get_decl HSD.thy "GenerateSignatureW" 4)) 1;
by (convert2hol_tac [] 1);

by(intro_sch_ex_tac 1);
br conjI 1; ba 1; ba 1;
by(ALLGOALS (fn x => TRY(rtac refl x)));
bd(stripS (get_decl HSD.thy "GenerateSignatureW" 4)) 1;
by (convert2hol_tac [] 1);

by(intro_sch_ex_tac 1);
br conjI 1; ba 1; ba 1;
by(ALLGOALS (fn x => TRY(rtac refl x)));
bd(stripS (get_decl HSD.thy "LogoutW" 3)) 1;
by (convert2hol_tac [] 1);
qed"SysArch_decomposition_theorem";

(* Although the proof technique is simple and straight-forward, the
   proof-states become quite large and very unpleasant to work with.
   Therefore, architectural re-wiring of this kind is better hidden
   inside this theorem ... *)



zgoal HSDArch.thy
"((%E DARMA @   AuthenticateUserW & AuthenticateUserL) |    \
\ (%E DARMA @   GenerateSignatureW & NopOperationL) |       \
\ (%E DARMA @   GenerateSignatureW & GenerateSignatureL) |  \
\ (%E DARMA @   LogoutW & LogoutL))  =+=>                   \
\ System";
by(stripS_tac 1);
by(full_expand_schema_tac System_def 1);
by(Safe_tac);

by(elim_sch_ex_tac 1);
be conjE 1;
by(intro_sch_ex_tac 1);
by(ALLGOALS (fn x => TRY(rtac refl x)));
bd(stripS (get_decl HSD.thy "AuthenticateUserW" 4)) 2;
by (convert2hol_tac [] 2);
by(full_expand_schema_tac ClientOperation_def 1);
by(full_expand_schema_tac ServerOperation_def 1);

by(elim_sch_ex_tac 1);
be conjE 1;
by(intro_sch_ex_tac 1);
by(ALLGOALS (fn x => TRY(rtac refl x)));
bd(stripS (get_decl HSD.thy "GenerateSignatureW" 4)) 2;
by (convert2hol_tac [] 2);
by(full_expand_schema_tac ClientOperation_def 1);
by(full_expand_schema_tac ServerOperation_def 1);

by(elim_sch_ex_tac 1);
be conjE 1;
by(intro_sch_ex_tac 1);
by(ALLGOALS (fn x => TRY(rtac refl x)));
bd(stripS (get_decl HSD.thy "GenerateSignatureW" 4)) 2;
by (convert2hol_tac [] 2);
by(full_expand_schema_tac ClientOperation_def 1);
by(full_expand_schema_tac ServerOperation_def 1);

by(elim_sch_ex_tac 1);
be conjE 1;
by(intro_sch_ex_tac 1);
by(ALLGOALS (fn x => TRY(rtac refl x)));
bd(stripS (get_decl HSD.thy "LogoutW" 3)) 2;
by (convert2hol_tac [] 2);
by(full_expand_schema_tac ClientOperation_def 1);
by(full_expand_schema_tac ServerOperation_def 1);
qed"SysArch_introduction_theorem";




*)
