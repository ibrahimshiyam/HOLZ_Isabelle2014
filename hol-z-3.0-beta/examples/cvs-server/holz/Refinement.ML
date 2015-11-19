(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * Refinement.ML --- 
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
(* $Id: Refinement.ML 6746 2007-08-03 07:25:55Z brucker $ *)

open Refinement;

toToplevel axdefs;
toToplevel schemes;

(* complete file

(**********************************************************************
 *  login
 **********************************************************************)

(* login 1 *)
zgoalw thy [login_1_def] "login_1";
by (stripS_tac 1);
(* PreLogin is yet to be shown!! *)
br PreLogin_axdef2 1;
by(ALLGOALS (asm_simp_tac (simpset() addsimps [asSet_def])));
by(expand_schema_tac pre_of_cvs_login_def 1);
br DECL_I 1;
by (Asm_simp_tac 1);
br (stripS (get_decl FileSystem.thy "FileSystem" 1)) 1;
br (stripS (get_decl CVSServer.thy "Cvs_FileSystem" 1)) 1;
by (asm_simp_tac Z2HOL_ss 1);
by (Step_tac 1);
by (elim_pre_tac 1);
by (forward_tac [stripS (get_conj thy "R" 4)] 1);
by (forward_tac [stripS (get_conj AbsOperations.thy "abs_login" 1)] 1);
by (forward_tac [stripS (get_conj Refinement.thy "Asm_login" 1)] 1);
by (forward_tac [stripS (get_conj Refinement.thy "Asm_login" 2)] 1);
auto();
qed "login_1";


(* *******

Ein paar Ideen für neue Taktiken:
- canonize_mvars : 
    normalizes P_1(?mvar) /\ ... /\ ?mvar = t /\ ... /\ P_n(?mvar)
    to         P_1(t) /\ ... /\ P_n(t)
  Specialty:   critical equations ?mvar = t may occur not only
               in conjunctions, but in arbitrary contexts 
               described by a list of operators 

  too complicated.  Instead: What about:


fun find_eq t = 
    let fun fi(Const("op =",_) $ s $ t) n = if is_Var(head_of s) orelse
                                               is_Var(head_of t)
                                            then [Bound n] else []
           |fi(s $ t) n  = map (fn x => x $ t)(fi s n) @
                           map (fn x => s $ x)(fi t n)
           |fi(Abs(s,t,e)) n = map (fn x => Abs(s,t,x)) 
                                   (fi e (n+1))
           |fi _ _ = []
    in  map (fn x => Abs("",boolT,x))(fi (dest_Trueprop t) 0) end;

fun refl_tac n  = 
    let val trule     = (prover "(x = x) = True") RS ssubst
        val t         = Logic.strip_assums_concl(getgoal n)
        val pS        = map (fn(x,y)=>Var((x,1),y))
                            (Logic.strip_params(getgoal n))
        val t'        = subst_bounds (rev pS,t)
        val Ps        = rev(find_eq(t'))
(* val a::R = Ps; print_cterm(cterm_of sg a) *)
        val sg        = #sign(rep_thm(topthm()))
        val P         = cterm_of sg (Var(("P",0),boolT --> boolT))
        fun doit[]    = no_tac
           |doit(a::R)= ((rtac (cterm_instantiate [(P,cterm_of sg a)] trule) n)
                         THEN  (simp_tac HOL_ss n))
                        ORELSE (doit R)
    in  doit Ps
    end;


fun apply_refl_tac n  = REPEAT(refl_tac n)


Das funktioniert bloss nicht, weil die Regel ja triviale
Unifier haben kann. Der erstbeste unifier wuerde die Taktik allerbings
unakzeptabel unvollständig machen. Folglich muessen alle Kandidaten
fuer Unifier berechnet und durchprobiert werden.

Was anderes: Es könnte strategisch Sinn machen, erst mal
alle impliziten Gleichheiten in den Hypothesen explizit zu machen.
Das kann erforderlich machen:
- Thetas verfolgen
- pre S mit eq's in den Konjunkten des Rumpfs.

Noch was anderes: auto hat den doofen Dreckeffekt das
SNAME eliminiert wird - zumindest in conclusions.
Das ist n Uraltproblem. Tendentiell sollten wir ja

*)


(* login_2 *)

zgoalw thy [login_2_def] "login_2";
(* general massage; including expansion of all pre'd 
   schemas in the premises; 
   and a theta-equality-expansion done by hand;
   additionally, abs_login and Asm_login_def are expanded;
   (also in the conclusion to show). *)
by (stripS_tac 1);
by (Step_tac 1);
by (elim_pre_tac 1);
by (full_expand_schema_tac abs_login_def 1); (*method specific *)
by (full_expand_schema_tac Asm_login_def 1); (*method specific *)
(* poor man's theta-equality-expansion *)
by (forward_tac [stripS(get_decl thy "cvs_login" 2)] 1);
by (forward_tac [stripS(get_conj thy "cvs_login" 3)] 1);
by (forward_tac [stripS(get_conj thy "cvs_login" 4) RS sym] 1);
by (forward_tac [stripS(get_conj thy "R" 1)] 1);
(* smash eq-related stuff *)
by (asm_full_simp_tac (HOL_ss addsimps [DELTA_def, XI_def, theta_def]) 1);
auto();

(* openening of the schema existentials. 
   Following steps keep the proof state small ... *)
by (intro_sch_ex_tac 1);
by (intro_sch_ex_tac 1);
(* "refl away" by hand ... *)
   br conjI 1;
   br DECL_I 2;
   by (REPEAT((rtac conjI 3) THEN (defer_tac 3)));
   by (ALLGOALS (fn n => TRY(rtac refl n)));
   auto();
   
(* automatic variant of "refl-away" - not working
   (* by (refl_tac 1); *)
   by (apply_refl_tac 1);
   auto();
 *)
by(full_expand_schema_tac ClientState_def 2);
auto();

(* we now turn to R... *)
by(full_expand_schema_tac R_def 1);
be DECL_E 1;
(*eliminate cvs_passwd'*)
by (forward_tac [stripS(get_conj thy "cvs_login" 2)] 1);
by (hyp_subst_tac 1);
by (Asm_full_simp_tac 1);
by (asm_simp_tac Z2HOL_ss 1);
qed "login_2";



(**********************************************************************
 *  cvs add
 **********************************************************************)

(* add 1 *)

zgoalw thy [add_1_def] "add_1";
(* General Massage *)
by (stripS_tac 1);
by (Step_tac 1);
by (elim_pre_tac 1);
by (full_expand_schema_tac abs_add_def 1);
by (full_expand_schema_tac Asm_add_def 1);
by (asm_full_simp_tac (HOL_ss addsimps [DELTA_def, XI_def, theta_def]) 1);
auto();

(* opening *)
by (intro_pre_tac [cvs_add_def] 1);
by (expand_schema_tac cvs_add_error_def 1);

(* case distinction: normal vs. exceptional behaviour *)
by(cut_facts_tac [excluded_middle] 1);
be disjE 1;
br disjI1 1;
br disjI2 2;

(* we attack exceptional behaviour first ... *)
br DECL_I 2; 
ba 3; (* here we propagate the exceptional behaviour into the
         positive clause of the excluded middle :
         we proove that the case distinction is indeed complete ... *)
by (asm_simp_tac (HOL_ss addsimps [DELTA_def, XI_def, theta_def]) 2);

(* "de-refln" by hand ... *)
   by (REPEAT((rtac conjI 2) THEN (defer_tac 2)));
   by (ALLGOALS (fn n => TRY(rtac refl n)));
by (asm_simp_tac (HOL_ss addsimps [SNAME_def]) 2);
by (asm_simp_tac (HOL_ss addsimps [SNAME_def]) 2);
by (asm_simp_tac (HOL_ss addsimps [SNAME_def]) 2);
by (asm_simp_tac (HOL_ss addsimps [SNAME_def]) 2);


(* now we turn to normal behaviour ... *)
by (expand_schema_tac cvs_add_normal_def 1);
by(Asm_full_simp_tac 1);

br DECL_I 1;
by (Fast_tac 2);
by (asm_full_simp_tac (HOL_ss addsimps 
                       [SNAME_def,DELTA_def, XI_def, theta_def]) 1);
qed "add_1";


(* add_2 *)

zgoalw thy [add_2_def] "add_2";
(* general massage; including expansion of all pre'd 
 * schemas in the premises; 
 * and a theta-equality-expansion done by hand;
 * additionally, abs_login and Asm_login_def are expanded;
 * (also in the conclusion to show). *)
   by (stripS_tac 1);
   by (Step_tac 1);
   by (elim_pre_tac 1);
   by (full_expand_schema_tac abs_add_def 1); (*method specific *)
   by (full_expand_schema_tac Asm_add_def 1); (*method specific *)
   by (full_expand_schema_tac cvs_add_def 1); 
(* case distinction: normal behaviour vs. exceptional beaviour *)
   be disjE 1;

(* poor man's theta-equality-expansion (for both cases) *)
   by (forward_tac [stripS(get_decl thy "cvs_add_normal" 2)] 1);
   by (forward_tac [stripS(get_conj thy "cvs_add_normal" 7)] 1);
   by (forward_tac [stripS(get_conj thy "cvs_add_normal" 8)] 1);
   by (forward_tac [stripS(get_conj thy "R" 1)] 1);

   by (forward_tac [stripS(get_decl thy "cvs_add_error" 1)] 2);
   by (forward_tac [stripS(get_decl thy "cvs_add_error" 2)] 2);
   (* smash eq-related stuff *)
   by (ALLGOALS(asm_full_simp_tac (HOL_ss addsimps 
                                   [DELTA_def, XI_def, theta_def])));
   auto();


(* First, we attack the case od exceptional behaviour *)
   (* openening of the schema existentials. 
      Following steps keep the proof state small ... *)
   by (intro_sch_ex_tac 2);
   by (intro_sch_ex_tac 2);
   (* "weg-refln" by hand ... *)
   br conjI 2;
   br DECL_I 3;
   by (REPEAT((rtac conjI 4) THEN (defer_tac 4)));
   by (ALLGOALS (fn n => TRY(rtac refl n)));
   auto();
   by(full_expand_schema_tac ClientState_def 3);
   auto();

   (* now we attack R in this case ... *)
   by(full_expand_schema_tac R_def 2);
   be DECL_E 2;
   by (Asm_simp_tac 2);
   br DECL_I 2;
   by (Asm_simp_tac 2);
   by (Asm_full_simp_tac 2);
   by (REPEAT (etac thin_rl 2)); (* ... *)
(*
(*eliminate attributes'*)
by (forward_tac [stripS(get_conj thy "cvs_add" 2)] 1);
by (hyp_subst_tac 1);
by (Asm_full_simp_tac 1);
by (asm_simp_tac Z2HOL_ss 1);
*)

(* Then, we attack the case of normal behaviour *)
   (* openening of the schema existentials. 
      Following steps keep the proof state small ... *)
   by (intro_sch_ex_tac 1);
   by (intro_sch_ex_tac 1);
   (* "weg-refln" by hand ... *)
   br conjI 1;
   br DECL_I 2;
   by (REPEAT((rtac conjI 3) THEN (defer_tac 3)));
   by (ALLGOALS (fn n => TRY(rtac refl n)));
   auto();
   by(asm_full_simp_tac (Z2HOL_ss) 2);
   (* now we attack R in this case ... *)
   by(full_expand_schema_tac R_def 1);
   be DECL_E 1;
   
(*
qed "add_2";
 *)




(**********************************************************************
 *  update
 **********************************************************************)

(* temp. hack ... *)
goal thy "(p : dom (A (+) (A (+) B))) = (p: dom (A (+) B))";
auto();
qed "override_left_idem";
Addsimps [override_left_idem];


(* update 1 *)

zgoalw thy [update_1_def] "update_1";
by (stripS_tac 1);

by(case_tac "(uid,  wdir %&^ p?, attributes) : has_w_access_" 1);

by (intro_pre_tac [cvs_update_def] 2);
br disjI2 2;
br disjI2 2;
by (full_expand_schema_tac cvsUpErr_def 2);

by (Step_tac 2);

by (asm_simp_tac Z2HOL_ss 2);
by (Step_tac 2);
by (ALLGOALS Asm_simp_tac);

by (asm_simp_tac Z2HOL_ss 2);
by (Step_tac 2);
by (ALLGOALS Asm_simp_tac);

(* now next case *)
by(case_tac "cvs_rep %&^ repOf %^ (wcs_attributes %^ wdir) %&^ p? : dom files" 1);
by (intro_pre_tac [cvs_update_def] 2);
br disjI1 2;
by (full_expand_schema_tac cvsUpNoAct_def 2);
by (Step_tac 2);

by (asm_simp_tac Z2HOL_ss 2);
by (Step_tac 2);
by (ALLGOALS Asm_simp_tac);

by (asm_simp_tac Z2HOL_ss 2);
by (Step_tac 2);
by (ALLGOALS Asm_simp_tac);

(* third case *)
by (elim_pre_tac 1);
by(forward_tac [stripS (get_decl thy "abs_up" 2)] 1);
by(forward_tac [stripS (get_conj thy "abs_up" 3)] 1);
by(forward_tac [stripS (get_conj thy "abs_up" 4)] 1);
by (asm_full_simp_tac (HOL_ss addsimps [DELTA_def,XI_def,theta_def]) 1);
auto();

by (intro_pre_tac [cvs_update_def] 1);
br disjI2 1;
br disjI1 1;
by (expand_schema_tac cvsUp_def 1);


br DECL_I 1;
by (asm_full_simp_tac (HOL_ss addsimps [DELTA_def,XI_def,theta_def]) 1);

by (asm_simp_tac Z2HOL_ss 2);

by (REPEAT ((resolve_tac [conjI] 2) THEN (defer_tac 2)));

by (ALLGOALS (fn n => TRY (rtac refl n)));

auto();

by (asm_simp_tac Z2HOL_ss 1);
by (asm_simp_tac Z2HOL_ss 2);
by (asm_simp_tac Z2HOL_ss 2);

by (expand_schema_tac Cvs_FileSystem_def 1);
by (Asm_simp_tac 1);
br DECL_I 1;
br conjI 1;
br conjI 2;

by(rtac (stripS (get_decl thy "Cvs_FileSystem" 3)) 3);
by (asm_simp_tac Z2HOL_ss 3);

by (REPEAT ((resolve_tac [conjI] 3) THEN (defer_tac 3)));

by (expand_schema_tac FileSystem_def 1);

by (ALLGOALS (asm_full_simp_tac (HOL_ss addsimps [image_def])));
br DECL_I 1;
by (defer_tac 1);
br conjI 1;


br ballI 1;
by(case_tac "p = %<%>" 1);

(* first case: p=<> *)
br disjI1 1;
ba 1;

(* second case: p~=<> *)
br disjI2 1;

br (isdirin_def RS iffD2) 1;
by (fold_goals_tac [Path_def,FILESYS_TAB_def]);
by (Asm_simp_tac 1);

br (stripS front_p_is_path) 1;
br conjI 1;
br (stripS path_in_files_override) 1;
br conjI 1;
br conjI 1;

by (rtac(stripS(get_decl thy "Cvs_FileSystem" 1)) 1);
by (asm_full_simp_tac Z2HOL_ss 1);

be conjE 1;
by (asm_full_simp_tac Z2HOL_ss 1);

by (simp_tac (HOL_ss addsimps [override_left_idem]) 1);

ba 1;

br conjI 1;
br (isin_def RS iffD2) 1;
be conjE 1;
by (fold_goals_tac [FILESYS_TAB_def]);
ba 1;

br (stripS front_p_is_path) 1;
be conjE 1;
by (rewrite_goals_tac [FILESYS_TAB_def]);
by (Asm_simp_tac 1);
br dom_pfun 1;
by (asm_full_simp_tac Z2HOL_ss 1);

by (asm_full_simp_tac Z2HOL_ss 1);




by (asm_full_simp_tac (HOL_ss addsimps [Overrid_Domain]) 1);
by (case_tac "p: dom files" 1);
by (HINT "front p: dom files" (K all_tac) 1);
by (Fast_tac 1);

by (defer_tac 1);

by (case_tac "front p: dom files" 1);

by (Fast_tac 1);

by (rotate_tac ~2 1);
by (asm_full_simp_tac (simpset() addsimps [maplet_def]) 1);
be bexE 1;

*)

