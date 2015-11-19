

goal LTL.thy  "sat t (Neg f)   = (~ sat t f)";
by (Auto_tac); 
qed "Neg";



goalw LTL.thy [Disj_def] "sat t (Disj f g)   = ((sat t f) | (sat t g))";
by (Auto_tac);
qed "DisjEq";


goalw LTL.thy [Disj_def,F_def] 
  "sat t (F (Disj f g))   = ((sat t  (F f)) | (sat t (F g)))";
  by (Auto_tac);
  qed "FDisj";

goalw LTL.thy [G_def,F_def] 
  "sat t (G (Conj f g))   = ((sat t  (G f)) & (sat t (G g)))";
  by (Auto_tac);
  qed "GConj";


goalw LTL.thy [G_def,F_def]
"!! k. sat t (G f) ==> sat t (F f)";
auto();
qed"GimpF";

Delsimps[suffix_add];

goal LTL.thy
"sat t (Until f g) = ((sat t g) | (sat t f) & \
\ (sat (suffix t 1) (Until f g)))";
br iffI 1;
by (Asm_full_simp_tac 1);
be exE 1;
by (case_tac "j=0" 1);
by (Asm_full_simp_tac 1);
br disjI2 1;
by (Step_tac 1);
by (SELECT_GOAL Auto_tac 1);
by (res_inst_tac [("x","j - 1")] exI 1);
Addsimps[suffix_add RS sym];
by (SELECT_GOAL Auto_tac 1);
by (subgoal_tac "Suc i < j" 1);
by (SELECT_GOAL Auto_tac 1);
bd Suc_mono 1; back();
auto();
by (res_inst_tac [("x","0")] exI 1);
by (SELECT_GOAL Auto_tac 1);
by (res_inst_tac [("x","Suc j")] exI 1);
by (SELECT_GOAL Auto_tac 1);
by (case_tac "i=0" 1);
by (SELECT_GOAL Auto_tac 1);
by (eres_inst_tac [("x","i - 1")] allE 1);
by (subgoal_tac "(i - 1) < j" 1);
by (SELECT_GOAL Auto_tac 1);
br (Suc_less_eq RS iffD1) 1;
by (Asm_full_simp_tac 1);
qed"Until_eq";

Delsimps[suffix_add RS sym];
Addsimps[suffix_add];

goal LTL.thy
"sat t (Until f g) = ((sat t g) | (sat t f) & \
\ (sat t (Next(Until f g))))";
br iffI 1;
bd (Until_eq RS iffD1) 1;
br (Until_eq RS iffD2) 2;
auto();
qed "Until_Next";

goalw LTL.thy [G_def,F_def] "sat t (G f)=(!i. sat (suffix t i) f)";
auto(); 
qed "G_eq";

goalw LTL.thy [G_def,F_def] "sat t (F f)=(? i. sat (suffix t i) f)";
auto(); 
qed "F_eq";

val [p1,p2] = goal LTL.thy 
"[| sat t f;  \
\   !! i. sat (suffix t i) f ==> sat (suffix t (Suc i)) f |] \
\   ==> sat t (G f) ";
Addsimps [p1];
br (G_eq RS iffD2) 1;
br allI 1;
by (induct_tac "i" 1);
br p2 2;
by (ALLGOALS Asm_simp_tac);
Delsimps [p1];
qed"G_induct";

val [p1,p2] = goal LTL.thy 
"[| sat t f;             \
\   !! i. sat (suffix t i) f ==> sat (suffix t i) (Next f) |] \
\   ==> sat t (G f) ";
Addsimps [p1,suffix_add RS sym];
br G_induct 1;
bd p2 2;
auto();
Delsimps [p1, suffix_add RS sym];
qed"G_induct_next";
