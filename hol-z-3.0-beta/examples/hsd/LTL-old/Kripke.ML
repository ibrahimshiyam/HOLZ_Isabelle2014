
 
Goalw [Reach_def, reachable_from_def]
"!! K. q : Reach K ==> ? q0:init K. K |- q0 -*> q";
auto();
qed "ReachD";

val _ = bind_thm ("ReachE", ReachD RS bexE);

Goalw [Reach_def, reachable_from_def]
"!! K. [| q0:init K; K |- q0 -*> q |] ==> q : Reach K ";
auto();
qed "ReachI";

Goal
"(t:(traces k) & ((t j)=q') ) --> (k |- (t 0)-*> q' )";
bw reachable_from_def;
bw traces_def;
bw is_trace_def;
auto();
by (induct_tac "j" 1);
br rtrancl_refl 1;
br rtrancl_into_rtrancl 1;
ba 1;
bd allE 1;
auto();
qed "state_in_trace_imp_reachable_state";

goalw Kripke.thy [suffix_def]
"(suffix t i) j = t(i + j)";
br refl 1;
qed"suffix";

Addsimps[suffix];

goal Kripke.thy "suffix t 0 = t";
br ext 1;
auto();
qed"suffix0";


Addsimps add_ac;
goal Kripke.thy "suffix t (i+j) = suffix (suffix t i) j";
by (induct_tac "j" 1);
br ext 2;
auto();
qed"suffix_add";
Delsimps add_ac;

Addsimps[suffix0, suffix_add];



(* ********************************************************************* *)
goalw  Main.thy []
"(R O (R^n)) = ((R^n) O R)";
by(induct_tac "n" 1);
by(ALLGOALS(simp_tac (simpset() addsimps [O_assoc])));
by(Asm_simp_tac 1);
qed"O_power_shift";
                                                                                
                                                                                
goalw  Main.thy []
"(ALL n. P n) = (ALL n. P n & P(Suc n))";
auto();
qed"nat_split_lemma";
             


goalw Kripke.thy [is_trace_def]
"is_trace K t = (t(0) : (init K) & (ALL k n. t(n+k) : ((next K)^n) ``{t k}))";
auto();
by(eres_inst_tac [("x","i")] allE 2);
by(eres_inst_tac [("x","1")] allE 2);
auto();
by(induct_tac "n" 1);
auto();
qed"is_trace_charn";
