(*******************************************************************************

  module: TransitionSystems.thy
  
  Transition systems and their runs 

  ID:     $Id: TransitionSystems.thy 12195 2004-10-25 20:20:36Z csprenge $
  author: Christoph Sprenger

*******************************************************************************)


header {* Transition Systems *}

theory TransitionSystems = Main :

subsection {* Definition *}

record 's trsys =
  init :: "'s set"
  trans :: "('s * 's) set"


subsection {* Runs of a transition system *} 

types 's run = "nat => 's"

constdefs 
  is_run :: "'s trsys => 's run => bool"
  "is_run T r == (r 0) : (init T) & (ALL i. ((r i), (r (Suc i))): trans T)"

  runs :: "'s trsys => 's run set"
  "runs T == { r. is_run T r }"

lemmas run_defs = runs_def is_run_def


lemma run_reflection: "EX T. r: runs T"
apply (rule_tac 
         x="(| init = {r 0}, trans = {(r i, r (Suc i)) | i. True} |)" 
       in exI)
apply (auto simp add: run_defs)
done


end
