(*****************************************************************************
 * HOL-Z --- a shallow embedding of Z into Isabelle/HOL
 *             http://projects.brucker.ch/hol-z/
 *                                                                            
 * BBSpec.thy --- 
 * This file is part of HOL-Z.
 *
 * Copyright (c) 2000-2003 University Freiburg, Germany
 *               2003-2007 ETH Zurich, Switzerland
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
(* $Id: BBSpec.thy 8132 2008-06-16 12:25:34Z wolff $ *)

header{* Import, Inspection, and Basic Analysis of the Specification *}

theory  BBSpec
imports Z

begin

section{* Loading a ZETA-unit and the Consequences *}
text{* The following HOL-Z toplevel commands allows for
       loadong directly the output of the ZETA format,
       in this case, we load the previous specification \verb+BBSpec+
       presented in the previous section.*}        
(* switch on xsymbols *)
ML{* print_mode:= !print_mode @ ["xsymbols"]; *}

load_holz "BBSpec"

(* For internal debugging purposes only:
ML{*
print_depth 200;
ZEncoder.PARSES;
ZEnv.schemas_of(ZTheory.get_zenv(the_context()));
*}
*)

thm AddBirthday_def

text{* This leads to a new state of the proof environment where
       all sorts of elements of the specification were bound
       to ISAR names and can therefore be referenced in future 
       proofs. *}

text{* A guided tour through the generated definitions 
  looks as follows: For abstract types, constants
  destribing the type sets exist: *}
thm NAME_def

text{* Data types result in a number of simplification rules *}
thm BBSpec.REPORT.simps

text{* Schema (both states and operation schemas) were converted
       to constant definitions denoting the "set of records", i.e.
       their value *}
thm BirthdayBook_def

thm Remind_def 
    InitBirthdayBook_def 
    AddBirthday_def 
    RAddBirthday_def


text{* Schemas, axiomatic definitions and conjectures were collected into 
       the variables: *}
thm SCHEMAS
thm AXDEFS
thm CONJECTURES

section{* Analysis I: Proving Conjectures *}

text{* Example: *}

lemma conjecture_0_proof : "conjecture_0"
by(unfold conjecture_0_def,zstrip,
   zunfold BirthdayBook_def BirthdayBook1_def, auto simp: Z2HOL)

text{* Of course, the conjecture can also be stated in the analysis
       document (the .thy-file) directly. *}

zlemma PO_refine_1_AddBirthday_simple :
" \<Sforall> BirthdayBook \<spot> (\<Sforall> BirthdayBook1 \<spot>                                  
    (\<forall> name? \<in> NAME. \<forall> date? \<in> DATE.         
      ((name? \<notin> known \<and> known = {n. \<exists> i \<in> 1..hwm. n = names\<rappll>i\<rapplr>})          
      \<longrightarrow>                                          
      (\<forall>i \<in> 1..hwm. name? \<noteq> names\<rappll>i\<rapplr>))          
 ))"
by(zstrip,auto)


text{* Note that the input of the formula must be done with the zlemma
       command since this supports HOL-Z syntax (and not just HOL syntax).*}

section{* Analysis II: Checking Consistency *}


text{* Now we turn to the statement of analysis judgements
       and refinement judgements. Both lead to the generation
       of proof obligations. *}

text{* The refinement package provides a number of generic
       toplevel commands for these analysis judgements and,
       moreover, methods to inspect and discharge proof obligations.

         Such method-specific support helps a lot to improve
       critical review of specifications ("is this really what
       you want to specifiy?"), as well as a basis for specific
       tactics. *}

text{* Generic inspection commands are: *}

list_po
check_po

text{* \ldots which provide functionality for listing pending
       proof obligations and also checks that they have been
       discharged. At the moment, both commands are nops 
       since no proof obligation has been generated. *}

text{* The first analytic judgement statement commands are: *}
 
gen_state_cc BirthdayBook
gen_state_cc BirthdayBook1

text{* \ldots which lead to the generation of the proof obligations
       \verb+BBSpec.ccState_BirthdayBook_1+ and
       \verb+BBSpec.ccState_BirthdayBook1_1+. They state that
       the state schemas (representing invariants)
       should be satisfiable. With the generic command: *}

show_po      BBSpec.ccState_BirthdayBook1_1

text{* As an example, we will dicharge this proof oblifation by providing a proof
       for it. *}

po "BBSpec.ccState_BirthdayBook1_1"
txt{* This means that we have to show: *}
txt{* @{subgoals} *}
txt{* Obvioulsly, we have to eliminate the schema quantifier by an respective 
      introduction tactic for the schema calulus: *}
apply(zintro_sch_ex,clarify,(rule refl)+)
apply(zunfold BirthdayBook1_def)
apply(auto simp: Z2HOL)
apply(rule_tac [3] ZInteg.zero_is_natural, simp_all)
apply(rule_tac f="\<lambda> x. arbitrary" in lambda_total1,simp)+
discharged


text{* \ldots we can display the precise form of proof obligation. *}


text{* Moreover, we generate proof obligations that assure that
       an operation schema is in fact implementable or ``non-blocking'',
       in the sense that there is a (not necessarily computable) 
       function mapping pre-state and input to a post-state and
       output. *}

gen_op_cc    AddBirthday
gen_op_cc    AddBirthday1

show_po      BBSpec.ccOp_AddBirthday1_1

text{* Note that the listing of now active proof obligations can be
       parameterized by filters excluding certain proof-obligation
       classes (more filtering functions are desirable, but currently
       not implemented): *}

list_po except ccOp




end


