  


header {* Generic Refinement Notions in Isabelle/HOL - a study *}

theory Refinement = Main:

text {* Refinement notions for standard data refinement 
were introduced. Coming in two versions 
~\cite{woodcock.ea:using:1996}:
\begin{enumerate}
\item forward simulation
\item backward simulation
\end{enumerate}

The first is also used in
Spivery~\cite{spivey:z_notation:1992}.

In Z schema-calculus, this looks quite easy as a combination
of three conditions; two of them address refinement of operations,
one refinement of initial states.
\begin{enumerate}
\item[init-refined]
 $\forall Cstate \bullet Cinit \implies (\exists Astate \bullet Abs \and Ainit)
\item[transition-refined]
 $\forall Astate Cstate Cstate' x? y! 
          \bullet pre Aop \land Abs \land Cop \limplies 
              (\exists Astate' \bullet Abs'\and Aop)
\item[non-blocking-refined] 
 $\forall Astate Cstate x? \bullet pre Aop \land Abs \limplies pre Cop$
\end{enumerate}

(This corresponds to F-init, Fcorr(1) and F-corr(2) in 
 ~\cite{woodcock.ea:using:1996}, pp. 260)

Woodcock/Davis describe also the backward simultion
in terms of rules ~\cite{woodcock.ea:using:1996}, pp. 270):
\begin{enumerate}
\item[init-refined]
 $\forall AState' Cstate' \bullet 
        Cinit \and Abs' \limplies AInit  
\item[transition-refined]
 $\forall Cstate ($\forall Astate \bullet R \implies pre Aop) \implies
          \forall Astate' Cstate'\bullet Cop \land Abs' \implies
            \exists Astate\bullet R \land Aop
\item[non-blocking-refined] 
 $\forall Cstate \bullet (\forall A \bullet Abs \implies pre Aop) \limplies pre Cop$ 
\end{enumerate}

*}

(*state monad: general interface for functional 
               and imperative programs.
  Problem: Excludes non-determinism, is therefore
           too specialized. *)
types ('s, 'a, 'b) monF = "'a \<Rightarrow> ('s \<Rightarrow> ('b \<times> 's))"
types ('s, 'a, 'b) monP = "'a \<Rightarrow> ('s \<Rightarrow> ('b \<times> 's)set)"


(*state-enriched IO relation. Overcomes this. *)
types ('i, 'o, 's) ios_rel = "(('i \<times> 's) \<times> ('o \<times> 's))set"

(*IOS abstraction relation 
  (generalizes conventional S-abstraction in Z literature *)
record ('i,'i','o,'o','s,'s') abs_rel =
  i    :: "('i \<times> 'i') set"
  o    :: "('o \<times> 'o') set"
  abs  :: "('s \<times> 's') set"

record ('i,'o,'s) spec =
  init :: "('s) set"
  inv  :: "('s) set"
  opn  :: "('i, 'o, 's) ios_rel"


constdefs
   FS_init ::"[('i,'o,'s) spec, 
                ('i,'ii,'o,'oo,'s,'ss) abs_rel, 
                ('ii,'oo,'ss) spec] \<Rightarrow> bool"
  "FS_init A R C  \<equiv>
   \<forall> cs\<in>(inv C). cs\<in>(init C) \<longrightarrow> (\<exists> as\<in>(inv A). as\<in>(init A) \<and> (as,cs)\<in>abs R)" 


lemma FS_init_simple :
   "\<lbrakk> init A = inv A; init C = inv C \<rbrakk>
    \<Longrightarrow> FS_init A R C = (\<forall> cs\<in>(inv C). \<exists> as\<in>(inv A). (as,cs)\<in>abs R)"
    by(auto simp: FS_init_def Range_def converse_def)

(* TODO: weaken this to: *)
lemma FS_init_simple2:
   "\<lbrakk> init A \<subseteq> inv A; init C \<subseteq> inv C \<rbrakk>
    \<Longrightarrow> FS_init A R C = (\<forall> cs\<in>(inv C). \<exists> as\<in>(inv A). (as,cs)\<in>abs R)"
    apply(auto simp: FS_init_def Range_def converse_def)
    sorry

(* TODO: find a characterization of FS_init *)
lemma FS_init_charn:
   "\<lbrakk> init A = inv A; init C = inv C \<rbrakk>
    \<Longrightarrow> FS_init A R C \<longrightarrow> ((inv C) \<subseteq> Range(abs R))"
    by(auto simp: FS_init_def Range_def converse_def)

(* < < < < TODO: find a characterization of FS_init *)

constdefs
   FS_corr1 ::"[('i,'o,'s) spec, 
                ('i,'i','o,'o','s,'s') abs_rel, 
                ('i','o','s') spec] \<Rightarrow> bool"
  "FS_corr1 A R C \<equiv>
    \<forall>as\<in>(inv A). \<forall>cs\<in>(inv C). \<forall>cs'\<in>(inv C). 
    \<forall>inp\<in>(Domain(i R)). \<forall>inp'\<in>(Range(i R)). \<forall>out'\<in>(Range(abs_rel.o R)).
            ((inp,as) \<in>(Domain(opn A)) \<and> 
             (as,cs)\<in>(abs R) \<and> (inp,inp')\<in>(i R) \<and> 
             ((inp',cs),(out',cs'))\<in>(opn C)
            ) 
            \<longrightarrow> 
            (\<exists> as'\<in>(inv A). \<exists> out\<in>(Domain(abs_rel.o R)). 
                  (as',cs')\<in>(abs R) \<and>
                  (out,out')\<in>(abs_rel.o R)  \<and>
                  ((inp,as),(out,as'))\<in>(opn A))"



constdefs
   FS_corr2 ::"[('i,'o,'s) spec, 
                ('i,'i','o,'o','s,'s') abs_rel, 
                ('i','o','s') spec] \<Rightarrow> bool"
  "FS_corr2 A R C \<equiv>
    \<forall>as\<in>(inv A). \<forall>cs\<in>(inv C). 
    \<forall>inp\<in>(Domain(i R)). \<forall>inp'\<in>(Range(i R)).
            ((inp,as)\<in>(Domain (opn A)) \<and> 
             (as,cs) \<in>(abs R) \<and> (inp,inp')\<in>(i R)
            ) 
            \<longrightarrow> 
            ((inp',cs) \<in>(Domain (opn C)))"


constdefs
   FS_refine :: "[('i,'o,'s) spec, 
                  ('i,'i','o,'o','s,'s') abs_rel, 
                  ('i','o','s') spec] \<Rightarrow> bool"
   "FS_refine A R C \<equiv> FS_init A R C \<and> FS_corr1 A R C \<and> FS_corr2 A R C"


syntax
  "_FS_refine" :: "[('i,'o,'s) spec, 
                    ('i,'i','o,'o','s,'s') abs_rel, 
                    ('i','o','s') spec] \<Rightarrow> bool"        
                    ("(2 (_)[=fs(_)/(_))" [10,10,10]50)
syntax (xsymbols)
  "_FS_refine" :: "[('i,'o,'s) spec, 
                    ('i,'i','o,'o','s,'s') abs_rel, 
                    ('i','o','s') spec] \<Rightarrow> bool"        
                    ("(2 (_)\<sqsubseteq>\<^sub>_ (_))" [10,10,10]50)
(*
translations
  "FS_refine A R C" == "A [=fs R C"
 *)

text {* 
 Fact: FS_refine is not reflexive in general.
         An ad-hoc precondition would be that 
         all converses of the components of R are functional on a reasonable
         domain; for $i$ this should be UNIV, for $o$ this should be UNIV,
         and for $abs$ this should be $inv A$. 
*}
         
lemma FS_refine_refl : "?COND R \<Longrightarrow> FS_refine A R A"
    apply(auto simp: FS_refine_def FS_init_def FS_corr1_def FS_corr2_def)
    oops
(* TODO: find characterization \<dots> *)

constdefs
   COMP :: "[('i,'i','o,'o','s,'s')       abs_rel, 
             ('i','i'','o','o'','s','s'') abs_rel]
            \<Rightarrow> ('i,'i'','o,'o'','s,'s'')  abs_rel"
   "COMP R R' \<equiv> \<lparr> abs_rel.i  = (abs_rel.i R') O (abs_rel.i R), 
                 abs_rel.o   = (abs_rel.o R') O(abs_rel.o R),  
                 abs_rel.abs = (abs_rel.abs R') O (abs_rel.abs R) \<rparr> "

lemma FS_refine_trans : 
    "\<lbrakk> ?COND R R'; FS_refine A R B; FS_refine  B R' C\<rbrakk>
     \<Longrightarrow> FS_refine A (COMP R R') C"
    apply(auto simp: FS_refine_def FS_init_def 
                     FS_corr1_def FS_corr2_def)
    oops


constdefs
   fun2op :: "['i set, 'i \<Rightarrow> 'o] \<Rightarrow>  ('i,'o,unit) spec"
   "fun2op precond F \<equiv> \<lparr> init  = {()}, inv = {()}, 
                        opn = {(a,b). \<exists> x\<in>precond. a=(x,()) \<and> b=(F x,())}\<rparr>"

lemma FS_refine_fun :
    assumes R_form  : "R =  \<lparr>i = RI, abs_rel.o  = RO, abs = Id\<rparr>"

    assumes A_abstr : "\<forall> inp \<in> pa. A inp \<in> Domain RO"
    assumes pre_corr: "\<forall> inp \<in> pa. \<forall> inp'.    (inp,inp')\<in>RI \<longrightarrow> inp'\<in>pc"
    assumes res_corr: "\<forall> inp \<in> pa. \<forall> inp'\<in> pc.(A inp, C inp') \<in> RO"

    shows             "FS_refine (fun2op pa A) R (fun2op pc C)"

    apply(auto simp: A_abstr res_corr pre_corr R_form 
                     fun2op_def FS_refine_def FS_init_def 
                     FS_corr1_def FS_corr2_def) 
    done



constdefs
   pre :: "[('i, 'o, 's) ios_rel, 'i\<times>'s] \<Rightarrow> bool"
   "pre step \<equiv>  \<lambda>(inp,s). (\<exists> s' out. ((inp,s),(out,s'))\<in>step)"


lemma pre_charn : "pre step x = (x \<in> Domain(step))"
   by(auto simp: pre_def)



lemma FS_refine_opn :
    assumes R_form  : "R =  \<lparr>i = Id, abs_rel.o  = Id, abs = Abs\<rparr>"

    assumes FS_init : "\<forall>cs\<in>(inv C). cs\<in>(init C) \<longrightarrow> 
                                    (\<exists> as\<in>(inv A). as\<in>(init A) \<and> (as,cs)\<in>Abs)" 
    assumes FS_corr2: "\<forall>as\<in>(inv A). \<forall>cs\<in>(inv C). \<forall>inp\<in>(Domain(i R)). 
                           ((inp,as)\<in>(Domain (opn A)) \<and> 
                            (as,cs) \<in>(abs R)) 
                           \<longrightarrow> 
                           ((inp,cs) \<in>(Domain (opn C)))"
    assumes FS_corr1: "\<forall>as\<in>(inv A). \<forall>cs\<in>(inv C). \<forall>cs'\<in>(inv C). 
                       \<forall>inp. \<forall>out.
                            ((inp,as)\<in>(Domain (opn A))  \<and> 
                             (as,cs)\<in> Abs \<and> ((inp,cs),(out,cs'))\<in>(opn C)) 
                            \<longrightarrow> 
                            (\<exists> as'\<in>(inv A). (as',cs')\<in> Abs \<and>
                                            ((inp,as),(out,as'))\<in>(opn A))"


    shows             "FS_refine A R C"
    apply(auto simp: R_form fun2op_def 
                     FS_init FS_corr1 FS_corr2 FS_refine_def 
                     FS_init_def FS_corr1_def FS_corr2_def) 
    done


lemma FS_refine_opn_Z :
    assumes R_form  : "R =  \<lparr>i = Id, abs_rel.o  = Id, abs = Abs\<rparr>"

    assumes FS_init : "\<forall>cs\<in>(inv C). cs\<in>(init C) \<longrightarrow> 
                                    (\<exists> as\<in>(inv A). as\<in>(init A) \<and> (as,cs)\<in>Abs)" 
    assumes FS_corr2: "\<forall>as\<in>(inv A). \<forall>cs\<in>(inv C). \<forall>inp\<in>(Domain(i R)). 
                           ( pre(opn A)(inp,as) \<and> 
                            (as,cs) \<in>(abs R)) 
                           \<longrightarrow> 
                           (pre(opn C)(inp,cs))"
    assumes FS_corr1: "\<forall>as\<in>(inv A). \<forall>cs\<in>(inv C). \<forall>cs'\<in>(inv C). 
                       \<forall>inp. \<forall>out.
                            (pre(opn A)(inp,as)  \<and> 
                             (as,cs)\<in> Abs \<and> ((inp,cs),(out,cs'))\<in>(opn C)) 
                            \<longrightarrow> 
                            (\<exists> as'\<in>(inv A). (as',cs')\<in> Abs \<and>
                                            ((inp,as),(out,as'))\<in>(opn A))"


    shows             "FS_refine A R C"
    apply (rule  FS_refine_opn, rule R_form)
    apply (simp_all add : pre_charn[symmetric])
    apply (auto simp: FS_init FS_corr1 FS_corr2) 
    done


(* ******************************************************************* *)
(* Example: Refinement of a function ********************************* *)
(* ******************************************************************* *)


consts 
   insort :: "['a::order, 'a list] \<Rightarrow> 'a list"
primrec 
   insort_mt  : "insort a [] = [a]"
   insort_cons: "insort a (x#S) = (if a < x then a#(x#S)
                                   else if a = x then x#S
                                       else x#(insort a S))"  

consts 
   is_sorted :: "['a list] \<Rightarrow> bool"
   data_R    :: "('a::order set \<times> 'a list)set"
   set_list_R:: "('a::order \<times> 'a set,'a \<times> 'a list,
                  'a set,'a list,
                  unit,unit) abs_rel"

defs
   data_R_def:  "data_R \<equiv> {(x,y). x=set y \<and> is_sorted y}"
   set_list_R_def:
                "set_list_R \<equiv> \<lparr>i = {(x,y). fst x = fst y \<and> 
                                          (snd x,snd y)\<in>data_R},
                               abs_rel.o = data_R, abs = Id\<rparr>"

lemma insert_insort_refine_FS: 
      "FS_refine (fun2op {(x,S). finite S}    (%(x,S). insert x S)) 
                 set_list_R 
                 (fun2op {(x,S). is_sorted S} (%(x,S). insort x S))" 
apply(rule FS_refine_fun)
apply(simp_all add: set_list_R_def data_R_def)
apply(rule conjI, rule refl, rule refl)
apply(simp_all)

(* This results in:

    1. \<forall>a b. finite b \<longrightarrow> (\<exists>y. insert a b = set y \<and> is_sorted y)
    2. \<forall>a b. finite b \<longrightarrow>
          (\<forall>aa ba.
              is_sorted ba \<longrightarrow> insert a b = set (insort aa ba) \<and> 
                              is_sorted (insort aa ba)) *)
apply auto
(* This results in:

    1. \<And>a b. finite b \<Longrightarrow> \<exists>y. insert a b = set y \<and> is_sorted y
    2. \<And>a b aa ba. \<lbrakk>finite b; is_sorted ba\<rbrakk> \<Longrightarrow> a \<in> set (insort aa ba)
    3. \<And>b aa ba x. \<lbrakk>finite b; is_sorted ba; x \<in> b\<rbrakk> 
                   \<Longrightarrow> x \<in> set (insort aa ba)
    4. \<And>a b aa ba x. \<lbrakk>finite b; is_sorted ba; 
                      x \<in> set (insort aa ba); x \<notin> b\<rbrakk> 
                      \<Longrightarrow> x = a
    5. \<And>b aa ba. \<lbrakk>finite b; is_sorted ba\<rbrakk> \<Longrightarrow> is_sorted (insort aa ba)

 *)
oops


(* ******************************************************************* *)
(* Example: Refinement of an operation ******************************* *)
(* ******************************************************************* *)

(* TODO: Birthdaybook - Example ! *)

types Name = nat Date = nat

record BirthdayBook =
  birthday :: "Name ~=> Date"
  known    :: "Name set"

record BirthdayBook1 = 
  dates    :: "(nat ~=> Date)"
  hwm      :: nat
  names    :: "nat ~=> Name"

consts
  AddBirthday  :: "((Name \<times> Date), unit, BirthdayBook)  spec"
  AddBirthday1 :: "((Name \<times> Date), unit, BirthdayBook1) spec"



constdefs 
   Abs :: "(BirthdayBook \<times> BirthdayBook1) set"
  "Abs \<equiv>  {(x,y).((known x) = {n. \<exists> i\<in>{1..(hwm y)}. 
                                    n = the (names y i)}) \<and> 
                 (\<forall>i\<in>{1..(hwm y)}. birthday x (the(names y i)) 
                                   = dates y (the(names y i)))}"
constdefs 
   gen_Abs :: "('a,'a,'b,'b,BirthdayBook,BirthdayBook1) abs_rel"
  "gen_Abs \<equiv>  \<lparr>i = Id, abs_rel.o  = Id, abs = Abs\<rparr>"



lemma AddBirthday_refine: "FS_refine AddBirthday gen_Abs AddBirthday1"
   apply(rule FS_refine_opn_Z)
   apply(simp add: gen_Abs_def)
(* This results in the proof-obligations:
 1. \<forall>cs\<in>spec.inv AddBirthday1.
       cs \<in> init AddBirthday1 \<longrightarrow>
       (\<exists>as\<in>spec.inv AddBirthday. as \<in> init AddBirthday \<and> (as, cs) \<in> Abs)
 2. \<forall>as\<in>spec.inv AddBirthday.
       \<forall>cs\<in>spec.inv AddBirthday1.
          \<forall>inp\<in>Domain (i gen_Abs).
             pre (opn AddBirthday) (inp, as) \<and> (as, cs) \<in> abs_rel.abs gen_Abs \<longrightarrow>
             pre (opn AddBirthday1) (inp, cs)
 3. \<forall>as\<in>spec.inv AddBirthday.
       \<forall>cs\<in>spec.inv AddBirthday1.
          \<forall>cs'\<in>spec.inv AddBirthday1.
             \<forall>inp out.
                pre (opn AddBirthday) (inp, as) \<and>
                (as, cs) \<in> Abs \<and> ((inp, cs), out, cs') \<in> opn AddBirthday1 \<longrightarrow>
                (\<exists>as'\<in>spec.inv AddBirthday.
                    (as', cs') \<in> Abs \<and> ((inp, as), out, as') \<in> opn AddBirthday)
*)
oops   


(* ******************************************************************* *)
(* Projections for behavioral refinement ***************************** *)
(* ******************************************************************* *)

(* A: Projection into Kripke-Structure *)

types
  's trace = "nat \<Rightarrow> 's"
  
record 's kripke =
  init   :: "'s set"
  step   :: "('s \<times> 's) set"

constdefs
  kripke_projection :: "('i,'o,'s) spec \<Rightarrow> 's kripke"
  "kripke_projection A \<equiv>  
   \<lparr>kripke.init = spec.init A, 
    kripke.step = {(s1,s2). \<exists> i' o'.((i',s1),(o',s2))\<in>spec.opn A}\<rparr>"


constdefs

  is_trace  :: "['s kripke, 's trace] => bool"
  "is_trace K t \<equiv> t 0 \<in> kripke.init K \<and> 
                 (\<forall>i. (t i, t (Suc i)) \<in> kripke.step K)"

  traces    :: "'s kripke => 's trace set"
  "traces K \<equiv>  { t. is_trace K t }"

  (* and now, a temporal logicscan be defined as in 
     projects/HITACHI/src/lib/LTL.thy *)


(* B: Projection into (Event)-Trace Sets *)

constdefs
  is_gen_trace  ::"[('i,'o,'s)spec,(('i \<times>'s)\<times>('o \<times>'s))trace] \<Rightarrow> bool"
 "is_gen_trace A t \<equiv> (snd(fst(t 0)) \<in> spec.init A \<and> 
                      (\<forall>i. t i \<in> spec.opn A) \<and>
                      (\<forall>i. snd(snd(t i))= snd(fst(t (Suc i)))))"
  gen_traces   :: "('i,'o,'s) spec \<Rightarrow> (('i\<times>'s)\<times>('o\<times>'s))trace set"
 "gen_traces A \<equiv>  { t.  is_gen_trace A t }"

  event_traces_projection :: "('i,'o,'s) spec \<Rightarrow> ('i\<times>'o)trace set"
 "event_traces_projection A  \<equiv> (\<lambda>f n.(\<lambda>(x,y). (fst x,fst y))(f n))
                                              ` (gen_traces A)"

(* In order to accomodate the setting for processes in the sense of CSP,
   states 's must be instantiated
   with process terms, the transition relation is the one
   given by the operational CSP semantics . . . *)


(* C: Projection into (Event)-Failure Sets *)


end



