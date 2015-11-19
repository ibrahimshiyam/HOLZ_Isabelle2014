LTL =  Kripke +

types

  'a pred = 'a => bool


datatype

  'a ltl =
    T
  | Atom  ('a pred)
  | Neg   ('a ltl)
  | Conj  ('a ltl) ('a ltl)
  | Next  ('a ltl)
  | Until ('a ltl) ('a ltl)
  

consts
  
  sat  :: "['a trace, 'a ltl] => bool"


primrec

  "sat t T            = True "
  "sat t (Atom p)     = p(t 0)"
  "sat t (Neg f)      = (~(sat t f))"
  "sat t (Conj f g)   = ((sat t f) & (sat t g))"
  "sat t (Next f)     = (sat (suffix t 1) f)"
  "sat t (Until f g)  = (? j. (sat (suffix t j) g) &
                                (! i. i<j --> sat (suffix t i) f))"

constdefs  
  Disj :: "['a ltl, 'a ltl] => 'a ltl"       (infixr "or" 55) 
  "Disj f g == Neg (Conj (Neg f) (Neg g))"

  Imp :: "['a ltl, 'a ltl] => 'a ltl"        (infixr "-+->" 50)
  "Imp f g == Disj (Neg f) g"


consts
  F   :: "'a ltl => 'a ltl"                  ("<*>")           
  G   :: "'a ltl => 'a ltl"                  ("[*]")


defs
  F_def "<*> f  == Until T f"
  G_def "[*] f  == Neg (<*> (Neg f))"


constdefs
  
  Sat  :: "['a kripke, 'a ltl] => bool"
  "Sat K f == ALL t:traces K. sat t f"


syntax   "@validS" :: ['a, bool] => bool     ("(1_) |= (1_)"  50)

translations
         "K |= f" == "Sat K f"


end
  