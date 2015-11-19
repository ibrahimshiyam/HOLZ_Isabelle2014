Kripke = Main +

types
  'a trace =  nat => 'a
  
record 'a kripke =
  init   :: "'a set"
  next   :: "('a * 'a) set"

constdefs

  is_trace :: "['a kripke, 'a trace] => bool"
  "is_trace K t == ( ( (t 0) : (init K)             ) &
		     ( !i. (t i, t(Suc i)) : next K )      )"


  traces :: "'a kripke => 'a trace set"
  "traces K == { t. is_trace K t }"


  suffix :: ['a trace, nat] => 'a trace
  "suffix t i == %j. t(i+j)"
  

  reachable_from :: "['a kripke, 'a, 'a] => bool"
                                            ("_ |- _ -*> _" [61,61,61]60)
  "K |- q -*> q' == (q, q') : (next K)^*"

  Reach :: "'a kripke => 'a  set"
  "Reach K == (next K)^* ``  init K"
  
end
