// $Id: unify.cpp,v 1.9 2000/07/05 05:47:45 wg Exp $


#include "unify.h"

#include "natives.h"
#include "data.h"
#include "admin.h"

#include <algorithm>
#include <cstring>

// --------------------------------------------------------------------------
// Base Unification 

struct BaseUnification : public UnifyMethod {

  // method for binding variables
  virtual void uniVar(VarData* var, Value val) THROW(Failure) = 0;

  // method for unifying sets
  virtual void uniSet(SetData* set1, SetData* set2) THROW(Failure) = 0;

  // unify two values. 
  void uni(Value val1, Value val2) THROW(Failure) {
    // first try identity
    if (val1 == val2)
      return;
    // next try variables
    if (val1->kind == ValueData::VAR) {
      uniVar(static_cast<VarData*>(val1), val2);
    } else if (val2->kind == ValueData::VAR) {
      uniVar(static_cast<VarData*>(val2), val1);
    } else {
      // next try 'OTHER' data. their unification methods may be
      // able to convert the operand
      if (val1->kind == ValueData::OTHER){
	OtherData* dat = static_cast<OtherData*>(val1);
	dat->unifyWith(val2, this);
      } else if (val2->kind == ValueData::OTHER){
	try {
	  OtherData* dat = static_cast<OtherData*>(val2);
	  dat->unifyWith(val1, this);
	}
	catch (UnequalFailure& f){
	  f.order = -f.order;
	  throw;
	}
      } else {
	// next try terms and sets
	switch (val1->kind) {
	case ValueData::TERM:
	  switch (val2->kind){
	  case ValueData::TERM:{
	    TermData * term1 = static_cast<TermData *>(val1);
	    TermData * term2 = static_cast<TermData *>(val2);
	    if (term1->cons == term2->cons){
	      int arity = term1->cons->arity;
	      for (int i = 0; i < arity; i++){
		uni(term1->args[i], term2->args[i]);
	      }
	    } else {
	      throw UnequalFailure(term1->cons - term2->cons);
	    }
	    break;
	  }
	  default:
	    // cannot be var or other, must be set
	    throw UnequalFailure(-1);
	  }
	  break;
	case ValueData::SET:
	  switch (val2->kind){
	  case ValueData::SET:
	    uniSet(static_cast<SetData *>(val1), static_cast<SetData *>(val2));
	    break;
	  default:
	    // must be term
	    throw UnequalFailure(1);
	  }
	  break;
	default:
	  // never reached
	  ASSERT(false);
	}
      }
    }
  }

  
};

// --------------------------------------------------------------------------
// Unification with Flexible Set Treatment


struct FlexSetUnification : public BaseUnification {

  
  // unify two sets
  void uniSet(SetData* d1, SetData* d2) THROW(Failure) {
    if (d1->icount != 0 || d2->icount != 0){
      // need to extensionalize both sets before comparsion
      addSubgoal(
	new (GC) IntenData(BuiltinUnit::theUnit->schemas
			   [BuiltinUnit::extUnifySchemaIndex],
			   newGCArray<Value>(d1, d2))
      );
    } else {
      if (d1->ecount == 1 && d2->ecount == 1){
	// special case of normal unification
	uni(d1->extens[0], d2->extens[0]);
      } else {
	VarData* var = Data::findFree(d1);
	if (var != 0){
	  // PLUGIN finite set unification here 
	  // currently we just wait for free variables
	  residuate(var, d1, d2);
	} else {
	  var = Data::findFree(d2);
	  if (var != 0){
	    residuate(var, d1, d2);
	  } else {
	    d1 = Data::freeze(d1); // EFFICIENCY PROBLEM !!!!!!!!!!
	    d2 = Data::freeze(d2);
	    if (d1->ecount == d2->ecount){ 
	      // normal procedure
	      Value * e1beg = d1->extens;
	      Value * e1end = d1->extens+d1->ecount;
	      Value * e2beg = d2->extens;
	      while (e1beg < e1end){
		uni(*e1beg++, *e2beg++);
	      }
	    } else {
	      throw UnequalFailure(d1->ecount - d2->ecount);
	    }
	  }
	}
      }
    }
  }

};

// --------------------------------------------------------------------------
// Flexible Unification

struct FlexUnification : public FlexSetUnification {

  Goal goal;

  FlexUnification(Goal g) : goal(g) {}

  virtual void bindVar(VarData* var, Value val) = 0;

  bool inline bindable(VarData* var, Value v){
    if (var->goal == 0 || // schema binder variable: never frozen
	var->goal == goal)  // is not frozen 
      return true;
    else {
      return false;
      /*
      if (var->goal == goal->machine->root &&
	  v->ground){ // ground assignment to a global variable
	char const * cp = var->name;
	int qcnt = 0;
	while (*cp){
	  if (*cp++ == '?') qcnt++;
	}
	return qcnt == 2;
      } else
	return false;
      */
    }
  }

  void uniVar(VarData* var, Value val) THROW(UnifyFailure) {
    // check in which order to bind
    bool swapped = false;
    if (val->kind == ValueData::VAR){
      VarData* ovar = static_cast<VarData*>(val);
      if (ovar->binding == 0 && // free
	  bindable(ovar,var) && // bindable
	  (ovar->index < 0 || ovar->index > var->index || // younger
	   var->binding != 0 || // var not free
	   !bindable(var,val) // var not bindable
	  )){
	val = var;
	var = ovar;
	swapped = true;
      }
    }
    if (var->binding != 0){
      // substitute
      if (var->visiting){
	// a cycle: left side considered greater
	DPRINT(iendl << "CYCLE " << *var);
	throw UnequalFailure(swapped ? -1 : 1);
      }
      try {
	var->visiting = true;
	uni(var->binding.ptr(), val);
	var->visiting = false;
      }
      catch (UnequalFailure&f){
	var->visiting = false;
	if (swapped) f.order = -f.order;
	throw;
      }
      catch (Failure&f){
	var->visiting = false;
	throw;
      }
    } else if (bindable(var,val)){
      // bind it
      bindVar(var, val);
    } else {
      // residuate
      DPRINT(*var << " =?= " << *Data::freeze(val));
      residuate(var, var, val);
    }
  }
};


/*
static void occuresCheck(VarData* var, Value val){
  DynArray<VarData*> vars;
  Data::freeVars(val);
  for (int i = 0; i < vars.length(); i++){
    if (vars[i] == var){
      ostrstream os;
      os << "cyclic " << *var << " := " << *val << ends;
      throw UndefFailure(os.str());
    }
  }
}
*/
	
	
// --------------------------------------------------------------------------
// Instance of Flexible Unification Directly Working on Variables

	
struct InPlaceUnification : public FlexUnification {

  InPlaceUnification(Goal g) : FlexUnification(g) {}

  void addSubgoal(Inten inten){
    Admin::spawnThreads(goal, inten, 
			Admin::instantiate(goal, inten));
  }

  void residuate(VarData* var, Value v1, Value v2){
    // throw RequireFailure(var);
    addSubgoal(
      new (GC) IntenData(BuiltinUnit::theUnit->schemas
			 [BuiltinUnit::waitUnifySetSchemaIndex],
			 newGCArray<Value>(var, v1, v2))
    );
  }
  void bindVar(VarData* var, Value val){
    ASSERT(var->goal != 0);
    TPRINT(iendl << *var << " := " << *val);
    // occuresCheck(var, val);
    if (var->waiting != 0){
      Thread waiter = var->waiting->pop();
      while (waiter != 0){
	// CHECMKE GcHeap::delForward(waiter->scheduleInfo);
	if (waiter->status == ThreadData::SEARCH) {
	  Admin::search(waiter);
	} else {
	  Admin::contin(waiter);
	}
	waiter->waitFor.clear();
	waiter = var->waiting->pop();
      }
      var->waiting.clear();
    }
    var->binding.assign(var, val);
    var->visiting = false;
    if (goal->choiceDepth > 0){
      ChoiceData& choice = *goal->choices;
      if (var->index < choice.varmark){
	// dump this variable
	DPRINT(iendl << "dumped " << var->name);
	choice.bound.assign(&choice, 
			    new (GC) VarDump(choice.bound.ptr(), var));
      } else {
      }
    } 
  }

};

void Unify::unify(Goal goal, Value val1, Value val2){
  InPlaceUnification u(goal);
  u.uni(val1, val2);
}

// --------------------------------------------------------------------------
// Testing Unification 

struct VarBinding : GcObject {
  VarData* var;
  Value binding;

  inline VarBinding() {}
  
  inline VarBinding(VarData* _var, Value _binding)
    : var(_var), binding(_binding) {
  }

  inline VarBinding(GCPlacement, VarBinding& x){
    var = GcHeap::collect(x.var);
    binding = GcHeap::collect(x.binding);
  }
  void gc(){ GcHeap::gc(this); }

};

struct Residuation : GcObject {
  VarData* var;
  Value val1;
  Value val2;

  inline Residuation() {}

  inline Residuation(VarData* _var, Value _val1, Value _val2) 
		    : var(_var), val1(_val1), val2(_val2) {
  }

  inline Residuation(GCPlacement, Residuation& x) {
    var = GcHeap::collect(x.var);
    val1 = GcHeap::collect(x.val1);
    val2 = GcHeap::collect(x.val2);
  }
  void gc(){ GcHeap::gc(this); }

};

struct TestUnification : public MatchData, FlexUnification {
  
  DynArrayAgg<VarBinding> bindings;
  DynArray<Inten> subgoals;
  DynArrayAgg<Residuation> residuations;

  inline TestUnification(Goal g) : FlexUnification(g){}

  inline TestUnification(GCPlacement, TestUnification& x) : FlexUnification(0){
    inten = GcHeap::collect(x.inten);
    goal = GcHeap::collect(x.goal);
    GcHeap::collect(bindings, x.bindings);
    GcHeap::collect(subgoals, x.subgoals);
    GcHeap::collect(residuations, x.residuations);
  }
  void gc(){ GcHeap::gc(this); }

  MatchData* copy(){
    TestUnification* u = new (GC) TestUnification(goal);
    u->inten = inten;
    u->bindings = bindings.clone();
    u->subgoals = subgoals.clone();
    u->residuations = residuations.clone();
    return u;
  }

  void print(std::ostream& os){
    os << "MATCH ";
    if (inten != 0) os << *inten;
    os << ind;
    int i;
    for (i = 0; i < bindings.length(); i++){
      os << iendl << *bindings[i].var << " := " << *bindings[i].binding;
    }
    for (i = 0; i < residuations.length(); i++){
      os << iendl << *residuations[i].var << ": "
	 << *residuations[i].val1 << " =?= " 
	 << *residuations[i].val2;
    }
    for (i = 0; i < subgoals.length(); i++){
      os << iendl << *subgoals[i];
    }
    os << unind << iendl;
  }
      
  void addSubgoal(Inten inten){
    subgoals.push(inten);
  }

  void residuate(VarData* var, Value val1, Value val2){
    // throw RequireFailure(var);
    residuations.push(Residuation(var, val1, val2));
  }

  
  void bindVar(VarData* var, Value val) THROW(UnifyFailure) {
    DPRINT(iendl << *var << " :== " << *Data::freeze(val));
    // occuresCheck(var, val);
    bindings.push(VarBinding(var, val));
    var->binding.assign(var, val);
    var->visiting = false;
  }

  void unbind(){
    for (int i = 0; i < bindings.length(); i++){
      VarBinding& b = bindings[i];
      b.var->binding.clear();
    }
  }

  Match refine(Goal goal) THROW(Failure) {

    // refine bindings
    // 1st pass: check if new variable bindings occured
    bool newNormBindings = false;
    int i;
    for (i = 0; i < bindings.length(); i++){
      if (bindings[i].var->binding != 0){
	newNormBindings = true;
	break;
      }
    }
    bool newResiBindings = false;
    for (i = 0; i < residuations.length(); i++){
      if (residuations[i].var->binding != 0){
	newResiBindings = true;
	break;
      }
    }
    if (newNormBindings || newResiBindings){
      TestUnification* u = new (GC) TestUnification(goal);
      u->inten = inten;
      // refine bindings
      for (i = 0; i < bindings.length(); i++){
	VarBinding& b = bindings[i];
	if (b.var->binding == 0){
	  // just copy
	  u->bindings.push(VarBinding(b.var, b.binding));
	  b.var->binding.assign(b.var, b.binding);
	  b.var->visiting = false;
	} else {
	  try {
	    // call uni
	    u->uni(b.var->binding.ptr(), b.binding);
	  }
	  catch (Failure&){
	    u->unbind();
	    throw;
	  }
	}
      }
      // refine residuations
      for (i = 0; i < residuations.length(); i++){
	Residuation& r = residuations[i];
	if (r.var->binding == 0){
	  // just copy
	  u->residuations.push(r);
	} else {
	  try {
	    // call uni
	    u->uni(r.val1, r.val2);
	  }
	  catch (Failure&){
	    u->unbind();
	    throw;
	  }
	}
      }
      u->unbind();
      return u;
    } else
      return 0;

  }

  VarData* required() THROW(Failure) {
    for (int i = 0; i < residuations.length(); i++){
      VarData* var = residuations[i].var;
      if (var->binding == 0)
	return var;
    }
    return 0;
  }

  void commit(Goal goal, Thread thread) THROW(Failure) {
    DPRINT(iendl << "COMMIT" << *this);
    int count;
    VarRecord vrec;
    if (inten != 0){
      // allocate fresh variables for this intension
      vrec = Admin::instantiate(goal, inten);
      count = inten->schema->varcount;
    } else {
      vrec = 0;
      count = 0;
    }
    // commit bindings
    int i;
    for (i = 0; i < bindings.length(); i++){
      VarBinding& b = bindings[i];
      Value binding = count > 0 ? Admin::shift(vrec->vars, b.binding) 
                                          : b.binding;
      if (b.var->index < 0){
	// bound fresh variable
	Unify::unify(goal, vrec->vars[-(b.var->index+1)], binding);
      } else {
	// bound outer variable
	Unify::unify(goal, b.var, binding);
      }
    } 
    // commit residuations
    for (i = 0; i < residuations.length(); i++){
      Residuation& r = residuations[i];
      Unify::unify(goal, r.val1, r.val2);
    }
    // commit subgoals
    for (i = 0; i < subgoals.length(); i++){
      Inten s = subgoals[i];
      if (count > 0){
	for (int i = 0; i < s->schema->paramcount; i++){
	  s->params[i] = Admin::shift(vrec->vars, s->params[i]);
	}
      }
      Admin::spawnThreads(goal, s, Admin::instantiate(goal, s),
			  thread->depthFirst ? thread : 0);
    }
    // finally, commit the intension belonging to this match
    if (inten != 0)
      // spawn threads
      Admin::spawnThreads(goal, inten, vrec,
			  thread->depthFirst ? thread : 0);
  }

};
    


MatchData* Unify::testUnify(Goal goal, Value val1, Value val2) THROW(Failure){
  TestUnification* u = new (GC) TestUnification(goal);
  try {
    u->uni(val1, val2);
    u->unbind();
    return u;
  } catch (Failure&){
    u->unbind();
    throw;
  }
}
    

// --------------------------------------------------------------------------
// Comparsion 

struct CompareUnification : public BaseUnification {

  // compare two intensions 
  inline void uniInten(Inten i1, Inten i2) THROW(Failure) {
    if (i1->schema != i2->schema){
      int c = strcmp(i1->schema->name, i2->schema->name);
      throw UnequalFailure(c); // i1->schema - i2->schema);
    }
    else {
      int pcount = i1->schema->paramcount;
      for (int i = 0; i < pcount; i++){
	uni(i1->params[i], i2->params[i]);
      }
    }
  }

  // compare two sets 
  void uniSet(SetData* d1, SetData* d2) THROW(Failure) {
    if (d1->ecount != d2->ecount)
      throw UnequalFailure(d1->ecount - d2->ecount);
    else if (d1->icount != d2->icount) 
      throw UnequalFailure(d1->icount - d2->icount);
    else {
      Value * e1beg = d1->extens;
      Value * e1end = d1->extens+d1->ecount;
      Value * e2beg = d2->extens;
      while (e1beg < e1end){
	uni(*e1beg++, *e2beg++);
      }
      Inten * i1beg = d1->intens;
      Inten * i1end = d1->intens+d1->icount;
      Inten * i2beg = d2->intens;
      while (i1beg < i1end){
	uniInten(*i1beg++, *i2beg++);
      }
    }
  }

  // compare a variable with a second term 
  void uniVar(VarData* var, Value val) THROW(UnifyFailure) {
    if (var->binding != 0){
      if (var->visiting) throw UnequalFailure(1);
      try {
	var->visiting = true;
	uni(var->binding.ptr(), val);
	var->visiting = false;
      }
      catch (Failure&){
	var->visiting = false;
	throw;
      }
    } else {
      if (val->kind == ValueData::VAR){
	VarData* ovar = static_cast<VarData*>(val);
	if (ovar->binding != 0){
	  if (ovar->visiting) throw UnequalFailure(-1);
	  try {
	    ovar->visiting = true;
	    uni(ovar->binding.ptr(), var);
	    ovar->visiting = false;
	  }
	  catch (UnequalFailure& f){
	    ovar->visiting = false;
	    f.order = -f.order;
	    throw;
	  }
	  catch (Failure&){
	    ovar->visiting = false;
	    throw;
	  }
	} else 
	  throw RequireFailure(ovar->index > var->index ? ovar : var);
      } else {
	throw RequireFailure(var);
      }
    }
  }

  // add a subgoal -- fails
  void addSubgoal(Inten inten){
    // CHECKME!!!!
    throw UndefFailure("cannot compare");
  }

  // add a residuation
  void residuate(VarData* var, Value, Value){
    throw RequireFailure(var);
  }


};

void Unify::equal(Value val1, Value val2){
  CompareUnification u;
  u.uni(val1, val2);
}

void Unify::equal(Inten i1, Inten i2){
  CompareUnification u;
  u.uniInten(i1, i2);
}

