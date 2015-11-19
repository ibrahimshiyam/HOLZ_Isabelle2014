// $Id: admin.cpp,v 1.16 2000/07/26 16:00:38 wg Exp $


#include "admin.h"

#include "natives.h"
#include "data.h"
#include "unify.h"

#include <algorithm>

//----------------------------------------------------------------------------
// Continuation

void Admin::failure(Thread thread) NoTHROW() {
  Goal goal = thread->parent;
  goal->status = ThreadData::FAILED;
  thread->status = ThreadData::FAILED;
  goal->running--;
  thread->home.remove();
  // CHECKME GcHeap::delForward(thread->homeInfo);
  TPRINT(iendl << "failed  " << thread);
  if (Session::doFAILTRACE()){
    printbt(goal, "FAILED", thread);
  }
  // try to backtrack
  try {
    if (!tryNext(goal)){
      // awake parent
      if (goal->parent != 0)
	Admin::contin(goal->parent);
    }
  }
  catch (Failure& f){
    // during backtrack this means the entire goal becomes undefined
    // terminate all threads of this goal
    Choice c = goal->choices.ptr();
    while (c != 0){
      while (!c->enriched.empty()){
	Thread t = c->enriched.pop();
	t->schedule.remove();
	// CHECKME GcHeap::delForward(t->scheduleInfo);
	t->home.remove();
	// CHECKME GcHeap::delForward(t->homeInfo);
	goal->running--;
      }
      c = c->parent;
    }
    while (!goal->threads.empty()){
      Thread t = goal->threads.pop();
      t->schedule.remove();
      // CHECKME GcHeap::delForward(t->scheduleInfo);
      t->home.remove();
      // CHECKME GcHeap::delForward(t->homeInfo);
      goal->running--;
    }
    goal->status = ThreadData::UNDEFINED;
    if (goal->parent != 0) Admin::contin(goal->parent);
  }
}

void Admin::undef(Thread thread, char const* reason) NoTHROW() {
  Goal goal = thread->parent;
  // printbt(goal, "UNDEF", thread);
  goal->running--;
  // thread->home.remove();   
  // CHECKME GcHeap::delForward(thread->homeInfo);
  thread->status = ThreadData::UNDEFINED;
  thread->undefReason = reason;
  TPRINT(iendl << "undefined " << thread << ": " << reason);
  goal->status = ThreadData::UNDEFINED;
  if (goal->running == 0 && goal->parent != 0)
    Admin::contin(goal->parent);
}

void Admin::success(Thread thread) NoTHROW() {
  Goal goal = thread->parent;
  goal->running--;
  thread->home.remove();
  // CHECKME GcHeap::delForward(thread->homeInfo);
  thread->status = ThreadData::SUCCEEDED;
  if (goal->running == 0 && goal->parent != 0)
    Admin::contin(goal->parent);
}

      
//----------------------------------------------------------------------------
// Checking Free Vars
 
void Admin::checkFreeVars(Goal goal, Value value){
  if (value->ground) return;
  switch (value->kind) {
  case ValueData::VAR: {
    VarData * dat = static_cast<VarData*>(value);
    if (dat->binding == 0) {
      if (dat->goal == goal) throw RequireFailure(dat);
    } else {
      if (!dat->visiting){
	dat->visiting = true;
	checkFreeVars(goal, dat->binding.ptr());
	dat->visiting = false;
      } 
    }
    break;
  }
  case ValueData::TERM: {
    TermData const * dat = static_cast<TermData const *>(value);
    int arity = dat->cons->arity;
    for (int i = 0; i < arity; i++){
      checkFreeVars(goal, dat->args[i]);
    }
    break;
  }
  case ValueData::SET: {
    SetData const * set = static_cast<SetData const *>(value);
    int i;
    for (i = 0; i < set->ecount; i++){
      checkFreeVars(goal, set->extens[i]);
    }
    for (i = 0; i < set->icount; i++){
      Inten inten = set->intens[i];
      for (int j = 0; j < inten->schema->paramcount; j++){
	checkFreeVars(goal, inten->params[j]);
      }
    }
  }
  default:
    ;
  }
}


//----------------------------------------------------------------------------
// Matching & Instantiating 


/*
void Admin::commitMatch(Goal goal, MatchData& match) THROW(Failure) {
  DPRINT(iendl << "COMMIT" << match);
  int count;
  VarRecord vrec;
  if (match.inten != 0){
    // allocate fresh variables for this intension
    vrec = instantiate(goal, match.inten);
    count = match.inten->schema->varcount;
  } else {
    vrec = 0;
    count = 0;
  }
  // commit match elems
  MatchElem e = match.elems;
  while (e != 0){
    if (e->kind == MatchElemData::VAR){
      MatchElemVarData* v = static_cast<MatchElemVarData*>(e);
      Value binding = count > 0 ? shift(vrec->vars, v->binding) : v->binding;
      if (v->var->index < 0){
	// bound fresh variable
	Unify::unify(goal, vrec->vars[-(v->var->index+1)], binding);
      } else {
	// bound outer variable
	Unify::unify(goal, v->var, binding);
      }
    } else {
      MatchElemSubgoalData* s = static_cast<MatchElemSubgoalData*>(e);
      if (count > 0){
	for (int i = 0; i < s->subgoal->schema->paramcount; i++){
	  s->subgoal->params[i] = shift(vrec->vars, s->subgoal->params[i]);
	}
      }
      spawnThreads(goal, s->subgoal, instantiate(goal, s->subgoal));
    }
    e = e->previous;
  }
  match.elems = 0;
  if (match.inten != 0)
    // spawn threads
    spawnThreads(goal, match.inten, vrec);
}
*/

VarRecord Admin::instantiate(Goal goal, Inten inten){
  int count = inten->schema->varcount;
  char const * const * names = inten->schema->varnames;
  int start = goal->varcount;
  VarData** tab = new (GC) VarData*[count];
  for (int i = 0; i < count; i++){
    tab[i] = new (GC) VarData(goal, start+i, names[i]);
    DPRINT(iendl << "ALLOC VAR " << *tab[i] << " FOR " << *inten);
  }
  goal->vars.assign(
	  goal,
	  new (GC) VarRecordData(goal->vars.ptr(), 
				 inten, goal->varcount, tab)
	);
  goal->varcount += count;
  return goal->vars.ptr();
}
 
Value Admin::shift(VarData** tab, Value x){
  // CHECKME: shifting in SET and OTHER???????????
  if (x == 0 || x->ground) return x;
  switch (x->kind) {
  case ValueData::TERM: {
    TermData const * dat = static_cast<TermData const *>(x);
    int arity = dat->cons->arity;
    Value * const args = new (GC) Value[arity];
    bool ground = true;
    for (int i = 0; i < arity; i++){
      args[i] = shift(tab, dat->args[i]);
      ground = ground && args[i]->ground;
    }
    return new (GC) TermData(ground, dat->cons, args);
  }
  case ValueData::VAR: {
    VarData const * dat = static_cast<VarData const*>(x);
    if (dat->index < 0)
      return Data::resolveVars(tab[-(dat->index+1)]);
    else
      return x;
  }
  default:
    return x;
  }
}

static int ageCounter = 0;

      
void Admin::spawnThreads(Goal goal, Inten inten, VarRecord vrec, 
			 Thread creator) 
NoTHROW() {
  VarData** tab = vrec != 0 ? vrec->vars : 0;
  Schema schema = inten->schema;
  int count = schema->constrcount;
  int countercell;
  int& counter = creator == 0 ? ageCounter : countercell;
  if (creator != 0){
    if (creator->depthFirst)
      countercell = creator->age  - count;
    else
      countercell = creator->age;
  }
  for (int i = 0; i < count; i++){
    Constr constr = schema->constrs[i];
    Thread thr = 
      new (GC) ThreadData(
		 goal, inten, constr,
		 constr->regcount > 0 ? 
		           DynPtrArr<ValueData>(constr->regcount) :
			   DynPtrArr<ValueData>(),
		 tab,
		 goal->choiceDepth,
		 constr->code
	       );
    thr->age = counter++;
    if (creator != 0) thr->depthFirst = creator->depthFirst;
    if (Session::doTPRINT()){
      TPRINT(iendl << "spawned ");
      printThreadAt(*Session::debug, thr, thr->pc);
      DPRINT(iendl << "FOR " << *inten);
    }
    if (goal->choiceDepth > 0){
      goal->choices->enriched.enqueue(goal->choices.ptr(),
				      thr->home);
      thr->choice = goal->choices.ptr();
    } else {
      goal->threads.enqueue(goal, thr->home);
    }
    goal->running++;
    contin(thr);
  }
}

static void checkIndex(Value v, int mark){
  switch (v->kind) {
  case ValueData::VAR: {
    VarData * dat = static_cast<VarData*>(v);
    ASSERT(dat->index < mark);
    if (dat->binding != 0)
      checkIndex(dat->binding.ptr(), mark);
    break;
  }
  case ValueData::TERM: {
    TermData const * dat = static_cast<TermData const *>(v);
    int arity = dat->cons->arity;
    for (int i = 0; i < arity; i++){
      checkIndex(dat->args[i], mark);
    }
  }
  default:
    ;
  }
}
  
    
inline void Admin::release(Goal goal, int mark){
  while (goal->vars != 0 && goal->varcount > mark){
    VarRecord r = goal->vars.ptr();
    goal->vars.assign(goal, r->parent);
    goal->varcount = r->index;
  }
  if (Session::doXASSERT()){
    // check whether old variables point to new ones
    VarRecord r = goal->vars.ptr();
    while (r != 0) {
      for (int i = 0; i < r->inten->schema->varcount; i++){
	checkIndex(r->vars[i], mark);
      }
      r = r->parent;
    }
  }
}

//----------------------------------------------------------------------------
// Choice Points & Backtracking

ChoiceData& Admin::makeChoice(SearchState::Kind kind,
			      Thread thread,
			      int matchcount, Match* matchdata) NoTHROW() {
  Goal goal = thread->parent;
  goal->choiceDepth++;
  goal->choices.assign(
    goal,
    new (GC) ChoiceData(kind,
			goal->choices.ptr(),
			thread,
			thread->pc,
			goal->choiceDepth,
			goal->varcount,
			matchcount, matchdata)
	);
  if (Session::doTPRINT()){
    printThreadTrace(*Session::debug, thread);
    *Session::debug << iendl << "{" << ind;
  }
  thread->dumpDepth = goal->choiceDepth;
  return *goal->choices;
}


bool Admin::tryFirst(Goal const goal) THROW(Failure) {
  int mcurrent,mcount;
  while (goal->choices != 0 && 
	 (mcurrent = goal->choices->mcurrent) < 
	 (mcount = goal->choices->mcount)){
    try {
      Match match = goal->choices->matches[mcurrent];
      Thread thread = goal->choices->thread;
      if (mcurrent == mcount-1){
	// last one: tail optimization
	goal->choices.assign(goal, goal->choices->parent);
	goal->choiceDepth--;
	TPRINT(unind << iendl << "}");
      } else {
	goal->choices->matches[mcurrent] = 0;
	goal->choices->mcurrent++;
      }
      match->commit(goal, thread);
      return true;
    }
    catch (UnequalFailure& f){
      // undo possible variable bindings of unify
      if (goal->choices != 0) {
	reset(goal, goal->choices->bound);
	// kill threads started by commit
	kill(goal->choices->enriched);
	// release variables added by commit 
	release(goal, goal->choices->varmark);
      }
      // ... continue with next match
    }
    // propagate other failures
  }
  return false;
}


bool Admin::tryNext(Goal const goal) THROW(UnifyFailure) {
  if (goal->choiceDepth > 0){
    do {
      ChoiceData& choice = *goal->choices;
      Thread thread = choice.thread;
      release(goal, choice.varmark);
      reset(goal, choice.bound);
      reset(goal, choice.stepped);

      kill(choice.enriched);
      if (tryFirst(goal)){
	goal->status = ThreadData::SUCCEEDED;
	thread->pc = choice.pc;
	thread->dumpDepth = goal->choiceDepth; // choice.dumpDepth;
	switch (thread->status){
	case ThreadData::FAILED: 
	case ThreadData::SUCCEEDED: 
	case ThreadData::UNDEFINED: 
	  // it again runs
	  goal->running++;
	  if (thread->choice != 0){
	    thread->choice->enriched.append(thread->choice, thread->home);
	  } else {
	    goal->threads.append(goal, thread->home);
	  }
	  break;
	case ThreadData::ZOMBIE:
	  ASSERT(false);
	  break;
	default:
	  ;
	}
	thread->status = ThreadData::NORMAL;
	thread->schedule.remove();
	// CHECKME GcHeap::delForward(thread->scheduleInfo);
	contin(thread);
	return true;
      } else {
	if (Session::doDPRINT()){
	  DPRINT(iendl << "no more choices of ");
	  printThreadAt(*Session::debug, thread, thread->pc);
	}
      }
      if (goal->choiceDepth > 0){
	goal->choices.assign(goal, choice.parent);
	goal->choiceDepth--;
	TPRINT(unind << iendl << "}");
      }
    } while (goal->choiceDepth > 0);
  } 
  // no more choices: kill threads of goal
  kill (goal->threads);
  return false;
}

//----------------------------------------------------------------------------
// Trailing etc

void Admin::dumpThread(Thread thread, Instr::Pointer at, 
		       ThreadData::Status status){
  Goal goal = thread->parent;
  ChoiceData& choice = *goal->choices;
  switch (status){
  case ThreadData::SEARCH:{
    choice.stepped.assign(
      &choice,
      new (GC) ThreadDump(choice.stepped.ptr(),
			  thread,
			  thread->search->origin,
			  ThreadData::NORMAL,
			  thread->dumpDepth)
    );
      /*
      new (GC) ThreadDump(choice.stepped,
			  thread,
			  at, 
			  thread->dumpDepth,
			  thread->search->matches, 
			  thread->search->matchcount);
      */
    break;
  }
  default:
    choice.stepped.assign(
      &choice,
      new (GC) ThreadDump(choice.stepped.ptr(),
			  thread,
			  at, status,
			  thread->dumpDepth)
    );
  }
  thread->dumpDepth = goal->choiceDepth;
  if (Session::doDPRINT()){
    *Session::debug << iendl << "dumped ";
    printThreadAt(*Session::debug, thread, thread->pc);
    DPRINT(iendl << "to CHOICE # " 
	   << thread->dumpDepth
	   << " of ");
    printThreadAt(*Session::debug, choice.thread, choice.thread->pc);
  }
}

void Admin::reset(Goal const goal, DynPtr<ThreadDump>& dump){
  // recursive procedure, in order to preserve original round-robbing order
  if (dump == 0) return;
  DynPtr<ThreadDump> dprev(dump->previous);
  reset(goal, dprev);
  Thread t = dump->thread;
  ASSERT(t->status != ThreadData::ZOMBIE);
  /*
  ASSERT(dump->status == ThreadData::NORMAL ||
	 dump->status == ThreadData::FAILED ||
	 dump->status == ThreadData::FAILED ||
	 dump->status == ThreadData::SUCCEEDED ||
	 dump->status == ThreadData::UNDEFINED);
  */
  switch (t->status){
  case ThreadData::SUBRESO:
    kill(t->sub->subgoal);
    break;
  case ThreadData::SEARCH:
  case ThreadData::NORMAL:
    break;
  default:
    goal->running++;
    t->home.remove();
    if (t->choice != 0){
      t->choice->enriched.append(t->choice, t->home);
    } else {
      goal->threads.append(goal, t->home);
    }
  }
  if (Session::doDPRINT()){
    *Session::debug << iendl << "restore ";
    printThreadAt(*Session::debug, t, dump->pc);
    DPRINT(" status " << dump->status);
  }
  t->pc = dump->pc;
  t->status = dump->status;
  t->dumpDepth = dump->dumpDepth;
  t->schedule.remove(); 
  // CHECKME GcHeap::delForward(t->scheduleInfo);
  switch (t->status){
  case ThreadData::SEARCH:
    if (Session::doDPRINT()){
      DPRINT(iendl << "WITH " << dump->search.matchcount << " MATCHES");
      for (int i = 0; i < dump->search.matchcount; i++){
	DPRINT(iendl << *dump->search.matches[i]);
      }
    }
    t->search.assign(t, new (GC) SearchState());
    t->search->matchcount = dump->search.matchcount;
    t->search->matches = dump->search.matches;
    t->search->kind = SearchState::MEMBER;
    t->search->elem = 0;
    t->search->set = 0;
    t->search->origin = 0;
    search(t);
    break;
  default:
    contin(t);
  }
  dump.clear();
}


void Admin::kill(DynPtr<GoalData> & dptr){
  Goal goal = dptr.ptr();
  while (!goal->threads.empty()){
    kill(goal->threads.pop());
  }
  Choice c = goal->choices.ptr();
  while (c != 0){
    c->bound.clear();
    c->stepped.clear();
    while (!c->enriched.empty()){
      kill(c->enriched.pop());
    }
    c = c->parent;
  }
  goal->choices.clear();
  release(goal, 0);
  dptr.clear();
}


void Admin::kill(Thread thread){
  Goal goal = thread->parent;
  switch (thread->status){
  case ThreadData::SUBRESO:
    kill(thread->sub->subgoal);
    thread->sub.clear();
    goal->running--;
    break;
  case ThreadData::SEARCH:
    thread->search.clear();
    goal->running--;
    break;
  case ThreadData::NORMAL:
    goal->running--;
    break;
  default:
    ;
  }
  thread->schedule.remove();
  // CHECKME GcHeap::delForward(thread->scheduleInfo);
  thread->home.remove();      // redundant in context of goal kill
  // CHECKME GcHeap::delForward(thread->homeInfo);
  thread->status = ThreadData::ZOMBIE;
}

       

//----------------------------------------------------------------------------
// Checking the Status of a Goal

ThreadData::Status Admin::status(Goal const goal){
  return goal->status;
}
      

