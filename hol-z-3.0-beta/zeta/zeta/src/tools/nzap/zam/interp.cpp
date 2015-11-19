// $Id: interp.cpp,v 1.21 2000/07/20 06:44:07 wg Exp $


#include "interp.h"

#include "session.h"
#include "print.h"
#include "natives.h"
#include "data.h"
#include "admin.h"
#include "unify.h"

#include <typeinfo>
#include <list>

#define XPRINT DPRINT

static inline Value ffreeze(Value v){
  return Data::freeze(v);
}

static inline Value freeze(Value v){
  return Data::freeze(v);
}

static inline Value xfreeze(Value v){
  return Data::freeze(v);
}

static inline SetData* freeze(SetData* v){
  return Data::freeze(v);
}

static inline SetData* xfreeze(SetData* v){
  return Data::freeze(v);
}


//----------------------------------------------------------------------------
// Auxiliaries for waiting

static inline void waitFor(Thread thread, Instr::Pointer at, VarData* var){
  // wait for variable
  if (var->waiting == 0) {
    var->waiting.assign(var, new (GC) Ring<ThreadData>());
  }
  var->waiting->enqueue(var->waiting.ptr(), thread->schedule);
  TPRINT(iendl << "waiting for " << *var);
  thread->waitFor.assign(thread, var);
  thread->pc = at;
}

  

//----------------------------------------------------------------------------
// LOAD & WAIT Instructions


static inline Value waitLoad(Thread thread, Instr::Pointer at,
			     Value value) NoTHROW() {
  switch (value->kind) {
  case ValueData::VAR: {
    VarData * data = static_cast<VarData*>(value);
    if (data->binding == 0) {
      waitFor(thread, at, data);
      return 0;
    } else {
      if (!data->visiting) {
	data->visiting = true;
	Value val = waitLoad(thread, at, data->binding.ptr());
	data->visiting = false;
	return val;
      } else {
	return value;
      }
    }
  }
  default:
    return value;
  }
}

static inline void move(Thread const thread)
NoTHROW() {
  thread->pc++;
  int index1 = Data::readIndex(thread->pc);
  int index2 = Data::readIndex(thread->pc);
  thread->regs.assign(index2, xfreeze(thread->regs[index1]));
  Admin::contin(thread);
}

static inline void load(Thread const thread)
NoTHROW() {
  thread->pc++;
  int index = Data::readIndex(thread->pc);
  int reg = Data::readIndex(thread->pc);
  Value res = thread->vars[index];
  thread->regs.assign(reg, xfreeze(res));
  Admin::contin(thread);
}
  
static inline void loadParam(Thread const thread)
NoTHROW() {
  thread->pc++;
  int index = Data::readIndex(thread->pc);
  int reg = Data::readIndex(thread->pc);
  thread->regs.assign(reg, xfreeze(thread->inten->params[index]));
  Admin::contin(thread);
}

static inline void loadGlobal(Thread const thread)
NoTHROW() {
  thread->pc++;
  int gindex = Data::readIndex(thread->pc);
  int reg = Data::readIndex(thread->pc);
  int vindex = thread->inten->schema->unit->globals[gindex]->varinx;
  Value res = thread->parent->machine->globals[vindex];
  thread->regs.assign(reg, xfreeze(res));
  Admin::contin(thread);
}
  
  
static inline void wait(Thread const thread)
NoTHROW() {
  Instr::Pointer at = thread->pc;
  thread->pc++;
  int index = Data::readIndex(thread->pc);
  Value res = waitLoad(thread, at, thread->regs[index]);
  if (res != 0){
    // okay
    Admin::contin(thread);
  }
}

static inline void waitLoad(Thread const thread)
NoTHROW() {
  Instr::Pointer at = thread->pc;
  thread->pc++;
  int index = Data::readIndex(thread->pc);
  Value res = waitLoad(thread, at, thread->vars[index]);
  if (res != 0){
    int reg = Data::readIndex(thread->pc);
    thread->regs.assign(reg, xfreeze(res));
    Admin::contin(thread);
  }
}

static inline void waitLoadParam(Thread const thread)
NoTHROW() {
  Instr::Pointer at = thread->pc;
  thread->pc++;
  int index = Data::readIndex(thread->pc);
  Value res = waitLoad(thread, at, thread->inten->params[index]);
  if (res != 0){
    int reg = Data::readIndex(thread->pc);
    thread->regs.assign(reg, xfreeze(res));
    Admin::contin(thread);
  }
}

static inline void waitGlobal(Thread const thread)
NoTHROW() {
  Instr::Pointer at = thread->pc;
  thread->pc++;
  int gindex = Data::readIndex(thread->pc);
  int vindex = thread->inten->schema->unit->globals[gindex]->varinx;
  Value res = waitLoad(thread, at, thread->parent->machine->globals[vindex]);
  if (res != 0)
    // okay
    Admin::contin(thread);
}

static inline void waitLoadGlobal(Thread const thread)
NoTHROW() {
  Instr::Pointer at = thread->pc;
  thread->pc++;
  int gindex = Data::readIndex(thread->pc);
  int vindex = thread->inten->schema->unit->globals[gindex]->varinx;
  Value res = waitLoad(thread, at, thread->parent->machine->globals[vindex]);
  if (res != 0){
    int reg = Data::readIndex(thread->pc);
    thread->regs.assign(reg, xfreeze(res));
    Admin::contin(thread);
  }
}



//----------------------------------------------------------------------------
// STORE and UNIFY Instruction


static inline void handleUnify(Thread const thread,
			       Instr::Pointer at,
			       Value v1, Value v2) NoTHROW() {
  try {
    Unify::unify(thread->parent, v1, v2);
    Admin::contin(thread);
  }
  catch (UnequalFailure& f){
    Admin::failure(thread);
  }
  catch (RequireFailure& f){
    waitFor(thread, at, f.var);
  }
  catch (Failure& f){
    ASSERT(false);
  }
}

static inline void store(Thread const thread)
NoTHROW() {
  Instr::Pointer at = thread->pc;
  thread->pc++;
  int reg = Data::readIndex(thread->pc);
  int var = Data::readIndex(thread->pc);
  handleUnify(thread, at, thread->vars[var], thread->regs[reg]);
}

static inline void storeGlobal(Thread const thread)
NoTHROW() {
  Instr::Pointer at = thread->pc;
  thread->pc++;
  int reg = Data::readIndex(thread->pc);
  int index = Data::readIndex(thread->pc);
  int var = thread->inten->schema->unit->globals[index]->varinx;
  handleUnify(thread, at,
	      thread->parent->machine->globals[var], 
	      thread->regs[reg]);
}

static inline void unify(Thread const thread)
NoTHROW() {
  Instr::Pointer at = thread->pc;
  thread->pc++;
  int reg1 = Data::readIndex(thread->pc);
  int reg2 = Data::readIndex(thread->pc);
  handleUnify(thread, at, thread->regs[reg1], thread->regs[reg2]);
}


//----------------------------------------------------------------------------
// MEMBER Instruction

static int testSearch(Thread thread){
  
  Goal goal = thread->parent;
  SearchState& state = *thread->search;

  if (state.matches == 0){
    if (Session::doDPRINT()){
      DPRINT(iendl << "MATCHING FOR " << thread);
    }
    // build match data for the first time
    Value elem = state.elem;
    SetData* set = state.set;
#ifndef ZAM_WIN32
    Match mdata[set->ecount+set->icount];
#else
    Match* mdata = new (GC) Match[set->ecount+set->icount];
#endif
    int mcount = 0;
    VarData* required = 0;
    Value const * ebeg = set->extens;
    Value const * eend = set->extens + set->ecount;
    while (ebeg != eend){
      try {
	Value cand = *ebeg++;
	mdata[mcount] = Unify::testUnify(thread->parent, elem, cand);
	// a possible match
	if (required == 0) required = mdata[mcount]->required();
	mdata[mcount]->inten = 0;
	DPRINT(iendl << "FOUND " 
	       << " " << *elem << " = " << *cand << *mdata[mcount]);
	mcount++;
      }
      catch (UnequalFailure&){
	// continue
      }
      catch (Failure&){
	ASSERT(false);
      }
    }
    Inten const * ibeg = set->intens;
    Inten const * iend = set->intens+set->icount;
    while (ibeg != iend){
      try {
	Inten inten = *ibeg++;
	mdata[mcount] = Unify::testUnify(thread->parent,
					 elem, inten->schema->binder);
	// a possible match
	if (required == 0) required = mdata[mcount]->required();
	mdata[mcount]->inten = inten;
	DPRINT(iendl << "FOUND " << *mdata[mcount]);
	mcount++;
      }
      catch (UnequalFailure&){
	// continue
      }
      /*
      catch (RequireFailure& f){
	waitFor(thread, origin, f.var);
	return;
      }
      */
      catch (Failure&){
	ASSERT(false);
      }
    }
    state.matchcount = mcount;
#ifndef ZAM_WIN32
    state.matches = new (GC) Match[mcount];
    uninitialized_copy(&mdata[0], &mdata[mcount], state.matches);
#else
    state.matches = mdata;
#endif
    if (required != 0){
      // queue this thread to wait for a variable
      DPRINT(iendl << "MATCH SUSPENSES");
      thread->schedule.remove();
      // CHECKME GcHeap::delForward(thread->scheduleInfo);
      waitFor(thread, thread->pc, required);
      return -1;
    } else {
      DPRINT(iendl << "MATCHED " << dec << mcount);
      return mcount;
    }
  } else {
    // refine match data
    if (Session::doDPRINT()){
      DPRINT(iendl << "REFINING FOR " << thread);
    }
    VarData* required = 0;
#ifndef ZAM_WIN32
    Match mdata[state.matchcount];
#else
    Match* mdata = new (GC) Match[state.matchcount];
#endif
    int mcount = 0;
    bool change = false;
    for (int i = 0; i < state.matchcount; i++){
      try {
	mdata[mcount] = state.matches[i]->refine(goal);
	if (mdata[mcount] != 0){
	  DPRINT(iendl << "CHANGED " << *mdata[mcount]);
	  if (required == 0) required = mdata[mcount]->required();
	  change = true;
	} else {
	  mdata[mcount] = state.matches[i];
	  DPRINT(iendl << "UNCHANGED " << *mdata[mcount]);
	}
	mcount++;
      }
      catch (UnequalFailure&){
	change = true;
	DPRINT(iendl << "INVALIDATED " << *state.matches[i]);
      }
      catch (Failure&){
	ASSERT(false);
      }
    }
    if (!change){
      DPRINT(iendl << "REFINE: NO CHANGE AT ALL");
      return mcount;
    } else {
      if (thread->dumpDepth < goal->choiceDepth){
	// save old match state
	Admin::dumpThread(thread, thread->pc, ThreadData::SEARCH);
	// Admin::dumpThread(thread, state.origin, ThreadData::NORMAL);
      }
      // set new match state
      state.matchcount = mcount;
#ifndef ZAM_WIN32
      state.matches = new (GC) Match[mcount];
      uninitialized_copy(&mdata[0], &mdata[mcount], state.matches);
#else
      state.matches = mdata;
#endif      
      if (required != 0){
	// queue this thread to wait for a variable
	DPRINT(iendl << "REFINE: SUSPENSES");
	thread->schedule.remove();
	// CHECKME GcHeap::delForward(thread->scheduleInfo);
	waitFor(thread, thread->pc, required);
	return -1;
      } else {
	DPRINT(iendl << "REFINE: CHANGES, " << dec << mcount);
	return mcount;
      }
    }
  }
}

static inline void member(SearchState::Kind kind,
			  Thread const thread)
NoTHROW() {
  Instr::Pointer origin = thread->pc;
  thread->pc++;
  int reg1 = Data::readIndex(thread->pc);
  int reg2 = Data::readIndex(thread->pc);
  SetData * set;
  try {
    set = Data::tryGetSet(thread->regs[reg2]);
  }
  catch (UndefFailure& f){
    // printbt(thread->parent, f.message, thread);
    Admin::undef(thread, f.message);
    return;
  }

  if (set == 0){
    Admin::undef(thread, "not resovable as set (direct recursive equation)");
    // printbt(thread->parent, "undefined");
    return;
  }

  Value elem = thread->regs[reg1];
  DPRINT(iendl << "MEMBER " << *elem << " IN " << *set);

  // try shortcuts
  switch (set->ecount){
  case 0:
    switch (set->icount){
    case 1: 
      Inten inten = *set->intens;
      VarRecord inst = Admin::instantiate(thread->parent, inten);
      try {
	Unify::unify(thread->parent, 
		     elem,
		     Admin::shift(inst->vars, inten->schema->binder));
	Admin::spawnThreads(thread->parent, inten, inst, thread);
	Admin::contin(thread);
      }
      catch (UnequalFailure&){
	Admin::failure(thread);
      }
      catch (RequireFailure& f){
	waitFor(thread, origin, f.var);
      }
      catch (Failure&){
	ASSERT(false);
      }
      return;
    }
    break;
  case 1:
    switch (set->icount){
    case 0:
      try {
	Unify::unify(thread->parent, elem, *set->extens);
	Admin::contin(thread);
      }
      catch (UnequalFailure&){
	Admin::failure(thread);
      }
      catch (RequireFailure& f){
	waitFor(thread, origin, f.var);
      }
      catch (Failure&){
	ASSERT(false);
      }
      return;
    }
  }
  // prepare for search
  Goal goal = thread->parent;
  ASSERT(thread->dumpDepth == goal->choiceDepth);
  thread->status = ThreadData::SEARCH;
  thread->search.assign(thread, new (GC) SearchState());
  thread->search->origin = origin;
  thread->search->elem = elem;
  thread->search->set = set;
  thread->search->matches = 0; // not yet calculated
  thread->search->matchcount = 0;

  int w = testSearch(thread);
  if (w < 0){
    // residuated
  } else 
    switch (w) {
    case 0:
      // failure
      thread->search.clear();
      Admin::failure(thread);
      break;
    case 1:
      // deterministic step 
      thread->status = ThreadData::NORMAL;
      try {
	thread->search->matches[0]->commit(goal, thread);
	thread->search.clear();
	Admin::contin(thread);
      }
      catch (UnequalFailure& f){
	// complete failure of this goal
	Admin::failure(thread);
      }
      catch (Failure& f){
	DPRINT(iendl << "undefined in member: " << thread->constr->name);
	Admin::undef(thread);
      }
      break;
    default:
      if (!thread->depthFirst){
	// schedule in search queue
	Admin::search(thread);
      } else {
	// make a choice point
	thread->status = ThreadData::NORMAL;
	Admin::makeChoice(thread->search->kind,
			  thread, 
			  thread->search->matchcount,
			  thread->search->matches);
	thread->search.clear();
	try {
	  if (Admin::tryFirst(goal)){
	    Admin::contin(thread);
	  }
	  else
	    Admin::failure(thread);
	}
	catch (Failure& f){
	  DPRINT(iendl << "undefined in member: " << thread->constr->name);
	  Admin::undef(thread);
	}
      }
    }
}


	
//----------------------------------------------------------------------------
// Memoization 

// equality and hashing for values as keys

bool MemoApplTab::keyEquals(Value v1, Value v2){
  /*
  1 630 000
  120s
  try {
    Unify::equal(v1, v2);
    return true;
  }
  catch (Failure&){
    return false;
  }
  1 732 000
  22,4s
  */
  v1 = Data::resolveVars(v1);
  v2 = Data::resolveVars(v2);
  if (v1 == v2) return true;
  switch (v1->kind){
  case ValueData::TERM:
    switch (v2->kind){
    case ValueData::TERM:{
      TermData* d1 = static_cast<TermData*>(v1);
      TermData* d2 = static_cast<TermData*>(v2);
      if (d1->cons == d2->cons){
	for (int i = 0; i < d1->cons->arity; i++){
	  if (!keyEquals(d1->args[i], d2->args[i])) return false;
	}
	return true;
      } else
	return false;
    }
    default:
      return false;
    }
  case ValueData::OTHER:{
    OtherData* d = static_cast<OtherData*>(v1);
    return d->cacheEq(v2);
  }
  default:
    return false;
  }
}

unsigned MemoApplTab::keyHash(Value v){
  v = Data::resolveVars(v);
  switch (v->kind){
  case ValueData::TERM:{
    TermData* d = static_cast<TermData*>(v);
    unsigned h = reinterpret_cast<unsigned>(static_cast<void*>(d->cons));
    for (int i = 0; i < d->cons->arity; i++){
      h += keyHash(d->args[i]);
    }
    return h;
  }
  case ValueData::OTHER:{
    OtherData* d = static_cast<OtherData*>(v);
    return d->cacheHash();
  }
  default:
    return reinterpret_cast<unsigned>(static_cast<void*>(v));
  }
}

Value MemoApplTab::keyValidate(Value v){
  v = Data::resolveVars(v);
  if (v->generation >= GcHeap::collectFrom){
    Value n = static_cast<Value>(v->forward);
    if (n != 0) return n;
    switch (v->kind) {
    case ValueData::TERM:{
      TermData* d = static_cast<TermData*>(v);
      Value* args = new (GC)Value[d->cons->arity];
      for (int i = 0; i < d->cons->arity; i++){
	if ((args[i] = keyValidate(d->args[i])) == 0) return 0;
      }
      return new (GC) TermData(d->ground, d->cons, args);
    }
    // FIXME: other data
    default:
      return 0;
    }
  } else
    return v;
}

// cache equality and hashing for homomorphisms as keys

bool MemoHomTab::keyEquals(Hom h1, Hom h2){
  return h1 == h2;
}

unsigned MemoHomTab::keyHash(Hom h){
  return reinterpret_cast<unsigned>(static_cast<void*>(h));
}

Hom MemoHomTab::keyValidate(Hom h){
  return h;
}


static inline Value findApplMemo(MemoTab* tab, Value arg){
  if (tab == 0) return 0;
  Value v = tab->applTab.get(arg);
  if (v != 0) TPRINT("hit apply " << *arg << " |-> " << *v);
  return v;
}

static inline Value findHomMemo(MemoTab* tab, Hom hom){
  if (tab == 0) return 0;
  Value v = tab->homTab.get(hom);
  if (v != 0) TPRINT("hit hom " << hom << " |-> " << *v);
  return v;
}

static inline int findEmptyMemo(MemoTab* tab){
  if (tab == 0) return MemoTab::UNKNOWN;
  TPRINT("hit not-empty " << tab->isEmpty);
  return tab->isEmpty;
}

  
static inline MemoInten* makeMemoInten(MemoTab* tab, Hom hom, Value arg){
  if (tab != 0){
    return new (GC) MemoInten(tab, hom, arg);
  } else
    return 0;
}
  
static inline Value addMemo(MemoInten* inten, Value res){
  if (inten != 0){
    if (inten->hom == 0){
      if (inten->arg == 0){
	// empty/isempty
	XPRINT("add empty " << *res);
	if (res == Data::emptySet)
	  inten->tab->isEmpty = MemoTab::YES;
	else
	  inten->tab->isEmpty = MemoTab::NO;
      } else {
	// application
	if (res->ground){
	  Value v = inten->tab->applTab.get(inten->arg);
	  if (v == 0){
	    XPRINT("add appl " << *inten->arg 
		   << "/" << inten->arg << " |-> " << *res);
	    inten->tab->applTab.add(inten->arg, res);
	  } else {
	    res = v;
	    XPRINT("par appl " << *inten->arg << " |-> " << *res);
	  }
	}
      }
    } else {
      // hom
      // XPRINT("add hom " << inten->hom << " |-> " << *res);
      if (res->ground)
	inten->tab->homTab.add(inten->hom, res);
    }
  }
  return res;
}
  
//----------------------------------------------------------------------------
// Subresolution 

// select the next (existent) intension from subresolution
static inline void selectInten(Thread const thread)
NoTHROW() {
  SubResoState& sub = *thread->sub;
  Goal subgoal = 
    new (GC) GoalData(thread,thread->parent->machine);
  sub.subgoal.assign(&sub, subgoal);
  subgoal->varcount = thread->parent->varcount;
  Inten inten = sub.intens[sub.intencur++];
  VarRecord inst = Admin::instantiate(subgoal, inten);
  subgoal->unif = Admin::shift(inst->vars, inten->schema->binder);
  Admin::spawnThreads(subgoal, inten, inst, thread);
  thread->status = ThreadData::SUBRESO;
  if (subgoal->running != 0)
    // sleep
    ;
  else
    // no threads spawned: success
    Admin::contin(thread);
}
    
// homorphism instruction
static inline void hom(Thread const thread) NoTHROW() {
  Instr::Pointer at = thread->pc;
  thread->pc++;
  Hom hom = thread->inten->schema->unit->homs[Data::readIndex(thread->pc)];
  SetData * set = 
    Data::tryGetSet(thread->regs[Data::readIndex(thread->pc)]);
  if (set == 0){
    Admin::undef(thread, "not resovable as set (direct recursive equation)");
    // printbt(thread->parent, "undefined");
    return;
  }

  int destreg = Data::readIndex(thread->pc);

  Value memoRes = findHomMemo(set->memo.ptr(), hom);
  if (memoRes != 0){
    thread->regs.assign(destreg, memoRes);
    Admin::contin(thread);
    return;
  }
  MemoInten* memoInten = makeMemoInten(set->memo.ptr(), hom, 0);
  
  HomState hs;
  try {
    hs = hom->start(0, set);
  }
  catch (RequireFailure& f){
    waitFor(thread, at, f.var);
    return;
  }
  catch (UndefFailure& f){
    // printbt(thread->parent, f.message, thread);
    Admin::undef(thread, f.message);
    return;
  }

  // iterate over extensions
  HomStateData::Order order = 
    set->ground ? HomStateData::INORDER : HomStateData::OUTOFORDER;
  for (int i = 0; i < set->ecount; i++){
    try {
      if (!hs->next(0, order, ffreeze(set->extens[i]))) {
	thread->regs.assign(destreg, 
			    addMemo(memoInten, ffreeze(hs->end(0))));
	Admin::contin(thread);
	return;
      }
    }
    catch (RequireFailure& f){
      waitFor(thread, at, f.var);
      return;
    }
    catch (UndefFailure& f){
      // printbt(thread->parent, f.message, thread);
      Admin::undef(thread, f.message);
      return;
    }
  }
    
  if (set->icount == 0){
    // here we are
    try {
      Value res = ffreeze(hs->end(0));
      res = addMemo(memoInten, res);
      thread->regs.assign(destreg, res);
      Admin::contin(thread);
    }
    catch (RequireFailure& f){
      waitFor(thread, at, f.var);
    }
    catch (UndefFailure& f){
      // printbt(thread->parent, f.message, thread);
      Admin::undef(thread, f.message);
    }
  } else {
    // start a subresolution
    thread->sub.assign(thread, new (GC) SubResoState());
    SubResoState& sub = *thread->sub;
    sub.origin = at;
    sub.kind = SubResoState::HOM;
    sub.hom.assign(thread->sub.ptr(), hs);
    sub.destreg = destreg;
    sub.intens = set->intens;
    sub.intencur = 0;
    sub.intencount =  set->icount;
    sub.memoInten = memoInten;

    selectInten(thread);
  }
}

// IF/IFNOT instruction
static inline void ififnot(Thread const thread, bool branchOnEmpty) {
  Instr::Pointer at = thread->pc;
  thread->pc++;
  SetData * set = 
    Data::tryGetSet(thread->regs[Data::readIndex(thread->pc)]);
  if (set == 0){
    Admin::undef(thread, "not resovable as set (direct recursive equation)");
    // printbt(thread->parent, "undefined");
    return;
  }
  int offset = Data::readIndex(thread->pc);

  int memoRes = findEmptyMemo(set->memo.ptr());
  if (memoRes != MemoTab::UNKNOWN){
    if (memoRes == MemoTab::YES){
      // empty
      if (branchOnEmpty) thread->pc = thread->pc + offset;
      Admin::contin(thread);
    } else {
      if (!branchOnEmpty) thread->pc = thread->pc + offset;
      Admin::contin(thread);
    }
    return;
  }
  MemoInten* memoInten = makeMemoInten(set->memo.ptr(), 0, 0);

  // shortcut
  if (set->ecount == 0 && set->icount == 0){
    // empty
    if (branchOnEmpty) thread->pc = thread->pc + offset;
    addMemo(memoInten, Data::emptySet);
    Admin::contin(thread);
    return;
  } else if (set->ecount != 0){
    // at least one
    if (!branchOnEmpty) thread->pc = thread->pc + offset;
    addMemo(memoInten, Data::univSet);
    Admin::contin(thread);
    return;
  }

  // normal procedure (extens = 0, intens > 0)
  thread->sub.assign(thread, new (GC) SubResoState());
  SubResoState& sub = *thread->sub;
  sub.origin = at;
  sub.kind = branchOnEmpty ? SubResoState::BRANCHONEMPTY 
                                   : SubResoState::BRANCHONNONEMPTY;
  sub.destreg = offset;
  sub.intens = set->intens;
  sub.intencur = 0;
  sub.intencount = set->icount;
  sub.memoInten = memoInten;

  selectInten(thread);
}

// SUBSET instruction
static inline void subset(Thread const thread){ 
  Instr::Pointer at = thread->pc;
  thread->pc++;
  SetData * const set1 = 
    Data::tryGetSet(thread->regs[Data::readIndex(thread->pc)]);
  SetData * const set2 = 
    Data::tryGetSet(thread->regs[Data::readIndex(thread->pc)]);
  if (set1 == 0 || set2 == 0){
    Admin::undef(thread, "not resovable as set (direct recursive equation)");
    // printbt(thread->parent, "undefined");
    return;
  }

  // build the set {x|x in set1; ~(x in set2)}
  Inten inten = 
    new (GC) IntenData(BuiltinUnit::theUnit->schemas
		       [BuiltinUnit::subsetSchemaIndex],
		       newGCArray<Value>(set1, set2));
  // test if this set is empty 
  thread->sub.assign(thread, new (GC) SubResoState());
  SubResoState& sub = *thread->sub;
  sub.origin = at;
  sub.kind = SubResoState::FAILONNONEMPTY;
  sub.intens = newGCArray<Inten>(inten);
  sub.intencur = 0;
  sub.intencount = 1;
  sub.memoInten = 0;

  selectInten(thread);
}


// function application

static inline void apply(Thread thread, Instr::Pointer at,
			 Value func, Value arg, int destreg) NoTHROW() {
  SetData * set = Data::tryGetSet(func);
  if (set == 0){
    Admin::undef(thread, "not resovable as set (direct recursive equation)");
  }

  if (arg->ground){
    Value memoRes = findApplMemo(set->memo.ptr(), arg);
    if (memoRes != 0){
      thread->regs.assign(destreg, memoRes);
      Admin::contin(thread);
      return;
    }
  }
  
  Inten inten = 
    new (GC) IntenData(BuiltinUnit::theUnit->schemas
		       [BuiltinUnit::applySchemaIndex],
		       newGCArray<Value>(set, arg));
  Inten* intens = newGCArray<Inten>(inten);
  thread->sub.assign(thread, new (GC) SubResoState());
  SubResoState& sub = *thread->sub;
  sub.origin = at;
  sub.kind = SubResoState::HOM;
  Hom h = BuiltinUnit::theUnit->homs[BuiltinUnit::muHomIndex];
  sub.hom.assign(thread->sub.ptr(), h->start(0,0)); // MU does not throws
  sub.destreg = destreg;
  sub.intens = intens;
  sub.intencur = 0;
  sub.intencount = 1;
  if (arg->ground)
    sub.memoInten = makeMemoInten(set->memo.ptr(), 0, arg);
  else
    sub.memoInten = 0;
  selectInten(thread);
}

// clean sub-resolution state
static inline void cleanSub(Thread const thread){
  Admin::kill(thread->sub->subgoal);
  thread->sub.clear();
}

// perform a sub-resolution check
static inline void subresocheck(Thread const thread)
NoTHROW() {
  // here we reach after the subgoal has been resolved
  SubResoState& sub = *thread->sub;
  DPRINT(iendl << "SUBGOAL CHECK: " << thread << iendl << *sub.subgoal);
  Goal goal = thread->parent;
  if (thread->dumpDepth < goal->choiceDepth){
    // if this happens this subresolution's live time
    // crosses a choice point (usually since it residuates because
    // of an unbound context variable). Since we cannot backtrack
    // inside an incomplete subresolution, we have to create
    // a restore entry which backtracks to the start of the sub-resolution
    TPRINT(iendl << "crossed choice point " << thread);
    Admin::dumpThread(thread, sub.origin, ThreadData::NORMAL);
  }

  switch (sub.subgoal->status) {
  case ThreadData::UNDEFINED:
    DPRINT(iendl << "SUBGOAL UNDEFINED");
    // printbt(sub.subgoal.ptr(), "undefined in subgoal");  
    // cleanSub(thread);
    Admin::undef(thread, "undefined in subgoal");
    break;
  case ThreadData::SUCCEEDED:
    // test for deadlock 
    if (sub.subgoal->running != 0){
      DPRINT(iendl << "SUBGOAL UNRESOLVABLE");
      // printbt(sub.subgoal, "unresolvable constraints in subgoal");
      cleanSub(thread);
      Admin::undef(thread, "unresolvable constraints in subgoal");
    } else {
      DPRINT(iendl << "SUBGOAL SUCCEEDED");
      switch (sub.kind){
      case SubResoState::HOM:{
	Value res = ffreeze(thread->sub->subgoal->unif);
	HomState hs = sub.hom.ptr();
	try {
	  if (!hs->next(sub.subgoal.ptr(), HomStateData::OUTOFORDER, res)){
	    // homomorphism ready 
	    res = hs->end(sub.subgoal.ptr());
	    res = addMemo(sub.memoInten, res);
	    thread->regs.assign(sub.destreg, res);
	    cleanSub(thread);
	    thread->status = ThreadData::NORMAL;
	    Admin::contin(thread);
	  } else if (Admin::tryNext(sub.subgoal.ptr())){
	    DPRINT(iendl << "BACKTRACKED " << *sub.subgoal);
	    // continue 
	  } else if (sub.intencur < sub.intencount){
	    DPRINT(iendl << "NEXT INTENSION  " << *sub.intens[sub.intencur]);
	    selectInten(thread);
	    // continue 
	  } else {
	    // no more solutions
	    res = hs->end(sub.subgoal.ptr());
	    res = addMemo(sub.memoInten, res);
	    thread->regs.assign(sub.destreg, res);
	    cleanSub(thread);
	    thread->status = ThreadData::NORMAL;
	    Admin::contin(thread);
	  }
	}
	catch (RequireFailure& f){
	  waitFor(thread, thread->pc, f.var);
	}
	catch (UndefFailure& f){
	  // printbt(thread->parent, f.message, thread);
	  Admin::undef(thread, f.message);
	}
	break;
      }
      case SubResoState::BRANCHONEMPTY:
      case SubResoState::FAILONEMPTY:
	// don't branch, don't fail
	addMemo(sub.memoInten, Data::univSet);
	cleanSub(thread);
	thread->status = ThreadData::NORMAL;
	Admin::contin(thread);
	break;
      case SubResoState::BRANCHONNONEMPTY:
	// branch
	thread->pc = thread->pc + sub.destreg;
	addMemo(sub.memoInten, Data::univSet);
	cleanSub(thread);
	thread->status = ThreadData::NORMAL;
	Admin::contin(thread);
	break;
      case SubResoState::FAILONNONEMPTY:
	// fail
	addMemo(sub.memoInten, Data::univSet);
	cleanSub(thread);
	Admin::failure(thread);
	break;
      }
    }
    break;
  case ThreadData::FAILED:
    DPRINT(iendl << "SUBGOAL FAILED");
    if (sub.intencur < sub.intencount){
      DPRINT(iendl << "NEXT INTENSION  " << *sub.intens[sub.intencur]);
      selectInten(thread);
      // continue 
    } else {
      // no more solutions
      DPRINT(iendl << "SUBGOAL NO MORE SOLUTIONS");
      switch (sub.kind){
      case SubResoState::HOM:
	try {
	  HomState hs = sub.hom.ptr();
	  Value res = ffreeze(hs->end(sub.subgoal.ptr()));
	  res = addMemo(sub.memoInten, res);
	  thread->regs.assign(sub.destreg, res);
	  cleanSub(thread);
	  thread->status = ThreadData::NORMAL;
	  Admin::contin(thread);
	}
	catch (RequireFailure& f){
	  waitFor(thread, thread->pc, f.var);
	}
	catch (UndefFailure& f){
	  // printbt(thread->parent, f.message, thread);
	  Admin::undef(thread, f.message);
	}
	break;
      case SubResoState::BRANCHONNONEMPTY:
      case SubResoState::FAILONNONEMPTY:
	// don't branch, don't fail
	addMemo(sub.memoInten, Data::emptySet);
	cleanSub(thread);
	thread->status = ThreadData::NORMAL;
	Admin::contin(thread);
	break;
      case SubResoState::BRANCHONEMPTY:
	// branch
	thread->pc = thread->pc + sub.destreg;
	addMemo(sub.memoInten, Data::emptySet);
	cleanSub(thread);
	thread->status = ThreadData::NORMAL;
	Admin::contin(thread);
	break;
      case SubResoState::FAILONEMPTY:
	// fail
	addMemo(sub.memoInten, Data::emptySet);
	cleanSub(thread);
	Admin::failure(thread);
	break;
      }
    }
    break;
  default:
    Session::assertFailed("invalid goal state");
  }
}
      

    
//----------------------------------------------------------------------------
// GOTO

static inline void gotopc(Thread thread){
  thread->pc++;
  int offset = Data::readIndex(thread->pc);
  thread->pc = thread->pc + offset;
  Admin::contin(thread);
}

    
//----------------------------------------------------------------------------
// DEPTHFIRST

static inline void depthFirst(Thread thread){
  thread->pc++;
  thread->depthFirst = true;
  Admin::contin(thread);
}



//----------------------------------------------------------------------------
// NATIVE Instructions



static inline void callNative(Thread thread)
NoTHROW() {
  Instr::Pointer origin = thread->pc;
  thread->pc++;
  int index = Data::readIndex(thread->pc);
  int base = Data::readIndex(thread->pc);
  int dest = Data::readIndex(thread->pc);
  try {
    thread->regs.assign(dest,
			thread->inten->schema->unit->nativeFuncs[index]->funct
			(thread, &thread->regs.data()[base]));
    Admin::contin(thread);
  }
  catch (UndefFailure& f){
    // printbt(thread->parent, f.message, thread);
    Admin::undef(thread, f.message);
  }
  catch (RequireFailure& f){
    waitFor(thread, origin, f.var);
  }
  catch (Failure& f){
    ASSERT(false);
  }
}

static inline void testNative(Thread thread)
NoTHROW() {
  Instr::Pointer origin = thread->pc;
  thread->pc++;
  int index = Data::readIndex(thread->pc);
  int base = Data::readIndex(thread->pc);
  try {
    thread->inten->schema->unit->nativePreds[index]->pred
                     (thread, &thread->regs.data()[base]);
    Admin::contin(thread);
  }
  catch (UnsatisfiedFailure&){
    Admin::failure(thread);
  }
  catch (UndefFailure& f){
    // printbt(thread->parent, f.message, thread);
    Admin::undef(thread, f.message);
  }
  catch (RequireFailure& f){
    waitFor(thread, origin, f.var);
  }
  catch (Failure& f){
    ASSERT(false);
  }
}

//----------------------------------------------------------------------------
// Function application

static inline void apply(Thread thread, Value fun, Value arg, 
			 int dest, Instr::Pointer at){

  fun = Data::resolveVars(fun);
  switch (fun->kind){
  case ValueData::OTHER:{
    // use virtual apply
    OtherData* dat = static_cast<OtherData*>(fun);
    try {
      thread->regs.assign(dest, dat->apply(thread->parent, arg));
      Admin::contin(thread);
    }
    catch (UndefFailure& f){
      // printbt(thread->parent, f.message, thread);
      Admin::undef(thread, f.message);
    }
    catch (RequireFailure& f){
      waitFor(thread, at, f.var);
    }
    catch (Failure& f){
      ASSERT(false);
    }
    break;
  }
  case ValueData::SET:
    apply(thread, at, static_cast<SetData*>(fun), arg, dest);
    break;
  default:
    ASSERT(false);
  }
}
      
static inline void apply(Thread const thread)
NoTHROW() {
  Instr::Pointer at = thread->pc;
  thread->pc++;
  int reg1 = Data::readIndex(thread->pc);
  int reg2 = Data::readIndex(thread->pc);
  int dest = Data::readIndex(thread->pc);
  apply(thread, thread->regs[reg1], 
	xfreeze(thread->regs[reg2]), dest, at);
}

static inline void applyGlobal(Thread const thread)
NoTHROW() {
  Instr::Pointer at = thread->pc;
  thread->pc++;
  int gindex = Data::readIndex(thread->pc);
  int reg2 = Data::readIndex(thread->pc);
  int dest = Data::readIndex(thread->pc);
  int vindex = thread->inten->schema->unit->globals[gindex]->varinx;
  apply(thread, thread->parent->machine->globals[vindex],
	xfreeze(thread->regs[reg2]), dest, at);
}



//----------------------------------------------------------------------------
// MKxxx Instructions


static inline void mkDeno(Thread const thread) NoTHROW() {
  thread->pc++;
  int index = Data::readIndex(thread->pc);
  int dest = Data::readIndex(thread->pc);
  thread->regs.assign(dest,
    new (GC) NativeDeno(
	 const_cast<char*>(thread->inten->schema->unit->denotations[index])));
  Admin::contin(thread);
}

static inline void mkTerm(Thread const thread)
NoTHROW() {
  thread->pc++;
  Constructor cons = 
    thread->inten->schema->unit->constructors[Data::readIndex(thread->pc)];
  int base = Data::readIndex(thread->pc);
  int dest = Data::readIndex(thread->pc);
  int arity = cons->arity;
  Value * args = new (GC) Value[arity];
  bool ground = true;
  for (int i = 0; i < arity; i++){
    args[i] = xfreeze(thread->regs[base++]);
    ground = ground && args[i]->ground;
  }
  thread->regs.assign(dest,
		      new (GC) TermData(ground,
					cons, const_cast<Value*>(args)));
  Admin::contin(thread);
}
  
static inline void mkVar(Thread const thread)
NoTHROW() {
  thread->pc++;
  int inx = Data::readIndex(thread->pc);
  int dest = Data::readIndex(thread->pc);
  thread->regs.assign(dest, xfreeze(thread->vars[inx]));
  Admin::contin(thread);
}
  
  
static inline void mkEmpty(Thread const thread)
NoTHROW() {
  thread->pc++;
  int dest = Data::readIndex(thread->pc);
  thread->regs.assign(dest, Data::emptySet);
  Admin::contin(thread);
}

static inline void mkUniv(Thread const thread)
NoTHROW() {
  thread->pc++;
  int dest = Data::readIndex(thread->pc);
  thread->regs.assign(dest, Data::univSet);
  Admin::contin(thread);
}
  
static inline void mkSingle(Thread const thread)
NoTHROW() {
  thread->pc++;
  int src = Data::readIndex(thread->pc);
  int dest = Data::readIndex(thread->pc);
  Value val = xfreeze(thread->regs[src]); 
  Value * extens = newGCArray<Value>(val);
  thread->regs.assign(dest, new (GC) SetData(val->ground, 1, extens, 0, 0)); 
  Admin::contin(thread);
}
  
static inline void mkInten(Thread const thread)
NoTHROW() {
  thread->pc++;
  int index = Data::readIndex(thread->pc);
  int base = Data::readIndex(thread->pc);
  int dest = Data::readIndex(thread->pc);
  Schema schema = 
    thread->inten->schema->unit->schemas[index];
  bool ground = true;
  int n = schema->paramcount;
  Value * params = new (GC) Value[n];
  for (int i = 0; i < n; i++){
    params[i] = xfreeze(thread->regs[base+i]);
    ground = ground && params[i]->ground;
  }
  Inten * intens = 
	 newGCArray<Inten>(new (GC) IntenData(schema, params));
  thread->regs.assign(dest, new (GC) SetData(ground, 0, 0, 1, intens)); 
  Admin::contin(thread);
}

static inline void mkOuterInten(Thread const thread)
NoTHROW() {
  thread->pc++;
  int index = Data::readIndex(thread->pc);
  int dest = Data::readIndex(thread->pc);
  Schema schema = 
    thread->inten->schema->unit->schemas[index];
  Inten * intens = 
    newGCArray<Inten>(new (GC) IntenData(schema, 0));
  thread->regs.assign(dest, new (GC) SetData(true, 0, 0, 1, intens));
  Admin::contin(thread);
}
  
//----------------------------------------------------------------------------
// UNION/ISECT Instructions


static inline void merge(Thread const thread)
NoTHROW() {
  thread->pc++;
  int s1 = Data::readIndex(thread->pc);
  int s2 = Data::readIndex(thread->pc);
  int d = Data::readIndex(thread->pc);
  SetData* set1 = Data::tryGetSet(thread->regs[s1]);
  SetData* set2 = Data::tryGetSet(thread->regs[s2]);
  if (set1 == 0 || set2 == 0){
    Admin::undef(thread, "not resovable as set (direct recursive equation)");
    // printbt(thread->parent, "undefined");
    return;
  }
  // CHECKME: freeze here doesn't work. Why?
  thread->regs.assign(d, Data::merge(freeze(set1), freeze(set2)));
  Admin::contin(thread);
}

static inline void join(Thread const thread)
NoTHROW() {
  thread->pc++;
  int s1 = Data::readIndex(thread->pc);
  int s2 = Data::readIndex(thread->pc);
  int d = Data::readIndex(thread->pc);
  SetData* set1 = Data::tryGetSet(thread->regs[s1]);
  SetData* set2 = Data::tryGetSet(thread->regs[s2]);
  if (set1 == 0 || set2 == 0){
    Admin::undef(thread, "not resovable as set (direct recursive equation)");
    // printbt(thread->parent, "undefined");
    return;
  }
  thread->regs.assign(d, Data::join(freeze(set1), freeze(set2)));
  Admin::contin(thread);
}
  
  

//----------------------------------------------------------------------------
// Dispatching

static inline void normal(Thread const thread) 
  THROW(Abort) {
  Goal goal = thread->parent;
  if (thread->dumpDepth < goal->choiceDepth){
    Admin::dumpThread(thread, thread->pc, thread->status);
  }
  switch (*thread->pc){
  case Instr::MOVE:
    move(thread);
    break;
  case Instr::LOAD:
    load(thread);
    break;
  case Instr::LOADPARAM:
    loadParam(thread);
    break;
  case Instr::LOADGLOBAL:
    loadGlobal(thread);
    break;
  case Instr::WAIT:
    wait(thread);
    break;
  case Instr::WAITGLOBAL:
    waitGlobal(thread);
    break;
  case Instr::WAITLOAD:
    waitLoad(thread);
    break;
  case Instr::WAITLOADPARAM:
    waitLoadParam(thread);
    break;
  case Instr::WAITLOADGLOBAL:
    waitLoadGlobal(thread);
    break;
  case Instr::STORE:
    store(thread);
    break;
  case Instr::STOREGLOBAL:
    storeGlobal(thread);
    break;
  case Instr::UNIFY:
    unify(thread);
    break;
  case Instr::MEMBER:
    member(SearchState::MEMBER, thread);
    break;
  case Instr::UNIQMEMBER:
    member(SearchState::UNIQMEMBER, thread);
    break;
  case Instr::HOM:
    hom(thread);
    break;
  case Instr::APPLY:
    apply(thread);
    break;
  case Instr::APPLYGLOBAL:
    applyGlobal(thread);
    break;
  case Instr::MKDENO:
    mkDeno(thread);
    break;
  case Instr::MKTERM:
    mkTerm(thread);
    break;
  case Instr::MKVAR:
    mkVar(thread);
    break;
  case Instr::MKEMPTY:
    mkEmpty(thread);
    break;
  case Instr::MKUNIV:
    mkUniv(thread);
    break;
  case Instr::MKSINGLE:
    mkSingle(thread);
    break;
  case Instr::MKINTEN:
    mkInten(thread);
    break;
  case Instr::MKOUTERINTEN:
    mkOuterInten(thread);
    break;
  case Instr::UNION:
    merge(thread);
    break;
  case Instr::ISECT:
    join(thread);
    break;
  case Instr::FAILURE:
    Admin::failure(thread);
    break;
  case Instr::SUCCESS:
    Admin::success(thread);
    break;
  case Instr::UNDEF:
    Admin::undef(thread);
    break;
  case Instr::CALLNATIVE:
    callNative(thread);
    break;
  case Instr::TESTNATIVE:
    testNative(thread);
    break;
  case Instr::DEPTHFIRST:
    depthFirst(thread);
    break;
  case Instr::GOTO:
    gotopc(thread);
    break;
  case Instr::SUBSET:
    subset(thread);
    break;
  case Instr::IF:
    ififnot(thread, false);
    break;
  case Instr::IFNOT:
    ififnot(thread, true);
    break;
  default:{
    int step = 0;
    *Session::debug << "invalid instr: ";
    printNext(*Session::debug, thread->pc, step);
    *Session::debug << iendl;
    Session::assertFailed("invalid instruction");
    }
  }
}

static inline void stepThread(Thread const thread)
THROW(Abort) {
  switch (thread->status){
  case ThreadData::NORMAL:
    normal(thread);
    break;
  case ThreadData::SEARCH:
    Session::assertFailed("trying to step on a waiting thread");
    break;
  case ThreadData::SUBRESO:
    subresocheck(thread);
    break;
  default:
    Session::assertFailed("invalid thread state");
  }
}


static inline bool selectSearch(Goal goal){

  DPRINT(iendl << "SELECT SEARCH ");
  
  // first find a searching thread in subresolutions
  bool hasSub = false;
  RingIterator<ThreadData> beg,end;
  Choice c = goal->choices.ptr();
  while (c != 0){
    beg = c->enriched.begin();
    end = c->enriched.end();
    while (beg != end){
      Thread t = &*beg++;
      if (t->status == ThreadData::SUBRESO){
	if (selectSearch(t->sub->subgoal.ptr())) return true;
	hasSub = true;
      }
    }
    c = c->parent;
  }
  beg = goal->threads.begin();
  end = goal->threads.end();
  while (beg != end){
    Thread t = &*beg++;
    if (t->status == ThreadData::SUBRESO){
      if (selectSearch(t->sub->subgoal.ptr())) return true;
      hasSub = true;
    }
  }
    
  // no searching thread in subresolution, try one of this goal
  Thread cand = 0;
  bool foundDet = false;
  beg = goal->searching.begin();
  end = goal->searching.end();
  while (beg != end){
    Thread t = &*beg++;
    XPRINT("CAND " << t << "; " << dec << t->age);
    int w = testSearch(t);
    if (w < 0){
      // residuated, skip
      XPRINT("... residuated");
    } else 
      switch (w){
      case 0:
	// complete failure of this goal
	XPRINT("... failed");
	t->schedule.remove();
	// CHECKME GcHeap::delForward(t->scheduleInfo);
	t->search.clear();
	Admin::failure(t);
	return true;
      case 1:
	XPRINT("... det");
	// deterministic step possible: commit it
	t->schedule.remove();
	// CHECKME GcHeap::delForward(t->scheduleInfo);
	t->status = ThreadData::NORMAL;
	try {
	  t->search->matches[0]->commit(goal, t);
	  t->search.clear();
	  Admin::contin(t);
	  foundDet = true;
	  // continue to find more of them
	}
	catch (UnequalFailure& f){
	  // complete failure of this goal
	  Admin::failure(t);
	  return true;
	}
	catch (Failure& f){
	  DPRINT(iendl << "undefined in member: " << t->constr->name);
	  Admin::undef(t);
	  return true;
	}
	break;
      default:
	if (!foundDet && cand == 0){
	  cand = t;
	  /*
	  if (cand == 0 || t->age - cand->age < 0){
	    cand = t;
	  }
	  */
	}
      }
  }
  if (foundDet){
    // we have recovered some deterministic steps
    XPRINT("NO CHOICE");
    return true;
  } else if (cand != 0) {
#ifdef ZAM_PROFILE
    cand->constr->profileSteps++;
    goal->machine->profileSteps++;
#endif
    if (false && hasSub){
      // we dont suppot a non-deterministic
      // search step as long as sub-resolutions exist since we cannot
      // dump them currently ...
      // brute-force: restart all sub-resolutions here!!!
      RingIterator<ThreadData> beg,end;
      Choice c = goal->choices.ptr();
      while (c != 0){
	beg = c->enriched.begin();
	end = c->enriched.end();
	while (beg != end){
	  Thread t = &*beg++;
	  if (t->status == ThreadData::SUBRESO){
	    XPRINT(iendl << "RESTART SUBRESO " << t);
	    Admin::kill(t->sub->subgoal);
	    t->pc = t->sub->origin;
	    t->sub.clear();
	    t->status = ThreadData::NORMAL;
	    t->schedule.remove();
	    // CHECKME GcHeap::delForward(t->scheduleInfo);
	    Admin::contin(t);
	  }
	}
	c = c->parent;
      }
      beg = goal->threads.begin();
      end = goal->threads.end();
      while (beg != end){
	Thread t = &*beg++;
	if (t->status == ThreadData::SUBRESO){
	  XPRINT(iendl << "RESTART SUBRESO " << t);
	  Admin::kill(t->sub->subgoal);
	  t->pc = t->sub->origin;
	  t->sub.clear();
	  t->status = ThreadData::NORMAL;
	  t->schedule.remove();
	  // CHECKME GcHeap::delForward(t->scheduleInfo);
	  Admin::contin(t);
	}
      }
    }

    // make cand's choice point
    cand->schedule.remove();
    XPRINT("CHOICE " << cand);
    // CHECKME GcHeap::delForward(cand->scheduleInfo);
    if (Session::doDPRINT()){
      DPRINT(iendl << "SEARCH STEP ");
      printThreadAt(*Session::debug, cand, cand->pc);
    }
    Goal goal = cand->parent;
    if (cand->dumpDepth < goal->choiceDepth){
      Admin::dumpThread(cand, cand->pc, ThreadData::SEARCH);
      // Admin::dumpThread(cand, cand->search->origin, ThreadData::NORMAL);
    }
    cand->status = ThreadData::NORMAL;
    Admin::makeChoice(cand->search->kind,
		      cand, 
		      cand->search->matchcount,
		      cand->search->matches);
    cand->search.clear();
    try {
      if (Admin::tryFirst(goal)){
	Admin::contin(cand);
      }
      else
	Admin::failure(cand);
    }
    catch (Failure& f){
      DPRINT(iendl << "undefined in member: " << cand->constr->name);
      Admin::undef(cand);
    }
    return true;
  } else
    // no search cand in this goal
    return false;
}
      
  
  

//----------------------------------------------------------------------------
// Initialization and execution step

Interp::Interp(int unitCount, Unit * units, 
	       int globCount, VarData** globals) {
  // create machine
  mach = new (GC) MachineData(unitCount, units, globCount, globals);
  Goal root = mach->root = new (GC) GoalData(0, mach);
  root->unif = 0;
  root->varcount = globCount; // FIXME ugly: needed to get globals dumped
  int i;
  for (i = 0; i < globCount; i++){
    globals[i]->goal = root;
  }
  
  // instantiate initialization schemas
  for (i = 0; i < mach->unitCount; i++){
    Unit u = mach->units[i];
    if (u->initSchemaIndex >= 0){
      Inten inten = new (GC) IntenData(u->schemas[u->initSchemaIndex], 0);
      Admin::spawnThreads(root, inten, Admin::instantiate(root, inten));
    }
  }

  // prepare for stepping
  target.assign(this, new (GC) SetTarget(this, 0, root));
}
  

bool Interp::possiblyMore() {
  return target->possiblyMore();
}

bool Interp::TermTarget::possiblyMore() {
  return false;
}

bool Interp::SeqTarget::possiblyMore() {
  return false;
}

bool Interp::SetTarget::possiblyMore() {
  Goal root = goal;
  if (root->choiceDepth > 0){
    return root->choices->mcurrent < root->choices->mcount;
  } else
    return false;
}
  

Interp::StepResult Interp::step(int count) {
  return target->step(count);
}

Interp::StepResult Interp::TermTarget::step(int count) {
  return NOMORE;
}

Interp::StepResult Interp::SeqTarget::step(int count) {
  return NOMORE;
}

Interp::StepResult Interp::SetTarget::step(int count) {
    
  Goal root = goal;
  count = stepCount+count;

  for (;;) {
    if (stepCount >= count)
      // done count steps and no solution yet
      return MORE;

    if (lastWasSolution){
      // backtrack
      try {
	if (!Admin::tryNext(root))
	  return NOMORE;
      }
      catch (Failure& f){
	printbt(root, "unification not decidable in toplevel goal");
	return UNDEF;
      }
      lastWasSolution = false;
    }
  
    // 1. try to schedule deterministic computations
    Thread next = interp->mach->schedule.pop();
    if (next != 0){
      // CHECKME GcHeap::delForward(next->scheduleInfo);
      if (Session::doTPRINT()){
	TPRINT(iendl << "STEP #" << dec << stepCount << " ");
	printThreadAt(*Session::debug, next, next->pc);
      }
      stepThread(next);
#ifdef ZAM_PROFILE
      next->constr->profileSteps++;
      interp->mach->profileSteps++;
#endif
      stepCount++;
      continue;
    }
    
    // 2. select the next SEARCH thread
    if (selectSearch(root)){
      stepCount++;
      continue;
    }

    break;
  } 

  DPRINT(iendl << "------- no more threads" << iendl);
  // no more threads to execute
  if (root->status == ThreadData::SUCCEEDED){
    if (Session::doDPRINT()){
      printtree(*Session::debug, *root);
    }
    // check zombies
    if (root->running == 0){
      // this is a solution
      solutionCount++;
      lastWasSolution = true;
      return SOLUTION;
    } else {
      // undefined 
      printbt(root, "unresolvable constraints in toplevel goal");
      return UNDEF;
    }
  }
  else if (root->status == ThreadData::UNDEFINED){
    printbt(root, "undefined in toplevel goal");
    return UNDEF;
  } else
    return NOMORE;
}
   

void Interp::printState(std::ostream& os){
  /*
  Goal root = target->goal;
  int oldInd = setPrintInd(0);
  os << iendl << "global variables" << ind;
  printGlobals(os, mach);
  if (Session::doDPRINT()){
    os << unind << iendl << "choices" << ind;
    printChoices(os, root, root->choices);
    os << unind;
  }
  */
}

long Interp::noOfSteps(){
#ifdef ZAM_PROFILE
  return mach->profileSteps;
#else
  return 0;
#endif
}

void Interp::printProfile(std::ostream& os){
#ifdef ZAM_PROFILE
  typedef std::list< std::pair<int,std::string> > CList;
  CList clist;
  for (int n = 0; n < mach->unitCount; n++){
    Unit u = mach->units[n];
    for (int i = 0; i < u->schemaCount; i++){
      Schema s = u->schemas[i];
      for (int j = 0; j < s->constrcount; j++){
		  clist.push_back(std::pair<int,std::string>(s->constrs[j]->profileSteps,
					 s->constrs[j]->name));
      }
    }
  }
  clist.sort();
  CList::const_iterator beg = clist.begin();
  CList::const_iterator end = clist.end();
  os << std::dec << mach->profileSteps << " total steps" << std::endl;
  while (beg != end){
    end--;
    if (end->first > 0){
      double perc = ((double)end->first * (double)100 / 
		     (double)mach->profileSteps);
      if (perc >= 0.001){
		  os << std::dec << perc << "%  (" << end->first  
	   << " steps) in " << end->second << std::endl;
      }
    }
  }
#else
  os << "ZAM not configured for profiling!";
#endif
}  
    
  

  

Value Interp::getBinding(char const* name){
  Value val = target->getBinding(name);
  return val;
}

Value Interp::TermTarget::getBinding(char const* name){
  Value b = previous->getBinding(name);
  if (b != 0){
    b = Data::resolveVars(b);
    switch (b->kind){
    case ValueData::TERM:{
      TermData* dat = static_cast<TermData*>(b);
      return dat->args[pos];
    }
    default:
      // fall through
      ;
    }
  }
  return 0;
}

Value Interp::SeqTarget::getBinding(char const* name){
  Value b = previous->getBinding(name);
  if (b != 0){
    b = Data::resolveVars(b);
    switch (b->kind){
    case ValueData::OTHER:{
      OtherData* dat = static_cast<OtherData*>(b);
      NativeSeq* s = dynamic_cast<NativeSeq*>(dat);
      if (s != 0){
	int i = pos;
	while (i > 0){
	  if (s->tail->kind == ValueData::OTHER){
	    dat = static_cast<OtherData*>(s->tail);
	    s = dynamic_cast<NativeSeq*>(dat);
	    if (s == 0) return 0;
	    i--;
	  } else
	    return 0;
	}
	return s->head;
      }
    }
    default:
      // fall through
      ;
    }
  }
  return 0;
}
 

Value Interp::SetTarget::getBinding(char const* name){
  VarData* const * tab;
  int count;
  if (previous == 0){
    // search for global
    tab = interp->mach->globals;
    count = interp->mach->globalCount;
  } else {
    // the most inner VarRecord ...
    VarRecord vars = goal->vars.ptr();
    while (vars->parent != 0) vars = vars->parent;
    tab = vars->vars;
    count = vars->inten->schema->varcount;
  }
  for (int i = 0; i < count; i++){
    VarData* v = tab[i];
    if (strcmp(v->name, name) == 0){
      if (v->binding != 0){
	return ffreeze(v->binding.ptr());
      } else 
	return v;
    }
  }
  return 0;
}

void Interp::printBinding(std::ostream& os, char const* name){
  Value v = getBinding(name);
  if (v == 0){
    os << "*UNDECLARED `" << name << "'*";
  } else
    printres(os,v);
}
  

char const * Interp::setSetTarget(SetData* const value){
  Goal root = new (GC) GoalData(0, mach);
  // CHECKME
  if (target != 0){
    root->varcount = target->getVarMark();
  }
  // { x | x in target }
  Inten inten = new (GC) IntenData(BuiltinUnit::theUnit->schemas
			      [BuiltinUnit::enumSchemaIndex],
			      newGCArray<Value>(value));
  VarRecord inst = Admin::instantiate(root, inten);
  root->unif = Admin::shift(inst->vars, inten->schema->binder);
  Admin::spawnThreads(root, inten, inst);

  target.assign(this, new (GC) SetTarget(this, target.ptr(), root));
  return inst->vars[0]->name;
}

void Interp::setTermTarget(int pos){
  target.assign(this, new (GC) TermTarget(this, target.ptr(), pos));
}

void Interp::setSeqTarget(int pos){
  target.assign(this, new (GC) SeqTarget(this, target.ptr(), pos));
}
  

void Interp::retSubTarget(){
  ASSERT(target->previous != 0);
  target->kill();
  target.assign(this, target->previous);
}

void Interp::SetTarget::kill(){
  DynPtr<GoalData> dptr(goal);
  Admin::kill(dptr);
}
