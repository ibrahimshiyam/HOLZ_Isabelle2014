// $Id: admin.h,v 1.10 2000/07/03 06:59:28 wg Exp $

#ifndef ADMIN_H_INCLUDED
#define ADMIN_H_INCLUDED

#include "zam.h"
#include "zamutil.h"


struct Admin {

  // check if val contains any free variables wrt goal
  // throw UNDEFINED if so
  static void checkFreeVars(Goal goal, Value val) THROW(Abort);

  // push a record for the intensions variables
  static VarRecord instantiate(Goal goal, Inten inten) NoTHROW();

  // release variable stack
  static void release(Goal goal, int mark);

  // shift a binder of a schema according to the variable table
  static Value shift(VarData** tab, Value binder);


  // commit a match
  // static void commitMatch(Goal goal, MatchData& match) THROW(UnifyFailure);


  // spawn threads of intension
  static void spawnThreads(Goal goal, Inten inten, VarRecord vrec,
			   Thread creator=0) NoTHROW();

  // dump thread status
  static void dumpThread(Thread thread, Instr::Pointer at,
			 ThreadData::Status status); 

  // return overall status of goals threads
  static ThreadData::Status status(Goal const goal);

  // make a choice point
  static ChoiceData& makeChoice(SearchState::Kind kind,
				Thread const thread,
				int matchcount, Match* matchdata)
			       NoTHROW();

  // try the first of current choice
  static bool tryFirst(Goal const goal) THROW(Failure);


  // (obsolote) tell wether we must try more
  static bool inline mustTryMore(Goal goal){
    Choice c = goal->choices.ptr();
    return c != 0 && (c->kind == SearchState::UNIQMEMBER ||
		      c->kind == SearchState::NESTEDUNIQMEMBER);
  }

  // try the next of current choice
  static bool tryNext(Goal goal) THROW(Failure);


  // unbind according to binding dumps (clearing dump anchor)
  static inline void reset(Goal const goal, DynPtr<VarDump>& dump){
    while (dump != 0){
      dump->var->binding.clear();
      dump->var->waiting.clear();
      dump.assign(goal, dump->previous);
    }
  }

  // reset according to thread dumps (clearing dump anchor)
  static void reset(Goal const goal, DynPtr<ThreadDump>& dump);

  // kill a goal and its threads
  static void kill(DynPtr<GoalData>& goal);

  // kill a thread and its subgoals
  static void kill(Thread thread);

  // kill the threads in a ring (clearing the ring)
  static inline void kill(Ring<ThreadData>& threads) {
    while (!threads.empty()){
      kill(threads.pop());
    }
  }

  // let the thread fail
  static void failure(Thread thread) NoTHROW();

  // let the thread succeed
  static void success(Thread thread) NoTHROW();

  // let the thread be undefined
  static void undef(Thread thread, char const* reason="undefined") NoTHROW();

  // let the thread continue
  static inline void contin(Thread thread) NoTHROW() {
    // tail optimizations
    switch (thread->status){
    case ThreadData::NORMAL:
      switch (*thread->pc){
      case Instr::SUCCESS:
	success(thread);
	return;
      case Instr::FAILURE:
	failure(thread);
	return;
      default:
	;
      }
    default:
      ;
    }
    Machine mach = thread->parent->machine;
    mach->schedule.enqueue(mach, thread->schedule);
  }

  static inline void search(Thread thread) NoTHROW() {
    Goal goal = thread->parent;
    goal->searching.enqueue(goal, thread->schedule);
  }
    
  
};


#endif
