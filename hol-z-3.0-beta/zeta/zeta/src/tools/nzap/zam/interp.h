// $Id: interp.h,v 1.16 2000/06/12 18:30:10 wg Exp $

#ifndef INTERP_H_INCLUDED
#define INTERP_H_INCLUDED

#include "zam.h"

#include "session.h"
#include "loader.h"

struct Interp : GcObject {

  enum StepResult { SOLUTION, MORE, NOMORE, UNDEF }; 
  
  struct Target : GcObject {
    enum Kind { SET, SEQ, TERM } kind;
    Target* previous;
    Interp* interp;
    Target(Kind _kind, Interp* _interp, Target* _previous) :
      kind(_kind), previous(_previous), interp(_interp){}

    virtual bool possiblyMore() = 0;
    virtual Value getBinding(char const * name) = 0;
    virtual StepResult step(int count) = 0;
    virtual void kill() {}
    virtual int getVarMark() = 0;

  };
    
  struct SetTarget : Target {
    Goal goal;
    int solutionCount;
    int stepCount;
    bool lastWasSolution;
    SetTarget(Interp* _interp, Target* _previous, Goal _goal):
      Target(SET, _interp, _previous), goal(_goal),
      solutionCount(0), stepCount(0), lastWasSolution(false){}
    inline SetTarget(GCPlacement, SetTarget& x) :
      Target(SET, 0, 0), solutionCount(x.solutionCount), 
      stepCount(x.stepCount),
      lastWasSolution(x.lastWasSolution){
      interp = GcHeap::collect(x.interp);
      previous = GcHeap::collect(x.previous);
      goal = GcHeap::collect(x.goal);
    }
    void gc(){ GcHeap::gc(this); }
    bool possiblyMore();
    Value getBinding(char const * name);
    StepResult step(int count);
    void kill();
    int getVarMark() { return goal->varcount; }
  };


  struct TermTarget : Target {
    int pos;
    TermTarget(Interp* _interp,
	       Target* _previous, int _pos):
      Target(TERM, _interp, _previous),  pos(_pos) {}
    inline TermTarget(GCPlacement, TermTarget& x) :
      Target(TERM, 0, 0), pos(x.pos) {
      interp = GcHeap::collect(x.interp);
      previous = GcHeap::collect(x.previous);
      // term = GcHeap::collect(x.term);
    }
    void gc(){ GcHeap::gc(this); }
    bool possiblyMore();
    Value getBinding(char const * name);
    StepResult step(int count);
    int getVarMark() { return previous->getVarMark(); }
  };

  struct SeqTarget : Target {
    int pos;
    SeqTarget(Interp* _interp,
	      Target* _previous, int _pos):
      Target(TERM, _interp, _previous), pos(_pos) {}
    inline SeqTarget(GCPlacement, SeqTarget& x) :
      Target(TERM, 0, 0), pos(x.pos) {
      interp = GcHeap::collect(x.interp);
      previous = GcHeap::collect(x.previous);
    }
    void gc(){ GcHeap::gc(this); }
    bool possiblyMore();
    Value getBinding(char const * name);
    StepResult step(int count);
    int getVarMark() { return previous->getVarMark(); }
  };



  Machine mach;
  DynPtr<Target> target;


  Interp(int unitCount, Unit * units, 
	 int globCount, VarData** globals);

  Interp(GCPlacement, Interp& x){
    mach = GcHeap::collect(x.mach);
    target.collect(x.target);
  }

  void gc(){ GcHeap::gc(this); }
  
  void printState(std::ostream& os);

  StepResult step(int count);
  bool possiblyMore();
  Value getBinding(char const * name);
  void printBinding(std::ostream& os, char const * name);
  char const * setSetTarget(SetData* value);
  void setTermTarget(int pos);
  void setSeqTarget(int pos);
  void retSubTarget();
  void printProfile(std::ostream& os);
  long noOfSteps();

  /*
  int inline noOfSteps(){
    switch (target->kind){
    case Target::SET:
      return static_cast<SetTarget*>(target.ptr())->stepCount;
    default:
      return 0;
    }
  }
  */

  int inline noOfSolutions(){
    switch (target->kind){
    case Target::SET:
      return static_cast<SetTarget*>(target.ptr())->solutionCount;
    default:
      return 0;
    }
  }


};

#endif
