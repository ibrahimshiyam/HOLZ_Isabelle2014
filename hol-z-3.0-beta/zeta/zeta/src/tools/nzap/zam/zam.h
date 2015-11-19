// $Id: zam.h,v 1.50 2000/07/26 16:00:38 wg Exp $

#ifndef ZAM_H_INCLUDED
#define ZAM_H_INCLUDED

#include "zammem.h"

#include <map>
#include <vector>
#include <iostream>

#include "session.h"
#include "zamutil.h"


// --------------------------------------------------------------------------
// General Declarations and Forwards

struct GlobalData;
struct ConstructorData;
struct NativeFuncData;
struct NativePredData;
struct HomData;
struct UnitData;
struct ValueData;
struct VarData;
struct SetData;
struct ConstrData;
struct SchemaData;
struct IntenData;
struct ChoiceData;
struct ThreadData;
struct GoalData;
struct UnitData;
struct MachineData;
struct VarRecordData;
struct MatchElemData;
struct VarMatchElemData;
struct SubgoalMatchElemData;
struct MatchData;
struct MemoEntry;
struct MemoTab;


// pointers to structures which are usually persistent
typedef GlobalData * Global;
typedef ConstructorData * Constructor;
typedef NativeFuncData * NativeFunc;
typedef NativePredData * NativePred;
typedef HomData * Hom;
typedef SchemaData * Schema;
typedef UnitData * Unit;
typedef IntenData * Inten;
typedef ConstrData * Constr;
typedef VarRecordData * VarRecord;

// pointers to structures which are usually volatile
typedef ValueData * Value;
typedef ChoiceData* Choice;
typedef ThreadData* Thread;
typedef GoalData* Goal;
typedef MachineData* Machine;
typedef MatchData* Match;
typedef MatchElemData* MatchElem;




// --------------------------------------------------------------------------
// Instructions

struct Instr {

  enum Kind { LOAD = 1, 
	      LOADPARAM = 2,
	      WAIT = 3,
	      WAITLOAD = 4,
	      STORE = 5,
	      UNIFY = 6,
	      MEMBER = 7,
	      CALLNATIVE = 9,
	      TESTNATIVE = 10,
	      MKTERM = 11,
	      MKVAR = 12,
	      MKEMPTY = 13,
	      MKINTEN = 14,
	      MKSINGLE = 15,
	      UNION = 16,
	      ISECT = 17,
	      GOTO = 18,
	      IF = 19,
	      IFNOT = 20,
	      HOM = 21,
	      FAILURE = 22,
	      SUCCESS = 23,
	      DEPTHFIRST = 24,
	      UNDEF = 25,
	      MKOUTERINTEN = 26,
	      MKUNIV = 27,
	      MKNUMBER = 28,
	      LOADGLOBAL = 29,
	      LOADGENCONST = 30,
	      NOP = 31,
	      MKDENO = 32,
	      SUBSET = 33,
	      WAITLOADGLOBAL = 34,
	      WAITGLOBAL = 35,
	      STOREGLOBAL = 36,
	      APPLY = 37,
	      APPLYGLOBAL = 38,
	      UNIQMEMBER = 39,
	      MOVE = 40,
	      WAITLOADPARAM = 41,

	      INSTRNUMBER = 42
  };


  typedef unsigned char Unit;
  typedef Unit const * Pointer;

  static inline Kind index(unsigned int n) { // works only for unsigned < 128
    return static_cast<Kind>(n + 128);
  }

};



// --------------------------------------------------------------------------
// Exceptions thrown during execution of a ZAM execution step

enum Abort { FAILURE, UNDEFINED };


// --------------------------------------------------------------------------
// Exception thrown by unification or primitive operations 

struct Failure {
  virtual char const * describe() = 0; // necessary at least to let type
                                       // infos work
};

struct UnsatisfiedFailure : public Failure {
  char const* describe(){
    return "native predicate unsatisified";
  }
};

struct UnequalFailure : public Failure {
  int order;    // an ordering criterion ala strcmp
  inline UnequalFailure(int _order) : order(_order) {}
  char const* describe(){
    return "values not equal";
  }
};
  
/*
struct UncertainFailure : public virtual Failure {
  Value v1;
  Value v2;
  inline UncertainFailure(Value _v1, Value _v2) : v1(_v1), v2(_v2) {}
};
*/

struct RequireFailure : public Failure {
  VarData* var;
  inline RequireFailure(VarData* _var) : var(_var) {}
  char const* describe(){
    return "requiring variable";
  }
};
/*
struct CycleFailure : public Failure {
  VarData* var;
  inline CycleFailure(VarData* _var) : var(_var) {}
};
*/

struct UndefFailure : public Failure {
  char const * message; // a message describing this kind of failure
  inline UndefFailure(char const *msg) : message(msg) {}
  char const* describe(){
    return message;
  }
};



// --------------------------------------------------------------------------
// Constraints & Schemas

struct ConstrData {
  Schema schema;
  char const * name;
  int regcount;
  Instr::Pointer code;
#ifdef ZAM_PROFILE
  int profileSteps;
#endif

  ConstrData(Schema _schema, char const * _name, int _regcount, 
	     Instr::Pointer _code)
  : schema(_schema), name(_name), regcount(_regcount), code(_code)
#ifdef ZAM_PROFILE
    , profileSteps(0)
#endif
    {}
};

struct SchemaData {
  Unit unit;
  char const * name;
  int paramcount;
  char const * const * paramnames;
  int varcount;
  char const * const * varnames;
  Value binder;
  int constrcount;
  Constr const * constrs;
  inline SchemaData(Unit _unit,
		    char const * _name,
		    int _paramcount,
		    char const * const * _paramnames,
		    int _varcount,
		    char const * const * _varnames,
		    Value _binder,
		    int _constrcount,
		    Constr const * _constrs)
    : unit(_unit), name(_name), 
      paramcount(_paramcount), paramnames(_paramnames),
      varcount(_varcount), varnames(_varnames),
      binder(_binder), 
      constrcount(_constrcount), constrs(_constrs){}
};



// --------------------------------------------------------------------------
// Globals and  Constructors

struct GlobalData {
  char const *name;
  bool isExtern;
  int varinx;
  inline GlobalData(char const *_name, bool _isExtern, int _varinx)
    : name(_name), isExtern(_isExtern), varinx(_varinx)
  {}
};

struct ConstructorData {
  char const *name;
  int arity;
  inline ConstructorData(char const *_name, int _arity)
    : name(_name), arity(_arity)
  {}
};

// --------------------------------------------------------------------------
//  Natives and Homomorphisms


typedef Value (*NativeFuncType)(Thread, Value *) THROW(Failure);
struct NativeFuncData {
  char const *name;
  int arity;
  NativeFuncType funct;
  inline NativeFuncData(char const *_name, int _arity, NativeFuncType _funct)
    : name(_name), arity(_arity), funct(_funct)
  {}
};


typedef void (*NativePredType)(Thread, Value *) THROW(Failure);
struct NativePredData {
  char const *name;
  int arity;
  NativePredType pred;
  inline NativePredData(char const *_name, int _arity, NativePredType _pred)
    : name(_name), arity(_arity), pred(_pred)
  {}
};


struct HomStateData : public GcObject {
  enum Order { INORDER, OUTOFORDER };
  virtual bool next(Goal, Order, Value) THROW(Failure) = 0;
  virtual Value end(Goal) THROW(Failure) = 0;
};

typedef HomStateData* HomState;

typedef HomState (*HomStart)(Goal,SetData*) THROW(Failure);

struct HomData {
  char const *name;
  HomStart start;
  inline HomData(char const *_name, HomStart _start)
	 : name(_name), start(_start) {}
};


// --------------------------------------------------------------------------
// Units

struct UnitData {
  char const *name;
  int parentCount;
  char const *const *parents;
  int globalCount;
  Global const * globals;
  int constructorCount;
  Constructor const * constructors;
  int nativeFuncCount;
  NativeFunc const * nativeFuncs;
  int nativePredCount;
  NativePred const * nativePreds;
  int homCount;
  Hom const * homs;
  int denotationCount;
  char const *const *denotations;
  int initSchemaIndex;
  int schemaCount;
  Schema const * schemas;
  int codeSize;
  Instr::Pointer code;
  inline UnitData(char const * _name,
	   int _parentCount,
	   char const *const* _parents,
	   int _globalCount,
	   Global const * _globals,
	   int _constructorCount,
	   Constructor const * _constructors,
	   int _nativeFuncCount,
	   NativeFunc const * _nativeFuncs,
	   int _nativePredCount,
	   NativePred const * _nativePreds,
	   int _homCount,
	   Hom const * _homs,
	   int _denotationCount,
	   char const * const * _denotations,
	   int _initSchemaIndex,
	   int _schemaCount,
	   Schema const * _schemas,
	   int _codeSize,
	   Instr::Pointer _code)
  : name(_name),
    parentCount(_parentCount), parents(_parents),
    globalCount(_globalCount), globals(_globals),
    constructorCount(_constructorCount), constructors(_constructors),
    nativeFuncCount(_nativeFuncCount), nativeFuncs(_nativeFuncs),
    nativePredCount(_nativePredCount), nativePreds(_nativePreds),
    homCount(_homCount), homs(_homs),
    denotationCount(_denotationCount), denotations(_denotations),
    initSchemaIndex(_initSchemaIndex),
    schemaCount(_schemaCount), schemas(_schemas),
    codeSize(_codeSize), code(_code)  {}
				      
};


// --------------------------------------------------------------------------
// Values

struct ValueData : public GcObject {
  enum Kind { TERM, VAR, SET, OTHER } kind;
  bool ground;
  inline ValueData(Kind _kind, bool _ground)
    : kind(_kind), ground(_ground){
  }
};

struct TermData : public ValueData {
  Constructor cons;
  Value *args;
  inline TermData(bool _ground, Constructor  _cons, Value * _args) 
    : ValueData(TERM, _ground),cons(_cons), args(_args)
  {}
  inline TermData(GCPlacement, TermData& x) 
		 : ValueData(TERM,x.ground), cons(x.cons) {
    args = GcHeap::collectArr(cons->arity, x.args);
  }
  void gc(){
    GcHeap::gc(this);
  }
};


struct VarData : public ValueData {
  DynPtr<ValueData> binding;
  int const index;
  char const * name;
  Goal goal; 
  DynPtr<Ring<ThreadData> > waiting;
  bool visiting; 

  inline VarData(Goal _goal, int _index, char const * _name) : 
    ValueData(VAR, false), binding(0), index(_index), name(_name), goal(_goal),
    waiting(0) {
  }
  inline VarData(int _index, char const * _name) : 
    ValueData(VAR, false), binding(0), index(_index),
    name(_name), goal(0), waiting(0) {}
  VarData(VarData const &s) : 
                 ValueData(VAR, false), index(0), name(0), goal(0) {
    Session::assertFailed("copying a variable");
  }
  inline VarData(GCPlacement, VarData& x) : 
    ValueData(VAR,x.ground),
    index(x.index), name(x.name) {
    goal = GcHeap::collect(x.goal);
    if (x.binding == 0){
      waiting.collect(x.waiting);
    } else {
      binding.collect(x.binding);
      visiting = x.visiting;
    }
  }
  void gc(){
    GcHeap::gc(this);
  }

};


struct SetData : public ValueData {
  int ecount;
  Value * extens;
  int icount;
  Inten * intens;
  DynPtr<MemoTab> memo;
  inline SetData(bool _ground, int _ecount, Value * _extens, int _icount, 
		 Inten * _intens)
    : ValueData(SET, _ground), ecount(_ecount), extens(_extens), 
      icount(_icount), intens(_intens)
  {}

  inline SetData(GCPlacement, SetData& x) : 
    ValueData(SET,x.ground), ecount(x.ecount), icount(x.icount) {
    extens = GcHeap::collectArr(ecount, x.extens);
    intens = GcHeap::collectArr(icount, x.intens);
    memo.collect(x.memo);
  }
  void gc(){
    GcHeap::gc(this);
  }

};

struct UnifyMethod {
  virtual void uni(Value, Value) THROW(Failure) = 0;
  virtual void residuate(VarData* var, Value v1, Value v2) THROW(Failure) = 0;
  virtual void addSubgoal(Inten subgoal) THROW(Failure) = 0;
};

struct PrintMethod {
  virtual void print(std::ostream&, Value) = 0;
  virtual int maxPrintLeng() = 0;
};

struct FreezeInfo {
 private:
  typedef std::map<Value,Value> VisitMap;
  typedef std::vector<VarData*> VarList;
  typedef std::map<Value,VarList> CycleMap;
  VisitMap visited;
  CycleMap cycles;
 public:
  inline void markVisited(Value val, Value nval){
    visited.insert(VisitMap::value_type(val, nval));
  }
  inline Value getVisited(Value value){
    VisitMap::iterator i = visited.find(value);
    return i != visited.end() ? i->second : 0;
  }
  inline void markCycle(Value value, VarData* var){
    CycleMap::iterator i = cycles.find(value);
    if (i != cycles.end()){
      i->second.push_back(var);
    } else {
      VarList l;
      l.push_back(var);
      cycles.insert(CycleMap::value_type(var, l));
    }
  }
  inline void commitGround(Value value, bool ground){
    CycleMap::iterator i = cycles.find(value);
    if (i != cycles.end()){
      VarList::iterator b = i->second.begin();
      VarList::iterator e = i->second.end();
      while (b != e){
	(*b++)->ground = ground;
      }
    }
  }
};
  
struct OtherData : public ValueData {
  OtherData(bool _ground) : ValueData(OTHER, _ground) {}
  virtual void print(std::ostream& stream, PrintMethod*) = 0;
  virtual void unifyWith(Value value, UnifyMethod*) THROW(Failure) = 0;
  virtual bool cacheEq(Value value) = 0;
  virtual unsigned cacheHash() = 0;
  virtual Value apply(Goal goal, Value arg) THROW(Failure) = 0;
  virtual SetData* asSet() THROW(Abort) = 0;
  virtual Value freeze(FreezeInfo&) = 0;
  virtual VarData* findFree() = 0;
};

extern int compare(Value, Value);

// --------------------------------------------------------------------------
// Intensions

struct IntenData : GcObject {
  Schema schema;
  Value * params;
  inline IntenData(Schema _schema, Value * _params)
	   : schema(_schema), params(_params) {}
  inline IntenData(GCPlacement, IntenData& x) : schema(x.schema){
    params = GcHeap::collectArr(schema->paramcount, x.params);
  }
  void gc(){
    GcHeap::gc(this);
  }
};


// Ordering

struct IntenOrdering {
  bool operator()(const Inten v1, const Inten v2) const;
};


// --------------------------------------------------------------------------
// Memoizations

struct MemoApplTab : public Cache<ValueData,ValueData> {
  MemoApplTab(int size) : Cache<ValueData,ValueData>(size, 0.75){}
  MemoApplTab(GCPlacement, MemoApplTab& x) :
      Cache<ValueData,ValueData>(GC, x){}
  unsigned keyHash(Value v); 
  bool keyEquals(Value v1, Value v2); 
  Value keyValidate(Value v); 
  void gc() { GcHeap::gc(this); }
};

struct MemoHomTab : public Cache<HomData,ValueData> {
  MemoHomTab() : Cache<HomData,ValueData>(4, 0.75){}
  MemoHomTab(GCPlacement, MemoHomTab& x) :
      Cache<HomData,ValueData>(GC, x){}
  unsigned keyHash(Hom h); 
  bool keyEquals(Hom h1, Hom h2); 
  Hom keyValidate(Hom h); 
  void gc() { GcHeap::gc(this); }
};


struct MemoTab : public GcObject {
  MemoApplTab applTab;
  MemoHomTab homTab;
  enum { UNKNOWN, YES, NO } isEmpty;
  inline MemoTab(int _size) : applTab(_size), homTab(),
			      isEmpty(UNKNOWN)  {
  }
  inline MemoTab(GCPlacement, MemoTab& x) : 
    applTab(GC, x.applTab),
    homTab(GC, x.homTab),
    isEmpty(x.isEmpty) {
  }
  void gc() { GcHeap::gc(this); }
};

struct MemoInten : public GcObject {
  MemoTab* tab;
  Hom hom;
  Value arg;
  MemoInten(MemoTab* _tab, Hom _hom, Value _arg) 
	   : tab(_tab), hom(_hom), arg(_arg) {}
  MemoInten(GCPlacement, MemoInten& x) : hom(x.hom) {
    tab = GcHeap::collect(x.tab);
    arg = GcHeap::collect(x.arg);
  }
  void gc() { GcHeap::gc(this); }
};



// --------------------------------------------------------------------------
// Subresolutions

struct SubResoState : public GcObject {
  enum { HOM, BRANCHONNONEMPTY, BRANCHONEMPTY,
              FAILONEMPTY, FAILONNONEMPTY } kind;
  Instr::Pointer origin;
  Inten * intens; 
  int intencur;
  int intencount;
  DynPtr<GoalData> subgoal;
  DynPtr<HomStateData> hom;
  int destreg;
  MemoInten* memoInten;
  inline SubResoState() : origin(0), intens(0), intencur(0), 
                          destreg(0), memoInten(0){}
  inline SubResoState(GCPlacement, SubResoState& x)
   : kind(x.kind), origin(x.origin), intencur(x.intencur), 
                   intencount(x.intencount) {
    intens = GcHeap::collectArr(x.intencount, x.intens);
    subgoal.collect(x.subgoal);
    hom.collect(x.hom);
    destreg = x.destreg;
    memoInten = GcHeap::collect(x.memoInten);
  }
  void gc(){ GcHeap::gc(this); }
};

struct SearchState : public GcObject {
  enum Kind { MEMBER, UNIQMEMBER, NESTEDUNIQMEMBER } kind;
  Value elem;
  SetData* set;
  Match* matches;
  int matchcount;
  Instr::Pointer origin;
  inline SearchState() {}
  inline SearchState(GCPlacement, SearchState& x) :
    kind(x.kind), matchcount(x.matchcount), origin(x.origin){
    elem = GcHeap::collect(x.elem);
    set = GcHeap::collect(x.set);
    matches = GcHeap::collectArr(x.matchcount, x.matches);
  }
  void gc(){ GcHeap::gc(this); }
};


struct MatchData : GcObject {
  Inten inten;
  virtual VarData* required() = 0;
  virtual MatchData* refine(Goal goal) THROW(Failure) = 0;
  virtual void commit(Goal goal, Thread thread) THROW(Failure) = 0;
  virtual void print(std::ostream& os) = 0;
  virtual MatchData* copy() = 0;
};

  

struct ThreadData : GcObject {
  enum Status { NORMAL, SEARCH, SUBRESO,
		FAILED, SUCCEEDED, UNDEFINED, ZOMBIE,
		STATUSNUMBER } status;
  Goal parent;
  Choice choice;
  Inten inten;
  Constr constr;
  RLink<ThreadData> home;
  RLink<ThreadData> schedule;
  DynPtrArr<ValueData> regs;
  VarData** vars; 
  Instr::Pointer pc;
  int dumpDepth;
  int age;
  bool depthFirst;
  DynPtr<VarData> waitFor;
  char const* undefReason;
  DynPtr<SubResoState> sub;
  DynPtr<SearchState> search;
  inline ThreadData(Goal _parent, Inten _inten, Constr _constr,
		    DynPtrArr<ValueData> _regs, 
		    VarData** _vars, int _dumpDepth, 
		    Instr::Pointer _pc) :
    status(NORMAL), parent(_parent), choice(0), 
    inten(_inten), constr(_constr), 
    home(this), schedule(this), 
    regs(_regs), vars(_vars), pc(_pc), dumpDepth(_dumpDepth),
    age(0), depthFirst(false), waitFor(0), undefReason(0) {
  }
  inline ThreadData(GCPlacement, ThreadData& x) : 
    status(x.status), constr(x.constr), 
    home(this), schedule(this), 
    pc(x.pc), dumpDepth(x.dumpDepth), age(x.age), depthFirst(x.depthFirst),
    undefReason(x.undefReason){
    parent = GcHeap::collect(x.parent);
    choice = GcHeap::collect(x.choice);
    inten = GcHeap::collect(x.inten);
    GcHeap::collect(regs, x.regs);
    vars = GcHeap::collectArr(inten->schema->varcount, x.vars);
    waitFor.collect(x.waitFor);
    switch (x.status){
    case SUBRESO: 
      sub.collect(x.sub);
      break;
    case SEARCH:
      search.collect(x.search);
      break;
    default:
      ;
    }
  }
  void gc(){ GcHeap::gc(this); }
      
};


static inline int compare(ThreadData* t1, ThreadData* t2){
  return t1->age - t2->age;
}

// --------------------------------------------------------------------------
// Choices

struct VarDump : GcObject {
  VarDump* previous;
  VarData* var;
  inline VarDump(VarDump* _previous, VarData* _var)
	 : previous(_previous), var(_var){
  }
  inline VarDump(GCPlacement, VarDump& x){
    // never shared, never cyclic: iterative version
    VarDump* o = &x;
    VarDump* n = this;
    n->var = GcHeap::collect(o->var);
    while (o->previous != 0){
      o = o->previous;
      VarDump* n1 = new (GC)VarDump(0, GcHeap::collect(o->var));
      o->forward = n1;
      n->previous = n1;
      n = n1;
    }
    n->previous = 0;
  }
  void gc(){ GcHeap::gc(this); }
};

struct SearchDump {
  Match* matches;
  int matchcount;
};


struct ThreadDump : GcObject {
  ThreadDump* previous;
  Thread thread;
  Instr::Pointer pc;
  ThreadData::Status status;
  int dumpDepth;
  union {
    SearchDump search;
  };
  inline ThreadDump(ThreadDump* _previous,
		    Thread _thread,
		    Instr::Pointer _pc,
		    ThreadData::Status _status,
		    int _dumpDepth):
    previous(_previous), 
    thread(_thread), pc(_pc), status(_status), 
    dumpDepth(_dumpDepth) {
  }
  inline ThreadDump(ThreadDump* _previous,
		    Thread _thread,
		    Instr::Pointer _pc,
		    int _dumpDepth,
		    Match* _matches,
		    int _matchcount):
    previous(_previous), 
    thread(_thread), pc(_pc), status(ThreadData::SEARCH), 
    dumpDepth(_dumpDepth){
    search.matches = _matches;
    search.matchcount = _matchcount;
  }

  inline ThreadDump(GCPlacement, ThreadDump& x) :
    pc(x.pc), status(x.status), dumpDepth(x.dumpDepth) {
    previous = GcHeap::collect(x.previous);
    thread = GcHeap::collect(x.thread);
    switch(x.status){
    case ThreadData::SEARCH:
      search.matchcount = x.search.matchcount;
      search.matches = GcHeap::collectArr(x.search.matchcount, x.search.matches);
      break;
    default:
      ;
    }
  }
  void gc(){ GcHeap::gc(this); }

};



struct ChoiceData : GcObject {
  SearchState::Kind kind;
  Choice parent;
  Thread thread;
  Instr::Pointer pc;
  int dumpDepth;
  Match* matches;
  int mcount, mcurrent;
  DynPtr<VarDump> bound;
  DynPtr<ThreadDump> stepped;
  int varmark;
  Ring<ThreadData> enriched;
  Value cand;
  inline ChoiceData(SearchState::Kind _kind,
	     Choice _parent,
	     Thread _thread,
	     Instr::Pointer _pc,
	     int _dumpDepth,
	     int _varmark,
	     int _mcount,
	     Match* _matches)
  : kind(_kind),
    parent(_parent), thread(_thread), pc(_pc), dumpDepth(_dumpDepth),
    matches(_matches), mcount(_mcount), mcurrent(0),
    bound(0), stepped(0), varmark(_varmark), cand(0) {
  }
 private:
  inline void collect(ChoiceData& x){
    mcurrent = x.mcurrent;
    thread = GcHeap::collect(x.thread);
    matches = GcHeap::collectArr(x.mcount, x.matches);
    bound.collect(x.bound);
    stepped.collect(x.stepped);
    GcHeap::collect(enriched, x.enriched);
    cand = GcHeap::collect(x.cand);
  }
 public:
  inline ChoiceData(GCPlacement, ChoiceData& x) :
    kind(x.kind), pc(x.pc), dumpDepth(x.dumpDepth), mcount(x.mcount),
    mcurrent(x.mcurrent), varmark(x.varmark) {
    // iterative method to avoid stack overflow

    // first pass: gc shallow structure
    ChoiceData* o = &x;
    ChoiceData* n = this;
    ChoiceData* stop = 0;
    while (o->parent != 0){
      o = o->parent;
      if (o->forward != 0){
	// already visited
	stop = (ChoiceData*)o->forward;
	break;
      } else if (o->generation >= GcHeap::collectFrom){
	ChoiceData* n1 = new (GC) ChoiceData(o->kind,
					     0,
					     0,
					     o->pc,
					     o->dumpDepth,
					     o->varmark,
					     o->mcount,
					     0);
	o->forward = n1;
	n->parent = n1;
	n = n1;
      } else {
	// from an older generation
	stop = o;
	break;
      }
    }
    n->parent = stop;
    // second pass: gc subcomponents
    o = &x;
    n = this;
    while (n != stop){
      n->collect(*o);
      n = n->parent;
      o = o->parent;
    }
  }
  void gc(){ GcHeap::gc(this); }

};


// --------------------------------------------------------------------------
// Variable allocation records

struct VarRecordData : GcObject {
  VarRecord parent;
  Inten inten;
  int index;
  VarData** vars;
  inline VarRecordData(VarRecord _parent, Inten _inten, int _index,
		VarData** _vars)
	       : parent(_parent), inten(_inten), index(_index), vars(_vars){}
  inline VarRecordData(GCPlacement, VarRecordData& x) : index(x.index){
    VarRecordData* o = &x;
    VarRecordData* n = this;
    for (;;){
      n->inten = GcHeap::collect(o->inten);
      n->vars = GcHeap::collectArr(o->inten->schema->varcount, o->vars);
      if (o->parent != 0){
	o = o->parent;
	if (o->forward != 0){
	  // already collected
	  n->parent = static_cast<VarRecordData*>(o->forward);
	  break;
	} else if (o->generation >= GcHeap::collectFrom){
	  VarRecordData* n1 = new (GC)VarRecordData(0, 0, o->index, 0);
	  o->forward = n1;
	  n->parent = n1;
	  n = n1;
	} else {
	  // from an older generation
	  n->parent = o;
	  break;
	}
      } else {
	n->parent = 0;
	break;
      }
    }
  }

  void gc(){ GcHeap::gc(this); }

};

  


// --------------------------------------------------------------------------
// Goals


struct GoalData : GcObject {
  Thread parent;
  Machine machine;
  DynPtr<VarRecordData> vars;
  int varcount;
  DynPtr<ChoiceData> choices;
  int choiceDepth;
  Value unif;
  int running;
  ThreadData::Status status;
  Ring<ThreadData> threads;
  Ring<ThreadData> searching;
  inline GoalData(Thread _parent, Machine _machine) : 
    parent(_parent), machine(_machine),
    vars(0), varcount(0), choices(0), choiceDepth(0), unif(0), running(0),
    status(ThreadData::SUCCEEDED){ 
  }
  inline GoalData(GCPlacement, GoalData& x) :
    varcount(x.varcount), choiceDepth(x.choiceDepth), 
    running(x.running), status(x.status) {
    parent = GcHeap::collect(x.parent);
    machine = GcHeap::collect(x.machine);
    vars.collect(x.vars);
    choices.collect(x.choices);
    unif = GcHeap::collect(x.unif);
    GcHeap::collect(threads, x.threads);
    GcHeap::collect(searching, x.searching);
  }

  void gc(){ GcHeap::gc(this); }

};



// --------------------------------------------------------------------------
// Machines


/*
static const int PRIORITIES = 3;
static const int HIGH = 0;
static const int NORMAL = 1;
static const int LOW = 2;
*/

struct MachineData : GcObject {
  Ring<ThreadData> schedule; 
  Goal root;
  int globalCount;
  VarData** globals;
  int unitCount;
  Unit * units;
#ifdef ZAM_PROFILE
  int profileSteps;
#endif
  inline MachineData(int _unitCount, Unit * _units,
		     int _globalCount, VarData** _globals)
	     : globalCount(_globalCount), globals(_globals),
               unitCount(_unitCount), units(_units)
#ifdef ZAM_PROFILE
  , profileSteps(0)
#endif
    { }
  inline MachineData(GCPlacement, MachineData& x) :
    globalCount(x.globalCount), unitCount(x.unitCount), units(x.units){
#ifdef ZAM_PROFILE
    profileSteps = x.profileSteps;
#endif
    GcHeap::collect(schedule, x.schedule);
    /*
    for (int i = 0; i < PRIORITIES; i++){
      GcHeap::collect(schedule[i], x.schedule[i]);
    }
    */
    root = GcHeap::collect(x.root);
    globals = GcHeap::collectArr(x.globalCount,x.globals);
  }

  void gc(){ GcHeap::gc(this); }

};

  
#endif
