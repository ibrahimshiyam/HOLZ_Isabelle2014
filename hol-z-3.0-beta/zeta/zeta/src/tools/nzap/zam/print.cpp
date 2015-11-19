
// $Id: print.cpp,v 1.10 2000/07/26 16:00:38 wg Exp $

#include "print.h"
#include "data.h"

#include <algorithm>
#include <cstdlib>
#include <cstdio>
#include <strstream>

// TIDY UP

static int currindent = 0;  // ugly stuff .... a PRETTY PRINTER IS NEEDED

FmtIndEndl iendl;
FmtInd ind(1);
FmtUnInd unind(1);
FmtAsync async;
FmtEndAsync endasync;


std::ostream& operator<<(std::ostream& os, FmtIndEndl) {
  os << std::endl;
  for (int i = currindent; i > 0; i--)
    os << " ";
  return os;
}

std::ostream& operator<<(std::ostream& os, FmtInd ind) {
  currindent += ind.amount;
  return os;
}

std::ostream& operator<<(std::ostream& os, FmtUnInd uind) {
  currindent -= uind.amount;
  return os;
}

std::ostream& operator<<(std::ostream& os, FmtAsync&) {
  return os << indent(20) << iendl << "-----------------" << iendl;
}

std::ostream& operator<<(std::ostream& os, FmtEndAsync&) {
  return os << iendl << "-----------------" << unindent(20) << iendl;
}

int setPrintInd(int newind){
  int ind = currindent;
  currindent = newind;
  return ind;
}

void restorePrintInd(int oldind){
  currindent = oldind;
}



template <class A, class B>
std::ostream& operator<<(std::ostream& os, std::pair<A,B> const& x){
  return os << "(" << x.first << "," << x.second << ")";
}

template <class iterator>
static void const printlist(std::ostream& os, iterator beg, iterator end, 
			    char const * open = "",
			    char const * delim = ",",
			    char const * close = ""){
  os << open;
  bool first = true;
  while (beg != end){
    if (!first) os << delim;
    first = false;
    os << *beg++;
  }
  os << close;
}


template <class iterator>
static void const printlistref(std::ostream& os, iterator beg, iterator end, 
			       char const * open = "",
			       char const * delim = ",",
			       char const * close = ""){
  os << open;
  bool first = true;
  while (beg != end){
    if (!first) os << delim;
    first = false;
    os << std::hex << &*beg++;
  }
  os << close;
}

template <class iterator>
static void const printlistcont(std::ostream& os, iterator beg, iterator end, 
				char const * open = "",
				char const * delim = ",",
				char const * close = ""){
  os << open;
  bool first = true;
  while (beg != end){
    if (!first) os << delim;
    first = false;
    os << **beg++;
  }
  os << close;
}

template <class A>
static void const printtable(std::ostream& _os, A* _tab, int _size){
  for (int _i = 0; _i < _size; _i++){
    _os << iendl << _i << ": " << _tab[_i];
  }
}


// printing constraints, schemas, and the like

std::ostream& operator<<(std::ostream& os, Constr x){
  os << "constr(" << ind << iendl
     << x->name 
     << "," << iendl << "schema=" << x->schema->name
     << "," << iendl << "regcount=" << std::dec << x->regcount 
     << ", codeoffs=" << std::dec << x->code - x->schema->unit->code
     << unind << iendl << ")";
  return os;
}

std::ostream& operator<<(std::ostream& os, Schema x){
  os << "schema(" << ind << iendl 
     << "unit=" << x->unit->name 
     << ", name=" << x->name 
     << ", paramcount=" << std::dec << x->paramcount
     << "," << iendl << "binder=" << *x->binder 
     << "," << iendl << "varcount=" << std::dec << x->varcount;
  for (int i = 0; i < x->constrcount; i++){
    os << "," << iendl << x->constrs[i];
  }
  os << unind << iendl << ")";
  return os;
}

std::ostream& operator<<(std::ostream& os, Global x){
  os << "global("
     << x->name
     << ", " << x->isExtern
     << ", " << x->varinx
     << ")";
  return os;
}

std::ostream& operator<<(std::ostream& os, Constructor x){
  os << "constructor("
     << x->name
     << ", " << x->arity
     << ")";
  return os;
}

std::ostream& operator<<(std::ostream& os, NativeFunc x){
  os << "nativeFunc("
     << x->name
     << ", " << x->arity
     << ")";
  return os;
}

std::ostream& operator<<(std::ostream& os, NativePred x){
  os << "nativeFunc("
     << x->name
     << ", " << x->arity
     << ")";
  return os;
}

std::ostream& operator<<(std::ostream& os, Unit x){
  os << "Unit(" << ind << iendl 
     << x->name;
  os << iendl << "PARENTS";
  printtable(os, x->parents, x->parentCount);
  os << iendl << "GLOBALS";
  printtable(os, x->globals, x->globalCount);
  os << iendl << "CONSTRUCTORS";
  printtable(os, x->constructors, x->constructorCount);
  os << iendl << "NATIVEFUNCS";
  printtable(os, x->nativeFuncs, x->nativeFuncCount);
  os << iendl << "NATIVEPREDS";
  printtable(os, x->nativePreds, x->nativePredCount);
  os << iendl << "DENOTATIONS";
  printtable(os, x->denotations, x->denotationCount);
  os << iendl << "initSchemaIndex=" << x->initSchemaIndex;
  os << iendl << "SCHEMAS";
  printtable(os, x->schemas, x->schemaCount);
  os << iendl << "CODE";
  int step = 0;
  while (step < x->codeSize){
    os << iendl;
    printNext(os, x->code, step);
  }
  os << unind << ")" << iendl;
  return os;
}
  
    


// printing values, intensions, and the like

struct ValPrinter : public PrintMethod {

  int depth;
  int maxDepth;
  int maxLeng;
  ValPrinter() : depth(0), maxDepth(-1), maxLeng(-1) {}
  ValPrinter(int md, int ml) : depth(0), maxDepth(md), maxLeng(ml) {}

  virtual void printVar(std::ostream& os, VarData* var) = 0;

  void printList(std::ostream& os, int count, Value* vals,
		 char const* open="", char const* next=",",
		 char const* close=")");
  void printInten(std::ostream& os, Inten inten);
  void print(std::ostream& os, Value val);

  int maxPrintLeng(){
    return maxLeng;
  }
};

void ValPrinter::print(std::ostream& os, Value val){
  if (maxDepth >= 0 && depth >= maxDepth){
    os << "...";
    return;
  }
  // if (!val->ground) os << "!";
  switch (val->kind) {
  case ValueData::TERM: {
    TermData const * dat = static_cast<TermData const *>(val);
    char const * name = dat->cons->name;
    bool escape = false;
    int mixcnt = 0;
    while (*name){
      switch (*name){
      case '\\':
	escape = true;
	break;
      case '_':
	if (!escape) mixcnt++;
      default:
	escape = false;
      }
      name++;
    }
    if (mixcnt == dat->cons->arity){
      name = dat->cons->name;
      mixcnt = 0;
      escape = false;
      while (*name){
	switch (*name){
	case '\\':
	  escape = true;
	  os << *name;
	  break;
	case '_':
	  if (!escape){
	    depth++;
	    print(os, dat->args[mixcnt++]);
	    depth--;
	  } else {
	    os << *name;
	    escape = false;
	  }
	  break;
	default:
	  os << *name;
	  escape = false;
	}
	name++;
      }
    } else {
      os << dat->cons->name;
      depth++;
      printList(os, dat->cons->arity, dat->args, "(", ",", ")");
      depth--;
    }
    break;
  }
  case ValueData::VAR: {
    printVar(os, static_cast<VarData*>(val));
    break;
  }
  case ValueData::SET: {
    SetData const * dat = static_cast<SetData const*>(val);
    if (dat->ecount == 0 && dat->icount == 0){
      os << "{}";
      break;
    } 
    if (dat->ecount > 0){
      printList(os, dat->ecount, dat->extens, "{", ",", "}");
    } 
    if (dat->icount > 0){
      for (int i = 0; i < dat->icount; i++){
	if (i != 0 || dat->ecount > 0) os << "+";
	printInten(os, dat->intens[i]);
      }
    }
    break;
  }
  default: {
    OtherData * dat = static_cast<OtherData *>(val);
    dat->print(os,this);
  }
  }
}



void ValPrinter::printList(std::ostream& os, int count, Value* vals,
			   char const* open, char const* next,
			   char const* close){
  os << open;
  if (maxDepth < 0 || depth < maxDepth){
    int i;
    for (i = 0; i < count && (maxLeng < 0 || i < maxLeng); i++){
      if (i != 0) os << next;
      print(os, vals[i]);
    }
    if (i < count){
      if (i != 0) os << next;
      os << "...";
    }
  } else
    os << "...";
  os << close;
}

void ValPrinter::printInten(std::ostream& os, Inten inten){
  os << inten->schema->name;
  if (inten->schema->paramcount > 0){
    os << "(";
    depth++;
    if (maxDepth < 0 || depth < maxDepth){
      for (int i = 0; i < inten->schema->paramcount; i++){
	if (i != 0) os << ",";
	os << inten->schema->paramnames[i] << "=";
	print(os,inten->params[i]);
      }
    }
    else
      os << "...";
    depth--;
    os << ")";
  }
}

struct DebugPrinter : public ValPrinter {
  
  virtual void printVar(std::ostream& os, VarData* dat){
    os << dat->name << "#" << std::dec << dat->index;
    // os << dat->name << "#" << std::dec << dat->index << std::hex << dat;
    if (dat->binding == 0 || dat->visiting){
      if (dat->binding == 0 && dat->waiting != 0){
	os << " (wait=";
	printlistref(os, dat->waiting->begin(),dat->waiting->end());
	os << ")";	
      }
    } else {
      dat->visiting = true;
      os << "=" << *dat->binding;
      dat->visiting = false;
    }
  }
};

std::ostream& operator<<(std::ostream& os, ValueData & valr){
  DebugPrinter d;
  d.print(os, &valr);
  return os;
}


std::ostream& operator<<(std::ostream& os, IntenData & intenr){
  DebugPrinter d;
  d.printInten(os, &intenr);
  return os;
}
  

std::ostream& operator<<(std::ostream& os, MachineData & machr){
  MachineData const * mach = &machr;
  os << "SCHEDULE : ";
  printlistref(os, mach->schedule.begin(), mach->schedule.end());
  os << iendl;
  /*
  for (int i = 0; i < PRIORITIES; i++){
    os << "SCHEDULE " << std::dec << i << ": ";
    printlistref(os, mach->schedule[i].begin(), mach->schedule[i].end());
    os << iendl;
  }
  */
  //  os << *mach->root;
  return os;
}

std::ostream& operator<<(std::ostream& os, GoalData & goalr){
  GoalData * goal = &goalr;
  os << "GOAL: this = " << std::hex << goal
     << ", parent = " << std::hex << goal->parent 
     << ind << iendl;
  os << "THREADS: ";
  printlistref(os, goal->threads.begin(), goal->threads.end());
  os << iendl << "RUNNING: " << std::dec << goal->running;
  os << iendl << "SEARCHING: ";
  printlistref(os, goal->searching.begin(), goal->searching.end());
  os << iendl << "UNIF: ";
  if (goal->unif != 0) os << *goal->unif; else os << "0";
  os << iendl << "STATUS: " << goal->status;
  VarRecord v = goal->vars.ptr();
  while (v != 0){
    os << iendl << "----------- " << v->inten->schema->name;
    for (int i = 0; i < v->inten->schema->varcount; i++){
      os << iendl;
      os << "VAR " << *static_cast<Value>(v->vars[i]);
    }
    v = v->parent;
  }
  Choice c = goal->choices.ptr();
  int s = goal->choiceDepth;
  while (c != 0){
    os << iendl;
    os << "CHOICE #" << std::dec << (s--) << ": "  
       << ind << iendl << *c << unind;
    c = c->parent;
  }
  os << unind << iendl;
  return os;
}

std::ostream& operator<<(std::ostream& os, ThreadData * thread) {
  if (thread != 0){
	os << thread->constr->name << ": " << std::dec << thread->age;
  } else
    os << "thread 0??";
  return os;
}


std::ostream& operator<<(std::ostream& os, ThreadData & threadr){
  ThreadData * thread = &threadr;
  os << "THREAD ";
  printThreadAt(os, thread, thread->pc);
  os << ", parent: " << std::hex << thread->parent 
     << iendl;
  os << ind;
  os << "STATUS: " << thread->status << ", ";
  int i;
  for (i = 0; i < thread->inten->schema->varcount; i++){
    os << iendl 
       << "VAR " << *thread->vars[i];
  }
  for (i = 0; i < thread->constr->regcount; i++){
    if (thread->regs[i] != 0){
      os << iendl 
	 << "REG #" << std::dec << i << ": " << *thread->regs[i];
    }
  }
  switch (thread->status){
  case ThreadData::SEARCH:
    for (i = 0; i < thread->search->matchcount; i++){
      os << *thread->search->matches[i];
    }
    break;
  default:
    ;
  }
  os << unind << iendl;
  return os;
}

/*
std::ostream& operator<<(std::ostream& os, ThreadDump const & t) {
  os << t.thread << "( " << t.status << ", ";
  int step = 0;
  printNext(os, t.pc, step);
  os << ")";
  return os;
}
*/
    
std::ostream& operator<<(std::ostream& os, ChoiceData & dat){
  switch (dat.kind){
  case SearchState::MEMBER:
    os << "MEMBER ";
    break;
  case SearchState::UNIQMEMBER:
    os << "UNIQMEMBER (cand=";
    if (dat.cand != 0) os << *dat.cand; else os << "0";
    os << ") ";
    break;
  case SearchState::NESTEDUNIQMEMBER:
    os << "NESTEDUNIQMEMBER ";
    break;
  }
  os << "THREAD ";
  printThreadAt(os, dat.thread, dat.pc);
  os << iendl << "MATCHES " << std::dec << (dat.mcount-dat.mcurrent);
  for (int i = dat.mcurrent; i < dat.mcount; i++){
    os << *dat.matches[i];
  }
  VarDump* b = dat.bound.ptr();
  while (b != 0){
    os << iendl << "BOUND " << *b->var;
    b = b->previous;
  }
  ThreadDump* s = dat.stepped.ptr();
  while (s != 0){
    os << iendl << "DUMP ";
    printThreadAt(os, s->thread, s->pc);
    s = s->previous;
  }
  os << iendl << "ENR ";
  printlistref(os, dat.enriched.begin(), dat.enriched.end());
  return os;
}

std::ostream& operator<<(std::ostream& os, MatchData & dat){
  os << iendl;
  dat.print(os);
  // os << iendl << "MATCH ";
  /*
  if (dat.inten != 0) 
    os << dat.inten->schema->name;
  else
    os << " extensional";
  os << ind;
  MatchElem e = dat.elems;
  while (e != 0){
    os << iendl;
    if (e->kind == MatchElemData::VAR){
      MatchElemVarData* v = static_cast<MatchElemVarData*>(e);
      os << *v->var << " = " << *v->binding;
    } else {
      MatchElemSubgoalData* s = static_cast<MatchElemSubgoalData*>(e);
      os << "SUBGOAL " << *s->subgoal;
    }
    e = e->previous;
  }
  */
  os << unind;
  return os;
}
  

  
std::ostream& operator<<(std::ostream& os, ThreadData::Status status){
  switch (status){
  case ThreadData::NORMAL:
    os << "NORMAL";
    break;
  case ThreadData::SEARCH:
    os << "SEARCH";
    break;
  case ThreadData::SUBRESO:
    os << "SUBRESO";
    break;
  case ThreadData::FAILED:
    os << "FAILED";
    break;
  case ThreadData::SUCCEEDED:
    os << "SUCCEEDED";
    break;
  case ThreadData::UNDEFINED:
    os << "UNDEFINED";
    break;
  case ThreadData::ZOMBIE:
    os << "ZOMBIE";
    break;
  default:
    os << "????";
  }
  return os;
}


void printVar(std::ostream& os, VarData* v){
  os << iendl << v->name << "#" << std::dec << v->index;
  if (v->binding != 0){
    os << " = " << *Data::freeze(v->binding.ptr());
				// << "  (=" << *v->binding << ")";
  } else {
    os << " free";
  }
}
  

void printGlobals(std::ostream& os, Machine mach){
  for (int i = 0; i < mach->globalCount; i++){
    printVar(os, mach->globals[i]);
  }
}

void printChoices(std::ostream& os, Goal goal, Choice choice){
  if (choice == 0) return;
  printChoices(os, goal, choice->parent);
  os << iendl;
  // printThreadAt(os, choice->thread, choice->pc);
  Thread thread = choice->thread;
  os << thread->constr->name;
  os << ind;
  for (int i = 0; i < thread->inten->schema->varcount; i++){
    printVar(os, thread->vars[i]);
  }
  VarRecord r = goal->vars.ptr();
  while (r != 0 && r->index != choice->varmark)
    r = r->parent;
  if (r != 0){
    os << iendl << "choosen " << r->inten->schema->name << ind;
    for (int i = 0; i < r->inten->schema->varcount; i++){
      printVar(os, r->vars[i]);
    }
    os << unind;
  }
  os << unind;
} 


void printThreadVars(std::ostream& os, Thread thread){
  Goal goal = thread->parent;
  VarRecord r = goal->vars.ptr();
  while (r != 0 && r->vars != thread->vars) r = r->parent;
  if (r != 0){
    Schema s = r->inten->schema;
    for (int i = 0; i < s->varcount; i++){
      printVar(os, r->vars[i]);
    }
  }
}

void printThreadTrace(std::ostream& os, Thread thread){
  // search for initiator: 
  // 1. the thread of a choice which have enriched this thread, or
  // 2. the intension of the goal
  Goal goal = thread->parent;
  Choice choice = goal->choices.ptr();
  while (choice != 0){
    RingIterator<ThreadData> beg = choice->enriched.begin();
    RingIterator<ThreadData> end = choice->enriched.end();
    while (beg != end){
      if (&*beg == thread){
	// print the trace of the initiator
	printThreadTrace(os, choice->thread);
	// print our state
	os << iendl << "-> " << thread->constr->name << FmtInd(8);
	printThreadVars(os, thread);
	os << FmtUnInd(8);
	return;
      }
      beg++;
    }
    choice = choice->parent;
  }
  os << iendl << thread->constr->name << FmtInd(8);
  printThreadVars(os, thread);
  os << FmtUnInd(8);
}
    
void printThreadAt(std::ostream& os, Thread thread, Instr::Pointer pc){
  int step = pc - thread->inten->schema->unit->code;
  os << thread << " at ";
  printNext(os, pc - step, step, false);
}

static int readIndex(Instr::Pointer code, int& step){
  unsigned int s = 0;
  for (;;){
    unsigned int c = code[step++];
    if (c >= 128){
      return (s << 7) + (c % 128);
    } else
      s = (s << 7) + c;
  }
}


void printNext(std::ostream& os, Instr::Pointer code, int& step,
			   bool prstep)
{
  if (prstep){
    os << std::dec;
    os << step << ": ";
  }
  int oldStep = step;
  switch (code[step++]){
  case Instr::MKDENO:{
    int di = readIndex(code,step);
    int ri = readIndex(code,step);
    os << "MKDENO d" << di << " -> r" << ri;
    break;}
  case Instr::CALLNATIVE:{
    int ni = readIndex(code,step);
    int pi = readIndex(code,step);
    int ri = readIndex(code,step);
    os << "CALLNATIVE n" << ni << " r" << pi << " -> r" << ri;
    break;}
  case Instr::TESTNATIVE:{
    int ni = readIndex(code,step);
    int pi = readIndex(code,step);
    os << "TESTNATIVE p" << ni << " r" << pi;
    break;}
  case Instr::LOADGLOBAL:{
    int ci = readIndex(code,step);
    int ri = readIndex(code,step);
    os << "LOADGLOBAL g" << ci << " -> r" << ri;
    break;}
  case Instr::WAITLOADGLOBAL:{
    int ci = readIndex(code,step);
    int ri = readIndex(code,step);
    os << "WAITLOADGLOBAL g" << ci << " -> r" << ri;
    break;}
  case Instr::LOADPARAM:{
    int vi = readIndex(code,step);
    int ri = readIndex(code,step);
    os << "LOADPARAM p" << vi << " -> r" << ri;
    break;}
  case Instr::WAITLOADPARAM:{
    int vi = readIndex(code,step);
    int ri = readIndex(code,step);
    os << "WAITLOADPARAM p" << vi << " -> r" << ri;
    break;}
  case Instr::WAITGLOBAL:{
    int vi = readIndex(code,step);
    os << "WAITGLOBAL g" << vi;
    break;}
  case Instr::WAIT:{
    int vi = readIndex(code,step);
    os << "WAIT v" << vi;
    break;}
  case Instr::LOAD:{
    int vi = readIndex(code,step);
    int ri = readIndex(code,step);
    os << "LOAD v" << vi << " -> r" << ri;
    break;}
  case Instr::WAITLOAD:{
    int vi = readIndex(code,step);
    int ri = readIndex(code,step);
    os << "WAITLOAD v" << vi << " -> r" << ri;
    break;}
  case Instr::MOVE:{
    int ri1 = readIndex(code,step);
    int ri2 = readIndex(code,step);
    os << "MOVE r" << ri1 << " -> r" << ri2;
    break;}
  case Instr::STORE:{
    int ri = readIndex(code,step);
    int vi = readIndex(code,step);
    os << "STORE r" << ri << " -> v" << vi;
    break;}
  case Instr::STOREGLOBAL:{
    int ri = readIndex(code,step);
    int gi = readIndex(code,step);
    os << "STOREGLOBAL r" << ri << " -> g" << gi;
    break;}
  case Instr::UNIFY:{
    int ri1 = readIndex(code,step);
    int ri2 = readIndex(code,step);
    os << "UNIFY r" << ri1 << ", r" << ri2;
    break;}
  case Instr::MEMBER:{
    int ri1 = readIndex(code,step);
    int ri2 = readIndex(code,step);
    os << "MEMBER r" << ri1 << ", r" << ri2;
    break;}
  case Instr::UNIQMEMBER:{
    int ri1 = readIndex(code,step);
    int ri2 = readIndex(code,step);
    os << "UNIQMEMBER r" << ri1 << ", r" << ri2;
    break;}
  case Instr::SUBSET:{
    int ri1 = readIndex(code,step);
    int ri2 = readIndex(code,step);
    os << "SUBSET r" << ri1 << ", r" << ri2;
    break;}
  case Instr::MKTERM:{
    int ci = readIndex(code,step);
    int pi = readIndex(code,step);
    int ri = readIndex(code,step);
    os << "MKTERM c" << ci << ", r" << pi 
       << " -> r" << ri;
    break;}
  case Instr::MKSINGLE:{
    int ri1 = readIndex(code,step);
    int ri2 = readIndex(code,step);
    os << "MKSINGLE r" << ri1 << " -> r" << ri2;
    break;}
  case Instr::HOM:{
    int hi = readIndex(code,step);
    int ri1 = readIndex(code,step);
    int ri2 = readIndex(code,step);
    os << "HOM h" << hi << " r" << ri1 << " -> r" << ri2;
    break;}
  case Instr::MKEMPTY:{
    int ri = readIndex(code,step);
    os << "MKEMPTY -> r" << ri;
    break;}
  case Instr::MKUNIV:{
    int ri = readIndex(code,step);
    os << "MKUNIV -> r" << ri;
    break;}
  case Instr::ISECT:{
    int ri1 = readIndex(code,step);
    int ri2 = readIndex(code,step);
    int ri3 = readIndex(code,step);
    os << "ISECT r" << ri1 << ", r " << ri2 
       << " -> r" << ri3;
    break;}
  case Instr::UNION:{
    int ri1 = readIndex(code,step);
    int ri2 = readIndex(code,step);
    int ri3 = readIndex(code,step);
    os << "UNION r" << ri1 << ", r " << ri2 
       << " -> r" << ri3;
    break;}
  case Instr::APPLY:{
    int ri1 = readIndex(code,step);
    int ri2 = readIndex(code,step);
    int ri3 = readIndex(code,step);
    os << "APPLY r" << ri1 << ", r" << ri2 <<
      " -> r" << ri3;
    break;}
  case Instr::APPLYGLOBAL:{
    int gi1 = readIndex(code,step);
    int ri2 = readIndex(code,step);
    int ri3 = readIndex(code,step);
    os << "APPLYGLOBAL g" << gi1 << ", r" << ri2 <<
      " -> r" << ri3;
    break;}
  case Instr::IF:{
    int ri = readIndex(code,step);
    int ti = readIndex(code,step);
    os << "IF r" << ri << ", " << (step+ti);
    break;}
  case Instr::IFNOT:{
    int ri = readIndex(code,step);
    int ti = readIndex(code,step);
    os << "IFNOT r" << ri << ", " << (step+ti);
    break;}
  case Instr::GOTO:{
    int ti = readIndex(code,step);
    os << "GOTO " << (step+ti);
    break;}
  case Instr::MKINTEN:{
    int ii = readIndex(code,step);
    int pi = readIndex(code,step);
    int ri = readIndex(code,step);
    os << "MKINTEN s" << ii <<
      ", r" << pi << " -> r" << ri;
    break;}
  case Instr::MKOUTERINTEN:{
    int ii = readIndex(code,step);
    int ri = readIndex(code,step);
    os << "MKOUTERINTEN s" << ii << " -> r" << ri;
    break;}
  case Instr::FAILURE:{
    os << "FAILURE";
    break;}
  case Instr::SUCCESS:{
    os << "SUCCESS";
    break;}
  case Instr::DEPTHFIRST:{
    os << "DEPTHFIRST";
    break;}
  default:
    os << "??? " << (int)code[oldStep];
  }
}
  

void printtree(std::ostream& os, GoalData & goal){
  os << goal;
  /*
  RingIterator<ThreadData> beg = goal.running.begin();
  RingIterator<ThreadData> end = goal.running.end();
  os << ind;
  while (beg != end){
    Thread thr = &*beg++;
    os << iendl << *thr;
    Goal sub = 0;
    if (thr->status == ThreadData::SUBRESO){
      sub = thr->sub.subgoal;
    }
    if (sub != 0){
      os << ind << iendl;
      printtree(os, *sub);
      os << unind;
    }
  }
  os << unind << iendl;
  */
}

// -------------------------------------------------------------------------
// the backtrace printer


struct BacktracePrinter : public ValPrinter {

  BacktracePrinter(int depth, int leng) : ValPrinter(depth, leng) {}
  BacktracePrinter() : ValPrinter(2, 2) {}

  std::map<VarData*,char const*> names;

  char const* getName(VarData* var){
    std::map<VarData*,char const*>::iterator i = names.find(var);
    if (i != names.end()) return i->second;
    char const * name = var->name;
    i = names.begin();
    while (i != names.end()){
      if (strcmp(i->second, name) == 0){
	// clash: use a variant of name
	int n = strlen(name);
	char* newname = new (GC) char[n+2];
	std::uninitialized_copy(name, name+n, newname);
	newname[n] = '~';
	newname[n+1] = 0;
	name = newname;
	i = names.begin();
      } else 
	i++;
    }
    names.insert(std::map<VarData*,char const*>::value_type(var, name));
    return name;
  }

  void printVar(std::ostream& os, VarData* var){
    if (var->binding == 0 || var->visiting){
      os << getName(var);
    } else {
      var->visiting = true;
      print(os, var->binding.ptr());
      var->visiting = false;
    }
  }

  void printbtvars(std::ostream& os, int count, VarData** vars){
    for (int i = 0; i < count; i++){
      VarData* var = vars[i];
      os << iendl << getName(var);
      if (var->binding != 0){
	os << " = ";
	print(os, var->binding.ptr());
      } else {
	os << " unbound";
      }
    }
  }

  void printbtparams(std::ostream& os, int count, 
		     char const * const * names,
		     Value * vals){
    for (int i = 0; i < count; i++){
      os << iendl << names[i] << " = ";
      print(os, vals[i]);
    }
  }


  void printbtgoal(std::ostream& os, Goal goal);

  void printbtthreads(std::ostream& os, char* msg, DynArray<Thread>& ts){
    bool first = true;
    for (int i = 0; i < ts.length(); i++){
      Thread t = ts[i];
      if (t->waitFor != 0){
	if (first){ os << iendl << msg << ind; }
	first = false;
	os << iendl << t->constr->name << " waiting for variable ";
	print(os, t->waitFor.ptr());
      } else if (t->undefReason != 0){
	if (first){ os << iendl << msg << ind; }
	first = false;
	os << iendl << t->constr->name << " undefined: " 
	   << iendl << " " << t->undefReason;
	if (t->sub != 0)
	  printbtgoal(os, t->sub->subgoal.ptr());
      } else {
	switch (t->status){
	case ThreadData::SEARCH:
	  if (first){ os << iendl << msg << ind; }
	  first = false;
	  os << iendl << t->constr->name << " suspended for search";
	  break;
	case ThreadData::SUBRESO:
	  if (first){ os << iendl << msg << ind; }
	  first = false;
	  os << iendl << t->constr->name << " waiting for subgoal";
	  printbtgoal(os, t->sub->subgoal.ptr());
	  break;
	case ThreadData::UNDEFINED:
	  if (first){ os << iendl << msg << ind; }
	  first = false;
	  os << iendl << t->constr->name << " undefined: " 
	     << iendl << " " << t->undefReason;
	  if (t->sub != 0)
	    printbtgoal(os, t->sub->subgoal.ptr());
	  break;
	default:
	  ;
	}
      }
    }
    if (!first) os << unind;
  }

};

typedef std::map<Inten,DynArray<Thread> > IntenMap;

static void addThreads(IntenMap& hanging, Ring<ThreadData>& r){
  RingIterator<ThreadData> beg = r.begin();
  RingIterator<ThreadData> end = r.end();
  while (beg != end){
    Thread t = &*beg;
    if (t->waitFor != 0
	|| t->status == ThreadData::SUBRESO
	|| t->status == ThreadData::SEARCH
	|| t->status == ThreadData::UNDEFINED){
      IntenMap::iterator i = hanging.find(t->inten);
      if (i != hanging.end()){
	i->second.push(t);
      } else {
	DynArray<Thread> ts;
	ts.push(t);
	hanging.insert(IntenMap::value_type(t->inten, ts));
      }
    }
    beg++; 
  }
}


void BacktracePrinter::printbtgoal(std::ostream& os, Goal goal){
  // identify hanging threads factorized by their intensions
  IntenMap hanging;
  addThreads(hanging, goal->threads);
  Choice c = goal->choices.ptr();
  while (c != 0){
    addThreads(hanging, c->enriched);
    c = c->parent;
  }
  if (hanging.empty()) return;
  os << " {" << ind << ind;
  // print the threads along the variable instantiation order
  VarRecord v = goal->vars.ptr();
  while (v != 0){
    Choice c = goal->choices.ptr();
    while (c != 0 && c->varmark != v->index){
      c = c->parent;
    }
    IntenMap::iterator i = hanging.find(v->inten);
    if (i != hanging.end()){
      os << iendl << "resolving " << v->inten->schema->name;
      if (c != 0){
	os << iendl << "as a choice of " << c->thread->constr->name;
      }
      if (v->inten->schema->paramcount > 0){
	os << iendl << "with parameters:" << ind;
	printbtparams(os, v->inten->schema->paramcount,
		      v->inten->schema->paramnames,
		      v->inten->params);
	os << unind;
      }
      if (v->inten->schema->varcount > 0){
	os << iendl << "with variables:" << ind;
	printbtvars(os, v->inten->schema->varcount, v->vars);
	os << unind;
      }
      printbtthreads(os, "unresolved constraints:", i->second);
    }
    v = v->parent;
  }
  /*
  if (goal->parent != 0){
    os << iendl << "this was a subresolution invoked from " 
       << goal->parent->constr->name;
  }
  */
  os << unind << unind << iendl << "}";
}

void printbt(Goal startgoal, const char* message, Thread thread){
  Session::errors->receive("generating backtrace ...");
  std::ostrstream os;
  Goal goal = startgoal;
  BacktracePrinter prn;
  currindent = 0;
  os << message;
  if (thread != 0)
    os << " in " << thread->constr->name;
  do {
    prn.printbtgoal(os, goal);
    if (goal->parent != 0){
      //<< endl << "  continuing ...";
      // goal = goal->parent->parent;
      break;
    } else 
      break;
  } while (true);
  if (false && startgoal->parent == 0){
    os << iendl << "global variables" << ind;
    prn.printbtvars(os, goal->machine->globalCount, goal->machine->globals);
    os << unind;
  }
  os << std::ends;
  Session::errors->receive(os.str());
}

void printres(std::ostream& os, Value val){
  BacktracePrinter prn(-1,-1);
  prn.print(os, val);
}

// eof

