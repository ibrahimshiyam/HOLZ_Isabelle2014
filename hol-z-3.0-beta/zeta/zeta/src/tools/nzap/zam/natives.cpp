// $Id: natives.cpp,v 1.18 2000/07/26 13:39:14 wg Exp $

#include <iostream>
#include <strstream>
#include <fstream>
#include <typeinfo>
#include <cstring>
#include <cstdlib>

#include "natives.h"
#include "data.h"
#include "admin.h"
#include "unify.h"


// --------------------------------------------------------------------------
// Denotation Value Type


static inline NativeDeno * getNativeDeno(Value val){
  do {
    switch (val->kind){
    case ValueData::VAR:{
      VarData *dat = static_cast<VarData*>(val);
      ASSERT(dat->binding != 0); // we dont handle flex arguments
      val = dat->binding.ptr();
      continue;
    }
    case ValueData::OTHER:
      return static_cast<NativeDeno *>(val);
    default:
      ASSERT(false);
    }
  } while (true);
}


void NativeDeno::unifyWith(Value other, UnifyMethod*) {
  int c = strcmp(val, getNativeDeno(other)->val);
  if (c != 0)
    throw UnequalFailure(c);
}

void NativeDeno::print(std::ostream& os, PrintMethod*) {
  char const * s = val;
  os << "\"";
  while (*s != 0){
    switch (*s){
    case '\\': case '"':
      os << '\\' << *s;
      break;
    case '\n':
      os << "\\n";
      break;
    case '\r':
      os << "\\r";
      break;
    case '\b':
      os << "\\b";
      break;
    case '\t':
      os << "\\t";
      break;
    case '\f':
      os << "\\f";
      break;
    default:
      os << *s;
    }
    s++;
  }
  os << "\"";
}

SetData* NativeDeno::asSet(){
  ASSERT(false);
  return 0;
}
  
Value NativeDeno::apply(Goal, Value){
  ASSERT(false);
  return 0;
}
  
Value NativeDeno::freeze(FreezeInfo& ){
  return this;
}
  
VarData* NativeDeno::findFree(){
  return 0;
}

bool NativeDeno::cacheEq(Value v){
  NativeDeno* d = dynamic_cast<NativeDeno*>(v);
  if (d != 0)
    return strcmp(val, d->val) == 0;
  else
    return false;
}

unsigned NativeDeno::cacheHash(){
  return 0;
}


static void registerDenos(Loader& loader){
}

// --------------------------------------------------------------------------
// Number Value Type

static inline NativeNum const * getNativeNum(ValueData* val){
  do {
    switch (val->kind){
    case ValueData::VAR: {
      VarData *dat = static_cast<VarData*>(val);
      // CHECKME
      if (dat->binding == 0)
	throw RequireFailure(dat);
      val = dat->binding.ptr();
      continue;
    }
    case ValueData::OTHER:
      return static_cast<NativeNum const *>(val);
    default:
      ASSERT(false);
    }
  } while (true);
}


void NativeNum::unifyWith(Value other, UnifyMethod*) {
  int c = val - getNativeNum(other)->val;
  if (c != 0)
    throw UnequalFailure(c);
}

void NativeNum::print(std::ostream& os, PrintMethod*) {
  os << val;
}

SetData* NativeNum::asSet(){
  ASSERT(false);
  return 0;
}
  
Value NativeNum::apply(Goal, Value){
  ASSERT(false);
  return 0;
}

Value NativeNum::freeze(FreezeInfo& ){
  return this;
}
  
VarData* NativeNum::findFree(){
  return 0;
}

bool NativeNum::cacheEq(Value v){
  NativeNum* d = dynamic_cast<NativeNum*>(v);
  if (d != 0)
    return val == d->val;
  else
    return false;
}

unsigned NativeNum::cacheHash(){
  return (unsigned)val;
}

Value static makeNumber(Thread thread, Value* args) {
  NativeDeno const * deno = getNativeDeno(args[0]);
  return new (GC) NativeNum(atol(deno->val));
}
  

Value static add(Thread thread, Value* args) {
  NativeNum const * d1 = getNativeNum(args[0]);
  NativeNum const * d2 = getNativeNum(args[1]);
  return new (GC) NativeNum(d1->val + d2->val);
}

Value static sub(Thread thread, Value* args) {
  NativeNum const * d1 = getNativeNum(args[0]);
  NativeNum const * d2 = getNativeNum(args[1]);
  return new (GC) NativeNum(d1->val - d2->val);
}

Value static mul(Thread thread, Value* args) {
  NativeNum const * d1 = getNativeNum(args[0]);
  NativeNum const * d2 = getNativeNum(args[1]);
  return new (GC) NativeNum(d1->val * d2->val);
}

Value static div(Thread thread, Value* args) {
  NativeNum const * d1 = getNativeNum(args[0]);
  NativeNum const * d2 = getNativeNum(args[1]);
  if (d2->val != 0){
    return new (GC) NativeNum(d1->val / d2->val);
  } else {
    throw UndefFailure("division by zero");
  }
}

Value static mod(Thread thread, Value* args) {
  NativeNum const * d1 = getNativeNum(args[0]);
  NativeNum const * d2 = getNativeNum(args[1]);
  if (d2->val != 0){
    return new (GC) NativeNum(d1->val % d2->val);
  } else {
    throw UndefFailure("divison by zero");
  }
}

void static xless(Thread thread, Value* args) THROW(Abort) {
  NativeNum const * d1 = getNativeNum(args[0]);
  NativeNum const * d2 = getNativeNum(args[1]);
  if (!(d1->val < d2->val)) {
    throw UnsatisfiedFailure(); 
  }
}

void static lessEq(Thread thread, Value* args) THROW(Abort) {
  NativeNum const * d1 = getNativeNum(args[0]);
  NativeNum const * d2 = getNativeNum(args[1]);
  if (!(d1->val <= d2->val)){
    throw UnsatisfiedFailure();
  }
}


void static registerNumbers(Loader& ld){
  ld.registerNativeFunc("NATIVEmakeNumber", 1, makeNumber);
  ld.registerNativeFunc("NATIVEnumAdd", 2, add);
  ld.registerNativeFunc("NATIVEnumSub", 2, sub);
  ld.registerNativeFunc("NATIVEnumMul", 2, mul);
  ld.registerNativeFunc("NATIVEnumDiv", 2, div);
  ld.registerNativeFunc("NATIVEnumMod", 2, mod);
  ld.registerNativePred("NATIVEnumLess", 2, xless);
  ld.registerNativePred("NATIVEnumLessEq", 2, lessEq);
}

// --------------------------------------------------------------------------
// Sequences

// CHECKME: SEQ OF SEQ

// auxiliaries

static inline NativeSeq* asSeq(Value v){
  if (v->kind == ValueData::OTHER){
    OtherData* dat = static_cast<OtherData*>(v);
    return dynamic_cast<NativeSeq*>(dat);
  } else {
    return 0;
  }
}

static inline bool isEmptySeq(Value v){
  if (v == Data::emptySet) return true;
  switch (v->kind){
  case ValueData::SET:{
    SetData* s = static_cast<SetData*>(v);
    return s->ecount == 0 && s->icount == 0;
  }
  default:
    return false;
  }
}

static inline Value makeSeq(Value* elems, int count){
  Value* end = elems+count;
  Value res = Data::emptySet;
  while (end-- > elems){
    res = new (GC) NativeSeq((*end)->ground && res->ground, *end, res);
  }
  return res;
}


// GC constructor; special iterative method 

NativeSeq::NativeSeq(GCPlacement, NativeSeq& oldr) : OtherData(oldr.ground) {
  NativeSeq* seq = this;
  NativeSeq* old = &oldr;
  seq->head = GcHeap::collect(old->head);
  while (!isEmptySeq(old->tail)){
    NativeSeq* old1 = dynamic_cast<NativeSeq*>(old->tail);
    if (old1 == 0){
      // not a sequence
      seq->tail = GcHeap::collect(old->tail);
      return;
    }
    old = old1;
    if (old->forward != 0){
      // already collected
      seq->tail = (Value)old->forward;
      return;
    } else if (old->generation >= GcHeap::collectFrom){
      // to be collected
      NativeSeq* n; 
      old->forward = n = new (GC) NativeSeq();
      n->ground = old->ground;
      n->head = GcHeap::collect(old->head);
      seq->tail = n;
      seq = n;
      continue;
    } else {
      // from an older generation
      seq->tail = old;
      return;
    }
  }
  seq->tail = Data::emptySet;
}

// virtuals of OtherData

Value NativeSeq::freeze(FreezeInfo& info){
  if (ground) return this;
  Value nval = info.getVisited(this);
  if (nval != 0) return nval;

  NativeSeq* nseq = new (GC) NativeSeq(true, 0, 0);
  info.markVisited(this, nseq);
  nseq->head = Data::doFreeze(info, head);
  nseq->tail = Data::doFreeze(info, tail);
  nseq->ground = nseq->head->ground && nseq->tail->ground;
  info.commitGround(nseq, nseq->ground);

  return nseq;
}
  

void NativeSeq::unifyWith(Value val, UnifyMethod* mth){
  // val = Data::resolveVars(val);
  NativeSeq* s = asSeq(val);
  if (s != 0){
    mth->uni(head, s->head);
    mth->uni(tail, s->tail);
  } else if (isEmptySeq(val)){
    throw UnequalFailure(1);
  } else {
    ASSERT(val->kind == ValueData::SET);
    // need to start subgoal which converts val to a sequence
    Inten subgoal =
      new (GC) IntenData(BuiltinUnit::theUnit->schemas
			 [BuiltinUnit::asSeqUnifySchemaIndex],
			 newGCArray<Value>(this, val));
    mth->addSubgoal(subgoal);
  }
}

Value NativeSeq::apply(Goal goal, Value arg){
  long inx = getNativeNum(arg)->val;
  if (inx < 1)
    throw UndefFailure("sequence index to small");
  NativeSeq* s = this;
  while (inx > 1){
    Value v = Data::resolveVars(s->tail);
    s = asSeq(v);
    if (s != 0){
      inx--;
      continue;
    } else if (isEmptySeq(v)){
      throw UndefFailure("sequence index to large");
    } else {
      ASSERT(v->kind == ValueData::VAR);
      throw RequireFailure(static_cast<VarData*>(v));
    }
  }
  return s->head;
}
    

void NativeSeq::print(std::ostream& os, PrintMethod* mth) {
  NativeSeq* s = this;
  int i = 0;
  int max = mth->maxPrintLeng();
  os << "<";
  do {
    mth->print(os, s->head);
    Value v = Data::resolveVars(s->tail);
    s = asSeq(v);
    if (s != 0){
      os << ",";
      if (max >= 0 && ++i >= max){
	os << "...";
	break;
      }
      else
	continue;
    } else {
      os << ">";
      if (!isEmptySeq(v)){
	os << "^";
	mth->print(os, v);
      }
      break;
    }
  }
  while (true);
}

SetData* NativeSeq::asSet(){
  DynArray<Value> arr;
  NativeSeq* s = this;
  bool rground = true;
  long inx = 1;
  do {
    rground = rground && s->head->ground;
    arr.push(Data::makePair(new (GC) NativeNum(inx++), s->head));
    Value v = Data::resolveVars(s->tail);
    s = asSeq(v);
    if (s != 0){
      continue;
    } else {
      int cnt;
      Value* els = arr.asArray(cnt);
      if (!isEmptySeq(v)){
	// {e_1}+...+{e_n} + {(i,x)\i' | (i',x) IN v; i=i'+n}
	Inten inten = 
	  new (GC) IntenData(BuiltinUnit::theUnit->schemas
			     [BuiltinUnit::seqAsSetSchemaIndex],
			     newGCArray<Value>(new (GC) NativeNum(cnt),
					       v));
	return new (GC) SetData(rground, cnt, els, 1, newGCArray(inten));
      } else {
	return new (GC) SetData(rground, cnt, els, 0, 0);
      }
    }
  }
  while (true);
}
  
VarData* NativeSeq::findFree(){
  if (ground) return 0;
  VarData* var = Data::findFree(head);
  if (var != 0) return var; else return Data::findFree(tail);
}

bool NativeSeq::cacheEq(Value v){
  return false;
}

unsigned NativeSeq::cacheHash(){
  return 0;
}



// homomorphisms

struct SeqHom : public HomStateData {

  Set<TermData*> elems;
  
  SeqHom() {}

  bool next(Goal goal, Order order, Value val){
    Admin::checkFreeVars(goal, val);
    val = Data::resolveVars(val);
    switch (val->kind){
    case ValueData::TERM:{
      // must be a pair
      TermData* dat = static_cast<TermData*>(val);
      Value inxVal = Data::resolveVars(dat->args[0]);
      if (inxVal->kind == ValueData::VAR)
	throw RequireFailure(static_cast<VarData*>(inxVal));
      elems.include(this, dat);
      return true;
    }
    default:
      ASSERT(val->kind == ValueData::VAR);
      throw RequireFailure(static_cast<VarData*>(val));
    }
  }

  Value makeSeq(){
    int i = elems.size();
    Value res = Data::emptySet;
    makeSeq(elems._tree.ptr(), i, res);
    return res;
  }
  void makeSeq(SetElem<TermData*>* tree, int& count, Value& res){
    if (tree == 0)
      return;
    else {
      makeSeq(tree->right.ptr(), count, res);
      if (res == 0) return;
      TermData* dat = tree->val;
      Value inxVal = Data::resolveVars(dat->args[0]);
      if (count != getNativeNum(inxVal)->val) {
	res = 0;
	return;
      }
      count--;
      Value e = dat->args[1];
      res = new (GC) NativeSeq(res->ground && e->ground, e, res);
      makeSeq(tree->left.ptr(), count, res);
    }
  }
  Value squashSeq(){
    Value res = Data::emptySet;
    squashSeq(elems._tree.ptr(), res);
    return res;
  }
  void squashSeq(SetElem<TermData*>* tree, Value& res){
    if (tree == 0)
      return;
    else {
      squashSeq(tree->right.ptr(), res);
      TermData* dat = tree->val;
      Value e = dat->args[1];
      res = new (GC) NativeSeq(res->ground && e->ground, e, res);
      squashSeq(tree->left.ptr(), res);
    }
  }

};

struct AsSeqHom : public SeqHom {

  AsSeqHom() {}

  AsSeqHom(GCPlacement, AsSeqHom& x) {
    GcHeap::collect(elems, x.elems);
  }
  void gc() { GcHeap::gc(this); }

  static HomState start(Goal goal, SetData* set){
    return new (GC) AsSeqHom();
  }

  Value end(Goal goal){
    Value res = makeSeq();
    if (res != 0)
      return res;
    else
      throw UndefFailure("not a sequence");
  }

};

struct IsSeqHom : public SeqHom {

  IsSeqHom() {}

  IsSeqHom(GCPlacement, IsSeqHom& x) {
    GcHeap::collect(elems, x.elems);
  }
  void gc() { GcHeap::gc(this); }

  static HomState start(Goal goal, SetData* set){
    return new (GC) IsSeqHom();
  }

  Value end(Goal goal){
    if (makeSeq() != 0){
      return Data::truthSet;
    } else
      return Data::emptySet;
  }

};

struct IsSeq1Hom : public SeqHom {

  IsSeq1Hom() {}

  IsSeq1Hom(GCPlacement, IsSeq1Hom& x) {
    GcHeap::collect(elems, x.elems);
  }
  void gc() { GcHeap::gc(this); }


  static HomState start(Goal goal, SetData* set){
    return new (GC) IsSeq1Hom();
  }

  Value end(Goal goal){
    Value res = makeSeq();
    if (res != 0 && res != Data::emptySet){
      return Data::truthSet;
    } else
      return Data::emptySet;
  }

};

struct SquashSeqHom : public SeqHom {

  SquashSeqHom() {}

  SquashSeqHom(GCPlacement, SquashSeqHom& x) {
    GcHeap::collect(elems, x.elems);
  }
  void gc() { GcHeap::gc(this); }

  static HomState start(Goal goal, SetData* set){
    return new (GC) SquashSeqHom();
  }

  Value end(Goal goal){
    return squashSeq();
  }

};

// native operations

      
static void isSeqRepr(Thread thread, Value* args) {
  Value v = Data::resolveVars(args[0]);
  if (asSeq(v) == 0 && !isEmptySeq(v) && !(v->kind == ValueData::VAR)){
    throw UnsatisfiedFailure();
  }
}

/*
static Value doCat(Value left, Value right){
  left = Data::resolveVars(left);
  NativeSeq* s = asSeq(left);
  if (s != 0){
    Value r = doCat(s->tail, right);
    return new (GC) NativeSeq(s->head->ground && r->ground, s->head, r);
  } else if (isEmptySeq(left)){
    return right;
  } else {
    ASSERT(left->kind == ValueData::VAR);
    throw RequireFailure(static_cast<VarData*>(left));
  }
}
*/
  
static Value cons(Thread thread, Value* args) {
  return new (GC) NativeSeq(args[0]->ground && args[1]->ground,
			    args[0], args[1]);
}

static Value head(Thread thread, Value* args) {
  Value v = Data::resolveVars(args[0]);
  NativeSeq* s = asSeq(v);
  if (s != 0){
    return s->head;
  } else if (isEmptySeq(v)){
    throw UndefFailure("head applied to empty sequence");
  } else {
    ASSERT(v->kind == ValueData::VAR);
    throw RequireFailure(static_cast<VarData*>(v));
  }
}

static Value tail(Thread thread, Value* args) {
  Value v = Data::resolveVars(args[0]);
  NativeSeq* s = asSeq(v);
  if (s != 0){
    return s->tail;
  } else if (isEmptySeq(v)){
    throw UndefFailure("tail applied to empty sequence");
  } else {
    ASSERT(v->kind == ValueData::VAR);
    throw RequireFailure(static_cast<VarData*>(v));
  }
}

static Value seqCard(Thread thread, Value* args) {
  Value v = Data::resolveVars(args[0]);
  int i = 0;
  do {
    NativeSeq* s = asSeq(v);
    if (s != 0){
      i++;
      v = Data::resolveVars(s->tail);
      continue;
    } else if (isEmptySeq(v)){
      return new (GC) NativeNum(i);
    } else {
      ASSERT(v->kind == ValueData::VAR);
      throw RequireFailure(static_cast<VarData*>(v));
    }
  } while (true);
}
		  
// denotation encoding

static Value decodeDeno(Thread thread, Value* args){
  NativeDeno* d = getNativeDeno(args[0]);
  int n = strlen(d->val);
  Value res = Data::emptySet;
  unsigned char const * s = (unsigned char const *)d->val + n;
  while (s != (unsigned char const *)d->val){
    s--;
    res = new (GC) NativeSeq(true, new (GC) NativeNum(*s), res);
  }
  return res;
}

static Value encodeDeno(Thread thread, Value* args){
  Value v = Data::resolveVars(args[0]);
  int i = 0;
  do {
    NativeSeq* s = asSeq(v);
    if (s != 0){
      i++;
      v = Data::resolveVars(s->tail);
      continue;
    } else if (isEmptySeq(v)){
      break;
    } else {
      ASSERT(v->kind == ValueData::VAR);
      throw RequireFailure(static_cast<VarData*>(v));
    }
  } while (true);
  unsigned char* deno = new (GC) unsigned char[i+1];
  unsigned char* d = deno;
  v = Data::resolveVars(args[0]);
  do {
    NativeSeq* s = asSeq(v);
    if (s != 0){
      NativeNum const * n = getNativeNum(s->head);
      if (n->val >= 0 && n->val <= 255){
	*d++ = (unsigned char)n->val;
      } else
	throw UndefFailure("encode: character code out of range (0..255)");
      v = Data::resolveVars(s->tail);
      continue;
    } else if (isEmptySeq(v)){
      break;
    } else {
      ASSERT(v->kind == ValueData::VAR);
      throw RequireFailure(static_cast<VarData*>(v));
    }
  } while (true);
  *d = 0;
  return new (GC) NativeDeno((char *)deno);
}
  
  

// registration

static void registerSeqs(Loader& ld){
  ld.registerHom("NATIVEisSeq", IsSeqHom::start);
  ld.registerHom("NATIVEisNonEmptySeq", IsSeq1Hom::start);
  ld.registerHom("NATIVEasSeq", AsSeqHom::start);
  ld.registerHom("NATIVEsquash", SquashSeqHom::start);
  ld.registerNativePred("NATIVEisSeqRepr", 1, isSeqRepr);
  ld.registerNativeFunc("NATIVEcons", 2, cons);
  ld.registerNativeFunc("NATIVEhead", 1, head);
  ld.registerNativeFunc("NATIVEtail", 1, tail);
  ld.registerNativeFunc("NATIVEseqCard", 1, seqCard);
  ld.registerNativeFunc("NATIVEencode", 1, encodeDeno);
  ld.registerNativeFunc("NATIVEdecode", 1, decodeDeno);
}
  

// --------------------------------------------------------------------------
// Set primitives

static void extIsEmpty(Thread thread, Value* args) {
  SetData* s = Data::tryGetSet(args[0]);
  if (s == 0 || s->ecount > 0){
    throw UnsatisfiedFailure();
  }
}

static Value extSplit(Thread thread, Value* args) {
  SetData* s = Data::tryGetSet(args[0]);
  if (s == 0 || s->ecount == 0){
    throw UndefFailure("splitting an empty set");
  }
  Value* rextens = new (GC) Value[s->ecount-1];
  std::uninitialized_copy(s->extens+1,s->extens+s->ecount,rextens);
  return Data::makePair(
		 s->extens[0],
		 new (GC) SetData(s->ground,
				  s->ecount-1,
				  rextens,
				  0,
				  0)
	       );
}

static void registerSets(Loader& ld){
  ld.registerNativePred("NATIVEextIsEmpty", 1, extIsEmpty);
  ld.registerNativeFunc("NATIVEextSplit", 1, extSplit);
}
  



// --------------------------------------------------------------------------
// Set Homomorphisms 

// searching homomorphism

struct SearchHom : public HomStateData {

  DynPtr<ValueData> cand;
  SearchHom() : cand(0) {}

  bool next(Goal goal, Order order, Value val){
    if (cand == 0){
      cand.assign(this, val);
      return true;
    } else {
      Admin::checkFreeVars(goal, val);
      try {
	Unify::equal(cand.ptr(), val);
	return true;
      }
      catch (UnequalFailure& f){
	cand.clear();
	return false;
      }
      // pass through other failures
    }
  }

};

struct MuHom : public SearchHom {

  MuHom() : SearchHom() {}

  MuHom(GCPlacement, MuHom& x){
    cand.collect(x.cand);
  }
  void gc() { GcHeap::gc(this); }

  static HomState start(Goal goal, SetData* set){
    return new (GC) MuHom();
  }

  Value end(Goal goal){
    if (cand != 0){
      return cand.ptr();
    } else
      throw UndefFailure("mu-value undefined");
  }

};

struct Ex1Hom : public SearchHom {
  
  Ex1Hom() : SearchHom() {}

  Ex1Hom(GCPlacement, Ex1Hom& x){
    cand.collect(x.cand);
  }
  void gc() { GcHeap::gc(this); }

  static HomState start(Goal goal, SetData* set){
    return new (GC) Ex1Hom();
  }

  Value end(Goal goal){
    if (cand != 0){
      return Data::truthSet;
    } else {
      return Data::emptySet;
    }
  }

};

struct Ex1SchemaHom : public SearchHom {
  
  Ex1SchemaHom() : SearchHom() {}

  Ex1SchemaHom(GCPlacement, Ex1SchemaHom& x){
    cand.collect(x.cand);
  }
  void gc() { GcHeap::gc(this); }

  static HomState start(Goal goal, SetData* set){
    return new (GC) Ex1SchemaHom();
  }

  Value end(Goal goal){
    if (cand != 0){
      // make a singleton 
      return new (GC)SetData(cand.ptr()->ground, 1, 
			     newGCArray<Value>(cand.ptr()), 0, 0);
    } else {
      return Data::emptySet;
    }
  }

};

// ext homomorphism

struct ExtHom : public HomStateData {

  SetData* set;
  bool identity;
  Set<Value> elems;
  bool ground;
  
  ExtHom(SetData* _set, bool _identity) 
	: set(_set), identity(_identity), ground(true) {}

  ExtHom(GCPlacement, ExtHom& x) : identity(x.identity), ground(x.ground){
    set = GcHeap::collect(x.set);
    GcHeap::collect(elems, x.elems);
  }
  void gc() { GcHeap::gc(this); }

  static HomState start(Goal goal, SetData* set){
    return new (GC) ExtHom(set, set->icount == 0);
  }

  bool next(Goal goal, Order order, Value val){
    if (identity) return false;
    Admin::checkFreeVars(goal, val);
    ground = ground && val->ground;
    elems.include(this, val);
    return true;
  }

  Value end(Goal goal){
    if (identity) return set;
    int ecount;
    Value* extens = elems.asArray(ecount);
    if (set->ground){ // better criterion?? (need depth)
      set->extens = extens;
      set->ecount = ecount;
      set->icount = 0;
      set->intens = 0;
      return set;
    } else {
      return new (GC) SetData(ground, ecount, extens, 0, 0);
    }
  }
  
};


// card homomorphism

struct CardHom : public HomStateData {

  SetData* set;
  bool identity;
  Set<Value> elems;
  
  CardHom(SetData* _set, bool _identity) 
	: set(_set), identity(_identity) {}

  CardHom(GCPlacement, CardHom& x) : identity(x.identity){
    set = GcHeap::collect(x.set);
    GcHeap::collect(elems, x.elems);
  }
  void gc() { GcHeap::gc(this); }

  static HomState start(Goal goal, SetData* set){
    return new (GC) CardHom(set, set->ground && set->icount == 0);
  }

  bool next(Goal goal, Order order, Value val){
    if (identity) return false;
    VarData* var = Data::findFree(val);
    if (var != 0)
      throw RequireFailure(var);
    elems.include(this, val);
    return true;
  }

  Value end(Goal goal){
    if (identity) return new (GC) NativeNum(set->ecount);
    if (set->ground) { // better criterion?? (need depth)
      int ecount;
      Value* extens = elems.asArray(ecount);
      set->extens = extens;
      set->ecount = ecount;
      set->icount = 0;
      set->intens = 0;
      return new (GC) NativeNum(set->ecount);
    } else {
      return new (GC) NativeNum(elems.size());
    }
  }
  
};

// power homomorphism

struct PowerHom : public HomStateData {

  struct Segment : GcObject {
    Set<Value> elems;
    bool ground;

    inline Segment() : ground(true){
    }
      
    inline Segment(GCPlacement, Segment& x) : ground(x.ground) {
      GcHeap::collect(elems,x.elems);
    }

    void gc() { GcHeap::gc(this); }
  };

      
  List<Segment*> segments;

  PowerHom(GCPlacement, PowerHom& x) {
    GcHeap::collect(segments, x.segments);
  }
  void gc() { GcHeap::gc(this); }

  PowerHom() {
    segments.push(this, new (GC) Segment());
  }

  static HomState start(Goal goal, SetData* set){
    return new (GC) PowerHom();
  }

  bool next(Goal goal, Order order, Value val) {
    if (!val->ground)
      Admin::checkFreeVars(goal, val);
    for (ListIterator<Segment*> it = segments.iterate(); it.more(); it.next()){
      Segment* olds = *it;
      Segment* news = new (GC) Segment();
      news->elems.copyFrom(news, olds->elems);
      news->elems.include(news, val);
      news->ground = olds->ground && val->ground;
      segments.push(this, news);
    }
    return true;
  }

  Value end(Goal goal){
    Set<Value> res;
    bool ground = true;
    for (ListIterator<Segment*> it = segments.iterate(); it.more(); it.next()){
      Segment* s = *it;
      int size;
      Value* elems = s->elems.asArray(size);
      ground = ground && s->ground;
      SetData* set = new (GC) SetData(s->ground, size, elems, 0, 0);
      res.include(0, set);
    }
    int size;
    Value* elems = res.asArray(size);
    return new (GC) SetData(ground, size, elems, 0, 0);
  }

};


// empty and none-empty homomorphisms

struct TestHom : HomStateData {
  bool testEmpty;
  bool firstSeen;

  TestHom(bool t) : testEmpty(t), firstSeen(false){}
  TestHom(GCPlacement, TestHom& x) : 
    testEmpty(x.testEmpty), firstSeen(x.firstSeen){}
  void gc() { GcHeap::gc(this); }

  static HomState emptyStart(Goal goal, SetData* set){
    return new (GC) TestHom(true);
  }

  static HomState notemptyStart(Goal goal, SetData* set){
    return new (GC) TestHom(false);
  }

  bool next(Goal goal, Order order, Value val){
    firstSeen = true;
    return false;
  }

  Value end(Goal goal){
  if (testEmpty == firstSeen)
    return Data::emptySet;
  else 
    return Data::truthSet;
  }

};


// bigcup and bigcap homomorphisms

struct BigHom : HomStateData {
  bool isect;
  SetData* current;
  BigHom(bool i, SetData* c) : isect(i), current(c){}
  BigHom(GCPlacement, BigHom& x) : isect(x.isect) {
    current = GcHeap::collect(current);
  }
  void gc() { GcHeap::gc(this); }

  static HomState unionStart(Goal goal, SetData* set){
    return new (GC) BigHom(false, 0);
  }

  static HomState isectStart(Goal goal, SetData* set){
    return new (GC) BigHom(true, 0);
  }


  bool next(Goal goal, Order order, Value val){
    Admin::checkFreeVars(goal, val);
    val = Data::resolveVars(val);
    SetData* set = Data::tryGetSet(val);
    if (set == 0) {
      // val must be a free variable
      throw RequireFailure(static_cast<VarData*>(val));
    }
    if (current == 0)
      current = set;
    else if (isect){
      current = Data::join(current, set);
    } else {
      current = Data::merge(current, set);
    }
    return true;
  }
      
  Value end(Goal goal){
    if (current == 0)
      return Data::emptySet;
    else
      return current;
  }

};



// register homomorphisms

void static registerHoms(Loader& ld){
  ld.registerHom("NATIVEmu", MuHom::start);
  ld.registerHom("NATIVEexists1", Ex1Hom::start);
  ld.registerHom("NATIVEexists1Schema", Ex1SchemaHom::start);
  ld.registerHom("NATIVEext", ExtHom::start);
  ld.registerHom("NATIVEcard", CardHom::start);
  ld.registerHom("NATIVEempty", TestHom::emptyStart);
  ld.registerHom("NATIVEnotempty", TestHom::notemptyStart);
  ld.registerHom("NATIVEpower", PowerHom::start);
  ld.registerHom("NATIVEbigcap", BigHom::isectStart);
  ld.registerHom("NATIVEbigcup", BigHom::unionStart);
}
  


// --------------------------------------------------------------------------
// Debugging & Other Stuff

Value static trace(Thread thread, Value* args) {
  std::ostrstream os;
  os << "TRACE: ";
  printres(os, args[0]);
  os << std::ends;
  Session::traces->receive(os.str());
  return args[1];
}

Value static deepForce(Thread thread, Value* args) {
  VarData* var = Data::findFree(args[0]);
  if (var != 0) throw RequireFailure(var);
  return args[0];
}

Value static force(Thread thread, Value* args) {
  Value v = Data::resolveVars(args[0]);
  if (v == 0) throw RequireFailure((VarData*)args[0]);
  return v;
}

Value static waitfor(Thread thread, Value* args) {
  Value v = Data::resolveVars(args[0]);
  if (v == 0) throw RequireFailure((VarData*)args[0]);
  return args[1];
}

Value static memoize(Thread thread, Value* args) {
  NativeNum const * num = getNativeNum(args[0]);
  SetData* set = Data::tryGetSet(args[1]);
  ASSERT(set != 0);
  SetData* newset = new (GC) SetData(set->ground, 
				     set->ecount, set->extens,
				     set->icount, set->intens);
  newset->memo.assign(set, new (GC) MemoTab((int)num->val));
  return newset;
}
		   

void static registerDebugging(Loader& ld){
  ld.registerNativeFunc("NATIVEtrace", 2, trace);
  ld.registerNativeFunc("NATIVEforce", 1, force);
  ld.registerNativeFunc("NATIVEdeepForce", 1, deepForce);
  ld.registerNativeFunc("NATIVEwaitfor", 2, waitfor);
  ld.registerNativeFunc("NATIVEmemoize", 2, memoize);
}

// --------------------------------------------------------------------------
// Reflection

static char * gcstrdup(char* s, int n=-1){
  if (n < 0) n = strlen(s);
  char *r = new (GC) char[n+1];
  strncpy(r, s, n);
  r[n] = 0;
  return r;
}

static char * tmstrdup(char* s, int n=-1){
  if (n < 0) n = strlen(s);
  char *r = new (TM) char[n+1];
  strncpy(r, s, n);
  r[n] = 0;
  return r;
}

static char * ncstrdup(char* s, int n=-1){
  if (n < 0) n = strlen(s);
  char *r = new (NC) char[n+1];
  strncpy(r, s, n);
  r[n] = 0;
  return r;
}


static DynArray<char*> scanTypeArgs(char* actuals){
  DynArray<char*> arr;
  while (*actuals && *actuals != '[') actuals++;
  if (*actuals == '[') actuals++;
  int nest = 0;
  char* last = actuals;
  while (*actuals){
    if (*actuals == '[' || *actuals == '('){
      nest++;
      actuals++;
    } else if ((*actuals == ']' || *actuals == ')') && nest > 0){
      nest--;
      actuals++;
    } else if (nest == 0 && 
	       (*actuals == ']' || *actuals == ')' || *actuals == ',')){
      arr.push(gcstrdup(last, actuals-last));
      if (*actuals == ']')
	break;
      else {
	actuals++;
	last = actuals;
      }
    } else
      actuals++;
  }
  return arr;
}

static char* instantiate(char* typedescr, char* actuals){
  DynArray<char*> acts = scanTypeArgs(actuals);
  std::ostrstream res;
  while (*typedescr != 0){
    if (*typedescr == '%' && *(typedescr+1) == '%'){
      typedescr += 2;
      int inx = strtol(typedescr, &typedescr, 10)-1;
      if (inx >= 0 && inx < acts.length()){
	res << acts[inx];
      } else
	throw UndefFailure("wrong arity of actualization of given type");
    } else {
      res << *typedescr;
      typedescr++;
    }
  }
  res << std::ends;
  return gcstrdup(res.str());
}



Value static givenTypeInfo(Thread thread, Value* args) {
  NativeDeno* ad = getNativeDeno(args[1]);
  char *actuals = ad->val;
  while (*actuals && *actuals != '[') actuals++;
  if (*actuals){
    TermData* d = static_cast<TermData*>(args[0]);
    NativeDeno* td = getNativeDeno(d->args[0]);
    td = new (GC) NativeDeno(instantiate(td->val, actuals));
    return new (GC) TermData(true, d->cons, newGCArray<Value>(td));
  } else
    return args[0];
  
}


void static registerReflection(Loader& ld){
  ld.registerNativeFunc("NATIVEgiventypeinfo", 2, givenTypeInfo);
}


// --------------------------------------------------------------------------
// I/O

#define TOKEN_BUFSIZE 512

struct Scanner {
  std::istream& in;
  int nextc;
  inline void getnext(){
    if (in.eof()) nextc = -1; else nextc = in.get();
  }
  Scanner(std::istream& _in) : in(_in), line(1) {
    getnext();
  };
  char tokenBuf[TOKEN_BUFSIZE];
  int line;

  void error(char* descr, char* adddescr=0){
    std::ostrstream s;
    s << "reader (line " << std::dec << line << "): " << descr;
    if (adddescr != 0) s << ": " << adddescr;
    s << std::ends;
    throw UndefFailure(ncstrdup(s.str()));
  }

  inline bool skipSpaceAndMore(){
    while (nextc >= 0){
      switch (nextc){
      case ' ': case '\t': case '\r': case '\f':
	break;
      case '\n': 
	line++;
	break;
      default:
	return true;
      }
      getnext();
    }
    return false;
  }

  char* getToken(){
    if (skipSpaceAndMore()){
      int i = 0;
      bool stop = false;
      while (!stop){
	if (i >= TOKEN_BUFSIZE-1) error("token to long");
	tokenBuf[i++] = nextc;
	getnext();
	if (nextc < 0) { 
	  stop = true;
	} else {
	  switch (nextc){
	  case ' ': case '\n': case '\t': case '\r': case '\f':
	  case '{': case '}': 
	    stop = true;
	  }
	}
      }
      tokenBuf[i] = 0;
      return tokenBuf;
    } else
      error("unexpected end of input");
  }

  long getNumber(){
    char* token = getToken();
    char* endtoken;
    long res = strtol(token, &endtoken, 10);
    if (token == endtoken || *endtoken != 0){
      error("expected a number, found", token);
    }
    return res;
  }

  bool testChar(char ch){
    if (skipSpaceAndMore()){
      if (nextc == ch){
	getnext();
	return true;
      } else {
	return false;
      }
    } else
      return false;
  }


};


struct Parser {
  virtual Value parse(Scanner& scanner) = 0;
};

struct NumberParser : Parser { 
  Value parse(Scanner& scanner){
    return new (GC) NativeNum(scanner.getNumber());
  }
};

struct TermParser : Parser {
  Constructor cons;
  Parser** subparsers;
  TermParser(Constructor _cons, Parser** _subparsers) 
    : cons(_cons), subparsers(_subparsers) {
  }
  Value parse(Scanner& scanner){
    Value* args = new (GC) Value[cons->arity];
    for (int i = 0; i < cons->arity; i++){
      args[i] = subparsers[i]->parse(scanner);
    }
    return new (GC) TermData(true, cons, args);
  }
};

struct FreeTypeParser : Parser {
  int variants;
  TermParser** subparsers;
  FreeTypeParser(int _variants, TermParser** _subparsers) 
    : variants(_variants), subparsers(_subparsers) {
  }
  Value parse(Scanner& scanner){
    char* name = scanner.getToken();
    for (int i = 0; i < variants; i++){
      if (strcmp(subparsers[i]->cons->name, name) == 0)
	return subparsers[i]->parse(scanner);
    }
    scanner.error("not a variant of free type", name);
  }
};

struct SetParser : Parser {
  Parser* subparser;
  SetParser(Parser* _subparser) : subparser(_subparser) {
  }
  Value parse(Scanner& scanner){
    if (scanner.testChar('{')){
      List<Value> elems;
      while (!scanner.testChar('}')){
	elems.include(0, subparser->parse(scanner));
      }
      int sz;
      Value* arr = elems.asArray(sz);
      return new (GC) SetData(true, sz, arr, 0, 0);
    } else
      scanner.error("not a set (expected '{')");
  }
}; 

static Parser* buildProductParser(char*& tyinfo);
static Parser* buildBindingParser(char*& tyinfo);
static Parser* buildGivenTypeParser(char*& tyinfo);
static Parser* buildParser(char*& tyinfo);

static Parser* buildParser(char*& tyinfo){
  switch (*tyinfo){
  case '(':
    tyinfo++;
    return buildProductParser(tyinfo);
  case '[':
    tyinfo++;
    return buildBindingParser(tyinfo);
  case '!':
    tyinfo++;
    return new (TM) SetParser(buildParser(tyinfo));
  default:
    return buildGivenTypeParser(tyinfo);
  }
}

static Parser* buildProductParser(char*& tyinfo){
  DynArray<Parser*> parsers;
  char buf[512];
  strcpy(buf, "(");
  bool first = true;
  while (*tyinfo != 0 && *tyinfo != ')'){
    if (first) 
      first = false;
    else {
      strcat(buf, ",");
      first = false;
    }
    parsers.push(buildParser(tyinfo));
    if (parsers.length() > 128) throw UndefFailure("product to large");
    strcat(buf, "_");
    if (*tyinfo == ',') tyinfo++;
  }
  if (*tyinfo) tyinfo++;
  strcat(buf, ")");
  int sz;
  return 
    new (TM) TermParser(
	  BuiltinUnit::theLoader->lookupConstructor(ncstrdup(buf), 
						    parsers.length()),
	  parsers.asArray(sz)
	     );
}

static Parser* buildBindingParser(char*& tyinfo){
  DynArray<Parser*> parsers;
  char buf[1024];
  strcpy(buf, "<");
  bool first = true;
  while (*tyinfo != 0 && *tyinfo != ']'){
    if (first) 
      first = false;
    else {
      strcat(buf, ",");
      first = false;
    }
    char* end = tyinfo;
    while (*end && *end != ':') end++;
    strncat(buf, tyinfo, end-tyinfo);
    strcat(buf, "==_");
    if (*end == ':') end++;
    tyinfo = end;
    parsers.push(buildParser(tyinfo));
    if (parsers.length() > 128) throw UndefFailure("binding to large");
    if (*tyinfo == ';') tyinfo++;
  }
  if (*tyinfo) tyinfo++;
  strcat(buf, ">");
  int sz;
  return 
    new (TM) TermParser(
	  BuiltinUnit::theLoader->lookupConstructor(ncstrdup(buf),
						    parsers.length()),
	  parsers.asArray(sz)
	     );
}

    
static char* scanTypeInfo(char*& tyinfo, bool skipBrack=false){
  char* end = tyinfo;
  int nest = 0;
  bool stop = false;
  while (*end && !stop){
    switch (*end){
    case '[': case '<': case '(':
      if (skipBrack){
	nest++;
	end++;
      } else
	stop = true;
      break;
    case ']': case '>': case ')':
      if (skipBrack){
	nest--;
	stop = nest == 0;
	end++;
      } else
	stop = true;
      break;
    case ',':  case ';': case '|':
      stop = nest == 0;
      if (!stop) end++;
      break;
    default:
      end++;
    }
  }
  char* res = tmstrdup(tyinfo, end-tyinfo);
  tyinfo = end;
  return res;
}
    
static std::map<std::string,Parser*> givenTypeParserCache;

static Parser* buildGivenTypeParser(char*& tyinfo){
  char* name = scanTypeInfo(tyinfo);
  char tyname[512];
  strcpy(tyname, name);
  strcat(tyname, "%giventypeinfo");
  Global g = BuiltinUnit::theLoader->lookupGlobal(tyname);
  TermData* td = 
    static_cast<TermData*>(
        Data::resolveVars(
		BuiltinUnit::theLoader->globalVarTab[g->varinx]
	      ));
					 
  char * ginfo = getNativeDeno(td->args[0])->val;
  if (*tyinfo == '['){
    char* acts = scanTypeInfo(tyinfo, true);
    ginfo = instantiate(ginfo, acts);
  }
  if (*ginfo == '1'){
    // no free type information associated
    if (strcmp(name, "\\baseNum") == 0)
      return new (TM) NumberParser();
    else
      throw new UndefFailure("unsupported given type for I/O");
  } else {
    // lookup in cache
    std::map<std::string,Parser*>::iterator i = 
      givenTypeParserCache.find(ginfo);
    if (i != givenTypeParserCache.end()){
      return i->second;
    }
    // create an empty entry in cache (to construct fixpoint)
    FreeTypeParser* ftparser = new (TM) FreeTypeParser(0, 0);
    givenTypeParserCache.insert(
      std::map<std::string,Parser*>::value_type(ginfo, ftparser)
    );
    // now actually build the stuff
    DynArray<TermParser*> variants;
    while (*ginfo){
      char* consName = scanTypeInfo(ginfo);
      DynArray<Parser*> elems;
      if (*ginfo == '<'){
	char* ctyinfo = scanTypeInfo(ginfo, true);
	if (!*ginfo == '>') throw UndefFailure("invalid type info");
	ginfo++;
	ctyinfo++;
	if (*ctyinfo == '('){
	  ctyinfo++;
	  while (*ctyinfo && *ctyinfo != ')'){
	    elems.push(buildParser(ctyinfo));
	    if (*ctyinfo == ',') ctyinfo++;
	  }
	  if (*ctyinfo) ctyinfo++;
	} else
	  elems.push(buildParser(ctyinfo));
      }
      Constructor cons =
	BuiltinUnit::theLoader->lookupConstructor(consName,
						  elems.length());
      int sz;
      variants.push(new (TM) TermParser(cons, elems.asArray(sz)));
      if (*ginfo == '|') ginfo++;
    }
    // patch
    ftparser->subparsers = variants.asArray(ftparser->variants);
    return ftparser;
  }
}
		  
static Value fromStream(char* tyinfo, std::istream& in){
  Scanner scanner(in);
  givenTypeParserCache.clear();
  Parser* parser = buildParser(tyinfo);
  Value res = Data::emptySet;
  Value* next = &res;
  while (scanner.skipSpaceAndMore()){
    Value val = parser->parse(scanner);
    NativeSeq* elem = new (GC) NativeSeq(true, val, Data::emptySet);
    *next = elem;
    next = &elem->tail;
  }
  givenTypeParserCache.clear();
  return res;
}
    
static Value fromFile(Thread thread, Value* args){
  TermData* d = static_cast<TermData*>(Data::resolveVars(args[0]));
  char* tyinfo = getNativeDeno(d->args[0])->val;
  char* fname = getNativeDeno(args[1])->val;
  std::ifstream in(fname);
  if (!in){
	std::ostrstream s;
    s << "cannot open file '" << fname << "'" << std::ends;
    throw UndefFailure(ncstrdup(s.str()));
  }
  Value res = fromStream(tyinfo, in);
  in.close();
  return res;
}

static Value fromDeno(Thread thread, Value* args){
  TermData* d = static_cast<TermData*>(Data::resolveVars(args[0]));
  char* tyinfo = getNativeDeno(d->args[0])->val;
  char* deno = getNativeDeno(args[1])->val;
  std::istrstream in(deno);
  Value res = fromStream(tyinfo, in);
  return res;
}

    
void static registerIO(Loader& ld){
  ld.registerNativeFunc("NATIVEfromFile", 2, fromFile);
  ld.registerNativeFunc("NATIVEfromDeno", 2, fromDeno);
}

    



// --------------------------------------------------------------------------
// Builtin unit

Unit BuiltinUnit::theUnit = 0;
Loader* BuiltinUnit::theLoader = 0;

static Instr::Unit const joinS1Code[] = {
  Instr::LOAD, Instr::index(0), Instr::index(0),
  Instr::WAITLOADPARAM, Instr::index(0), Instr::index(1),
  Instr::MEMBER, Instr::index(0), Instr::index(1),
  Instr::SUCCESS
};

static Instr::Unit const joinS2Code[] = {
  Instr::LOAD, Instr::index(0), Instr::index(0),
  Instr::WAITLOADPARAM, Instr::index(1), Instr::index(1),
  Instr::MEMBER, Instr::index(0), Instr::index(1),
  Instr::SUCCESS
};

static Schema makeJoin(Unit unit){
  ConstrData * c1 = new (NC) ConstrData(0, "'_x IN _S1'", 2, joinS1Code);
  ConstrData * c2 = new (NC) ConstrData(0, "'_x IN _S2'", 2, joinS2Code);
  Schema join = new (NC) SchemaData(unit, 
			       "'{_x|_x IN _S1; _x IN _S2}'",
			       2, newArray<char const*>("_S1", "_S2"),
			       1,
			       newArray<char const*>("_x"),
			       new (NC) VarData(-1, "_x"),
			       2,
			       newArray<Constr>(c1, c2)
			      );
  return c1->schema = c2->schema = join;
}


static Schema makeUniv(Unit unit){
  Schema univ = new (NC) SchemaData(unit, 
				    "'{_x|true}'",
				    0, 0,
				    1, newArray<char const*>("_x"),
				    new (NC) VarData(-1, "_x"),
				    0,
				    0
				   );
  return univ;
}


static Instr::Unit const applyCode[] = {
   Instr::LOADPARAM, Instr::index(1), Instr::index(0),
   Instr::LOAD, Instr::index(0), Instr::index(1),
   Instr::MKTERM, Instr::index(BuiltinUnit::pairConsIndex), Instr::index(0), 
                  Instr::index(2),
   Instr::WAITLOADPARAM, Instr::index(0), Instr::index(3),
   Instr::MEMBER, Instr::index(2), Instr::index(3),
   Instr::SUCCESS
};

static Schema makeApply(Unit unit){
  ConstrData * c = new (NC) ConstrData(0, "'(_x,_y) IN _S'", 4, applyCode);
  Schema apply = new (NC) SchemaData(unit, 
				     "'{_y|(_x,_y) IN _S}'",
				     2, newArray<char const*>("_S", "_x"),
				     1, newArray<char const*>("_y"),
				     new (NC) VarData(-1, "_y"),
				     1, newArray<Constr>(c)
				    );
  return c->schema = apply;
}

static Instr::Unit const enumCode[] = {
  Instr::LOAD, Instr::index(0), Instr::index(0),
  Instr::WAITLOADPARAM, Instr::index(0), Instr::index(1),
  Instr::MEMBER, Instr::index(0), Instr::index(1),
  Instr::SUCCESS
};

static Schema makeEnum(Unit unit){
  ConstrData * c = new (NC) ConstrData(0, "'_x IN _S'", 2, enumCode);
  Schema en = new (NC) SchemaData(unit, 
				  "'{_x|_x IN _S}'",
				  1, newArray<char const*>("_S"),
				  1, newArray<char const*>("_x"),
				  new (NC) VarData(-1, "_x"),
				  1,
				  newArray<Constr>(c)
				 );
  return c->schema = en;
}


static Instr::Unit const subsetCode[] = {
  Instr::LOAD, Instr::index(0), Instr::index(0),
  Instr::WAITLOADPARAM, Instr::index(0), Instr::index(1),
  Instr::MEMBER, Instr::index(0), Instr::index(1),
  Instr::WAITLOAD, Instr::index(0), Instr::index(2),
  Instr::MKSINGLE, Instr::index(2), Instr::index(3),
  Instr::LOADPARAM, Instr::index(1), Instr::index(4),
  Instr::ISECT, Instr::index(3), Instr::index(4), Instr::index(5),
  Instr::IF, Instr::index(5), Instr::index(1),
  Instr::SUCCESS,
  Instr::FAILURE
};

static Schema makeSubset(Unit unit){
  ConstrData * c = new (NC) ConstrData(0, "'_x IN _S1; _x NOTIN _S2'", 6,
				       subsetCode);
  Schema subset = new (NC) SchemaData(unit, 
				      "'{_x IN _S1; _x NOTIN _S2}'",
				      2, newArray<char const*>("_S1","_S2"),
				      1, newArray<char const*>("_x"),
				      new (NC) VarData(-1, "_x"),
				      1, newArray<Constr>(c)
				     );
  return c->schema = subset;
}


static Instr::Unit const extUnifyCode[] = {
  Instr::WAITLOADPARAM, Instr::index(0), Instr::index(0),
  Instr::HOM, Instr::index(BuiltinUnit::extHomIndex), 
              Instr::index(0), Instr::index(1),
  Instr::WAITLOADPARAM, Instr::index(1), Instr::index(2),
  Instr::HOM, Instr::index(BuiltinUnit::extHomIndex), 
              Instr::index(2), Instr::index(3),
  Instr::UNIFY, Instr::index(1), Instr::index(3),
  Instr::SUCCESS
};

static Schema makeExtUnify(Unit unit){
  ConstrData * c = new (NC) ConstrData(0, "'_S1 = _S2'", 4,
				       extUnifyCode);
  Schema s = new (NC) SchemaData(unit, 
				 "'{_S1 = _S2}'",
				 2, newArray<char const*>("_S1","_S2"),
				 0, 0,
				 0,
				 1, newArray<Constr>(c)
				);
  return c->schema = s;
}

static Instr::Unit const asSeqUnifyCode[] = {
  Instr::WAITLOADPARAM, Instr::index(1), Instr::index(0),
  Instr::HOM, Instr::index(BuiltinUnit::asSeqHomIndex), 
              Instr::index(0), Instr::index(1),
  Instr::LOADPARAM, Instr::index(0), Instr::index(2),
  Instr::UNIFY, Instr::index(2), Instr::index(1),
  Instr::SUCCESS
};

static Schema makeAsSeqUnify(Unit unit){
  ConstrData * c = new (NC) ConstrData(0, "'_SEQ = asSeq(_SET)'", 3,
				       asSeqUnifyCode);
  Schema s = new (NC) SchemaData(unit, 
				 "'{_SEQ = asSeq(_SET)}'",
				 2, newArray<char const*>("_SEQ","_SET"),
				 0, 0,
				 0,
				 1, newArray<Constr>(c)
				);
  return c->schema = s;
}


static Instr::Unit const waitUnifySetCode[] = {
  Instr::WAITLOADPARAM, Instr::index(0), Instr::index(0),
  Instr::LOADPARAM, Instr::index(1), Instr::index(0),
  Instr::LOADPARAM, Instr::index(2), Instr::index(1),
  Instr::UNIFY, Instr::index(0), Instr::index(1),
  Instr::SUCCESS
};

static Schema makeWaitUnifySet(Unit unit){
  ConstrData * c = new (NC) ConstrData(0, "'_S1[x] = _S2[x]'", 2,
				       waitUnifySetCode);
  Schema s = new (NC) SchemaData(unit, 
				 "'{_S1[_x] = _S2[_x]}'",
				 3, newArray<char const*>("_x", "_S1","_S2"),
				 0, 0,
				 0,
				 1, newArray<Constr>(c)
				);
  return c->schema = s;
}

static Instr::Unit const waitUnifyVarCode[] = {
  Instr::WAITLOADPARAM, Instr::index(0), Instr::index(0),
  Instr::LOADPARAM, Instr::index(1), Instr::index(1),
  Instr::UNIFY, Instr::index(0), Instr::index(1),
  Instr::SUCCESS
};

static Schema makeWaitUnifyVar(Unit unit){
  ConstrData * c = new (NC) ConstrData(0, "'_x = _v'", 2,
				       waitUnifyVarCode);
  Schema s = new (NC) SchemaData(unit, 
				 "'{_x = _v}'",
				 2, newArray<char const*>("_x", "_v"),
				 0, 0,
				 0,
				 1, newArray<Constr>(c)
				);
  return c->schema = s;
}

static Instr::Unit const seqAsSetCode[] = {
  // {(i,x)\i' | (i',x) : v; i=i'+n}
  Instr::LOAD, Instr::index(2), Instr::index(0),
  Instr::LOAD, Instr::index(1), Instr::index(1),
  Instr::MKTERM, Instr::index(BuiltinUnit::pairConsIndex), Instr::index(0), 
                                                           Instr::index(2),
  Instr::WAITLOADPARAM, Instr::index(1), Instr::index(3),
  Instr::MEMBER, Instr::index(2), Instr::index(3),
  Instr::WAITLOAD, Instr::index(2), Instr::index(4),
  Instr::WAITLOADPARAM, Instr::index(0), Instr::index(5),
  Instr::CALLNATIVE, Instr::index(BuiltinUnit::numAddIndex), 
                           Instr::index(4), Instr::index(6),
  Instr::STORE, Instr::index(6), Instr::index(0),
  Instr::SUCCESS
};

static Schema makeSeqAsSet(Unit unit){
  ConstrData * c = new (NC) ConstrData(0, "'(i',x) IN v; i=i'+n'",
				       7, seqAsSetCode);
  Schema s = new (NC) SchemaData(unit, 
				 "'{(i,x)\\i' | (i',x) IN v; i=i'+n}'",
				 2, newArray<char const*>("n", "v"),
				 3, newArray<char const*>("i", "x", "i'"),
				 Data::makePair(
					 new (NC) VarData(-1, "i"),
					 new (NC) VarData(-2, "x")
				       ),
				 1, newArray<Constr>(c)
				);
  return c->schema = s;
}

  


void BuiltinUnit::initialize(Loader& ld){

  // register native stuff
  registerDenos(ld);
  registerNumbers(ld);
  registerDebugging(ld);
  registerReflection(ld);
  registerIO(ld);
  registerSeqs(ld);
  registerSets(ld);
  registerHoms(ld);

  // construct builtin unit
  UnitData* unit =
    new (NC) UnitData("%BUILTIN%", 
			 0,0,
			 0,0,
			 0,0,
			 0,0,
			 0,0,
			 0,0,
			 0,0,
			 -1,
			 1,0,
			 0, 0);
  theUnit = unit;

  // constructors
  unit->constructorCount = 2;
  unit->constructors = 
    newArray<Constructor>(ld.lookupConstructor("(_,_)", 2),
			  ld.lookupConstructor("<>", 0));

  // native functions
  unit->nativeFuncCount = 1;
  unit->nativeFuncs =
    newArray<NativeFunc>(ld.lookupNativeFunc("NATIVEnumAdd", 2));

  // homomorphisms
  unit->homCount = 3;
  unit->homs =
    newArray<Hom>(ld.lookupHom("NATIVEmu"),
		  ld.lookupHom("NATIVEext"),
		  ld.lookupHom("NATIVEasSeq"));

  // schemas
  unit->schemaCount = 10;
  unit->schemas = new (NC) Schema[10];
  Schema* schemas = const_cast<Schema*>(unit->schemas);
  schemas[joinSchemaIndex] = makeJoin(unit);
  schemas[univSchemaIndex] = makeUniv(unit);
  schemas[applySchemaIndex] = makeApply(unit);
  schemas[enumSchemaIndex] = makeEnum(unit);
  schemas[subsetSchemaIndex] = makeSubset(unit);
  schemas[extUnifySchemaIndex] = makeExtUnify(unit);
  schemas[waitUnifySetSchemaIndex] = makeWaitUnifySet(unit);
  schemas[waitUnifyVarSchemaIndex] = makeWaitUnifyVar(unit);
  schemas[asSeqUnifySchemaIndex] = makeAsSeqUnify(unit);
  schemas[seqAsSetSchemaIndex] = makeSeqAsSet(unit);

}

