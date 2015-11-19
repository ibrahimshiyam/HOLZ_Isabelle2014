// $Id: data.cpp,v 1.7 2000/07/20 11:39:01 wg Exp $

#include "data.h"

#include "natives.h"
#include "unify.h"

#include <algorithm>

//----------------------------------------------------------------------------
// Sorting

int compare(Value v1, Value v2){
  try {
    Unify::equal(v1, v2);
    return 0;
  }
  catch (UnequalFailure& f){
    return f.order;
  }
  catch (RequireFailure&){
    return 1;
  }
}

/*
DynArray<Value>& Data::insertSorted(DynArray<Value>& arr, Value val){
  int n = arr.length();
  for (int i = 0; i < n; i++){
    int c = compare(arr[i], val);
    if (c < 0)
      // comes after
      continue;
    else if (c > 0){
      // insert here
      arr.insert(i, val);
      return arr;
    } else 
      // already there
      return arr;
  }
  // append
  arr.push(val);
  return arr;
}

static void qsort(Value* values, int fst, int lst){
  if (fst >= lst) return;
  Value pivot = values[fst+(lst-fst)/2];
  int i = fst-1;
  int j = lst+1;
  while (i < j){
    do {
      int c = compare(values[++i], pivot);
      if (c < 0)
	continue;
      else
	break;
    } while (false);
    do {
      int c = compare(values[--j], pivot);
      if (c > 0)
	continue;
      else
	break;
    } while (false);
    if (i < j){
      Value tmp = values[i];
      values[i] = values[j];
      values[j] = tmp;
    }
  }
  qsort(values, fst, j);
  qsort(values, j+1, lst);
}

static Value* removeDups(int count, Value* values, int& actcount){
  DynArray<Value> res(count);
  Value last = 0;
  bool dups = false;
  for (int i = 0; i < count; i++){
    Value v = values[i];
    if (last != 0){
      int c = compare(last, v);
      if (c != 0) res.push(v);
      last = v;
    } else {
      res.push(v);
      last = v;
    }
  }
  if (dups) {
    return res.asArray(actcount);
  } else {
    actcount = count;
    return values;
  }
}

Value* Data::sortWithDups(int ecount, Value* extens, int& rcount){
  qsort(extens, 0, ecount-1);
  return removeDups(ecount, extens, rcount);
} 

*/
//----------------------------------------------------------------------------
// Freezing Values

Value Data::doFreeze(FreezeInfo& info, Value value){
  if (value->ground) return value;

  Value nval = info.getVisited(value);
  if (nval != 0) return nval;

  for (;;){
  
    switch (value->kind) {
    case ValueData::VAR: {
      VarData * dat = static_cast<VarData*>(value);
      if (dat->binding == 0) {
	return value;
      } else {
	// see if the binding is cyclic
	Value nbinding  = info.getVisited(dat->binding.ptr());
	if (nbinding != 0){
	  // a cylcic variable binding: preserve the variable
	  dat->binding.assign(dat, nbinding);
	  // assume ground for the moment
	  dat->ground = true;
	  // mark the cycle so we can backpatch the actual ground information
	  info.markCycle(nbinding, dat);
	  return dat;
	} else {
	  // continue with the variables binding
	  if (dat->visiting){
	    // cycle with only variables involved (happens since we
	    // have no occurs check)
	    return dat;
	  } else {
	    dat->visiting = true;
	    Value val = doFreeze(info, dat->binding.ptr());
	    dat->visiting = false;
	    return val;
	  }
	}
      }
    }
    case ValueData::TERM: {
      TermData * dat = static_cast<TermData*>(value);
      int arity = dat->cons->arity;
      Value * args = new (GC) Value[arity];
      TermData * ndat = new (GC) TermData(true, dat->cons, args);
      info.markVisited(dat, ndat);
      bool ground = true;
      for (int i = 0; i < arity; i++){
	args[i] = doFreeze(info, dat->args[i]);
	ground = ground && args[i]->ground;
      }
      info.commitGround(ndat, ground);
      ndat->ground = ground;
      return ndat;
    }
    case ValueData::OTHER: {
      OtherData* dat = static_cast<OtherData*>(value);
      return dat->freeze(info);
    }
    case ValueData::SET: {
      SetData* dat = static_cast<SetData*>(value);
      return doFreeze(info, dat);
    }
    }
  }
}

SetData* Data::doFreeze(FreezeInfo& info, SetData* set){
  if (set->ground) return set;
  Value nval = info.getVisited(set);
  if (nval != 0) return (SetData*)nval;

  SetData* nset = new (GC) SetData(true, 0, 0, 0, 0);
  if (set->memo.ptr() != 0)
    nset->memo.assign(nset, set->memo.ptr());
  info.markVisited(set, nset);

  bool ground = true;
  Set<Value> elems;
  int i;
  for (i = 0; i < set->ecount; i++){
    Value val = doFreeze(info, set->extens[i]);
    ground = ground && val->ground;
    elems.include(0, val);
  }
  Inten* intens = new (GC) Inten[set->icount];
  for (i = 0; i < set->icount; i++){
    Inten inten = set->intens[i];
    int n = inten->schema->paramcount;
    Value * params = new (GC) Value[n];
    for (int j = 0; j < n; j++){
      Value val = doFreeze(info, inten->params[j]);
      ground = ground && val->ground;
      params[j] = val;
    }
    intens[i] = new (GC)IntenData(inten->schema, params);
  }
  nset->extens = elems.asArray(nset->ecount);
  nset->intens = intens;
  nset->icount = set->icount;
  nset->ground = ground;
  info.commitGround(nset, ground);
  return nset;
}



//----------------------------------------------------------------------------
// Getting Free Vars

VarData* Data::doFindFree(Value value){
  switch (value->kind) {
  case ValueData::VAR: {
    VarData * dat = static_cast<VarData*>(value);
    if (dat->binding == 0) 
      return dat;
    else if (!dat->visiting){
      dat->visiting = true;
      VarData* free = findFree(dat->binding.ptr());
      dat->visiting = false;
      return free;
    } else
      return 0;
  }
  case ValueData::TERM: {
    TermData * dat = static_cast<TermData*>(value);
    int arity = dat->cons->arity;
    for (int i = 0; i < arity; i++){
      VarData* free = findFree(dat->args[i]);
      if (free != 0) return free;
    }
    return 0;
  }
  case ValueData::SET: {
    SetData* dat = static_cast<SetData*>(value);
    return doFindFree(dat);
  }
  default:
    OtherData* dat = static_cast<OtherData*>(value);
    return dat->findFree();
  }
}

VarData* Data::doFindFree(SetData* set){
  int i;
  for (i = 0; i < set->ecount; i++){
    VarData* free = findFree(set->extens[i]);
    if (free != 0) return free;
  }
  for (i = 0; i < set->icount; i++){
    Inten inten = set->intens[i];
    int n = inten->schema->paramcount;
    for (int j = 0; j < n; j++){
      VarData* free = findFree(inten->params[j]);
      if (free != 0) return free;
    }
  }
  return 0;
}
      

    

/*
DynArray<VarData*>& Data::addVar(DynArray<VarData*>& arr, VarData* var){
  int n = arr.length();
  for (int i = 0; i < n; i++){
    int c = arr[i] - var;
    if (c < 0)
      // comes after
      continue;
    else if (c > 0){
      // insert here
      arr.insert(i, var);
      return arr;
    } else 
      // already there
      return arr;
  }
  // append
  arr.push(var);
  return arr;
}

void Data::sampleVars(DynArray<VarData*>& arr,  Value value){
  if (value->ground) return;
  switch (value->kind) {
  case ValueData::VAR: {
    VarData * dat = static_cast<VarData*>(value);
    if (dat->binding == 0) {
      Data::addVar(arr, dat);
    } else {
      if (!dat->visiting){
	dat->visiting = true;
	sampleVars(arr, dat->binding);
	dat->visiting = false;
      }
    }
    break;
  }
  case ValueData::TERM: {
    TermData * dat = static_cast<TermData*>(value);
    int arity = dat->cons->arity;
    for (int i = 0; i < arity; i++){
      sampleVars(arr, dat->args[i]);
    }
    break;
  }
  case ValueData::SET: {
    SetData* dat = static_cast<SetData*>(value);
    for (int i = 0; i < dat->ecount; i++){
      sampleVars(arr, dat->extens[i]);
    }
    // vars in intension parameters don't count 
    break;
  }
  default:
    OtherData* dat = static_cast<OtherData*>(value);
    dat->sampleVars(arr);
  }
}
      
*/
    
//----------------------------------------------------------------------------
// Resolving Variables

Value Data::resolveVars(Value val){
  if (val->ground) return val;
  switch (val->kind) {
  case ValueData::VAR:{
    VarData* dat = static_cast<VarData*>(val);
    if (dat->binding == 0){
      return val;
    } else {
      if (dat->visiting) return val;
      dat->visiting = true;
      val = resolveVars(dat->binding.ptr());
      dat->visiting = false;
      return val;
    }
  }
  default:
    return val;
  }
}

//----------------------------------------------------------------------------
// Getting Sets

SetData* Data::tryGetSet(Value const val){
  switch (val->kind) {
  case ValueData::VAR:{
    VarData* dat = static_cast<VarData*>(val);
    if (dat->binding == 0){
      return 0;
    } else {
      if (dat->visiting) return 0;
      dat->visiting = true;
      SetData* s = tryGetSet(dat->binding.ptr());
      dat->visiting = false;
      return s;
    }
  }
  case ValueData::SET:
    return static_cast<SetData*>(val);
  case ValueData::OTHER:{
    OtherData* dat = static_cast<OtherData*>(val);
    return dat->asSet();
  }
  default:
    // a term: type error
    ASSERT(false);
    return 0;
  }
}

// --------------------------------------------------------------------------
// Union and Intersection

static bool checkGround(Value* extens, int ecount){
  for (int i = 0; i < ecount; i++){
    if (!extens[i]->ground) return false;
  }
  return true;
}

static inline bool checkGround(Inten inten){
  int n = inten->schema->paramcount;
  for (int j = 0; j < n; j++){
    if (!inten->params[j]->ground) return false;
  }
  return true;
}

static bool checkGround(Inten* intens, int icount){
  for (int i = 0; i < icount; i++){
    if (!checkGround(intens[i])) return false;
  }
  return true;
}
  

template <class _A> 
  _A * sunion(_A const * beg1, _A const * end1, 
		 _A const * beg2, _A const * end2, int& actcount){
  int maxcount = (end1-beg1)+(end2-beg2);
  DynArray<_A> arr(maxcount * 2 / 3);
  while (beg1 != end1 && beg2 != end2){
    try {
      Unify::equal(*beg1, *beg2);
      // identical
      arr.push(*beg1++);
      beg2++;
    }
    catch (UnequalFailure& f){
      if (f.order < 0){
	// left less
	arr.push(*beg1++);
      } else {
	arr.push(*beg2++);
      }
    }
    catch (RequireFailure&){
      arr.push(*beg1++);
    }
  }
  while (beg1 != end1) arr.push(*beg1++);
  while (beg2 != end2) arr.push(*beg2++);
  return arr.asArray(actcount);
}

template <class _A> 
  _A * sisect(_A const * beg1, _A const * end1, 
	      _A const * beg2, _A const * end2, int& actcount) 
	      THROW(RequireFailure){
  int maxcount = end1-beg1;
  if (maxcount > end2-beg2) maxcount = end2-beg2;
  DynArray<_A> arr(maxcount);
  while (beg1 != end1 && beg2 != end2){
    try {
      Unify::equal(*beg1, *beg2);
      arr.push(*beg1++);
      beg2++;
    }
    catch (UnequalFailure& f){
      if (f.order < 0){
	beg1++;
      } else {
	beg2++;
      }
    }
    // RequireFailure passed
  }
  return arr.asArray(actcount);
}



SetData * Data::merge(SetData * s1, SetData * s2){
  if (s1 == Data::emptySet)
    return s2;
  else if (s2 == Data::emptySet)
    return s1;

  int ecount;
  Value * extens;

  if (s1->ecount == 0) {
    ecount = s2->ecount;
    extens = s2->extens;
  } 
  else if (s2->ecount == 0){
    ecount = s1->ecount;
    extens = s1->extens;
  }
  else {
    extens = sunion(s1->extens, s1->extens+s1->ecount,
		    s2->extens, s2->extens+s2->ecount,
		    ecount);
  }
  int icount;
  Inten * intens;
  if (s1->icount == 0) {
    icount = s2->icount;
    intens = s2->intens;
  } 
  else if (s2->icount == 0){
    icount = s1->icount;
    intens = s1->intens;
  }
  else {
    intens = sunion(s1->intens, s1->intens+s1->icount,
		    s2->intens, s2->intens+s2->icount,
		    icount);
  }
  return new (GC) SetData(s1->ground && s2->ground,
			  ecount, extens, icount, intens);
}


    
static inline Inten makeExtIntJoin(SetData* s1, bool ground1,
				   SetData* s2, bool ground2){
  return 
    new (GC) IntenData(
	  BuiltinUnit::theUnit->schemas[BuiltinUnit::joinSchemaIndex],
	  newGCArray<Value>(new (GC) SetData(ground1,
					     s1->ecount, s1->extens, 0, 0),
			    new (GC) SetData(ground2,
					     0, 0, s2->icount, s2->intens))
	     );
}

static inline Inten makeExtExtJoin(SetData* s1, bool ground1,
				   SetData* s2, bool ground2){
  return 
    new (GC) IntenData(
	  BuiltinUnit::theUnit->schemas[BuiltinUnit::joinSchemaIndex],
	  newGCArray<Value>(new (GC) SetData(ground1, 
					     s1->ecount, s1->extens, 0, 0),
			    new (GC) SetData(ground2,
					     s2->ecount, s2->extens, 0, 0))
	     );
}

static inline Inten makeIntIntJoin(SetData* s1, bool ground1,
				   SetData* s2, bool ground2){
  return 
    new (GC) IntenData(
	  BuiltinUnit::theUnit->schemas[BuiltinUnit::joinSchemaIndex],
	  newGCArray<Value>(new (GC) SetData(ground1,
					     0, 0, s1->icount, s1->intens),
			    new (GC) SetData(ground2,
					     0, 0, s2->icount, s2->intens))
	     );
}
  
  
SetData * Data::join(SetData * s1, SetData * s2){
  if (s1 == Data::emptySet || s2 == Data::emptySet)
    return Data::emptySet;

  Inten in[4];
  int icount = 0;
  int ecount = 0;
  Value* extens = 0;
  bool eground1 = s1->ground || s1->ecount == 0 || 
                  checkGround(s1->extens, s1->ecount);
  bool iground1 = s1->ground || s1->icount == 0 || 
                  checkGround(s1->intens, s1->icount);
  bool eground2 = s2->ground || s2->ecount == 0 || 
                  checkGround(s2->extens, s2->ecount);
  bool iground2 = s2->ground || s2->icount == 0 || 
                  checkGround(s2->intens, s2->icount);



  // exten1 * exten2 + ...
  if (s1->ecount != 0 && s2->ecount != 0){
    if (eground1 && eground2){
      try {
	extens = sisect(s1->extens, s1->extens+s1->ecount,
			s2->extens, s2->extens+s2->ecount,
			ecount);
      } catch (Failure&){
	// default to represent as an intension
	in[icount++] = makeExtExtJoin(s1, eground1, s2, eground2);
      }
    } else {
      in[icount++] = makeExtExtJoin(s1, eground1, s2, eground2);
    }
  }
  // inten1 * exten2 + ...
  if (s1->icount != 0 && s2->ecount != 0){
    in[icount++] = makeExtIntJoin(s2, eground2, s1, iground1);
  }
  // inten2 * exten1 + ...
  if (s2->icount != 0 && s1->ecount != 0){
    in[icount++] = makeExtIntJoin(s1, eground1, s2, iground2);
  }
  // inten1 * inten2
  if (s1->icount != 0 && s2->icount != 0){
    in[icount++] = makeIntIntJoin(s1, iground1, s2, iground2);
  }
  Inten * intens;
  if (icount == 0){
    intens = 0;
  } else {
    intens = new (GC) Inten[icount];
    std::uninitialized_copy(&in[0], &in[icount], intens);
  }
  if (ecount == 0 && icount == 0)
    return Data::emptySet;
  else {
    return new (GC) SetData(s1->ground&&s2->ground,
			    ecount, extens, icount, intens);
  }

}

 
//----------------------------------------------------------------------------
// Constants

Inten Data::univInten = 0;
TermData * Data::unitTerm = 0;
SetData * Data::emptySet = 0;
SetData * Data::truthSet = 0;
SetData * Data::univSet = 0;

void Data::initializeConstants(){
  univInten = new (NC) IntenData(
			 BuiltinUnit::theUnit->schemas[
						BuiltinUnit::univSchemaIndex],
			 0);
  unitTerm = new (NC) TermData(
			true,
			BuiltinUnit::theUnit->constructors[
						BuiltinUnit::unitConsIndex],
			0);
  emptySet = new (NC) SetData(true, 0, 0, 0, 0);
  truthSet = new (NC) SetData(true, 1, newArray<Value>(unitTerm), 0, 0);
  univSet = new (NC) SetData(true, 0, 0, 1, newArray<Inten>(univInten));
} 

						  


//----------------------------------------------------------------------------
// Priority Tables

/*

int Data::instrPriority[Instr::INSTRNUMBER];

static struct InitData {
  InitData(){
    Data::instrPriority[Instr::LOAD] = NORMAL;
    Data::instrPriority[Instr::WAIT] = NORMAL;
    Data::instrPriority[Instr::WAITLOAD] = NORMAL;
    Data::instrPriority[Instr::STORE] = NORMAL;
    Data::instrPriority[Instr::UNIFY] = NORMAL;
    Data::instrPriority[Instr::MEMBER] = LOW;
    Data::instrPriority[Instr::CALLNATIVE] = NORMAL;
    Data::instrPriority[Instr::TESTNATIVE] = NORMAL;
    Data::instrPriority[Instr::MKTERM] = NORMAL;
    Data::instrPriority[Instr::MKVAR] = NORMAL;
    Data::instrPriority[Instr::MKEMPTY] = NORMAL;
    Data::instrPriority[Instr::MKINTEN] = NORMAL;
    Data::instrPriority[Instr::MKSINGLE] = NORMAL;
    Data::instrPriority[Instr::UNION] = NORMAL;
    Data::instrPriority[Instr::ISECT] = NORMAL;
    Data::instrPriority[Instr::GOTO] = NORMAL;
    Data::instrPriority[Instr::IF] = NORMAL;
    Data::instrPriority[Instr::IFNOT] = NORMAL;
    Data::instrPriority[Instr::FAILURE] = HIGH;
    Data::instrPriority[Instr::SUCCESS] = HIGH;
    Data::instrPriority[Instr::FREEZE] = NORMAL;
    Data::instrPriority[Instr::UNDEF] = HIGH;
    Data::instrPriority[Instr::MKOUTERINTEN] = NORMAL;
    Data::instrPriority[Instr::MKUNIV] = NORMAL;
    Data::instrPriority[Instr::MKNUMBER] = NORMAL;
    Data::instrPriority[Instr::LOADGLOBAL] = NORMAL;
    Data::instrPriority[Instr::LOADGENCONST] = NORMAL;
    Data::instrPriority[Instr::NOP] = NORMAL;
    Data::instrPriority[Instr::MKDENO] = NORMAL;
    Data::instrPriority[Instr::SUBSET] = LOW;
    Data::instrPriority[Instr::WAITLOADGLOBAL] = NORMAL;
    Data::instrPriority[Instr::STOREGLOBAL] = NORMAL;
    Data::instrPriority[Instr::APPLY] = NORMAL;
    Data::instrPriority[Instr::APPLYGLOBAL] = NORMAL;
    Data::instrPriority[Instr::UNIQMEMBER] = LOW;
    Data::instrPriority[Instr::MOVE] = NORMAL;
  }
} initData;



int Data::statusPriority[] = {
  -1,   // NORMAL,
  LOW,     // WAIT,
  LOW,   // MEMCK,
  NORMAL, // IFCKPOST,
  NORMAL, // MUCKPOST,
  LOW,   // FAILED,
  LOW,   // SUCCEEDED,
  LOW,   // UNDEFINED
  LOW,   // ZOMBIE
};

*/
