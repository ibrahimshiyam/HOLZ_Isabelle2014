// $Id: data.h,v 1.24 2000/06/20 07:00:25 wg Exp $

#ifndef DATA_H_INCLUDED
#define DATA_H_INCLUDED

#include "zam.h"
#include "session.h"
#include "print.h"
#include "natives.h"


struct Data {

  // read an index from instruction stream
  static inline int readIndex(Instr::Pointer& pc){
    int s = 0;
    for (;;){
      unsigned int c = *pc++;
      if (c >= 128){
	return (s << 7) + (c % 128);
      } else
	s = (s << 7) + c;
    }
  }
  

  // freeze a value
  static inline Value freeze(Value val){
    if (val->ground){
      return val;
    } else {
      FreezeInfo info;
      return doFreeze(info, val);
    }
  }

  static Value doFreeze(FreezeInfo&, Value);

  static inline SetData* freeze(SetData* set){
    if (set->ground){
      return set;
    } else {
      FreezeInfo info;
      return doFreeze(info, set);
    }
  }

  static SetData* doFreeze(FreezeInfo&, SetData*);


  // find a free variable
  static inline VarData* findFree(Value val){
    if (val->ground)
      return 0;
    else
      return doFindFree(val);
  }

  static VarData* doFindFree(Value val);

  static inline VarData* findFree(SetData* set){
    if (set->ground)
      return 0;
    else
      return doFindFree(set);
  }

  static VarData* doFindFree(SetData* set);

  // sorting
  /*
  static Value* sortWithDups(int ecount, Value* extens, int& rcount);
  static DynArray<Value>& insertSorted(DynArray<Value>& arr, Value value);
  */


  // resolve outest variable binding(s)
  static Value resolveVars(Value val);

  // try to get a set (resolving bindings and calling conversions)
  static SetData * tryGetSet(Value const val);

  // merge & join sets
  static SetData * merge(SetData *, SetData *);
  static SetData * join(SetData *, SetData *);
  

  // make a pair
  static inline Value makePair(const Value v1, const Value v2) {
    return
      new (GC) TermData(v1->ground && v2->ground,
		   BuiltinUnit::theUnit->constructors[
					   BuiltinUnit::pairConsIndex],
		   newGCArray<Value>(v1, v2));
  }

  /*
  // get free variables of value
  static void sampleVars(DynArray<VarData*>& arr,  Value value);

  static inline DynArray<VarData*> freeVars(Value val){
    DynArray<VarData*> arr;
    sampleVars(arr, val);
    return arr;
  }
  */


  /*
  // insert a variable in an array (avoiding duplicates)
  static DynArray<VarData*>& addVar(DynArray<VarData*>& arr, VarData* var);
  */

  // Value Constants (need to be intialized!)
  static Inten univInten;
  static TermData* unitTerm;
  static SetData* emptySet;
  static SetData* univSet;
  static SetData* truthSet;
  static void initializeConstants();

  
};


#endif
