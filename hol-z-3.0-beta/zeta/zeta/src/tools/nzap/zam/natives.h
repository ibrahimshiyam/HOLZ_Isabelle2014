// $Id: natives.h,v 1.23 2000/07/10 06:35:48 wg Exp $

#ifndef NATIVES_H_INCLUDED
#define NATIVES_H_INCLUDED

#include <iostream>
#include <cstring>

#include "zam.h"
#include "loader.h"


struct BuiltinUnit {
  static void initialize(Loader& ld);
  static Unit theUnit;
  static Loader* theLoader;

  enum {
    joinSchemaIndex = 0,
    univSchemaIndex = 1,
    applySchemaIndex = 2,
    enumSchemaIndex = 3,
    subsetSchemaIndex = 4,
    extUnifySchemaIndex = 5,
    waitUnifySetSchemaIndex = 6,
    waitUnifyVarSchemaIndex = 7,
    asSeqUnifySchemaIndex = 8,
    seqAsSetSchemaIndex = 9,
    pairConsIndex = 0,
    unitConsIndex = 1,
    muHomIndex = 0,
    extHomIndex = 1,
    asSeqHomIndex = 2,
    numAddIndex = 0
  };

  /*
  static int const joinSchemaIndex = 0;
  static int const univSchemaIndex = 1;
  static int const applySchemaIndex = 2;
  static int const enumSchemaIndex = 3;
  static int const subsetSchemaIndex = 4;
  static int const extUnifySchemaIndex = 5;
  static int const waitUnifySetSchemaIndex = 6;
  static int const waitUnifyVarSchemaIndex = 7;
  static int const asSeqUnifySchemaIndex = 8;
  static int const seqAsSetSchemaIndex = 9;
  static int const pairConsIndex = 0;
  static int const unitConsIndex = 1;
  static int const muHomIndex = 0;
  static int const extHomIndex = 1;
  static int const asSeqHomIndex = 2;
  static int const numAddIndex = 0;
  */
};



struct NativeDeno : public OtherData {

  char * val;
  inline NativeDeno(char * _val) : OtherData(true), val(_val){}
  inline NativeDeno(GCPlacement, NativeDeno& x) : OtherData(true){
    val = GcHeap::collectArrPrim(strlen(x.val)+1, x.val);
  }
  void gc(){ GcHeap::gc(this); }
  void print(std::ostream&, PrintMethod*);
  void unifyWith(Value,UnifyMethod*) THROW(UnifyFailure);
  Value apply(Goal goal, Value arg) THROW(NativeAbort);
  SetData* asSet() THROW(Abort);
  Value freeze(FreezeInfo& );
  VarData* findFree();
  bool cacheEq(Value);
  unsigned cacheHash();
};
  
struct NativeNum : public OtherData {

  long val;
  inline NativeNum(long _val) : OtherData(true), val(_val){}
  inline NativeNum(GCPlacement, NativeNum& x) : OtherData(true), val(x.val){}
  void gc(){ GcHeap::gc(this); }
  void print(std::ostream&, PrintMethod*);
  void unifyWith(Value, UnifyMethod*) THROW(UnifyFailure);
  Value apply(Goal goal, Value arg) THROW(NativeAbort);
  SetData* asSet() THROW(Abort);
  Value freeze(FreezeInfo& );
  VarData* findFree();
  bool cacheEq(Value);
  unsigned cacheHash();
};


struct NativeSeq : public OtherData {

  Value head;
  Value tail;

  inline NativeSeq() : OtherData(false){}
  inline NativeSeq(bool _ground, Value _head, Value _tail) :
    OtherData(_ground), head(_head), tail(_tail) {}
  NativeSeq(GCPlacement, NativeSeq& x);
  void gc(){ GcHeap::gc(this); }
  void print(std::ostream&, PrintMethod*);
  void unifyWith(Value, UnifyMethod*) THROW(UnifyFailure);
  Value apply(Goal goal, Value arg) THROW(NativeAbort);
  SetData* asSet() THROW(Abort);
  Value freeze(FreezeInfo& );
  VarData* findFree();
  bool cacheEq(Value);
  unsigned cacheHash();
};



#endif

