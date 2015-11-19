// $Id: unify.h,v 1.4 2000/05/02 06:31:27 wg Exp $

#ifndef UNIFY_H_INCLUDED
#define UNIFY_H_INCLUDED

#include "zam.h"
#include "session.h"
#include "print.h"
#include "natives.h"


struct Unify {

  static void unify(Goal goal, Value val1, Value val2)
    THROW(UnifyFailure);

  static Match testUnify(Goal goal, Value val1, Value val2)
    THROW(UnifyFailure);

  static void equal(Value val1, Value val2) THROW(UnifyFailure);
  static void equal(Inten inten1, Inten inten2) THROW(UnifyFailure);

};


#endif
