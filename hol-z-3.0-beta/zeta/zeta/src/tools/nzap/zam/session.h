// $Id: session.h,v 1.27 2000/07/06 09:18:24 wg Exp $

#ifndef SESSION_H_INCLUDED
#define SESSION_H_INCLUDED

#include <iostream>
#include <strstream>

#undef ASSERT
#undef DPRINT
#undef TPRINT
#undef MPRINT

// go to configuration file:
#define ZAM_CHECK_ASSERT
#undef ZAM_CHECK_EXPANSIVE_ASSERT
#undef ZAM_DPRINT
#undef ZAM_TPRINT
#define ZAM_MPRINT
#undef ZAM_FAILTRACE
#define ZAM_PROFILE

#define ZAM_MAXMEMO 32



// TIDY UP:
// all messages over receivers? or receivers over C++ streams?

struct Session {

  // exceptions thrown by the session exit entries. May be caught
  // by the driver.
  enum Error { OUTOFMEM, ASSERTFAILED, NYI };

  static std::ostream* debug;
#ifdef ZAM_DPRINT
  static inline bool doDPRINT(){ return Session::debug != 0; }
#else
  static inline bool doDPRINT(){ return false; }
#endif
#ifdef ZAM_TPRINT
  static inline bool doTPRINT(){ return Session::debug != 0; }
#else
  static inline bool doTPRINT(){ return false; }
#endif
#ifdef ZAM_FAILTRACE
  static inline bool doFAILTRACE(){ return true; }
#else
  static inline bool doFAILTRACE(){ return false; }
#endif
#ifdef ZAM_CHECK_ASSERT
  static inline bool doASSERT(){ return true; }
#else  
  static inline bool doASSERT(){ return false; }
#endif
#ifdef ZAM_CHECK_EXPANSIVE_ASSERT
  static inline bool doXASSERT(){ return true; }
#else  
  static inline bool doXASSERT(){ return false; }
#endif
  static void assertFailed();
  static void assertFailed(char const *);
  static void assertFailed(char const * msg, char const *file, 
			   int line);
  static void nyi(char const *);
  static void outOfMemory(int heapSize);
  static void gcRecurDepth(int depth);
  static void logToFile(char* name);

  struct Receiver {
    virtual void receive(char const* message) = 0;
  };

  static Receiver* traces;
  static Receiver* errors;

  static void setTraceReceiver(Receiver* receiver){
    traces = receiver;
  }
  static void setErrorReceiver(Receiver* receiver){
    errors = receiver;
  }

};
  
// the following works only with macros ...

#define SESSION_SEND(recv,streamexpr){\
        std::ostrstream os;\
	os << streamexpr << std::ends;\
	recv->receive(os.str());\
}

#ifdef ZAM_CHECK_ASSERT
/*
// #  define ASSERT(cond) {if (!(cond)) Session::assertFailed(__STRING(cond),\
// 							 __FILE__,\
// 							 __LINE__);}
*/
#  define ASSERT(cond) {if (!(cond)) Session::assertFailed("oops!",\
							 __FILE__,\
							 __LINE__);}
#else
#  define ASSERT(cond) 
#endif

#ifdef ZAM_DPRINT
#  define DPRINT(expr) { if (Session::debug != 0) *Session::debug << expr; }
#else
#  define DPRINT(expr)
#endif

#ifdef ZAM_TPRINT
#  define TPRINT(expr) { if (Session::debug != 0) *Session::debug << expr; }
#else
#  define TPRINT(expr)
#endif

#ifdef ZAM_MPRINT
#  define MPRINT(expr) SESSION_SEND(Session::traces,expr)
#else
#  define MPRINT(expr)
#endif

#endif
