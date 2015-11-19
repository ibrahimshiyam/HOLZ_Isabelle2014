// $Id: session.cpp,v 1.4 2000/05/31 13:42:43 wg Exp $


#include <iostream>
#include <fstream>
#include <strstream>

#include "session.h"
#include "zammem.h"

using namespace std;

ostream* Session::debug = &cerr;


void Session::assertFailed(){
  throw ASSERTFAILED;
}

void Session::assertFailed(char const * msg){
  SESSION_SEND(Session::errors,
	       "FATAL: assertion failed: " << msg);
  *debug << flush;
  abort();
  throw ASSERTFAILED;
}

void Session::assertFailed(char const * msg, char const *file, 
			   int line) {
  SESSION_SEND(Session::errors,
	       "FATAL: assertion failed: " << msg << endl
	       << "       in " << file << " at " << dec << line);
  *debug << flush;
  abort();
  throw ASSERTFAILED;
}

void Session::nyi(char const * message){
  SESSION_SEND(Session::errors,
	       "FATAL: not yet implemented: " << message);
  throw NYI;
}

void Session::outOfMemory(int heapSize){
  SESSION_SEND(Session::errors,
	       "FATAL: out of memory after allocation " 
	       << dec << GcHeap::kb(GcHeap::allocated()) << "k");
  throw OUTOFMEM;
}

void Session::gcRecurDepth(int depth){
  SESSION_SEND(Session::errors,
	       "FATAL: recursive object to large for gc (" 
	       << dec << depth << " indirections)");
  *debug << flush;
  abort();
  throw ASSERTFAILED;
}

void Session::logToFile(char *name){
  ostream* os = new ofstream(name);
  if (os != 0){
    debug = os;
  }
}

struct DefaultTracer : public Session::Receiver {
  void receive(char const* message){
    cerr << message << flush;
  }
} defaultTracer;
  
Session::Receiver* Session::traces = &defaultTracer;
Session::Receiver* Session::errors = &defaultTracer;



