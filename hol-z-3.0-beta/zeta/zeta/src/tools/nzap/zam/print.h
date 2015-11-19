// $Id: print.h,v 1.9 2000/06/22 08:07:52 wg Exp $

#ifndef PRINT_H_INCLUDED
#define PRINT_H_INCLUDED

#include "zam.h"
#include "session.h"

// TIDY UP!!!!!!!!!!!!!!!!!!!

struct FmtIndEndl {};
struct FmtInd {
  int amount;
  FmtInd(int a) :amount(a){}
};
struct FmtUnInd {
  int amount;
  FmtUnInd(int a) :amount(a){}
};
struct FmtAsync {};
struct FmtEndAsync {};

extern FmtIndEndl iendl;
extern FmtInd ind;
extern FmtUnInd unind;
extern FmtAsync async;
extern FmtEndAsync endasync;

inline FmtInd indent(int n){
  return FmtInd(n);
}

inline FmtUnInd unindent(int n){
  return FmtUnInd(n);
}

int setPrintInd(int newind);
void restorePrintInd(int ind);


std::ostream& operator<<(std::ostream& os, FmtIndEndl);
std::ostream& operator<<(std::ostream& os, FmtInd);
std::ostream& operator<<(std::ostream& os, FmtUnInd);
std::ostream& operator<<(std::ostream& os, FmtAsync&);
std::ostream& operator<<(std::ostream& os, FmtEndAsync&);

      
std::ostream& operator<<(std::ostream& os, Constr x);
std::ostream& operator<<(std::ostream& os, Schema x);
std::ostream& operator<<(std::ostream& os, Global x);
std::ostream& operator<<(std::ostream& os, Constructor x);
std::ostream& operator<<(std::ostream& os, NativeFunc x);
std::ostream& operator<<(std::ostream& os, NativePred x);
std::ostream& operator<<(std::ostream& os, Unit x);

std::ostream& operator<<(std::ostream& os, ValueData & v);
std::ostream& operator<<(std::ostream& os, IntenData & i);
std::ostream& operator<<(std::ostream& os, MachineData & m);
std::ostream& operator<<(std::ostream& os, ThreadData & t);
std::ostream& operator<<(std::ostream& os, ThreadData * t);
std::ostream& operator<<(std::ostream& os, GoalData & t);
std::ostream& operator<<(std::ostream& os, MatchData & v);
std::ostream& operator<<(std::ostream& os, ChoiceData & t);
std::ostream& operator<<(std::ostream& os, ThreadData::Status t);
std::ostream& operator<<(std::ostream& os, ThreadDump & t);

void printVar(std::ostream& os, VarData* v);
void printGlobals(std::ostream& os, Machine mach);
void printChoices(std::ostream& os, Goal goal, Choice choice);

void printThreadAt(std::ostream& os, Thread thread, Instr::Pointer code);  

void printThreadTrace(std::ostream& os, Thread thread);  

void printNext(std::ostream& os, Instr::Pointer code, int& step,
	       bool prstep=true);  

void printtree(std::ostream& os, GoalData & goal);

void printbt(Goal goal, const char* msg, Thread thread=0);

void printres(std::ostream& os, Value val);


#endif
