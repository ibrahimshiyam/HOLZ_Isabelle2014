// $Id: loader.h,v 1.7 2000/05/03 16:16:57 wg Exp $

#ifndef LOADER_H_INCLUDED
#define LOADER_H_INCLUDED

#include "zam.h"

#include <cstdio>
#include <string>
#include <map>
#include <vector>


struct Loader {

 public:
  // a mapping for globals 
  std::map<std::string,Global> globals;

 private:

  // a mapping for constructors
  std::map<std::string,Constructor> constructors;

  // a mapping for native functions
  std::map<std::string,NativeFunc> nativeFuncs;

  // a mapping for native predicates
  std::map<std::string,NativePred> nativePreds;

  // a mapping for homorphisms
  std::map<std::string,Hom> homs;


  
 public:

  // the name of the currently loaded unit, if any
  std::string currUnit;

  // the variable table for globals
  std::vector<VarData*> globalVarTab;

  // load a unit from a file
  Unit loadUnit(char const * fname, FILE* file);

  // lookup, with implicite creation
  Global lookupGlobal (char const * name);
  Constructor lookupConstructor (char const * name, int arity);

  // lookup, needs prior registration
  NativePred lookupNativePred (char const * name, int arity);
  NativeFunc lookupNativeFunc (char const * name, int arity);
  Hom lookupHom (char const * name);

  // register a native function
  void registerNativeFunc(char const *name, int arity, NativeFuncType funct);

  // register a native predicate
  void registerNativePred(char const *name, int arity, NativePredType pred);

  // register a homomorphism
  void registerHom(char const *name, HomStart start);


 private:
  bool readBool(FILE* f);
  int readInt(FILE* f);
  char const* readString(FILE* f);
  char const*const* readStrings(FILE* f, int& count);

  Value readBinder(FILE* f, char const* const*vnames, VarData** vtab,
		   int size, Constructor* tab);
  
  void showCurrentUnit();

  enum { acceptableStringSize = 65536 };

};


#endif
