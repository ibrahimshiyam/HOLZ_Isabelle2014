// $Id: loader.cpp,v 1.3 2000/06/20 07:00:25 wg Exp $


#include "loader.h"
#include <map>
#include <string>
#include <algorithm>



// registering natives

void Loader::registerNativeFunc
  (char const * name, int arity, NativeFuncType funct){
  NativeFunc entry = new (NC) NativeFuncData(name, arity, funct);
  nativeFuncs.insert(
      std::map<std::string,NativeFunc>::value_type(name, entry)
  );
}
							
void Loader::registerNativePred
  (char const * name, int arity, NativePredType pred){
  NativePred entry = new (NC) NativePredData(name, arity, pred);
  nativePreds.insert(
    std::map<std::string,NativePred>::value_type(name, entry)
  );
}

void Loader::registerHom
  (char const * name, HomStart start){
  Hom entry = new (NC) HomData(name, start);
  homs.insert(
    std::map<std::string,Hom>::value_type(name, entry)
  );
}

// lookup

Global Loader::lookupGlobal (char const * name){
  std::map<std::string,Global>::iterator i = globals.find(name);
  if (i == globals.end()){
    // create a new global entry
    int index = globalVarTab.size();
    globalVarTab.push_back(new (GC) VarData(index, name));
    Global entry = new (NC) GlobalData(name, true, index);
    globals.insert(std::map<std::string,Global>::value_type(name, entry));
    return entry;
  } else
    return i->second;
}

Constructor Loader::lookupConstructor(char const * name, int arity){
  std::map<std::string,Constructor>::iterator i = constructors.find(name);
  if (i == constructors.end()){
    // create a new constructor entry
    Constructor entry = new (NC) ConstructorData(name, arity);
    constructors.insert(std::map<std::string,Constructor>::value_type(name, entry));
    return entry;
  } else {
    if (i->second->arity != arity){
      showCurrentUnit();
      SESSION_SEND(Session::errors,
		   "constructor '" << name << "'" << std::endl
		   << "provided with arity " << i->second->arity 
		   << ", but requested is " << arity << std::endl);
      Session::assertFailed();
    }
    return i->second;
  }
}

NativeFunc Loader::lookupNativeFunc (char const * name, int arity){
  std::map<std::string,NativeFunc>::iterator i = nativeFuncs.find(name);
  if (i == nativeFuncs.end()){
    showCurrentUnit();
    SESSION_SEND(Session::errors,
		 "unbound native function '" << name << "'" << std::endl); 
    Session::assertFailed();
  }
  if (i->second->arity != arity){
    showCurrentUnit();
    SESSION_SEND(Session::errors,
		 "native function '" << name << "'" << std::endl
		 << "provided with arity " << i->second->arity 
		 << ", but requested is " << arity << std::endl);
    Session::assertFailed();
  }
  return i->second;
}

NativePred Loader::lookupNativePred (char const * name, int arity){
  std::map<std::string,NativePred>::iterator i = nativePreds.find(name);
  if (i == nativePreds.end()){
    showCurrentUnit();
    SESSION_SEND(Session::errors,
		 "unbound native predicate '" << name << "'" << std::endl); 
    Session::assertFailed();
  }
  if (i->second->arity != arity){
    showCurrentUnit();
    SESSION_SEND(Session::errors,
		 "native predicate '" << name << "'" << std::endl
		 << "provided with arity " << i->second->arity 
		 << ", but requested is " << arity << std::endl);
    Session::assertFailed();
  }
  return i->second;
}

Hom Loader::lookupHom (char const * name){
  std::map<std::string,Hom>::iterator i = homs.find(name);
  if (i == homs.end()){
    showCurrentUnit();
    SESSION_SEND(Session::errors,
		 "unbound homomorphism '" << name << "'" << std::endl); 
    Session::assertFailed();
  }
  return i->second;
}


// basic file IO 


int Loader::readInt(FILE* f){
  unsigned int s = 0;
  for (;;){
    int c = getc(f);
    if (c == EOF){
      showCurrentUnit();
      SESSION_SEND(Session::errors,
		   "unexpected end of file input" << std::endl);
      Session::assertFailed();
    }
    if (c >= 128){
      return (s << 7) + (c % 128);
    } else
      s = (s << 7) + c;
  }
}


char const* Loader::readString(FILE* f){
  int l = readInt(f);
  if (l < 0 || l > acceptableStringSize){
    showCurrentUnit();
    SESSION_SEND(Session::errors,
		 "found string with invalid size (" 
		 << l << " notin [0.." << acceptableStringSize << "])");
    Session::assertFailed();
  }
  char *buf = new (NC) char[l+1];
  for (int i = 0; i < l; i++){
    int c = getc(f);
    if (c == EOF){
      showCurrentUnit();
      SESSION_SEND(Session::errors,
		   "unexpected end of file input" << std::endl);
      Session::assertFailed();
    }
    buf[i] = (unsigned char)c;
  }
  buf[l] = 0;
  return buf;
}

bool Loader::readBool(FILE* f){
  int b = getc(f);
  if (b == 0) return false;
  else if (b == 1) return true;
  else {
    showCurrentUnit();
    SESSION_SEND(Session::errors,
		 "found boolean with invalid encoding" << std::endl);
    Session::assertFailed();
    return false;
  }
}

char const * const * Loader::readStrings(FILE* f, int& count){
  count = readInt(f);
  char const * * strings = new (NC) char const *[count];
  for (int i = 0; i < count; i++){
    strings[i] = readString(f);
  }
  return strings;
}
  
  

// reading binders

Value Loader::readBinder(FILE* f, char const* const* vnames,
			 VarData** vtab, int size, Constructor * tab){
  bool isVar = readBool(f);
  if (isVar) {
    int index = readInt(f);
    if (vtab[index] == 0){
      // negative to indicate binder
      vtab[index] = new (NC) VarData((-index)-1, vnames[index]); 
    } 
    return vtab[index];
  } else {
    int index = readInt(f);
    if (index < 0 || index >= size){
      showCurrentUnit();
      SESSION_SEND(Session::errors,
		   "invalid constructor index in schema binder"
		   << std::endl);
      Session::assertFailed();
    }
    int count = readInt(f);
    Value * args = new (NC) Value[count];
    bool ground = true;
    for (int i = 0; i < count; i++){
      args[i] = readBinder(f, vnames, vtab,  size, tab);
      ground = ground && args[i]->ground;
    }
    return new (NC) TermData(ground, tab[index], args);
  }
}
    
  

// reading units

Unit Loader::loadUnit(char const * fname, FILE* f) {

  currUnit = fname; 

  // name
  char const * name = readString(f);


  // parents
  int parentCount;
  char const * const * parents = readStrings(f, parentCount);

  // globals
  int globalCount = readInt(f);
  Global * globals = new (NC) Global[globalCount];
  int i;
  for (i = 0; i < globalCount; i++){
    char const * name = readString(f);
    bool isExtern = readBool(f);
    if (isExtern){
      globals[i] = lookupGlobal(name);
    } else {
      // allocate a local variable
      int index = globalVarTab.size();
      globalVarTab.push_back(new (NC) VarData(index, name));
      globals[i] = new (NC) GlobalData(name, false, index);
    }
  }

  // constructors
  int constructorCount = readInt(f);
  Constructor * constructors = new (NC) Constructor[constructorCount];
  for (i = 0; i < constructorCount; i++){
    char const * name = readString(f);
    int arity = readInt(f);
    constructors[i] = lookupConstructor(name, arity);
  }

  // native functions
  int nativeFuncCount = readInt(f);
  NativeFunc * nativeFuncs = new (NC) NativeFunc[nativeFuncCount];
  for (i = 0; i < nativeFuncCount; i++){
    char const * name = readString(f);
    int arity = readInt(f);
    nativeFuncs[i] = lookupNativeFunc(name, arity);
  }

  // native predicates
  int nativePredCount = readInt(f);
  NativePred * nativePreds = new (NC) NativePred[nativePredCount];
  for (i = 0; i < nativePredCount; i++){
    char const * name = readString(f);
    int arity = readInt(f);
    nativePreds[i] = lookupNativePred(name, arity);
  }

  // homomorphisms
  int homCount = readInt(f);
  Hom * homs = new (NC) Hom[homCount];
  for (i = 0; i < homCount; i++){
    char const * name = readString(f);
    homs[i] = lookupHom(name);
  }

  // denotations
  int denotationCount;
  char const * const * denotations = readStrings(f, denotationCount);

  // code size (already here!!)
  int codeSize = readInt(f);
  Instr::Unit* code = new (NC) Instr::Unit[codeSize];

  // schema
  int initSchemaIndex = readInt(f);
  int schemaCount = readInt(f);
  Schema * schemas = new (NC) Schema[schemaCount];
  // allocate the unit such that we can backlink from schemas
  Unit unit = new (NC) UnitData(name, 
			   parentCount, parents,
			   globalCount, globals,
			   constructorCount, constructors,
			   nativeFuncCount, nativeFuncs,
			   nativePredCount, nativePreds,
			   homCount, homs,
			   denotationCount, denotations,
			   initSchemaIndex,
			   schemaCount,
			   schemas,
			   codeSize,
			   code);
  for (i = 0; i < schemaCount; i++){
    char const * name = readString(f);
    int paramcount;
    char const * const * paramnames = readStrings(f, paramcount);
    int varcount;
    char const * const * varnames = readStrings(f, varcount);
#ifdef ZAM_WIN32
    VarData** vtab = new VarData* [varcount];
#else
    VarData* vtab[varcount];
#endif
    for (int k = 0; k < varcount; k++) vtab[k] = 0;
    Value binder = readBinder(f, varnames, vtab,
			      constructorCount, constructors);
    int constrcount = readInt(f);
    // allocate the schema such that we can backlink from constraints
    Constr * constrs = new (NC) Constr[constrcount];
    Schema schema = new (NC) SchemaData(unit, name, paramcount, paramnames,
				   varcount, varnames, binder,
				   constrcount, constrs);
    for (int j = 0; j < constrcount; j++){
      char const * name = readString(f);
      int regCount = readInt(f);
      int codeOffs = readInt(f);
      constrs[j] = new (NC) ConstrData(schema, name, regCount, 
				       code+codeOffs);
    }
    schemas[i] = schema;
#   ifdef ZAM_WIN32
      delete vtab;
#   endif
  }
  Instr::Unit *pc = code;
  while (codeSize-- > 0){
    int c = getc(f);
    if (c == EOF){
      showCurrentUnit();
      SESSION_SEND(Session::errors,
		   "unexpected end of input" << std::endl);
      Session::assertFailed();
    }
    *pc++ = (unsigned)c;
  }
  currUnit = "";
  return unit;
}
  
  
// register builtin units

/*
void Loader::registerBuiltin(Unit unit){
  for (int i = 0; i < unit->globalCount; i++){
    Global x = unit->globals[i];
    // FIXME: varinx!!!
    globals.insert(std::map<std::string,Global>::value_type(x->name, x));
  }
  for (int i = 0; i < unit->constructorCount; i++){
    Constructor x = unit->constructors[i];
    constructors.insert(std::map<std::string,Constructor>::value_type(x->name, x));
  }
  for (int i = 0; i < unit->nativeFuncCount; i++){
    NativeFunc x = unit->nativeFuncs[i];
    nativeFuncs.insert(std::map<std::string,NativeFunc>::value_type(x->name, x));
  }
  for (int i = 0; i < unit->nativePredCount; i++){
    NativePred x = unit->nativePreds[i];
    nativePreds.insert(std::map<std::string,NativePred>::value_type(x->name, x));
  }
  for (int i = 0; i < unit->homCount; i++){
    Hom x = unit->homs[i];
    homs.insert(std::map<std::string,Hom>::value_type(x->name, x));
  }
}
*/



// error reporting

void Loader::showCurrentUnit(){
  if (currUnit.size() != 0){
    SESSION_SEND(Session::errors,
		 "while loading " << currUnit << ": ");
  }
}
