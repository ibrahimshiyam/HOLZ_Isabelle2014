// $Id: javadriver.cpp,v 1.11 2000/07/21 06:45:15 wg Exp $

#include <typeinfo>

#include "zam.h"
#include "session.h"
#include "loader.h"
#include "natives.h"
#include "print.h"
#include "data.h"
#include "interp.h"

#include "zeta_tools_nzap_ZamJniIface.h"

#include <cstdio>
#include <strstream>

static Interp* interp = 0;
static jobject self = 0;
static JNIEnv* jni = 0;

static void fail(JNIEnv *env, const char * message){
  jclass failClass = env->FindClass("zeta/tools/nzap/ZamIface$Fail");
  if (failClass == 0)
    env->FatalError(
	   "ZAM driver cannot find class zam.tools.nzap.ZamIface.Fail");
  env->ThrowNew(failClass, message);
}

struct JavaReceiver : public Session::Receiver {
  
  void recvJava(char const * mth, char const * msg){
    jclass clazz = jni->FindClass("zeta/tools/nzap/ZamIface");
    if (clazz == 0)
      jni->FatalError(
	     "ZAM driver cannot find class zam.tools.nzap.ZamIface");
    jmethodID send = jni->GetMethodID(clazz, mth, "(Ljava/lang/String;)V");
    if (send == 0){
      jni->FatalError(
    "ZAM driver cannot find sendProgress/sendError method in class ZamIface");
    }
    jstring str = jni->NewStringUTF(msg);
    jni->CallVoidMethod(self, send, str);
  }

};


static struct Tracer : public JavaReceiver {
  void receive(char const * msg){
    recvJava("sendProgress", msg);
  }
} tracer;

static struct Errors : public JavaReceiver {
  void receive(char const * msg){
    recvJava("sendError", msg);
  }
} errors;


JNIEXPORT void JNICALL Java_zeta_tools_nzap_ZamJniIface_start
(JNIEnv *env, jobject inst, jobjectArray fnames){    

  jni = env;
  self = env->NewGlobalRef(inst);
  Session::setTraceReceiver(&tracer);
  Session::setErrorReceiver(&errors);

  DPRINT(flush); DPRINT(flush);
  if (Session::doDPRINT() || Session::doTPRINT()){
    Session::logToFile("LOG");
  }
  GcHeap::init();
  Loader *ld = new (NC) Loader();
  BuiltinUnit::initialize(*ld);
  Data::initializeConstants();
  int nunits = env->GetArrayLength(fnames);
  Unit * units = new (NC) Unit[1+nunits];
  units[0] = BuiltinUnit::theUnit;
  bool errors = false;
  int i;
  for (i = 0; i < nunits; i++){
    jstring s = static_cast<jstring>(env->GetObjectArrayElement(fnames, i));
    const char* fn = env->GetStringUTFChars(s, 0);
    FILE* f = fopen(fn, "rb");
    if (f == NULL){
      std::ostrstream out;
      out << "cannot open file: " << fn << std::ends;
      env->ReleaseStringUTFChars(s, fn);
      fail(env, out.str());
      return; 
    } 
    try {
      units[1+i] = ld->loadUnit(fn, f);
    }
    catch (Session::Error reason){
      errors = true;
    }
    env->ReleaseStringUTFChars(s, fn);
    fclose(f);
  }
  if (errors){
    fail(env, "loading aborted");
    return;
  }
  // fprintf(stderr, "loading finished\n");

  VarData** gvars = new (GC) VarData*[ld->globalVarTab.size()];
  for (unsigned j = 0; j < ld->globalVarTab.size(); j++){
    gvars[j] = ld->globalVarTab[j];
  }
  BuiltinUnit::theLoader = ld;
  interp = new (GC) Interp(1+nunits, units, ld->globalVarTab.size(), gvars);
}

static bool checkInterp(JNIEnv *env){
  if (interp == 0){
    fail(env, "no previous evaluation");
    return false;
  } else
    return true;
}


#define ZAM_STEPSUNTILGC 1000

JNIEXPORT jint JNICALL Java_zeta_tools_nzap_ZamJniIface_step 
  (JNIEnv *env, jobject inst, jint count){
  if (!checkInterp(env)) return 0;
  Interp::StepResult res = Interp::MORE; 
  int steps = count;
  while (steps > 0 && res == Interp::MORE){
    try {
      if (steps > ZAM_STEPSUNTILGC){
	res = interp->step(ZAM_STEPSUNTILGC);
	steps -= ZAM_STEPSUNTILGC;
      } else {
	res = interp->step(steps);
	steps = 0;
      }
      GcObject* roots[] = { interp };
      GcHeap::reclaim(1, roots);
      interp = static_cast<Interp*>(roots[0]);
    }
    catch (Session::Error reason){
      fail(env, "aborted (see diagnostics)");
      DPRINT(flush); DPRINT(flush);
      return 0;
    }
    catch (Failure& f){
      Session::assertFailed(typeid(f).name());
    }
  }
  DPRINT(flush); DPRINT(flush);
  return static_cast<jint>(res);
}

JNIEXPORT jboolean JNICALL Java_zeta_tools_nzap_ZamJniIface_possiblyMore
  (JNIEnv *env, jobject inst){
  if (!checkInterp(env)) return false;
  return interp->possiblyMore();
}

JNIEXPORT jstring JNICALL Java_zeta_tools_nzap_ZamJniIface_getBinding 
  (JNIEnv *env, jobject inst, jstring name){
  if (!checkInterp(env)) return 0;
  const char* sym = env->GetStringUTFChars(name, 0);
  std::ostrstream out;
  interp->printBinding(out, sym);
  env->ReleaseStringUTFChars(name, sym);
  out << std::ends;
  return env->NewStringUTF(out.str());
}

JNIEXPORT jstring JNICALL Java_zeta_tools_nzap_ZamJniIface_profileInfo
  (JNIEnv *env, jobject inst){
  if (!checkInterp(env)) return 0;
  std::ostrstream out;
  interp->printProfile(out);
  out << std::ends;
  return env->NewStringUTF(out.str());
}

JNIEXPORT jlong JNICALL Java_zeta_tools_nzap_ZamJniIface_noOfSteps
  (JNIEnv *env, jobject inst){
  if (!checkInterp(env)) return 0;
  return interp->noOfSteps();
}


JNIEXPORT jstring JNICALL Java_zeta_tools_nzap_ZamJniIface_setSetTarget  
  (JNIEnv *env, jobject inst, jstring name){
  if (!checkInterp(env)) return 0;
  const char* sym = env->GetStringUTFChars(name, 0);
  Value val = interp->getBinding(sym);
  env->ReleaseStringUTFChars(name, sym);
  if (val != 0) val = Data::freeze(val);
  if (val != 0 && val->kind == ValueData::SET){
    const char* ssym = interp->setSetTarget(static_cast<SetData*>(val));
    return env->NewStringUTF(ssym);
  } else {
    fail(env, "variable is not bound or not a set");
    return 0;
  }
}

JNIEXPORT jstring JNICALL Java_zeta_tools_nzap_ZamJniIface_setTermTarget  
  (JNIEnv *env, jobject inst, jstring name, jint pos){
  if (!checkInterp(env)) return 0;
  const char* sym = env->GetStringUTFChars(name, 0);
  Value val = interp->getBinding(sym);
  env->ReleaseStringUTFChars(name, sym);
  if (val != 0) val = Data::freeze(val);
  if (val != 0 && val->kind == ValueData::TERM){
    interp->setTermTarget(pos);
    return name;
  } else {
    fail(env, "variable is not bound or not a term");
    return 0;
  }
}

JNIEXPORT jstring JNICALL Java_zeta_tools_nzap_ZamJniIface_setSeqTarget 
  (JNIEnv *env, jobject inst, jstring name, jint pos){
  if (!checkInterp(env)) return 0;
  const char* sym = env->GetStringUTFChars(name, 0);
  Value val = interp->getBinding(sym);
  env->ReleaseStringUTFChars(name, sym);
  if (val != 0) val = Data::freeze(val);
  if (val != 0 && val->kind == ValueData::OTHER){
    OtherData* dat = static_cast<OtherData*>(val);
    if (dynamic_cast<NativeSeq*>(dat) != 0){
      interp->setSeqTarget(pos);
      return name;
    }
  }
  fail(env, "variable is not bound or not a (resolved) sequence");
  return 0;
}


JNIEXPORT void JNICALL Java_zeta_tools_nzap_ZamJniIface_retSubTarget  
  (JNIEnv *env, jobject inst){
  if (!checkInterp(env)) return;
  interp->retSubTarget();
}
  
  
JNIEXPORT jboolean JNICALL Java_zeta_tools_nzap_ZamJniIface_isSet  
  (JNIEnv *env, jobject inst, jstring name){
  if (!checkInterp(env)) return false;
  const char* sym = env->GetStringUTFChars(name, 0);
  Value val = interp->getBinding(sym);
  env->ReleaseStringUTFChars(name, sym);
  if (val != 0) val = Data::freeze(val);
  return val != 0 && val->kind == ValueData::SET;
}

static bool isArg(char const * p){
  char const * q = p+1;
  return 
    *p == '_' && 
    (*q == 0 ||
     (!(*q >= '0' && *q <= '9') && *q != '{'));
}


JNIEXPORT jstring JNICALL Java_zeta_tools_nzap_ZamJniIface_isTermGet 
  (JNIEnv *env, jobject inst, jstring name){
  if (!checkInterp(env)) return 0;
  const char* sym = env->GetStringUTFChars(name, 0);
  Value val = interp->getBinding(sym);
  env->ReleaseStringUTFChars(name, sym);
  if (val != 0) val = Data::freeze(val);
  if (val != 0 && val->kind == ValueData::TERM){
    TermData* term = static_cast<TermData*>(val);
    char const *name = term->cons->name;
    bool isMix = false;
    while (*name){
      if (isArg(name)){
	isMix = true;
	break;
      }
      name++;
    }
    if (!isMix){
      std::ostrstream os;
      os << term->cons->name;
      if (term->cons->arity > 1){
	os << "(";
	for (int i = 0; i < term->cons->arity; i++){
	  if (i != 0) os << ",";
	  os << "_";
	}
	os << ")";
      } else if (term->cons->arity == 1)
	// os << " _";
	os << "(_)";
      os << std::ends;
      name = os.str();
    } else 
      name = term->cons->name;
    return env->NewStringUTF(name);
  } else
    return NULL;
}


JNIEXPORT jint JNICALL Java_zeta_tools_nzap_ZamJniIface_isSeqGet  
  (JNIEnv *env, jobject inst, jstring name){
  if (!checkInterp(env)) return 0;
  const char* sym = env->GetStringUTFChars(name, 0);
  Value val = interp->getBinding(sym);
  env->ReleaseStringUTFChars(name, sym);
  if (val != 0) val = Data::freeze(val);
  if (val != 0 && val->kind == ValueData::OTHER){
    OtherData* dat = static_cast<OtherData*>(val);
    NativeSeq* seq = dynamic_cast<NativeSeq*>(dat);
    if (seq != 0){
      int i = 1;
      do {
	switch (seq->tail->kind){
	case ValueData::SET:{
	  SetData* set = static_cast<SetData*>(seq->tail);
	  if (set->ecount == 0 && set->icount == 0)
	    // end of seq
	    return i;
	  else
	    return -1;
	}
	case ValueData::OTHER:{
	  dat = static_cast<OtherData*>(seq->tail);
	  seq = dynamic_cast<NativeSeq*>(dat);
	  if (seq != 0){
	    i++;
	    continue;
	  } else
	    return -1;
	}
	default:
	  return -1;
	}
      } while (true);
    } else
      return -1;
  } else
    return -1;
}
