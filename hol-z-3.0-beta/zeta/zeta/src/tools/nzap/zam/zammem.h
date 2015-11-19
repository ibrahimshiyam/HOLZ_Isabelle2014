// $Id: zammem.h,v 1.28 2000/07/17 08:31:45 wg Exp $

#ifndef ZAMMEM_H_INCLUDED
#define ZAMMEM_H_INCLUDED

#include <cstdlib>
#include <new>

#include <strstream>
#include "session.h"

#define GC_PAGESIZE     (1024 * 1024)
#define GC_MINHEAPSIZE  (32 * 1024l * 1024)
#define GC_MAXHEAPSIZE  (96 * 1024 * 1024)
#define GC_MAXSPACESIZE (16 * 1024 * 1024)
#define GC_COLLECT      100  // % of maxspacesize 
#define GC_MAXRECUR     (1000 * 30)
#define GC_COLLECTALLSTEP   16  // every nth collection full gc (?) ...
#define GC_COLLECTALL   80  // % of maxheapsize

#define GC_ALIGN        1


#undef GC_DISABLE


// --------------------------------------------------------------------------
// Object base classes

struct GcSpace;

// base class of any gc-ed object
struct GcObject {
  GcObject* forward;
  int generation;
  virtual void gc() = 0;
};

// pseudo base class for array objects
struct GcArrayObject {
  GcArrayObject* forward;
  int generation;
  // data starts here
};



// --------------------------------------------------------------------------
// Roots, used to represent entry tables

struct GcRootLink {
  GcRootLink* prev;
  GcRootLink* next;
  GcRootLink() : prev(this), next(this) {}
  inline void append(GcRootLink& after){
    prev = &after;
    next = after.next;
    after.next = after.next->prev = this;
  }
  inline void remove(){
    prev->next = next;
    next->prev = prev;
    next = prev = this;
  }
};

struct GcRoot : GcRootLink {

  // the space this root belongs to
  GcSpace* space;

  // virtual method to handle this root on collect
  virtual void collect() = 0;

  // virtual method to return destination generation
  virtual int generation() = 0;

  inline GcRoot() : space(0) {}

};

struct GcForwardInfo {
  GcRoot* root;
  inline GcForwardInfo() : root(0) {}
};


struct GcRootObject : GcRoot {
  
  // pointer to  GcObject
  GcObject** object;

  inline GcRootObject(GcObject** _object) : object(_object) {
  }

  void collect();

  inline int generation(){
    return (*object)->generation;
  }
};


// base class for gc-ed objects with weakly gc-ed contents
struct GcWeakObject : GcObject {
  GcWeakObject* previous;
  virtual void weakGc() = 0;
};
  
  
  

// --------------------------------------------------------------------------
// Memory Spaces

struct GcPage {

  // previous page
  GcPage* previous;

  // next page
  GcPage* next;

  // size of this page
  unsigned size;

  // how much it is filled 
  unsigned fill;

  // the memory base
  char* base;

  inline GcPage(GcPage* p, GcPage* n, unsigned s, unsigned f, char* b) :
    previous(p), next(n), size(s), fill(f), base(b){
  }

};




struct GcSpace {

  // the generation
  int generation;

  // a shared static generation counter
  static int generationCounter;

  // a shared total allocation counter
  static unsigned totalAlloc;

  // the previous space
  GcSpace* previous;

  // the roots of this space
  GcRootLink roots;

  // the weak objects of this space
  GcWeakObject* weakObjects;

  // the pages of this space
  GcPage* pages;

  // the size of this space (sum of size of its pages)
  int size;

  // create a new space with an empty dummy page
  GcSpace(GcSpace* _previous) : generation(++generationCounter),
    previous(_previous), weakObjects(0),
    pages(new GcPage(0,0,0,0,0)), size(0) {
  }

  // ensure that size bytes can be allocated
  void reserve(unsigned size);

  // clear a space, freeing all used memory
  void clear();

  // release a space, reusing its memory for alloc
  void release();

  // tell how many bytes are used in a space
  unsigned tell();

  // allocate object from this space
  inline GcObject* alloc(unsigned osize){
    osize = ((osize + GC_ALIGN - 1)/GC_ALIGN)*GC_ALIGN;
    if (pages->fill+osize > pages->size){
      reserve(osize);
    }
    GcObject* ob = static_cast<GcObject*>(
                       static_cast<void*>(pages->base+pages->fill)
		   );
    pages->fill += osize;
    ob->forward = 0;
    ob->generation = generation;
    return ob;
  }

  // allocate array from this space
  inline GcArrayObject* allocArray(unsigned osize){
    osize += sizeof(GcArrayObject);
    osize = ((osize + GC_ALIGN - 1)/GC_ALIGN)*GC_ALIGN;
    if (pages->fill+osize > pages->size){
      reserve(osize);
    }
    GcArrayObject* ob = static_cast<GcArrayObject*>(
                          static_cast<void*>(pages->base+pages->fill)
		        );
    pages->fill += osize;
    ob->forward = 0;
    ob->generation = generation;
    return ob;
  }

  // alloc temporary memory 
  inline void* allocTemp(unsigned osize){
    osize = ((osize + GC_ALIGN - 1)/GC_ALIGN)*GC_ALIGN;
    if (pages->fill+osize > pages->size){
      reserve(osize);
    }
    void* p = static_cast<void*>(pages->base+pages->fill);
    pages->fill += osize;
    return p;
  }

  // tell whether pointer belongs to this space
  /*
  inline bool here(GcObject *ob){
    return ob->origin == this;
  }
  inline bool here(GcArrayObject *ob){
    return ob->origin == this;
  }
  */

};


// --------------------------------------------------------------------------
// The heap

struct GcHeap {


 public:
  // the fixed (uncollected) space
  static GcSpace* fixed;

  // the most recent collected space
  static GcSpace* from;

 private:
  // allocated bytes after last GC
  static unsigned lastTotal;

  // a counter for recursion depth
  static unsigned recurDepth;

  // internal collection functions
  static void doCollect(int, int, GcSpace*, GcSpace*, int, GcObject**);
  static void collectRoots(GcSpace* space, int& rootCoount, 
			   int& activeRootCount);
  static void collectWeaks(GcWeakObject* start, GcWeakObject* end,
			   int& weakCount);
  

 public:

  // the oldest generation we currently collect
  static int collectFrom;

  // initialize heap, clearing an older heap if necessary
  static void init();

  // tell how many bytes are in use
  static inline unsigned allocated(){
    return GcSpace::totalAlloc;
  }

  // convert bytes into kilo byte
  static inline char* kb(int b){
    std::ostrstream os;
    if (b < 1024){
	os << std::dec << b << "b";
    } else {
      b = (b+1023)/1024;
      if (b < 1024){
	  os << std::dec << b << "k";
      } else {
	b = (b+1023)/1024;
	os << std::dec << b << "m";
      }
    }
    os << std::ends;
    return os.str();
  }

  // allocate gc'ed memory 
  static inline void* gcAlloc(int size){
    return static_cast<void*>(from->alloc(size));
  }

  // allocate gc'ed memory for an array 
  static inline void* gcAllocArray(int size){
    return static_cast<void*>(from->allocArray(size)+1);
  }

  // allocate non-gc'ed memory 
  static inline void* noGcAlloc(int size){
    if (fixed == 0) {
      fixed = new GcSpace(0);
      from = new GcSpace(fixed);
    }
    return static_cast<void*>(fixed->alloc(size));
  }

  // allocate non-gc'ed memory for an array 
  static inline void* noGcAllocArray(int size){
    if (fixed == 0) {
      fixed = new GcSpace(0);
      from = new GcSpace(fixed);
    }
    return static_cast<void*>(fixed->allocArray(size)+1);
  }

  // find space of generation
  static inline GcSpace* findGen(int gen){
    GcSpace* space = from;
    while (space->generation != gen){
      ASSERT(space->previous != 0);
      space = space->previous;
    }
    return space;
  }

  // allocate temporary memory in given generation 
  static inline void* tempAlloc(int gen, int size){
    return static_cast<void*>(findGen(gen)->allocTemp(size));
  }

  // remove a forward reference if it is set in info
  static inline void delForward(GcForwardInfo& info){
    if (info.root != 0 && info.root->next != info.root){
      info.root->remove();
    }
  }
    
  // a shortcut for forwarding the given object  
  template <class T>
  static inline void forwardRef(GcObject* context, 
				GcForwardInfo& info,
				T*& object){
    if (context != 0 &&
	object != 0 && context->generation < object->generation){
      void * p = &object;
      if (info.root != 0){
	GcRootObject* r = static_cast<GcRootObject*>(info.root);
	r->object = static_cast<GcObject**>(p);
	if (info.root->next == info.root)
	  r->append(info.root->space->roots);
      } else {
	GcSpace* space = findGen(context->generation);
	GcRoot* r = new (space->allocTemp(sizeof(GcRootObject))) 
			GcRootObject(static_cast<GcObject**>(p));
	r->space = space;
	r->append(space->roots);
	info.root = r;
      }
    } else {
      delForward(info);
    }
  }


 public:
  // collect some memory if necessary or forced
  static void reclaim(int rcount, GcObject** roots, bool force=false);

  // collect the given pointer. called from GC constructor to collect
  // a field.
  template <class T>
  static inline T* collect(T* x){
    if (x == 0) return x;

    GcObject* o = static_cast<GcObject*>(static_cast<void*>(x));
    if (o->forward != 0){
      // already collected
      return static_cast<T*>(static_cast<void*>(o->forward));
    } else if (o->generation >= collectFrom){
      // to be collected
      if (++recurDepth > GC_MAXRECUR) Session::gcRecurDepth(recurDepth);
      o->gc();
      recurDepth--;
      return static_cast<T*>(static_cast<void*>(o->forward));
    } else {
      // from an older generation
      return x;
    }
  }

  // collect the given array and its contents, pointers to GcObject.
  // called from GC constructor to collect an array field.
  template <class T>
  static inline T** collectArr(int size, T** x){
    if (x == 0) return x;
    GcArrayObject* a = static_cast<GcArrayObject*>(static_cast<void*>(x))-1;
    if (a->forward != 0){
      // already collected
      return static_cast<T**>(static_cast<void*>(a->forward+1));
    } else if (a->generation >= collectFrom){
      // to be collected
      GcArrayObject* n = 
	from->allocArray(size * sizeof(T*));
      T** r = static_cast<T**>(static_cast<void*>(n+1));
      a->forward = n;
      for (int i = 0; i < size; i++){
	r[i] = collect(x[i]);
      }
      return r;
    } else {
      // from an older generation
      return x;
    }
  }

  // collect the given aggregated GC object. Needs to be
  // specialized for non-gc objects (see example for <bool> below)
  template <class T>
  static inline void collect(T& n, T&x){
    new (static_cast<void*>(&n)) T(GC, x);
  }

  // collect the given array and its contents, aggregated GcObjects.
  // called from GC constructor to collect an array field.
  template <class T>
  static inline T* collectArrAgg(int size, T* x){
    if (x == 0) return x;
    GcArrayObject* a = static_cast<GcArrayObject*>(static_cast<void*>(x))-1;
    if (a->forward != 0){
      // already collected
      return static_cast<T*>(static_cast<void*>(a->forward+1));
    } else if (a->generation >= collectFrom){
      // to be collected
      GcArrayObject* n = from->allocArray(size * sizeof(T));
      T* r = static_cast<T*>(static_cast<void*>(n+1));
      a->forward = n;
      for (int i = 0; i < size; i++){
	collect(r[i], x[i]);
      }
      return r;
    } else {
      // from an older generation
      return x;
    }
  }

  // collect the given array and its contents, primitive objects.
  // called from GC constructor to collect an array field.
  template <class T>
  static inline T* collectArrPrim(int size, T* x){
    if (x == 0) return x;
    GcArrayObject* a = static_cast<GcArrayObject*>(static_cast<void*>(x))-1;
    if (a->forward != 0){
      // already collected
      return static_cast<T*>(static_cast<void*>(a->forward+1));
    } else if (a->generation >= collectFrom){
      // to be collected
      GcArrayObject* n = from->allocArray(size * sizeof(T));
      T* r = static_cast<T*>(static_cast<void*>(n+1));
      a->forward = n;
      for (int i = 0; i < size; i++){
	r[i] = x[i];
      }
      return r;
    } else {
      // from an older generation
      return x;
    }
  }


  // garbage collect the given object.
  // called by virtual "gc",
  // which is just a wrapper around this to get static type info
  template <class T>
  static inline void gc(T* x){
    GcObject* n = from->alloc(sizeof(T));
    x->forward = n;
    new (static_cast<void*>(n)) T(GC, *x);
  }
      
};

#ifndef ZAM_WIN32
template <>
  inline void GcHeap::collect<bool>(bool& n, bool& x){
  n = x;
}
#endif

  

// --------------------------------------------------------------------------
// Standard Memory Functions


enum GCPlacement { GC };
enum NCPlacement { NC };
enum TMPlacement { TM };

#ifdef GC_DISABLE

inline void* operator new(size_t size, GCPlacement) { 
  return malloc(size);
}

inline void operator delete(void* ptr, GCPlacement) { 
  free(ptr);
}

inline void* operator new[](size_t size, GCPlacement) {
  return malloc(size);
}

inline void operator delete[](void* ptr, GCPlacement) { 
  free(ptr);
}

inline void* operator new(size_t size, NCPlacement) { 
  return malloc(size);
}

inline void operator delete(void* ptr, NCPlacement) { 
  free(ptr);
}

inline void* operator new[](size_t size, NCPlacement) {
  return malloc(size);
}

inline void operator delete[](void* ptr, NCPlacement) { 
  free(ptr);
}

#else 

inline void* operator new(size_t size) { 
  return malloc(size);
}

inline void operator delete(void* ptr) { 
  free(ptr);
}

inline void* operator new[](size_t size) {
  return malloc(size);
}

inline void operator delete[](void* ptr) { 
  free(ptr);
}



inline void* operator new(size_t size, GCPlacement) { 
  return GcHeap::gcAlloc(size);
}

inline void operator delete(void* ptr, GCPlacement) { 
}

inline void* operator new[](size_t size, GCPlacement) {
  return GcHeap::gcAllocArray(size);
}

inline void operator delete[](void* ptr, GCPlacement) { 
}


inline void* operator new(size_t size, NCPlacement) { 
  return GcHeap::noGcAlloc(size);
}

inline void operator delete(void* ptr, NCPlacement) { 
}

inline void* operator new[](size_t size, NCPlacement) {
  return GcHeap::noGcAllocArray(size);
}

inline void operator delete[](void* ptr, NCPlacement) { 
}

inline void* operator new(size_t size, TMPlacement) { 
  return GcHeap::tempAlloc(GcHeap::from->generation, size);
}

inline void operator delete(void* ptr, TMPlacement) { 
}

inline void* operator new[](size_t size, TMPlacement) {
  return GcHeap::tempAlloc(GcHeap::from->generation, size);
}

inline void operator delete[](void* ptr, TMPlacement) { 
}



#endif



// --------------------------------------------------------------------------
// "dynamic" pointers -- pointers with the potential for refering to 
//  future spaces

template <class T>
struct DynPtr {
  T* _ptr;
  GcForwardInfo _info;
  inline DynPtr() : _ptr(0) {}
  inline DynPtr(DynPtr& x) : _ptr(x._ptr), _info(x._info){
  }
  explicit inline DynPtr(T* x) : _ptr(x) {
  }
  inline bool operator==(T* p){
    return _ptr == p;
  }
  inline bool operator!=(T* p){
    return _ptr != p;
  }
  inline T& operator*(){
    return *_ptr;
  }
  inline T* operator->(){
    return _ptr;
  }
  inline T* ptr(){
    return _ptr;
  }
  inline DynPtr& assign(GcObject* context, T* nptr){
    _ptr = nptr;
    GcHeap::forwardRef(context, _info, _ptr);
    return *this;
  }
  inline DynPtr(GcObject* context, T* ptr){
    assign(context, ptr);
  }
  inline void collect(DynPtr& x){
    _info.root = 0;
    _ptr = GcHeap::collect(x._ptr);
  }
  inline DynPtr(GCPlacement, DynPtr& x){
    collect(x);
  }
  inline void clear(){
    GcHeap::delForward(_info);
    _ptr = 0;
  }
};

template <class T>
struct DynPtrArr {
  T** _data;
  GcForwardInfo* _infos;
  int _size;
  inline DynPtrArr() : _data(0), _infos(0), _size(0) {
  }
  inline DynPtrArr(int n){
    _data = new (GC) T*[n];
    _infos = new (GC) GcForwardInfo[n];
    _size = n;
  }
  inline DynPtrArr(GCPlacement, DynPtrArr& x){
    _data = GcHeap::collectArr(x._size, x._data);
    _infos = new (TM) GcForwardInfo[x._size];
    _size = x._size;
  }
  inline T** data(){
    return _data;
  }
  inline void assign(int i, T* p){
    _data[i] = p;
    GcArrayObject* a =
      static_cast<GcArrayObject*>(static_cast<void*>(_data))-1;
    if (p != 0 && a->generation < p->generation){
      void *pp = &_data[i];
      if (_infos[i].root != 0){
	GcRootObject* r = static_cast<GcRootObject*>(_infos[i].root);
	r->object = static_cast<GcObject**>(pp);
	if (r->next == r) r->append(r->space->roots);
      } else {
	GcSpace* space = GcHeap::findGen(a->generation);
	GcRootObject* r = new (space->allocTemp(sizeof(GcRootObject))) 
			      GcRootObject(static_cast<GcObject**>(pp));
	r->space = space;
	r->append(space->roots);
	_infos[i].root = r;
      }
    } else {
      GcHeap::delForward(_infos[i]);
    }
  }
  inline void clear(int i){
    GcHeap::delForward(_infos[i]);
    _data[i] = 0;
  }
  inline T* const & operator[](int i){
    return _data[i];
  }
};


#if 0
// --------------------------------------------------------------------------
// "weak" pointers -- pointers which are automatically cleared on GC if
// their content is not reachable from somewhere else

template <class T>
struct WeakPtr : GcRootLink {
  T* _ptr;
  GcSpace* space;
  inline WeakPtr(GcSpace* _space, T* ptr) : _ptr(ptr), space(_space) {
    append(space->weakPtrs);
  }
  inline WeakPtr(GcObject* context, T* ptr) : _ptr(ptr) {
    space = GcHeap::findGen(context->generation);
    append(space->weakPtrs);
  }
  inline void collect(GcObject* context, WeakPtr& x){
    _ptr = x._ptr; // defer actual collection
    space = GcHeap::findGen(context->generation);
    append(space->weakPtrs);
  }
  inline bool operator==(T* p){
    return _ptr == p;
  }
  inline bool operator!=(T* p){
    return _ptr != p;
  }
  inline T& operator*(){
    return *_ptr;
  }
  inline T* operator->(){
    return _ptr;
  }
  inline T* ptr(){
    return _ptr;
  }
  inline WeakPtr& operator=(T* nptr){
    _ptr = nptr;
  }
};
#endif



#endif
