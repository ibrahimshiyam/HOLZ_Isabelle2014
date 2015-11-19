// $Id: zamutil.h,v 1.20 2000/07/19 08:17:09 wg Exp $

#ifndef ZAMUTIL_H_INCLUDED
#define ZAMUTIL_H_INCLUDED

#include <cstddef>
#include <cstdlib>
#include <iterator>
#include <iostream>
#include <algorithm>

#include "zammem.h"
#include "session.h"



// =========================================================================
// THROW Declarations

// it seems that throw declarations on most compilers currently
// in fact slow down execution
// because code is generated which checks the throw assertion at runtime ...

#define THROW(x) 
#define NoTHROW()


// =========================================================================
// Ring Lists

template <class T> struct Ring;
template <class T> struct RingIterator;

template <class T>
struct RLink : public GcObject {
  public:
  void gc(){ ASSERT(false); }
  friend class Ring<T>;
  friend class RingIterator<T>;
  // private:
  size_t offset; // FIXME: const, also copy method
  RLink* prev;
  RLink* next;
   //public:

  inline T* getBase(){
    return 
      static_cast<T*>(
        static_cast<void*>(
	   static_cast<char*>(static_cast<void*>(this)) - offset
	)
      );
  }
  inline RLink<T>* getLink(T* x){
    return 
      static_cast<RLink<T>*>(
        static_cast<void*>(
	   static_cast<char*>(static_cast<void*>(x)) + offset
	)
      );
  }

  RLink(RLink const& source){
    // if link is unattached, relocate pointers, otherwise fail
    if (this == source.prev && source.prev == source.next){
      prev = next = this;
    } else
      ASSERT(false);
  }
  RLink(T* _this)
	  : offset(_this != 0 ? static_cast<char*>(static_cast<void*>(this)) -
		               static_cast<char*>(static_cast<void*>(_this))
			     : -1),
            prev(this), next(this) {}

  inline void insert(RLink<T>& after){
    ASSERT(this->next == this->prev); // CHECKME
    ASSERT(this != &after);
    RLink<T>* n = after.next;
    RLink<T>* p = &after;
    // ASSERT(n < (void*)0xb0000000l);
    // ASSERT(p < (void*)0xb0000000l);
    next = n;
    prev = p;
    p->next = n->prev = this;
  }

  inline void insert_before(RLink<T>& before){
    insert(*before.prev);
  }
    
  inline void remove(){
    this->next->prev = this->prev;
    this->prev->next = this->next;
    this->next = this->prev = this;
  }
};

template <class T>
struct RingIterator {
  public:
  typedef RingIterator<T>  iterator;
  
typedef RingIterator<T>  const_iterator;
  typedef std::bidirectional_iterator_tag iterator_category;
  typedef T value_type;
  typedef T* pointer;
  typedef T& reference;
  typedef size_t size_type;
  typedef ptrdiff_t difference_type;

  RLink<T>* link;

  RingIterator(RLink<T>* _link) : link(_link) {}
  RingIterator() : link(0) {}
  RingIterator(iterator const & it) : link(it.link) {}

  bool operator==(const iterator& x) const { return link == x.link; }
  bool operator!=(const iterator& x) const { return link != x.link; }

  reference operator*() const { return *(link->getBase()); }
  pointer operator->() const { return &(operator*()); }
  
  iterator& operator++() {
    link = link->next;
    return *this;
  }
  iterator operator++(int) {
    iterator res = *this;
    link = link->next;
    return res;
  }
  iterator& operator--() {
    link = link->prev;
    return *this;
  }
  iterator operator--(int) {
    iterator res = *this;
    --*this;
    return res;
  }
};
  

template <class T>
struct Ring : public RLink<T> {
 public:
  GcForwardInfo _info;
  Ring() : RLink<T>(0) {}
  inline int collect(Ring& x){
    RLink<T>* l = x.next;
    next = prev = this;
    int maxgen = 0;
    while (l != &x){
      T* b = l->getBase();
      int offset = l->offset;
      l = l->next;
      T* y = GcHeap::collect(b);
      if (y->generation > maxgen) maxgen = y->generation;
      // recalculate RLink field
      RLink<T>* rl = 
	static_cast<RLink<T>*>(
	  static_cast<void*>(
		static_cast<char*>(static_cast<void*>(y)) + offset
	  )
	);
      rl->next = rl->prev = rl;
      rl->insert(*prev);
    }
    return maxgen;
  }

  Ring(GCPlacement, Ring& x) : RLink<T>(0) {
    collect(x);
  }
  inline void gc(){
    GcHeap::gc(this);
  }
  struct RingRoot : public GcRoot {
    Ring* ring;
    int gen;
    int generation(){
      if (ring->next == ring)
	return 0;
      else
	return gen;
    }
    void collect(){
      gen = ring->collect(*ring);
      if (gen <= space->generation) remove();
    }
  };
  inline bool empty(){
    return next == this;
  }
  inline Ring(Ring const& source) : RLink<T>(0) {
    // relocate pointers
    source.next->prev = source.prev->next = this;
    next = source.next;
    prev = source.prev;
  }
  inline T* pop(){
    if (!empty()){
      T* r = next->getBase();
      next->remove();
      if (empty() && _info.root != 0 && _info.root->next != _info.root){
	_info.root->remove();
      }
      return r;
    } else 
      return 0;
  }
  inline T* pop_back(){
    if (!empty()){
      T* r = prev->getBase();
      prev->remove();
      return r;
    } else 
      return 0;
  }
 private:
  inline void makeRoot(GcObject* context, RLink<T>& x){
    T* base = x.getBase();
    if (context->generation < base->generation){
      if (_info.root == 0){
	GcSpace* space = GcHeap::findGen(context->generation);
	RingRoot* r = new (space->allocTemp(sizeof(RingRoot)))
			  RingRoot();
	r->ring = this;
	r->gen = base->generation;
	r->space = space;
	r->append(space->roots);
	_info.root = r;
      } else {
	RingRoot* r = static_cast<RingRoot*>(_info.root);
	if (r->gen < base->generation)
	  r->gen = base->generation;
	if (r->next == r)
	  r->append(r->space->roots);
      }
    }
  }
 public:
  inline void append(GcObject* context, RLink<T>& x){
    x.insert(*prev);
    makeRoot(context, x);
  }
  void enqueue(GcObject* context, RLink<T>& x){
    if (next == this){
      append(context, x);
      return;
    }
    T* tx = x.getBase();
    int c = compare(prev->getBase(),tx);
    if (c <= 0){
      // add at end
      x.insert(*prev);
      makeRoot(context, x);
    } else {
      // search from begin
      RLink<T>* l = next;
      while (l != this){
	int c = compare(tx, l->getBase());
	if (c < 0){
	  x.insert_before(*l);
	  makeRoot(context, x);
	  return;
	}
	l = l->next;
      }
      x.insert(*this);
      makeRoot(context, x);
    }
  }

  /*
  inline void push(RLink<T>& x){
    x.insert(*this);
  }
  inline void clear(){
    while (!empty()){
      next->remove();
    }
  }
  */
  inline RingIterator<T> begin() const {
    return RingIterator<T>(next);
  }
  inline RingIterator<T> end() const {
    return RingIterator<T>(const_cast<Ring<T>*>(this));
  }
};

/*
template <class T>
struct RingRoot : public GcRoot {

  Ring<T>* ring;
  RLink<T>* elem;

  RingRoot(Ring<T>& _ring, RLink<T>& _elem) : 
    GcRoot(), ring(&_ring), elem(&_elem){}

  void collect(){
    if (elem->prev == elem) return; // ??????????????
    RLink<T>* prev = elem->prev;
    T* pbase = prev != ring ?  prev->getBase() : 0;
    T* ebase = elem->getBase();
    ASSERT (ring->prev != ring && ring->next != ring);
    elem->remove();
    ebase = GcHeap::collect(ebase);
    elem = elem->getLink(ebase);
    if (pbase != 0 && pbase->generation == GcSpace::generationCounter
                   && pbase->forward != 0){
      // has moved
      pbase = static_cast<T*>(pbase->forward);
      prev = prev->getLink(pbase);
    }
    elem->insert(*prev);
  }

  int generation(){
    return elem->getBase()->generation;
  }

  static inline void appendForwardRef(
		       GcObject* context, GcForwardInfo& info,
		       Ring<T>& ring,
		       RLink<T>& x){
    ring.append(x);
    T* p = x.getBase();
    if (context->generation < p->generation){
      if (info.root != 0){
	RingRoot* r = static_cast<RingRoot*>(info.root);
	r->ring = &ring;
	r->elem = &x;
	r->active = true;
      } else {
	RingRoot* r = new (GcHeap::tempAlloc(context->generation, 
					     sizeof(RingRoot)))
			  RingRoot(ring, x);
	GcHeap::addForward(context->generation, info, r);
      }
    } else {
      GcHeap::delForward(info);
    }
  }

};
*/
    

// =========================================================================
// Growing Arrays

#define DYNARRAY_RESIZE 33
#define DYNARRAY_WASTE 10

template <class T>
struct DynArray : GcObject {
 private:
  int size;
  int fill;
  T* data;
 public:
  inline DynArray(){
    size = fill = 0;
    data = 0;
  }
  inline DynArray(int capicity){
    size = capicity;
    if (capicity > 0){
      data = new (GC) T[capicity];
    }
    fill = 0;
  }
  inline DynArray(GCPlacement, DynArray& x) :
    // let array shrink on gc
    size(x.fill), fill(x.fill){
    data = GcHeap::collectArr(x.fill, x.data);
  }
  void gc(){
    GcHeap::gc(this);
  }
  DynArray clone(){
    DynArray x(fill);
    std::uninitialized_copy(data,data+fill,x.data);
    x.fill = fill;
    return x;
  }
  inline T& operator[](int index){
    return data[index];
  }
  inline int length(){
    return fill;
  }
  inline T* rawData(){
    return data;
  }
  inline T* asArray(int& sz){
    if (size > 0){
      if ((size-fill) * 100 / size > DYNARRAY_WASTE) {
	T* ndata = new (GC) T[fill];
	std::uninitialized_copy(data,data+fill,ndata);
	sz = fill;
	return ndata;
      } else {
	sz = fill;
	return data;
      }
    } else {
      sz = 0;
      return 0;
    }
  }
  inline void ensure(int add){
    if (fill+add > size){
      int newsize = (size * DYNARRAY_RESIZE / 100) + size + 1;
      if (fill+add > newsize) newsize = fill+add;
      T* ndata = new (GC) T[newsize];
      std::uninitialized_copy(data,data+fill,ndata);
      size = newsize;
      data = ndata;
    }
  }
  inline DynArray& push(T val){
    ensure(1);
    data[fill++] = val;
    return *this;
  }
  inline DynArray& insert(int i, T val){
    ensure(1);
    for (int j = fill; j > i; j--){
      data[j] = data[j-1];
    }
    data[i] = val;
    fill++;
    return *this;
  }
  inline DynArray& remove(int i){
    fill--;
    for (int j = i; j < fill; j++){
      data[j] = data[j+1];
    }
    return *this;
  }
  inline DynArray& append(DynArray& other){
    ensure(other.fill);
    for (int i = 0; i < other.size; i++){
      push(other.data[i]);
    }
    return *this;
  }
  inline DynArray& clear(){
    fill = 0;
    return *this;
  }
};



// =========================================================================
// Growing Arrays with non pointer contents (for VC++ ...)


template <class T>
struct DynArrayAgg : GcObject {
 private:
  int size;
  int fill;
  T* data;
 public:
  inline DynArrayAgg(){
    size = fill = 0;
    data = 0;
  }
  inline DynArrayAgg(int capicity){
    size = capicity;
    if (capicity > 0){
      data = new (GC) T[capicity];
    }
    fill = 0;
  }
  inline DynArrayAgg(GCPlacement, DynArrayAgg& x) :
    // let array shrink on gc
    size(x.fill), fill(x.fill){
    data = GcHeap::collectArrAgg(x.fill, x.data);
  }
  void gc(){
    GcHeap::gc(this);
  }
  DynArrayAgg clone(){
    DynArrayAgg x(fill);
    std::uninitialized_copy(data,data+fill,x.data);
    x.fill = fill;
    return x;
  }
  inline T& operator[](int index){
    return data[index];
  }
  inline int length(){
    return fill;
  }
  inline T* rawData(){
    return data;
  }
  inline T* asArray(int& sz){
    if (size > 0){
      if ((size-fill) * 100 / size > DYNARRAY_WASTE) {
	T* ndata = new (GC) T[fill];
	std::uninitialized_copy(data,data+fill,ndata);
	sz = fill;
	return ndata;
      } else {
	sz = fill;
	return data;
      }
    } else {
      sz = 0;
      return 0;
    }
  }
  inline void ensure(int add){
    if (fill+add > size){
      int newsize = (size * DYNARRAY_RESIZE / 100) + size + 1;
      if (fill+add > newsize) newsize = fill+add;
      T* ndata = new (GC) T[newsize];
      std::uninitialized_copy(data,data+fill,ndata);
      size = newsize;
      data = ndata;
    }
  }
  inline DynArrayAgg& push(T val){
    ensure(1);
    data[fill++] = val;
    return *this;
  }
  inline DynArrayAgg& insert(int i, T val){
    ensure(1);
    for (int j = fill; j > i; j--){
      data[j] = data[j-1];
    }
    data[i] = val;
    fill++;
    return *this;
  }
  inline DynArrayAgg& remove(int i){
    fill--;
    for (int j = i; j < fill; j++){
      data[j] = data[j+1];
    }
    return *this;
  }
  inline DynArrayAgg& append(DynArrayAgg& other){
    ensure(other.fill);
    for (int i = 0; i < other.size; i++){
      push(other.data[i]);
    }
    return *this;
  }
  inline DynArrayAgg& clear(){
    fill = 0;
    return *this;
  }
};


// =========================================================================
// Lists 

template <class T>
struct ListElem : GcObject {
  DynPtr<ListElem> next;
  T val;
  inline ListElem() {}
  inline ListElem(ListElem* _next, T _val) : val(_val) {
    next.assign(this, _next);
  }
  inline ListElem(GCPlacement, ListElem& x){
    ListElem* o = &x;
    ListElem* n = this;
    for (;;) {
      n->val = GcHeap::collect(o->val);
      if (o->next != 0){
	o = o->next.ptr();
	if (o->forward != 0){
	  n->next.assign(n, static_cast<ListElem*>(o->forward));
	  break;
	} else if (o->generation >= GcHeap::collectFrom){
	  ListElem* n1 = new (GC) ListElem();
	  o->forward = n1;
	  n->next.assign(n, n1);
	  n = n1;
	} else {
	  n->next.assign(n, o);
	  break;
	}
      } else {
	n->next.clear();
	break;
      }
    }
  }
  void gc() { GcHeap::gc(this); }
};

template <class T>
struct ListIterator {
  ListElem<T>* elem;
  inline ListIterator(ListElem<T>* e) : elem(e){}
  inline bool more(){
    return elem != 0;
  }
  inline void next() {
    elem = elem->next.ptr();
  }
  inline T& operator*(){
    return elem->val;
  }
};

template <class T>
struct List {
  DynPtr<ListElem<T> > _elems;
  DynPtr<ListElem<T> > _last;
  int _size;

  inline List() : _size(0) {}

  inline List(GCPlacement, List& x) : _size(x._size) {
    _elems.collect(x._elems);
    _last.collect(x._last);
  }


  void gc(){
    GcHeap::gc(this);
  }

  inline ListIterator<T> iterate(){
    return ListIterator<T>(_elems.ptr());
  }
  inline int size(){
    return _size;
  }
  inline void push(GcObject* context, T val) {
    _elems.assign(context, new (GC) ListElem<T>(_elems.ptr(), val));
    if (_last == 0) _last.assign(context, _elems.ptr());
    _size++;
  }

  inline void pushAll(GcObject* context, int size, T* arr){
    for (int i = 0; i < size; i++){
      push(context, arr[i]);
    }
  }

  inline void copyFrom(GcObject* context, List & x){
    _elems.clear();
    _last.clear();
    _size = 0;
    ListElem<T>* e = x._elems.ptr();
    ListElem<T>* l = 0;
    while (e != 0){
      ListElem<T>* n = new (GC) ListElem<T>(0, e->val);
      if (l == 0)
	_elems.assign(context, n);
      else
	l->next.assign(l, n);
      l = n;
      _last.assign(context, l);
      _size++;
      e = e->next.ptr();
    }
  }

  inline void include(GcObject* context, T val){
    if (_elems == 0){
      push(context, val);
    } else {
      int c = compare(val, _last->val);
      if (c < 0){
	// append after last
	ListElem<T>* e = new (GC) ListElem<T>(0, val);
	_last->next.assign(_last.ptr(), e);
	_last.assign(context, e);
	_size++;
      } else if (c == 0){
	// ignore
      } else if (_elems == _last.ptr()){
	push(context, val);
      } else {
	ListElem<T>* e = _elems.ptr();
	ListElem<T>* p = 0;
	while (e != _last.ptr()){
	  int c = compare(val,e->val);
	  if (c > 0){
	    break;
	  } else if (c == 0){
	    // ignore duplicate
	    return;
	  } else {
	    p = e;
	    e = e->next.ptr();
	  }
	}
	if (p == 0){
	  _elems.assign(context, new (GC) ListElem<T>(_elems.ptr(), val));
	} else {
	  p->next.assign(p, new (GC) ListElem<T>(p->next.ptr(), val));
	}
	_size++;
      }
    }
  }

  inline void includeAll(GcObject* context, int size, T* arr){
    for (int i = 0; i < size; i++){
      include(context, arr[i]);
    }
  }

  inline T* asArray(int& sz){
    sz = _size;
    if (_size == 0)
      return 0;
    else {
      T* arr = new (GC)T[_size];
      ListElem<T>* e = _elems.ptr();
      int i = _size;
      while (e != 0){
	arr[--i] = e->val;
	e = e->next.ptr();
      }
      return arr;
    }
  }


  /*
  inline void merge(GcObject* context, List& x){
    ListElem<T>* e = _elems.ptr();
    ListElem<T>* p = 0;
    ListElem<T>* e1 = x._elems.ptr();
    while (e != 0 && e1 != 0){
      int c = compare(e->val, e1->val);
      if (c > 0){
	if (p != 0){
	  p->next.assign(p, e);
	} else {
	  _elems.assign(context, e);
	}
	p = e; e = e->next.ptr();
      } else if (c < 0){
	if (p != 0){
	  p->next.assign(p, e1);
	} else {
	  _elems.assign(context, e1);
	}
	p = e1; e1 = e1->next.ptr();
      } else {
	if (p != 0){
	  p->next.assign(p, e);
	} else {
	  _elems.assign(context, e);
	}
	p = e; e = e->next.ptr(); e1 = e1->next.ptr();
      }
    }
    if (p != 0){
      p->next.assign(p, e == 0 ? e1 : e);
    } else
      _elems.assign(context, e == 0 ? e1 : e);
  }

  inline void join(GcObject* context, List& x){
    ListElem<T>* e = _elems.ptr();
    ListElem<T>* p = 0;
    ListElem<T>* e1 = x._elems.ptr();
    while (e != 0 && e1 != 0){
      int c = compare(e->val, e1->val);
      if (c > 0){
	e = e->next.ptr();
      } else if (c < 0){
	e1 = e1->next.ptr();
      } else {
	if (p != 0){
	  p->next.assign(p, e);
	} else {
	  _elems.assign(context, e);
	}
	p = e; e = e->next.ptr(); e1 = e1->next.ptr();
      }
    }
    if (p != 0){
      p->next.clear();
    } else
      _elems.clear();
  }
  */

};

// =========================================================================
// Sets (by AVL Trees)

template <class T>
struct SetElem : GcObject {
  DynPtr<SetElem> left;
  DynPtr<SetElem> right;
  int size;
  T val;
  inline SetElem() {}
  inline SetElem(SetElem* _left, SetElem* _right, int _size, T _val) 
		: size(_size), val(_val) {
    left.assign(this, _left);
    right.assign(this, _right);
  }
  inline SetElem(GCPlacement, SetElem& x) : size(x.size){
    left.collect(x.left);
    right.collect(x.right);
    val = GcHeap::collect(x.val);
  }
  void gc() { GcHeap::gc(this); }
};

template <class T>
struct Set {
  DynPtr<SetElem<T> > _tree;

  inline Set() {}

  inline Set(GCPlacement, Set& x) {
    _tree.collect(x._tree);
  }


  void gc(){
    GcHeap::gc(this);
  }

 private:
  static inline int getSize(SetElem<T>* e){
    if (e == 0) return 0; else return e->size;
  }
  static inline SetElem<T>* lrotate(SetElem<T>* e){
    SetElem<T>* r = e->right.ptr();
    e->right.assign(e,r->left.ptr());
    r->left.assign(r, e);
    r->size = e->size;
    e->size = getSize(e->left.ptr()) + getSize(e->right.ptr()) + 1;
    return r;
  }
  static inline SetElem<T>* rrotate(SetElem<T>* e){
    SetElem<T>* l = e->left.ptr();
    e->left.assign(e,l->right.ptr());
    l->right.assign(l, e);
    l->size = e->size;
    e->size = getSize(e->left.ptr()) + getSize(e->right.ptr()) + 1;
    return l;
  }
  static inline SetElem<T>* dlrotate(SetElem<T>* e){
    SetElem<T>* r = e->right.ptr();
    SetElem<T>* rl = r->left.ptr();
    e->right.assign(e,rl->left.ptr());
    r->left.assign(r, rl->right.ptr());
    rl->left.assign(rl, e);
    rl->right.assign(rl, r);
    rl->size = e->size;
    e->size = getSize(e->left.ptr()) + getSize(e->right.ptr()) + 1;
    r->size = getSize(r->left.ptr()) + getSize(r->right.ptr()) + 1;
    return rl;
  }
  static inline SetElem<T>* drrotate(SetElem<T>* e){
    SetElem<T>* l = e->left.ptr();
    SetElem<T>* lr = l->right.ptr();
    e->left.assign(e,lr->right.ptr());
    l->right.assign(l, lr->left.ptr());
    lr->right.assign(lr, e);
    lr->left.assign(lr, l);
    lr->size = e->size;
    e->size = getSize(e->left.ptr()) + getSize(e->right.ptr()) + 1;
    l->size = getSize(l->left.ptr()) + getSize(l->right.ptr()) + 1;
    return lr;
  }
  static inline void balance(GcObject* context, DynPtr<SetElem<T> >& target){
    SetElem<T>* e = target.ptr();
    int ls = getSize(e->left.ptr());
    int rs = getSize(e->right.ptr());
    if (ls+rs < 2) 
      return;
    else if (rs > ls*4){
      SetElem<T>* lr = e->right->left.ptr();
      SetElem<T>* rr = e->right->right.ptr();
      if (getSize(lr) < getSize(rr))
	target.assign(context, lrotate(e)); 
      else 
	target.assign(context, dlrotate(e));
    } else if (ls > rs*4){
      SetElem<T>* ll = e->left->left.ptr();
      SetElem<T>* rl = e->left->right.ptr();
      if (getSize(rl) < getSize(ll))
	target.assign(context, rrotate(e)); 
      else 
	target.assign(context, drrotate(e));
    }
  }
  static void insert(GcObject* context, 
		     DynPtr<SetElem<T> >& target, T val){
    SetElem<T>* e = target.ptr();
    if (e == 0){
      target.assign(context, new (GC) SetElem<T>(0,0,1,val));
    } else {
      int c = compare(val, e->val);
      if (c < 0){
	insert(e, e->left, val);
      } else if (c > 0){
	insert(e, e->right, val);
      } else {
	// already there: ignore
	return;
      }
      int news = getSize(e->left.ptr()) + getSize(e->right.ptr()) + 1;
      if (news != e->size){
	e->size = news;
	balance(context, target);
      }
    }
  }
  static SetElem<T>* copy(SetElem<T>* e){
    if (e == 0)
      return 0;
    else
      return new (GC) SetElem<T>(copy(e->left.ptr()), 
				 copy(e->right.ptr()), 
				 e->size, e->val);
  }
  static void copyInto(T* arr, int& index, SetElem<T>* e){
    if (e != 0) {
      copyInto(arr, index, e->left.ptr());
      arr[index++] = e->val;
      copyInto(arr, index, e->right.ptr());
    }
  }

 public:
    
  inline void copyFrom(GcObject* context, Set & x){
    _tree.assign(context, copy(x._tree.ptr()));
  }

  inline void include(GcObject* context, T val){
    insert(context, _tree, val);
  }

  inline void includeAll(GcObject* context, int size, T* arr){
    for (int i = 0; i < size; i++){
      include(context, arr[i]);
    }
  }

  inline int size(){
    return getSize(_tree.ptr());
  }

  inline T* asArray(int& sz){
    sz = getSize(_tree.ptr());
    if (sz == 0)
      return 0;
    else {
      T* arr = new (GC) T[sz];
      int i = 0;
      copyInto(arr, i, _tree.ptr());
      ASSERT(i == sz);
      return arr;
    }
  }

};




// =========================================================================
// Creating initialized arrays

template <class T>
static inline T* newArray(){
  return new (NC) T*[0];
}

template <class T>
static inline T* newArray(T x1){
  T* arr = new (NC) T[1];
  arr[0] = x1;
  return arr;
}

template <class T>
static inline T* newArray(T x1, T x2){
  T* arr = new (NC) T[2];
  arr[0] = x1;
  arr[1] = x2;
  return arr;
}

template <class T>
static inline T* newArray(T x1, T x2, T x3){
  T* arr = new (NC) T[3];
  arr[0] = x1;
  arr[1] = x2;
  arr[2] = x3;
  return arr;
}

template <class T>
static inline T* newArray(T x1, T x2, T x3, T x4){
  T* arr = new (NC) T[4];
  arr[0] = x1;
  arr[1] = x2;
  arr[2] = x3;
  arr[3] = x4;
  return arr;
}

template <class T>
static inline T* newArray(T x1, T x2, T x3, T x4, T x5){
  T* arr = new (NC) T[5];
  arr[0] = x1;
  arr[1] = x2;
  arr[2] = x3;
  arr[3] = x4;
  arr[4] = x5;
  return arr;
}

// GCed versions

template <class T>
static inline T* newGCArray(){
  return new (GC) T*[0];
}

template <class T>
static inline T* newGCArray(T x1){
  T* arr = new (GC) T[1];
  arr[0] = x1;
  return arr;
}

template <class T>
static inline T* newGCArray(T x1, T x2){
  T* arr = new (GC) T[2];
  arr[0] = x1;
  arr[1] = x2;
  return arr;
}

template <class T>
static inline T* newGCArray(T x1, T x2, T x3){
  T* arr = new (GC) T[3];
  arr[0] = x1;
  arr[1] = x2;
  arr[2] = x3;
  return arr;
}

template <class T>
static inline T* newGCArray(T x1, T x2, T x3, T x4){
  T* arr = new (GC) T[4];
  arr[0] = x1;
  arr[1] = x2;
  arr[2] = x3;
  arr[3] = x4;
  return arr;
}

template <class T>
static inline T* newGCArray(T x1, T x2, T x3, T x4, T x5){
  T* arr = new (GC) T[5];
  arr[0] = x1;
  arr[1] = x2;
  arr[2] = x3;
  arr[3] = x4;
  arr[4] = x5;
  return arr;
}

  
// =========================================================================
// Caches 

template <class Key, class Cont>
struct CacheEntry {
  CacheEntry* next;
  int hash;
  Key* key;
  Cont* cont;
  CacheEntry(CacheEntry* _next, int _hash, Key* _key, Cont* _cont)
    : next(_next), hash(_hash), key(_key), cont(_cont) {
  }
};

template <class Key, class Cont>
struct Cache : GcWeakObject {
  typedef CacheEntry<Key, Cont> Entry;
  
  int _threshold;
  float _loadFactor;
  int _count;
  int _size;
  int _initSize;
  GcSpace* _space;
  Entry** _table;

  virtual unsigned keyHash(Key*) = 0;
  virtual bool keyEquals(Key*, Key*) = 0;
  virtual Key* keyValidate(Key*) = 0;


  inline Cache(int initialCapicity, float loadFactor) 
    : _threshold((int)(initialCapicity * loadFactor)),
      _loadFactor(loadFactor), _count(0),
      _size(initialCapicity), _initSize(initialCapicity),
      _space(GcHeap::from) {
    _table = 
      new (_space->allocTemp(_size * sizeof(Entry*))) Entry*;
    previous = _space->weakObjects;
    _space->weakObjects = this;
  }

  private:
  void rehash(){
    int newSize = _size * 2 + 1;
    Entry** newTable = 
      new (_space->allocTemp(newSize * sizeof(Entry*))) Entry*;
    for (int i = 0; i < _size; i++){
      Entry* e = _table[i];
      while (e != 0){
	Entry* n = e->next;
	int index = (e->hash & 0x7FFFFFFF) % newSize;
	e->next = newTable[index];;
	newTable[index] = e;
	e = n;
      }
    }
    _table = newTable;
    _size = newSize;
    _threshold = (int)(_size * _loadFactor);
  }
  public:

    
  inline void add(int hash, Key* key, Cont* cont){
    if (_count > _threshold){
      rehash();
    }
    int index = (hash & 0x7FFFFFFF) % _size;
    _table[index] =
      new (_space->allocTemp(sizeof(Entry)))
          Entry(_table[index], hash, key, cont);
    _count++;
  }
  inline void add(Key* key, Cont* cont){
    add(keyHash(key), key,  cont);
  }
  inline Cont* get(Key* key){
    int hash = keyHash(key);
    int index = (hash & 0x7FFFFFFF) % _size;
    for (Entry* e = _table[index]; e != 0; e = e->next){
      if (e->hash == hash && keyEquals(e->key, key)){
	return e->cont;
      }
    }
    return 0;
  }
    
  inline Cache(GCPlacement, Cache& x) :
    _threshold(x._threshold), 
    _loadFactor(x._loadFactor),
    _count(x._count),
    _size(x._size),
    _initSize(x._initSize),
    _space(GcHeap::from),
    _table(x._table) {
    previous = _space->weakObjects;
    _space->weakObjects = this;
    // just collect cont-fields -- actual entries visited on weakGc
    /*
    for (int i = 0; i < _size; i++){
      for (Entry* e = _table[i]; e != 0; e = e->next){
	e->cont = GcHeap::collect(e->cont);
      }
    }
    */
  }

  void weakGc() {
    Entry** oldTable = _table;
    int oldSize = _size;
    _count = 0;
    _size = _initSize;
    _table = new (_space->allocTemp(_size * sizeof(Entry*))) Entry*;
    _threshold = (int)(_size * _loadFactor);
    for (int i = 0; i < oldSize; i++){
      for (Entry* e = oldTable[i]; e != 0; e = e->next){
	Key* k = keyValidate(e->key);
	if (k != 0){
	  add(keyHash(k), k, GcHeap::collect(e->cont));
	}
      }
    }
  }

};

	
#endif
