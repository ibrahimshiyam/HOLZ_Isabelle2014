// $Id: zammem.cpp,v 1.6 2000/06/12 18:30:10 wg Exp $

#include <cstddef>
#include <cstdlib>
#include <strstream>

#include "zammem.h"

using namespace std;

unsigned GcSpace::totalAlloc = 0;
int GcSpace::generationCounter = 0;

void GcSpace::reserve(unsigned osize){
  // we know that pages->fill+osize > pages->size
  // see if there is a next page which can satisifies this request
  bool found = false;
  while (pages->next != 0){
    pages = pages->next;
    if (pages->fill+osize <= pages->size){
      found = true;
      break;
    }
  }
  if (!found){
    // allocate a new page 
    int csize = osize > GC_PAGESIZE ? osize : GC_PAGESIZE;
    // if (totalAlloc+csize > GC_MAXHEAPSIZE) Session::outOfMemory(totalAlloc);
    char* base = static_cast<char*>(calloc(csize,1));
    // CHECKME char* base = static_cast<char*>(malloc(csize));
    if (base == 0) Session::assertFailed("out of virtual memory");
    totalAlloc += csize;
    pages->next = new GcPage(pages,0,csize,0,base);
    pages = pages->next;
    size += csize;
  }
} 

void GcSpace::clear(){
  // walk to the end
  while (pages->next != 0){
    pages = pages->next;
  }
  // remove pages apart of the front page
  while (pages->previous != 0){
    free(pages->base);
    totalAlloc -= pages->size;
    size -= pages->size;
    pages = pages->previous;
    delete pages->next;
    pages->next = 0;
  }
}

/*
void GcSpace::release(){
  // walk to the end
  while (pages->next != 0){
    pages = pages->next;
  }
  // clear fill of pages apart of the front page
  while (pages->previous != 0){
    pages->fill = 0;
    pages = pages->previous;
  }
}
*/

unsigned GcSpace::tell(){
  GcPage* p = pages;
  // walk to the end
  while (p->next != 0){
    p = p->next;
  }
  unsigned n = 0;
  while (p->previous != 0){
    n += p->fill;
    p = p->previous;
  }
  return n;
}



GcSpace* GcHeap::fixed = 0;
GcSpace* GcHeap::from = 0;
unsigned GcHeap::lastTotal = 0;
unsigned GcHeap::recurDepth = 0;
int GcHeap::collectFrom = 0;
static int gcCount = 0;

void GcHeap::init(){
#ifdef GC_DISABLE
  return;
#endif
  while (from != 0){
    from->clear();
    GcSpace* s = from;
    from = from->previous;
    delete s;
  }
  if (fixed != 0) fixed->clear();
  lastTotal = 0;
  GcSpace::generationCounter = 0;
  fixed = new GcSpace(0);
  from = new GcSpace(fixed);
  gcCount = 0;
}

void inline GcHeap::collectRoots(GcSpace* space, int& rootCount,
				 int& activeRootCount){
  GcRoot* r = static_cast<GcRoot*>(space->roots.next);
  while (r != &space->roots){
    GcRoot* n = static_cast<GcRoot*>(r->next);
    rootCount++;
    int g = r->generation();
    if (g >= collectFrom){
      if (from->size >= GC_MAXSPACESIZE){
	from = new GcSpace(from);
      }
      r->collect();
      activeRootCount++;
    }
    r = n;
  }
}
 
void inline GcHeap::collectWeaks(GcWeakObject *start, GcWeakObject* end,
				 int& weakCount){
  while (start != end){
    weakCount++;
    start->weakGc();
    start = start->previous;
  }
}
 


void GcHeap::doCollect(int spaces,
		       int fromGen,
		       GcSpace* start, 
		       GcSpace* locked,
		       int rcount, GcObject** roots){
  int genCount = 0;
  int rootCount = 0;
  int activeRootCount = 0;
  int before = GcSpace::totalAlloc;

  collectFrom = fromGen;
  recurDepth = 0;

  // collect roots from non-collected spaces
  while (locked != 0){
    genCount++;
    collectRoots(locked, rootCount, activeRootCount);
    locked = locked->previous;
  }
  // collect roots given as parameter
  for (int i = 0; i < rcount; i++){
    if (from->size >= GC_MAXSPACESIZE){
      from = new GcSpace(from);
    }
    roots[i] = collect(roots[i]);
    rootCount++;
  }

  // handle weak pointers
  int weakCount = 0;
  GcWeakObject* lastWeak = from->weakObjects;
  GcSpace* space = from;
  while (space != 0){
    collectWeaks(space->weakObjects, 0, weakCount);
    space = space->previous;
  }
  while (lastWeak != from->weakObjects){
    // new weak objects have been collected during weakGc
    GcWeakObject* nextWeak = from->weakObjects;
    collectWeaks(from->weakObjects, lastWeak, weakCount);
    lastWeak = nextWeak;
  }
    
  
  // free collected spaces
  int max = GcSpace::totalAlloc;
  int copied = max-before;
  while (start != 0 && start->generation >= fromGen){
    GcSpace* space = start;
    start = start->previous;
    space->clear();
    delete space;
  }
  lastTotal = GcSpace::totalAlloc;
  MPRINT("collected " << dec << spaces << "g, copied " 
	 << dec << kb(copied) << " of "
	 << kb(lastTotal) << ", peak " 
	 << kb(max) << ", " 
	 // << activeRootCount << "/" 
	 // < rootCount << " roots from "
	 << (activeRootCount+999)/1000 << "/" 
	 << (rootCount+999)/1000 << "k roots from "
	 << genCount
	 << "g, " << weakCount << "w" << endl);
}
      
void GcHeap::reclaim(int rcount, GcObject** roots, bool force){
  int grown = GcSpace::totalAlloc - lastTotal;
  bool run = force || 
    GcSpace::totalAlloc > GC_MINHEAPSIZE &&
    ((double)grown * 100.0) / (double)GC_MAXSPACESIZE >= (double)GC_COLLECT;
  if (run){
    gcCount++;
    int use = 
      (int)(((double)GcSpace::totalAlloc * 100.0)/(double)GC_MAXHEAPSIZE);
    int memToCollect = 2*grown/3;
    if (use > GC_COLLECTALL){
      memToCollect += GC_MAXHEAPSIZE/2;
      // (int)((double)use * (double)GC_MAXSPACESIZE / 100.0);
    } else if (gcCount % GC_COLLECTALLSTEP == 0){
      memToCollect += 
	(int)((double)use * (double)GC_MAXSPACESIZE / 100.0);
    }
    int genCollected = 1;
    GcSpace* collected = from;
    memToCollect -= from->size;
    from = from->previous;
    while (from != fixed && memToCollect > 0){
      memToCollect -= from->size;
      from = from->previous;
      genCollected++;
    }
    GcSpace* noncollected = from;
    if (from == fixed){
      from = new GcSpace(fixed);
    }
    doCollect(genCollected,
	      noncollected->generation+1, collected, noncollected, 
	      rcount, roots);
    from = new GcSpace(from);
  }
}

/*
      if (GcSpace::totalAlloc*100/GC_MAXHEAPSIZE >= GC_COLLECTALL){
	MPRINT("LOW mem, full gc #" << dec << gcCount);
	collected = from;
	from = new GcSpace(fixed);
	doCollect(2, collected, fixed, rcount, roots);
	if (GcSpace::totalAlloc >= GC_MAXHEAPSIZE){
	  Session::outOfMemory(GcSpace::totalAlloc);
	}
      }
    }
    from = new GcSpace(from);
      noncollected = from;
      GcSpace::generationCounter = 1;
      collected = 0;
      int required;
      while (noncollected != fixed){
	if (collected == 0){
	  collected = noncollected;
	  required = 0;
	}
	required += noncollected->size;
	noncollected = noncollected->previous;
	if (required > GC_MINHEAPSIZE){
	  // collect now, in order to avoid temporary peak
	  if (from->size+required > GC_MINHEAPSIZE)
	    from = new GcSpace(from);
	  doCollect(noncollected->generation+1,
		    collected, noncollected, rcount, roots);
	  collected = 0;
	}
      }
      if (collected != 0){
	if (from->size+required > GC_MINHEAPSIZE)
	  from = new GcSpace(from);
	doCollect(2, collected, fixed, rcount, roots);
      }
      if (GcSpace::totalAlloc >= GC_MAXHEAPSIZE){
	Session::outOfMemory(GcSpace::totalAlloc);
      }
  }
}
*/
      

void GcRootObject::collect(){
  GcObject* ob = *object = GcHeap::collect(*object);
  if (ob == 0 || ob->generation <= space->generation)
    remove();
}

