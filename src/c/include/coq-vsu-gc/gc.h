#ifndef COQ_VSU_GC__GC_H
#define COQ_VSU_GC__GC_H


typedef enum {
  GC__E_GENERATION_TOO_LARGE = -1,
  GC__E_COULD_NOT_CREATE_NEXT_GENERATION = -2,
  GC__E_COULD_NOT_CREATE_HEAP = -3,
  GC__E_NURSERY_TOO_SMALL = -4,
  GC__E_RAN_OUT_OF_GENERATIONS = -5,
  GC__E_LAST_ERROR = GC__E_RAN_OUT_OF_GENERATIONS
} gc__error_t;

typedef void (*gc_abort_t)(gc__error_t);

/* TODO: remove dependence on certicoq_block and int_or_ptr */
#include <coq-vsu-int_or_ptr/int_or_ptr.h>
#include <coq-vsu-certicoq-block/block.h>

typedef const certicoq_block_header_t *gc_block_header;
typedef certicoq_block_t gc_block;
typedef int_or_ptr gc_val;
/* END TODO */

typedef gc_block_header (*gc_block__header_get_ptr_t)(const gc_block block);
typedef gc_block (*gc_block__copy_t)(gc_val *dst, const gc_block src);
typedef void (*gc_block__ptr_iter_t)(gc_block block, void (*f)(void *, gc_val *), void *f_args);
typedef gc_block (*gc_block__of_base_t)(const gc_val *base);
typedef size_t (*gc_block__size_get_t)(gc_block_header header);
typedef size_t (*gc_rt__num_allocs_t)(void *rt);
typedef void (*gc_rt__resume_t)(void *rt, gc_val *alloc, gc_val *limit);
typedef void (*gc_rt__root_ptr_iter_t)(void *rt, void (*f)(void *, gc_val *), void *f_args);

typedef struct {
  gc_abort_t gc_abort;
  gc_block__header_get_ptr_t gc_block__header_get_ptr;
  gc_block__copy_t gc_block__copy;
  gc_block__ptr_iter_t gc_block__ptr_iter;
  gc_block__of_base_t gc_block__of_base;
  gc_block__size_get_t gc_block__size_get;
  gc_rt__num_allocs_t gc_rt__num_allocs;
  gc_rt__resume_t gc_rt__resume;
  gc_rt__root_ptr_iter_t gc_rt__root_ptr_iter;
  void *odata;
} gc_funs_t;


/* EXPLANATION OF THE CERTICOQ GENERATIONAL GARBAGE COLLECTOR.
 Andrew W. Appel, September 2016

CALLING THE GARBAGE COLLECTOR (this part is NOT standard Ocaml):

The mutator runs in this environment:

                                 NURSERY              OLDER GENERATIONS
      +-------------+  start---->+-------------+      +-------------+
      |    args[0]  |            |             |      |             |
      +-------------+            | <-\         |  /-->|             |
      |    args[1] *----\        |   |       *---/    |             |
      +-------------+    \-----> | *-/         |      |             |
      |      .      |       +-+  |             |      |             |
      |      .      |  alloc|*-->+-------------+      |             |
      |      .      |       +-+  |             |      |             |
      +-------------+            |             |      |             |
      | args[argc-1]|       +-+  |             |      |             |
      +-------------+  limit|*-->+-------------+      |             |
                            +-+                       +-------------+

There is a global "args" array.  Certain words in "args" may
point into the heap (either the nursery or into older generations).
The nursery may point within itself, or into older generations.
Older generations may not point into the nursery.
The heap may not point into the args array.

The mutator creates a new object by using the N+1 words (including header)
starting at "alloc", and then adding N+1 to alloc.  This is only
permitted if alloc+N+1 <= limit.  Otherwise, the mutator must
first call the garbage collector.

The variables "alloc" and "limit" are owned by the mutator.
The "start" value is not actually a variable of the mutator,
but it was the value of "alloc" immediately after the most
recent collection.

To call the garbage collector, the mutator passes a fun_info and
a thread_info, as follows. */


/* A "space" describes one generation of the generational collector.

  Either start==NULL (meaning that this generation has not yet been created),
  or start <= next <= limit.  The words in start..next  are allocated
  and initialized, and the words from next..limit are available to allocate.
*/
struct space {
  gc_val *start, *next, *limit, *end;
};


#define MAX_SPACES 12  /* how many generations */

/* A heap is an array of generations; generation 0 must be already-created */
struct heap
{
  struct space spaces[MAX_SPACES];
};

struct heap *create_heap(gc_abort_t gc_abort);

/* Deallocates all heap data associated with h, and returns the
 * memory to the operating system (via the malloc/free system).
 * After calling this function, h is a dangling pointer and should not be used.
 */
void free_heap(struct heap *h);

/* Empties the heap without freeing its storage.
 * After a complete execution of the mutator,
 * and after whoever invoked the mutator copies whatever result they want
 * out of the heap, one can call this function before starting 
 * another mutator execution.  This saves the operating-system overhead of 
 * free_heap() followed by the implicit create_heap that would have been
 * done in the first garbage_collect() call of the next execution.
 */
void reset_heap(struct heap *h);

/* Adds p_cell to the remember set */
void remember(struct heap *h, gc_val *p_cell);

/* Performs one garbage collection; 
   or if ti->heap==NULL, initializes the heap. 

 The returns in a state where
 (1) the "after" graph of nodes reachable from args[indices[0..num_args]]
    is isomorphic to the "before" graph; and
 (2) the alloc pointer points to N words of unallocated heap space
  (where N>=num_allocs), such that limit-alloc=N.
*/
void garbage_collect(const gc_funs_t *gc_funs, void *rt, struct heap *h);

#endif /* COQ_VSU_GC__GC_H */
