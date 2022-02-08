#ifndef COQ_CERTICOQ__GC_H
#define COQ_CERTICOQ__GC_H

#include <coq-vsu-int_or_ptr/int_or_ptr.h>

struct heap;

#define MAX_ARGS 1024

struct thread_info
{
  int_or_ptr *alloc;                    /* alloc pointer  */
  int_or_ptr *limit;                    /* limit pointer */
  struct heap *heap;                    /* Description of the generations in the heap */
  int_or_ptr args[MAX_ARGS];            /* the args array */
};

typedef const uintptr_t *fun_info;
/* fi[0]: How many words the function might allocate
   fi[1]: How many slots of the args array contain live roots
   fi[2..(fi[1]-2)]: Indices of the live roots in the args array
*/

typedef struct {
  fun_info fi;
  struct thread_info *ti;
} certicoq_gc__runtime_t;


void certicoq_gc__tinfo_init(struct thread_info *ti);

void certicoq_gc__heap_free(struct thread_info *ti);

void certicoq_gc__heap_reset(struct thread_info *ti);

void certicoq_gc__cell_modify(struct thread_info *ti, int_or_ptr *p_cell, int_or_ptr p_val);

void certicoq_gc__garbage_collect(fun_info fi, struct thread_info *ti);

#endif /* COQ_CERTICOQ__GC_H */
