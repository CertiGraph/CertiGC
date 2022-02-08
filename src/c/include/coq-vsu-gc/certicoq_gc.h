#ifndef COQ_CERTICOQ__GC_H
#define COQ_CERTICOQ__GC_H

#include <coq-vsu-int_or_ptr/int_or_ptr.h>

#include "gc.h"


void certicoq_gc__cell_modify(struct thread_info *ti, int_or_ptr *p_cell, int_or_ptr p_val);

struct thread_info *certicoq_gc__make_tinfo();

void certicoq_gc__garbage_collect(fun_info fi, struct thread_info *ti);

void certicoq_gc__free_heap(struct heap *h);

void certicoq_gc__reset_heap(struct heap *h);

#endif /* COQ_CERTICOQ__GC_H */
