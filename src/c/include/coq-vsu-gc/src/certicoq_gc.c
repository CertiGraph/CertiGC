#ifndef COQ_CERTICOQ__GC_C
#define COQ_CERTICOQ__GC_C

#include <stdlib.h>
#include <coq-vsu-certicoq-block/block.h>

#include "../certicoq_gc.h"

void certicoq_gc__abort(gc_error_t e)
{
  exit(-1);
}

void certicoq_gc__funs_init(gc_funs_t *out)
{
  out->gc_abort = certicoq_gc__abort;
  out->gc_block__header_get_ptr = certicoq_block__header_get_ptr;
  out->gc_block__copy = certicoq_block__copy;
  out->gc_block__ptr_iter = certicoq_block__field_ptr_iter;
  out->gc_block__of_header = certicoq_block__of_header;
  out->gc_block__size_get = certicoq_block__size_get;
}

void certicoq_gc__cell_modify(struct thread_info *ti, int_or_ptr *p_cell, int_or_ptr p_val)
{
  *p_cell = p_val;
  if (int_or_ptr__is_int(p_val) == 0)
  {
    remember(ti, p_cell);
  }
}

struct thread_info *certicoq_gc__make_tinfo()
{
  return make_tinfo(certicoq_gc__abort);
}

void certicoq_gc__garbage_collect(fun_info fi, struct thread_info *ti)
{
  gc_funs_t gc_funs;
  certicoq_gc__funs_init(&gc_funs);
  garbage_collect(&gc_funs, fi, ti);
}

void certicoq_gc__free_heap(struct heap *h)
{
  free_heap(h);
}

void certicoq_gc__reset_heap(struct heap *h)
{
  reset_heap(h);
}

#endif /* COQ_CERTICOQ__GC_C */
