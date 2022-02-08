#ifndef COQ_CERTICOQ__GC_C
#define COQ_CERTICOQ__GC_C

#include <stdlib.h>
#include <coq-vsu-certicoq-block/block.h>

#include "../gc.h"
#include "../certicoq_gc.h"

void certicoq_gc__abort(gc__error_t e)
{
  exit(-1);
}

size_t certicoq_gc__num_allocs(void *void_rt)
{
  certicoq_gc__runtime_t *rt = (certicoq_gc__runtime_t *)void_rt;
  return rt->fi[0];
}

void certicoq_gc__resume(void *void_rt, int_or_ptr *alloc, int_or_ptr *limit)
{
  certicoq_gc__runtime_t *rt = (certicoq_gc__runtime_t *)void_rt;
  rt->ti->alloc = alloc;
  rt->ti->limit = limit;
}

void certicoq_gc__root_ptr_iter(void *void_rt, void (*f)(void *, gc_val *), void *f_args)
{
  certicoq_gc__runtime_t *rt = (certicoq_gc__runtime_t *)void_rt;
  size_t n = rt->fi[1];
  const uintptr_t *roots = rt->fi+2;
  gc_val *args = rt->ti->args;
  size_t i;

  for (i = 0; i < n; i++)
  {
    int_or_ptr *p = args+roots[i];
    if (int_or_ptr__is_int(*p) == 0)
    {
      f(&f_args, p);
    }
  }
}

void certicoq_gc__funs_init(gc_funs_t *out)
{
  out->gc_abort                 = certicoq_gc__abort;
  out->gc_block__header_get_ptr = (gc_block__header_get_ptr_t)certicoq_block__header_get_ptr;
  out->gc_block__copy           = (gc_block__copy_t)certicoq_block__copy;
  out->gc_block__ptr_iter       = (gc_block__ptr_iter_t)certicoq_block__field_ptr_iter;
  out->gc_block__of_base        = (gc_block__of_base_t)certicoq_block__of_header;
  out->gc_block__size_get       = (gc_block__size_get_t)certicoq_block__size_get;
  out->gc_rt__num_allocs        = (gc_rt__num_allocs_t)certicoq_gc__num_allocs;
  out->gc_rt__resume            = (gc_rt__resume_t)certicoq_gc__resume;
  out->gc_rt__root_ptr_iter     = (gc_rt__root_ptr_iter_t)certicoq_gc__root_ptr_iter;
}

void certicoq_gc__make_tinfo(struct thread_info *tinfo)
{
  struct heap *h = create_heap(certicoq_gc__abort);
  tinfo->heap = h;
  tinfo->alloc = h->spaces[0].start;
  tinfo->limit = h->spaces[0].limit;
}

void certicoq_gc__heap_free(struct heap *h)
{
  free_heap(h);
}

void certicoq_gc__heap_reset(struct heap *h)
{
  reset_heap(h);
}

void certicoq_gc__remember(struct thread_info *ti, gc_val *p_cell)
{
  remember(ti->heap, p_cell);
  ti->limit = ti->heap->spaces[0].limit;
}

void certicoq_gc__cell_modify(struct thread_info *ti, int_or_ptr *p_cell, int_or_ptr p_val)
{
  *p_cell = p_val;
  if (int_or_ptr__is_int(p_val) == 0)
  {
    certicoq_gc__remember(ti, p_cell);
  }
}

void certicoq_gc__garbage_collect(fun_info fi, struct thread_info *ti)
{
  certicoq_gc__runtime_t rt = {
    .fi = fi,
    .ti = ti
  };
  gc_funs_t gc_funs;
  certicoq_gc__funs_init(&gc_funs);
  garbage_collect(&gc_funs, &rt, ti->heap);
}

#endif /* COQ_CERTICOQ__GC_C */
