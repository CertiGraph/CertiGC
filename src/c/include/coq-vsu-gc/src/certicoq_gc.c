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

void certicoq_gc__root_ptr_iter(void *void_rt, void (*f)(const void *, void *, gc_val *), const void *c_args, void *f_args)
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
      f(c_args, f_args, p);
    }
  }
}

void certicoq_gc__make_tinfo(struct thread_info *ti)
{
  struct heap *h = create_heap(certicoq_gc__abort);
  ti->heap = h;
  ti->alloc = h->spaces[0].start;
  ti->limit = h->spaces[0].limit;
}

void certicoq_gc__heap_free(struct thread_info *ti)
{
  free_heap(ti->heap);
}

void certicoq_gc__heap_reset(struct thread_info *ti)
{
  reset_heap(ti->heap);
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
  gc_funs_t gc_funs = {
    .gc_abort                 = certicoq_gc__abort,
    .gc_block__header_get_ptr = (gc_block__header_get_ptr_t)certicoq_block__header_get_ptr,
    .gc_block__copy           = (gc_block__copy_t)certicoq_block__copy,
    .gc_block__ptr_iter       = (gc_block__ptr_iter_t)certicoq_block__field_ptr_iter,
    .gc_block__of_base        = (gc_block__of_base_t)certicoq_block__of_header,
    .gc_block__size_get       = (gc_block__size_get_t)certicoq_block__size_get,
    .gc_rt__num_allocs        = (gc_rt__num_allocs_t)certicoq_gc__num_allocs,
    .gc_rt__resume            = (gc_rt__resume_t)certicoq_gc__resume,
    .gc_rt__root_ptr_iter     = (gc_rt__root_ptr_iter_t)certicoq_gc__root_ptr_iter
  };
  garbage_collect(&gc_funs, &rt, ti->heap);
}

#endif /* COQ_CERTICOQ__GC_C */
