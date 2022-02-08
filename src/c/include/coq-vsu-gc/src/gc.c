#ifndef COQ_VSU_GC__GC_C
#define COQ_VSU_GC__GC_C

#include "../gc.h"
#include "../mem.h"


#define MAX_SPACES 12  /* how many generations */

/*  Using RATIO=2 is faster than larger ratios, empirically */
#ifndef RATIO
#define RATIO 2   /* size of generation i+1 / size of generation i */
#endif

/* The size of generation 0 (the "nursery") should approximately match the
   size of the level-2 cache of the machine, according to:
      Cache Performance of Fast-Allocating Programs,
      by Marcelo J. R. Goncalves and Andrew W. Appel.
      7th Int'l Conf. on Functional Programming and Computer Architecture,
      pp. 293-305, ACM Press, June 1995.
   We estimate this as 256 kilobytes
     (which is the size of the Intel Core i7 per-core L2 cache).
    http://www.tomshardware.com/reviews/Intel-i7-nehalem-cpu,2041-10.html
    https://en.wikipedia.org/wiki/Nehalem_(microarchitecture)
   Empirical measurements show that 64k works well
    (or anything in the range from 32k to 128k).
*/
#ifndef NURSERY_SIZE
#define NURSERY_SIZE (1<<16)
#endif

#ifndef DEPTH
#define DEPTH 0  /* how much depth-first search to do */
#endif


/* The restriction of max space size is required by pointer subtraction.  If
   the space is larger than this restriction, the behavior of pointer
   subtraction is undefined.
*/
const uintptr_t MAX_SPACE_SIZE = ((uintptr_t)1) << (sizeof(int_or_ptr) == 8 ? 40 : 29);


/* A "space" describes one generation of the generational collector.

  Either start==NULL (meaning that this generation has not yet been created),
  or start <= next <= limit.  The words in start..next  are allocated
  and initialized, and the words from next..limit are available to allocate.
*/
struct space {
  int_or_ptr *start, *next, *limit, *end;
};


/* A heap is an array of generations; generation 0 must be already-created */
struct heap
{
  struct space spaces[MAX_SPACES];
};


int Is_from(int_or_ptr *from_start, int_or_ptr *from_limit, int_or_ptr *v)
{
  return (from_start <= v && v < from_limit);
}

/* What it does:  If *p is a pointer, AND it points into from-space,
   then make *p point at the corresponding object in to-space.
   If such an object did not already exist, create it at address *next
    (and increment *next by the size of the object).
   If *p is not a pointer into from-space, then leave it alone.

   The depth parameter may be set to 0 for ordinary breadth-first
   collection.  Setting depth to a small integer (perhaps 10)
   may improve the cache locality of the copied graph.
*/

int has_been_forwarded(int_or_ptr *v)
{
  return v[-1] == 0;
}

int_or_ptr new_addr_from_forwarded(int_or_ptr *v)
{
  return v[0];
}

void mark_as_forwarded(gc_block old, gc_block new)
{
  old[-1] = 0;
  old[0] = int_or_ptr__of_ptr(new);
}

typedef struct {
  const gc_funs_t *gc_funs;
  int_or_ptr *from_start;               /* beginning of from-space */
	int_or_ptr *from_limit;               /* end of from-space */
	int_or_ptr **next;                    /* next available spot in to-space */
  int depth;                            /* how much depth-first search to do */
} forward_args_t;

void forward(
  void *f_args,
  int_or_ptr *p)                        /* caller is responsible for ensuring that (*p) is a pointer */
{
  forward_args_t *args = (forward_args_t *)f_args;
  const gc_funs_t *gc_funs = args->gc_funs;
  int_or_ptr *from_start = args->from_start;
	int_or_ptr *from_limit = args->from_limit;
	int_or_ptr **next = args->next;
	int depth = args->depth;

  gc_block v = (gc_block)int_or_ptr__to_ptr(*p);
  if (Is_from(from_start, from_limit, v))
  {
    if (has_been_forwarded(v))
    {
      *p = new_addr_from_forwarded(v);
    }
    else
    {
      const gc_block_header hd = gc_funs->gc_block__header_get_ptr(v);
      const size_t sz = gc_funs->gc_block__size_get(hd);
      gc_block new = gc_funs->gc_block__copy(*next, v);
      mark_as_forwarded(v, new);
      *next += sz;
      *p = new_addr_from_forwarded(v);
      if (depth > 0)
      {
        forward_args_t f_args = {
          .gc_funs = gc_funs,
          .from_start = from_start,
          .from_limit = from_limit,
          .next = next,
          .depth = depth - 1,
        };
        gc_funs->gc_block__ptr_iter(new, forward, &f_args);
      }
    }
  }
}

int Is_block(int_or_ptr x)
{
  return int_or_ptr__is_int(x) == 0;
}

/* Forward each live root in the args array */
void forward_roots(
  const gc_funs_t *gc_funs,
  int_or_ptr *from_start,               /* beginning of from-space */
	int_or_ptr *from_limit,               /* end of from-space */
	int_or_ptr **next,                    /* next available spot in to-space */
	fun_info fi,                          /* which args contain live roots? */
	struct thread_info *ti)               /* where's the args array? */
{
   size_t i;
   size_t n = fi[1];
   const uintptr_t *roots = fi+2;
   int_or_ptr *args = ti->args;

  for (i = 0; i < n; i++)
  {
    forward_args_t f_args = {
      .gc_funs = gc_funs,
      .from_start = from_start,
      .from_limit = from_limit,
      .next = next,
      .depth = DEPTH,
    };
    int_or_ptr *p = args+roots[i];
    if (Is_block(*p))
    {
      forward(&f_args, p);
    }
  }
}


void forward_remset(
  const gc_funs_t *gc_funs,
  struct space *from,                   /* descriptor of from-space */
  struct space *to,                     /* descriptor of to-space */
  int_or_ptr **next)                    /* next available spot in to-space */
{
  int_or_ptr *q = from->limit;
  while (q != from->end)
  {
    if (!(from->start <= (int_or_ptr *)*q && (int_or_ptr *)*q < from->limit))
    {
      forward_args_t f_args = {
        .gc_funs = gc_funs,
        .from_start = from->start,
        .from_limit = from->limit,
        .next = next,
        .depth = DEPTH,
      };
      forward(&f_args, (int_or_ptr *)*q);
      *(--to->limit) = (int_or_ptr)q;
    }
    q++;
  }
}


/* Forward each word in the to-space between scan and *next.
  In the process, next may increase, so keep doing it until scan catches up.
  Leave alone:  header words, and "no_scan" (nonpointer) data.
*/
void do_scan(
  const gc_funs_t *gc_funs,
  int_or_ptr *from_start,               /* beginning of from-space */
	int_or_ptr *from_limit,               /* end of from-space */
	int_or_ptr *scan,                     /* start of unforwarded part of to-space */
 	int_or_ptr **next)                    /* next available spot in to-space */
{
  int_or_ptr *s;
  s = scan;
  while(s < *next) {
    gc_block_header hd = (gc_block_header)s;
    gc_block block = gc_funs->gc_block__of_header(hd);
    const size_t sz = gc_funs->gc_block__size_get(hd);
    forward_args_t f_args = {
      .gc_funs = gc_funs,
      .from_start = from_start,
      .from_limit = from_limit,
      .next = next,
      .depth = DEPTH,
    };
    gc_funs->gc_block__ptr_iter(block, forward, &f_args);
    s += sz;
  }
}

/* Copy the live objects out of the "from" space, into the "to" space,
   using fi and ti to determine the roots of liveness. */
void do_generation(
  const gc_funs_t *gc_funs,
  struct space *from,                   /* descriptor of from-space */
	struct space *to,                     /* descriptor of to-space */
	fun_info fi,                          /* which args contain live roots? */
	struct thread_info *ti)               /* where's the args array? */
{
  int_or_ptr *p = to->next;
  // forward_remset(from, to, &to->next);
  forward_roots(gc_funs, from->start, from->limit, &to->next, fi, ti);
  do_scan(gc_funs, from->start, from->limit, p, &to->next);
  int_or_ptr *start = from->start;
  int_or_ptr *end  = from->end;
  from->next  = start;
  from->limit = end;
}

/* malloc an array of words for generation "s", and set s->start and s->next
  to the beginning, and s->limit to the end.
*/
void create_space(
  gc_abort_t gc_abort,
  struct space *s,                      /* which generation to create */
  uintptr_t n)                          /* size of the generation */
{
  int_or_ptr *p;
  if (n >= MAX_SPACE_SIZE)
  {
    gc_abort(GC_E_GENERATION_TOO_LARGE);
  }
  p = (int_or_ptr *)malloc(n * sizeof(int_or_ptr));
  if (p==NULL)
  {
    gc_abort(GC_E_COULD_NOT_CREATE_NEXT_GENERATION);
  }
  s->start=p;
  s->next=p;
  s->limit = p+n;
  s->end = p+n;
}

/* To create a heap, first malloc the array of space-descriptors,
   then create only generation 0.  */
struct heap *create_heap(gc_abort_t gc_abort)
{
  int i;
  struct heap *h = (struct heap *)malloc(sizeof(struct heap));
  if (h == NULL)
  {
    gc_abort(GC_E_COULD_NOT_CREATE_HEAP);
  }
  create_space(gc_abort, h->spaces+0, NURSERY_SIZE);
  for (i = 1; i < MAX_SPACES; i++)
  {
    h->spaces[i].start = NULL;
    h->spaces[i].next = NULL;
    h->spaces[i].limit = NULL;
    h->spaces[i].end = NULL;
  }
  return h;
}

struct thread_info *make_tinfo(gc_abort_t gc_abort)
{
  struct heap *h;
  struct thread_info *tinfo;
  h = create_heap(gc_abort);
  tinfo = (struct thread_info *)malloc(sizeof(struct thread_info));
  if (!tinfo)
  {
    gc_abort(GC_E_COULD_NOT_CREATE_THREAD_INFO);
  }
  tinfo->heap=h;
  tinfo->alloc=h->spaces[0].start;
  tinfo->limit=h->spaces[0].limit;
  return tinfo;
}

/* When the garbage collector is all done, it does not "return"
   to the mutator; instead, it uses this function (which does not return)
   to resume the mutator by invoking the continuation, fi->fun.
   But first, "resume" informs the mutator
   of the new int_or_ptrs for the alloc and limit pointers.
*/
void resume(gc_abort_t gc_abort, fun_info fi, struct thread_info *ti)
{
  struct heap *h = ti->heap;
  int_or_ptr *lo, *hi;
  uintptr_t num_allocs = fi[0];
  lo = h->spaces[0].start;
  hi = h->spaces[0].limit;
  if (hi - lo < num_allocs)
  {
    gc_abort(GC_E_NURSERY_TOO_SMALL);
  }
  ti->alloc = lo;
  ti->limit = hi;
}

/* See the header file for the interface-spec of this function. */
void garbage_collect(const gc_funs_t *gc_funs, fun_info fi, struct thread_info *ti)
{
  struct heap *h = ti->heap;
  int i;
  for (i = 0; i < MAX_SPACES-1; i++)
  {
    /* Starting with the youngest generation, collect each generation
       into the next-older generation.  Usually, when doing that,
       there will be enough space left in the next-older generation
       so that we can break the loop by resuming the mutator. */

    /* If the next generation does not yet exist, create it */
    if (h->spaces[i+1].start==NULL)
    {
      uintptr_t w = h->spaces[i].end - h->spaces[i].start;
      create_space(gc_funs->gc_abort, h->spaces+(i+1), RATIO*w);
    }
    /* Copy all the objects in generation i, into generation i+1 */
    do_generation(gc_funs, h->spaces+i, h->spaces+(i+1), fi, ti);
    /* If there's enough space in gen i+1 to guarantee that the
       NEXT collection into i+1 will succeed, we can stop here */
    if (h->spaces[i].end - h->spaces[i].start <= h->spaces[i+1].limit - h->spaces[i+1].next)
    {
        resume(gc_funs->gc_abort, fi, ti);
        return;
    }
  }
  /* If we get to i==MAX_SPACES, that's bad news */
  gc_funs->gc_abort(GC_E_RAN_OUT_OF_GENERATIONS);
}

void remember(struct thread_info *ti, int_or_ptr *p_cell)
{
  *(int_or_ptr **)(--ti->limit) = p_cell;
  --ti->heap->spaces[0].limit;
}


/* REMARK.  The generation-management policy in the garbage_collect function
   has a potential flaw.  Whenever a record is copied, it is promoted to
   a higher generation.  This is generally a good idea.  But there is
   a bounded number of generations.  A useful improvement would be:
   when it's time to collect the oldest generation (and we can tell
   it's the oldest, at least because create_space() fails), do some
   reorganization instead of failing.
 */
void reset_heap (struct heap *h)
{
  size_t i;
  for (i = 0; i < MAX_SPACES; i++)
  {
    h->spaces[i].next = h->spaces[i].start;
    h->spaces[i].limit = h->spaces[i].end;
  }
}

void free_heap (struct heap *h)
{
  size_t i;
  for (i = 0; i < MAX_SPACES; i++)
  {
    int_or_ptr *p = h->spaces[i].start;
    if (p != NULL)
    {
      free(p);
    }
  }
  free (h);
}

#endif /* COQ_VSU_GC__GC_C */
