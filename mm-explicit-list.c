/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"yolo",
	/* First member's full name */
	"ccc12",
	/* First member's email address */
	"myemail",
	/* Second member's full name (leave blank if none) */
	"",
	/* Second member's email address (leave blank if none) */
	""
};

#define WSIZE       4
#define DSIZE       8
#define CHUNKSIZE   (1<<12)

/* single word (4) or double word (8) alignment */
#define ALIGNMENT   8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size)         (((size) + (ALIGNMENT-1)) & ~0x7)

/* Pack size(multiple of 8) with an allocate bit */
#define PACK(size, alloc)   ((size) | (alloc))
#define MAX(a, b)           (((a) > (b)) ? (a) : (b))

/* Put a word into where p points at */
#define PUT(p, val)         (*(unsigned int *)(p) = (val))
#define GET(p)              (*(unsigned int *)(p))

/* Get size or alloca bit of the block */
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)

/* 
 * Operates on block pointer which points to the first byte of the payload
 * comput its header and footer
 */
#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

#define GET_NEXTFREEP(bp)      (*((void **)((bp) + DSIZE)))
#define GET_PREVFREEP(bp)      (*((void **)(bp)))

#define PUT_NEXTP(bp, val)  (GET_NEXTFREEP((bp)) = (val))
#define PUT_PREVP(bp, val)  (GET_PREVFREEP((bp)) = (val))

#define SIZE_T_SIZE         (ALIGN(sizeof(size_t)))

/* Global variables */
static void *heap_listp = NULL; /* Pointer to the second Prologue block */
static void *heap_freep = NULL; /* Pointer to the first free block's header */

/* Helper functions */
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);

static void printblock(void *bp); 
static void checkblock(void *bp);
static void printfreeblock(void *bp);
void checkheap(int verbose);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
	/* Setting up the empty list with padding word 
	 * and Prologue and Epilogue blocks
	 */
    void *bp;

	if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1)	
		return -1;
	PUT(heap_listp, 0);                                 /* paddding word */
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));        /* Prologue block */
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
	PUT(heap_listp + (3*WSIZE), PACK(0, 1));            /* Epilogue block */
	heap_listp += (2 * WSIZE);

    /* Setting up free list to point at the first free block */
	if ((heap_freep = extend_heap(CHUNKSIZE / WSIZE)) == NULL)
		return -1;
    /* Setting up the first free block which has no next and 
     * prev free block
     */
    bp = heap_freep;    
    PUT_NEXTP(bp, 0);
    PUT_PREVP(bp, 0);

    checkheap(1);
	return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    /* Final size after alignment and added overhead*/
    size_t asize;
    size_t extendsize;
    void *bp;

    /* Igonore retarded calls to 0 */
    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else 
        asize = ALIGN(size + DSIZE);
    
    if ((bp = find_fit(asize))) {
        place(bp, asize);
        return bp;
    }
    
    /* Once I typed MAX(size, CHUNKSIZE) which made the extendsize 8 bytes
     * smaller than what I wanted and segfaulted the program. What a debug
     * experience
     */
    extendsize = MAX(asize, CHUNKSIZE);                  
    if (!(bp = extend_heap(extendsize / WSIZE)))
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t oldsize;

    /* Equivalent of calling mm_free() */
    if (size == 0)  {
        mm_free(ptr);
        return NULL;
    }
    /* Just malloc */
    if (ptr == NULL)
        return mm_malloc(size);

    newptr = mm_malloc(size);
    /* If mm_malloc() fails then then return NULL and 
     * the original block is untoched
     */
    if (!newptr) 
        return NULL;
    
    oldsize = GET_SIZE(HDRP(oldptr));
    oldsize = size < oldsize ? size : oldsize;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block */
    mm_free(ptr);

    return newptr;
}

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
	void *bp;
	size_t size;

	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *) -1)
		return NULL;
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(FTRP(bp) + WSIZE, PACK(0, 1));  /*New Epilogue */
	
	return coalesce(bp);
}

/* 
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {         /* Prev and next are both in use */
        return bp;
    } else if (prev_alloc && !next_alloc) { /* Pre in use and next free */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) { /* Pre free and next in use */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {                                /* Pre and next are both free */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize) 
{
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }
    return NULL;
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize) 
{
    size_t size;

    size = GET_SIZE(HDRP(bp));
    
    if ((size - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(size - asize, 0));
        PUT(FTRP(bp), PACK(size - asize, 0));
    } else {
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
    }
}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

static void printfreeblock(void *bp)
{
    void *nextp;
    void *prevp;

    if (bp == NULL)
        return;
    nextp = GET_NEXTFREEP(bp);
    prevp = GET_PREVFREEP(bp);
    printf("NEXT-> (%p)\n", nextp);
    printf("PREV-> (%p)\n", prevp);
    return printfreeblock(nextp);
}

/* 
 * checkheap - Minimal check of the heap for consistency 
 */
void checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose) {
        printf("Heap (%p):\n", heap_listp);
        printf("Freelist -> (%p)\n",heap_freep);
    }

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) 
            printblock(bp);
        checkblock(bp);
    }

    if (verbose) {
        printblock(bp);
        printfreeblock(heap_freep);
    }
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");

}

