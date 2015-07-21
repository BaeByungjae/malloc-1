/*
 * mm.c
 *
 * Zhexin Qiu id: zhexinq
 * 
 * Allocator implemented based on segregated fits.
 * Block format: one word for size and alloc state, one 
 * word for bondary tag coalescing. Free blocks have double
 * pointers to prev/next free blocks. Store 8-byte pointers 
 * as 4-byte unsigned int using the fact that heap address 
 * space is less than 32-bit. Minimum block size 16 bytes.
 * Free policy: LIFO, free'd and coalesced block 
 * inserted to front of appropriate list.
 * Allocation policy: first-search on appropriate list,
 * if found, split and insert the remainder to appropriate
 * list. Repeat on larger size class if not found. If no
 * fits on all size classes, request heap memory from OS,
 * coalesced with any previous free block, allocate
 * requested block out of this new block, and put remainder
 * into appropriate size class.
 * Size classes (in word size, 29 in total):
 * [4], [6], ..., [32]
 * [32+2, 2^6), [2^6, 2^7), ..., [2^17, 2^18), [2^18, inf]
 * 
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<21)  /* Extend heap by this amount (bytes) */
#define MIN_BLK_SIZE 16 /* minimum block size (bytes) */ 
#define NUM_SIZES 29 /* number of size classes */
#define IR_SIZES 15 /* number of irregular classes */
#define PWR2_SIZES 14 /* number of power of 2 classes */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                    

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                     
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Read and write a pointer at an address (64-bit) */
#define GET_PTR(addr) ((void *)(*(long *)(addr)))
#define PUT_PTR(addr, ptr) (*(long *)(addr) = (long)ptr)

/* Global variables */
static void *heap_listp = 0;
static void *free_lists_base = 0;
static void *free_lists_end = 0;
static void *free_lists_pwr2_base = 0;

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void deleteBlk(void *bp);
static void insertBlk(void *bp);
static void *hashBlkSize(size_t asize);
/* Internal routines for pointer arithmitic */
static unsigned int ptoi(void *bp);
static void *itop(unsigned int bpi);
static void *get_prev_free_bp(void *bp);
static void *get_next_free_bp(void *bp);
static size_t countOne(size_t n);

/*
 * Initialize: return -1 on error, 0 on success.
 * Initial heap: 29 size class pointers + proplogue + epilogue
 */
int mm_init(void) {
	int i;

	/* Create the initial empty free lists */
	free_lists_base = mem_heap_lo();
	if ((heap_listp = mem_sbrk(NUM_SIZES*DSIZE+4*WSIZE)) == (void *)-1)
		return -1;
	/* Initialize all list pointers to NULL */
	for (i = 0; i < NUM_SIZES; i++) {
		*(long *)(heap_listp) = 0;
		heap_listp = heap_listp + DSIZE;
	}
	free_lists_end = heap_listp;
	free_lists_pwr2_base = free_lists_base + IR_SIZES * DSIZE;
	/* Add prologue and epilogue */
	PUT(heap_listp, 0); /* Zero padding */
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
	PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
	heap_listp += (2*WSIZE);

    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
	// size_t asize; /* Adjusted block size */
	// size_t extendsize; /* Amount to extend heap if no fit found */
	size = size;
	extend_heap(0);
	find_fit(0);
	place(0, 0);
    return NULL;
}

/*
 * free a block at given ptr
 */
void free (void *bp) {
	if (bp == 0)
		return;

	/* get the allocated block size */
	size_t size = GET_SIZE(HDRP(bp));

	/* free the block */
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));

	/* coalesce with any ajacent blocks */
	bp = coalesce(bp);

	/* insert the free'd coalesced block to appropriate list */
	insertBlk(bp);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
	oldptr = oldptr;
	size = size;
    return NULL;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
	size_t bytes;
	void *ptr;

	bytes = nmemb * size;
	ptr = malloc(bytes);
	memset(ptr, 0, bytes);

    return ptr;
}

/*
 * internal helper routines 
 */

/*
 * extend the heap by words by asking the OS
 * return pointer to the paged-in coalesced free block of size requested
 */
static void *extend_heap(size_t words) {
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;
	/* Initialize free block header/footer and epilogue header */
	PUT(HDRP(bp), PACK(size, 0)); /* free block header */
	PUT(FTRP(bp), PACK(size, 0)); /* free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

	/* Coalesce if previous block is free */
	return coalesce(bp);
}

/*
 * merge any free blocks adjacent in address
 * 1. delete adjacent blocks from their coressponding free lists
 * 2. coalesce them to a larger free block
 * 3. return this new block to the caller
 *
 */
static void *coalesce(void *bp) {
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	/* both sides allocated */
	if (prev_alloc && next_alloc) {
		return bp;
	}
	/* prev allocated but next free */
	else if (prev_alloc && !next_alloc) {
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		/* delete next block from its list */
		deleteBlk(NEXT_BLKP(bp));
		/* coalesce with next */
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		return bp;
	}
	/* prev free and next allocated */
	else if (!prev_alloc && next_alloc) {
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		/* delete prev block from its list */
		deleteBlk(PREV_BLKP(bp));
		/* coalesce with prev */
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		return bp;
	}
	/* both sieds free */
	else {
		size += (GET_SIZE(HDRP(PREV_BLKP(bp))) +
				GET_SIZE(HDRP(NEXT_BLKP(bp))));
		/* detele prev and next free blocks from their lists */
		deleteBlk(NEXT_BLKP(bp));
		deleteBlk(PREV_BLKP(bp));
		/* coalesce with both sides */
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		return bp;
	}

}

/*
 * delete free block from lists
 * 1. bp's prev (if exists) points to its next
 * 2. bp's next (if exists) points to its prev
 * 3. change the list head to bp's next if bp is the head
 */
static void deleteBlk(void *bp) {
	unsigned int prev = GET(bp);
	unsigned int next = GET(bp+WSIZE);
	void *array_ptr = 0;

	if (prev)
		PUT(get_prev_free_bp(bp)+WSIZE, next); /* prev points to bp's next */
	/* bp is the head of this list */	
	else {
		/* get addr in the array of ptrs to lists */
		array_ptr = hashBlkSize(GET_SIZE(HDRP(bp)));
		/* set the ptr to lists to bp's next */ 
		PUT_PTR(array_ptr, itop(next));
	}
	if (next)
		PUT(get_next_free_bp(bp), prev); /* next points to bp's prev */
	return;
}

/*
 * insert free block into appropriate lists
 * 1. hash size to get addr in the array of ptrs to lists
 * 2. insert the free block in the front of appropriate list
 */
static void insertBlk(void *bp) {
	void *array_ptr;
	void *head_bp;

	array_ptr = hashBlkSize(GET_SIZE(HDRP(bp)));
	/* at least one free block already in the list */
	if ((head_bp = GET_PTR(array_ptr))) {
		PUT(bp, 0); /* set bp's prev */
		PUT(bp+WSIZE, ptoi(head_bp)); /* set bp's next */
		PUT(head_bp, ptoi(bp)); /* set old head's prev */
	}
	/* the list is empty */
	else {
		PUT(bp, 0); /* set bp's prev */
		PUT(bp+WSIZE, 0); /* set bp's next */
	}
	PUT_PTR(array_ptr, bp); /* reset the head to be bp */ 
}  

/*
 * find a fit in all the available free blocks
 * 1. use hash function to locate an appropriate list to start
 * 2. if fit not found, search larger size class
 * 3. repeate until a fit or exhaust all lists without a fit
 */
static void *find_fit(size_t asize) {
	void *bp;
	void *array_ptr;

	array_ptr = hashBlkSize(asize);

	for (; array_ptr < free_lists_end; array_ptr+=DSIZE) {
		bp = GET_PTR(array_ptr);
		while (bp) {
			if (GET_SIZE(HDRP(bp)) >= asize)
				return bp;
			bp = get_next_free_bp(bp);
		}
	}
	/* fit not found */
	return NULL;
}

/*
 * alloactes a block and split if possible
 */
static void place(void *bp, size_t asize) {
	bp = bp;
	asize = asize;
} 

/*
 * hashes the requested size to appropriate list
 * return an address storing 1st free block of the appropriate list
 */
static void *hashBlkSize(size_t asize) {
 	size_t words = asize / WSIZE;

 	if (words <= 32) {
 		return (free_lists_base + ((words-4)/2)*DSIZE);
 	}
 	else {
 		return (free_lists_pwr2_base + countOne(words >> 6) * DSIZE);
 	}
 }

static size_t countOne(size_t n) {
	size_t count = 0;
	while (n) {
		count++;
		if (count == (PWR2_SIZES-1))
			break;
		n >>= 1;
	}
	return count;
}

/* 
 * internal helper functions for 64-bit pointer and 32-bit int value
 * conversion, and free list traversing
 */
static unsigned int ptoi(void *bp) {
	return (unsigned int)(bp - mem_heap_lo());
}

static void *itop(unsigned int bpi) {
	return bpi? ((void *)((long)(bpi)) + (long)(mem_heap_lo())) : NULL;
}

static void *get_prev_free_bp(void *bp) {
	return itop(GET(bp));
}

static void *get_next_free_bp(void *bp) {
	return itop(GET((char *)bp + WSIZE));
}

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {
	in_heap(heap_listp);
	aligned(heap_listp);
	lineno = lineno;
}
