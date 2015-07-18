/* 
 * 32-bit and 64-bit clean allocator based on explicit free lists,
 * first fit policy, and immediate boundary tag coalescing. 
 * block alignment 8-byte, minimum block size 16 bytes.
 * free block has additional 2 words point to previous free block,
 * and next free block. A just free'd block is coalesced with any
 * ajacent free blocks and placed in the head of free list
 *
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"

/*
 * If NEXT_FIT defined use next fit search, else use first fit search 
 */
#define NEXT_FIT

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst 

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp

// /* Given heap base address hp, conversions between 64/32-bit data */
// #define PTOI(hp, p) ((unsigned int)(p - hp))
// #define ITOP(hp, val) ((char *)(val) + hp)

// /* Given a free block ptr bp, compute 32-bit val of prev/next free block */
// #define NEXT_FREE_VAL(bp) (GET(bp))
// #define PREV_FREE_VAL(bp) (GET((char *)bp + WSIZE))

// /* Given a free block ptr bp, put prev/next 32-bit val in it */
// #define PUT_NEXT_VAL(bp, val) (PUT(bp, val))
// #define PUT_PREV_VAL(bp, val) (PUT(((char *)(bp) + WSIZE), val))

/* $end mallocmacros */

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */  
#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif
static char *root = 0; /* Pointer to first free block */
static char *heap_base = 0; /* Starting address of the heap */

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void deleteFree(void *bp);
static void insertFree(void *bp);
/* Experimental helper function */
static unsigned int ptoi(char * p);
static char *itop(unsigned int p);
static unsigned int next_free_val(void *bp);
static unsigned int prev_free_val(void *bp);
static void put_prev_val(void *bp, unsigned int p);
static void put_next_val(void *bp, unsigned int p);

/* 
 * mm_init - Initialize the memory manager 
 * 1. start with 4-word structure (padding+proglogue+epilogue)
 * 2. insert a free block with CHUNKSIZE
 * 3. point the chunk to previous and next free blocks
 * 4. initialize root and heap_base address
 */
/* $begin mminit */
int mm_init(void) 
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) //line:vm:mm:begininit
		return -1;
	/* Get the heap base address */
	heap_base = heap_listp;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);                     //line:vm:mm:endinit  
/* $end mminit */

#ifdef NEXT_FIT
    rover = heap_listp;
#endif
/* $begin mminit */

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
		return -1;
	
	put_next_val(NEXT_BLKP(heap_listp), 0); /* next free block is NULL */
	put_prev_val(NEXT_BLKP(heap_listp), 0); /* previous free block is NULL */
	root = NEXT_BLKP(heap_listp); /* root points to 1st free block */

    return 0;
}
/* $end mminit */

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) 
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

/* $end mmmalloc */
    if (heap_listp == 0){
	mm_init();
    }
/* $begin mmmalloc */
    /* Ignore spurious requests */
    if (size == 0)
	return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                          //line:vm:mm:sizeadjust1
	asize = 2*DSIZE;                                        //line:vm:mm:sizeadjust2
    else
	asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); //line:vm:mm:sizeadjust3

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  //line:vm:mm:findfitcall
	place(bp, asize);                  //line:vm:mm:findfitplace
	return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 //line:vm:mm:growheap1
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
	return NULL;                                  //line:vm:mm:growheap2
    place(bp, asize);                                 //line:vm:mm:growheap3
    return bp;
} 
/* $end mmmalloc */

/* 
 * free an allocated block
 * 1. coalesce with any ajacent free blocks
 * 2. put it in the beginning of the free list
 */
/* $begin mmfree */
void mm_free(void *bp)
{
/* $end mmfree */
    if(bp == 0) 
		return;

/* $begin mmfree */
    size_t size = GET_SIZE(HDRP(bp));
/* $end mmfree */
    if (heap_listp == 0)
		mm_init();
 
/* $begin mmfree */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

	coalesce(bp);
}

/* $end mmfree */
/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 * 1. coalesce with ajacent blocks
 * 2. place the free'd and coalesce'd block in the beginning of free list
 */
/* $begin mmfree */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
    	/* inser to the list directly */
    	insertFree(bp);
    	return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		/* delete the next free block from list */
		deleteFree(NEXT_BLKP(bp));
		/* coalesce with the next */
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		/* insert free block into the list */
		insertFree(bp);
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		/* delete the previous free block from list */
		deleteFree(PREV_BLKP(bp));
		/* coalesce with the prev */
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		/* insert free block into the list */
		insertFree(bp);
    }

    else {                                     /* Case 4 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
	        	GET_SIZE(FTRP(NEXT_BLKP(bp)));
	    /* delete blocks in both sides */
	    deleteFree(NEXT_BLKP(bp));
	    deleteFree(PREV_BLKP(bp));
	    /* coalesce with both sides */    	
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		/* insert free block into the list */
		insertFree(bp);
    }
/* $end mmfree */
#ifdef NEXT_FIT
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp))) 
	rover = bp;
#endif
/* $begin mmfree */
    return bp;
}
/* $end mmfree */

/*
 * mm_realloc - Naive implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
	mm_free(ptr);
	return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
	return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
	return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}

/* 
 * checkheap - We don't check anything right now. 
 */
void mm_checkheap(int verbose)  
{ 
	verbose = verbose;
}

/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; //line:vm:mm:beginextend
    if ((long)(bp = mem_sbrk(size)) == -1)  
	return NULL;                                        //line:vm:mm:endextend

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   //line:vm:mm:freeblockhdr
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   //line:vm:mm:freeblockftr
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ //line:vm:mm:newepihdr
	
    /* Coalesce if the previous block was free */
    return coalesce(bp);                                          //line:vm:mm:returnblock
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
     /* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));   

    if ((csize - asize) >= (2*DSIZE)) { 
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));
	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else { 
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
    }
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
/* $begin mmfirstfit */
/* $begin mmfirstfit-proto */
static void *find_fit(size_t asize)
/* $end mmfirstfit-proto */
{
/* $end mmfirstfit */

#ifdef NEXT_FIT 
    /* Next fit search */
    char *oldrover = rover;

    /* Search from the rover to the end of list */
    for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
	if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
	    return rover;

    /* search from start of list to old rover */
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
	if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
	    return rover;

    return NULL;  /* no fit found */
#else 
/* $begin mmfirstfit */
    /* First fit search */
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
	    return bp;
	}
    }
    return NULL; /* No fit */
/* $end mmfirstfit */
#endif
}

/*
 * delete a free block from the list
 */
static void deleteFree(void *bp) {
	size_t next_free = next_free_val(bp);
	size_t prev_free = prev_free_val(bp);

	/* delete next free block from the list */
	if (prev_free) 
		put_prev_val(itop(prev_free), next_free); 
	if (next_free) 
		put_prev_val(itop(next_free), prev_free);
}

/*
 * insert a free block in the front of the list
 */
static void insertFree(void *bp) {
	/* new 1st has NULL prev */ 
	put_prev_val(bp, 0); 

	/* redirect the old 1st only when it was not coalesced */
	if ((root < (char *)bp) || (root >= NEXT_BLKP(bp))) {
		/* new 1st's next is the old 1st */
		put_next_val(bp, ptoi(root));
		/* old 1st's prev is the new 1st */ 
		put_prev_val(root, ptoi(bp));
	}
	else {
		/* new 1st's next is the old 1st's next */
		put_next_val(bp, next_free_val(root));
		/* old 1st's next's prev is the new 1st */
		put_prev_val(itop(next_free_val(root)), ptoi(bp));
	}
	/* root points to 1st free block */
	root = bp; 
}

/* convert a 64-bit ptr value to a 32-bit unsigned int value */
static unsigned int ptoi(char *p) {
	return (unsigned int)(p-heap_base);
}

/* convert a 32-bit unsigned int value back to 64-bit pointer */
static char *itop(unsigned int p) {
	return (char *)((long int)(p) + (long int)(heap_base));
}
/* given a free block ptr, get next block ptr 32-bit value */
static unsigned int next_free_val(void *bp) {
	return GET(bp); 
}
/* given a free block ptr, get prev block ptr 32-bit value */
static unsigned int prev_free_val(void *bp) {
	return GET(bp+WSIZE);
}
/* put a 32-bit value in a free block prev free block field */
static void put_prev_val(void *bp, unsigned int p) {
	PUT(bp+WSIZE, p);
}
/* put a 32-bit value in a free block next free block field */
static void put_next_val(void *bp, unsigned int p) {
	PUT(bp, p);
}
