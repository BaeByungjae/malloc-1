/*
 * mm.c
 *
 * Zhexin Qiu ID: zhexinq
 *
 * allocator implemented based on LIFO explicit free list,
 * first fit policy, and boundary tag coalescing.
 * the allocator maintains the free blocks as a
 * double-linked list, the links (pointers) are stored
 * as 32-bit unsinged integer to reduce internal fragmentation
 * based on the fact that max heap size of the simulated memory 
 * system is less than 2^32 bytes. Hence, the minimum block size
 * is 16 bytes. Worst-case allocation time is linear to the
 * number of free blocks. Free takes constant time.
 * 
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
// #define DEBUG
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

/*
 * If NEXT_FIT defined use next fit search, else use first fit search 
 */
#define NEXT_FITx

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define MIN_BLK_SIZE 16 /* minimum block size (bytes) */  

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

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
/* User helper function */
static unsigned int ptoi(char * p);
static char *itop(unsigned int p);
static unsigned int next_free_val(void *bp);
static unsigned int prev_free_val(void *bp);
static void put_prev_val(void *bp, unsigned int p);
static void put_next_val(void *bp, unsigned int p);
static char *get_next_free(void *bp);
static char *get_prev_free(void *bp);
/* heap checking helper function */
static void printImg(void);

/* 
 * mm_init - Initialize the memory manager,
 * return 0 if success, -1 if error.
 * 1. start with 4-word structure (padding+proglogue+epilogue)
 * 2. insert a free block with CHUNKSIZE
 * 3. point the chunk to previous and next free blocks
 * 4. initialize root and heap_base address
 */
int mm_init(void) 
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) 
		return -1;
	/* Get the heap base address */
	heap_base = heap_listp;
	/* Initialize root */
	root = 0;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);                     //line:vm:mm:endinit  

#ifdef NEXT_FIT
    rover = heap_listp;
#endif

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
		return -1;

	// mm_checkheap(__LINE__);
    return 0;
}

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload
 *  
 */
void *malloc(size_t size) 
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    dbg_printf("malloc %lu bytes\n", size);

    if (heap_listp == 0){
		mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
		return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                         
		asize = 2*DSIZE;                                       
    else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 

    /* Search the free list for a fit */
    // mm_checkheap(__LINE__);
    if ((bp = find_fit(asize)) != NULL) {
    	// mm_checkheap(__LINE__);  
		place(bp, asize);
		// mm_checkheap(__LINE__);                   
		return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
		return NULL;                                
    place(bp, asize);   

    return bp;
} 

/* 
 * free an allocated block
 * 1. coalesce with any ajacent free blocks
 * 2. put it in the beginning of the free list
 */
void free(void *bp)
{
	dbg_printf("free at %p\n", bp);
    if(bp == 0) 
		return;

    size_t size = GET_SIZE(HDRP(bp));

    if (heap_listp == 0)
		mm_init();

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

	coalesce(bp);
	// mm_checkheap(__LINE__);
}

/*
 * mm_realloc - Naive implementation of realloc
 */
void *realloc(void *ptr, size_t size)
{
	dbg_printf("realloc at %p, %lu bytes\n", ptr, size);
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
		free(ptr);
		return NULL;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
		return malloc(size);
    }

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
		return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    free(ptr);

    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
	size_t bytes = nmemb*size;
	char *newptr;

	newptr = malloc(bytes);
	memset(newptr, 0, bytes);

    return newptr;
}

/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */

static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)  
		return NULL;                                        
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 
	
    /* Coalesce if the previous block was free */
    return coalesce(bp);                                         
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 * 1. coalesce with ajacent blocks
 * 2. place the free'd and coalesce'd block in the beginning of free list
 */
static void *coalesce(void *bp) 
{

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
    	/* inser to the list directly */
    	insertFree(bp);
    	// mm_checkheap(__LINE__);
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
		// mm_checkheap(__LINE__);
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
		// mm_checkheap(__LINE__);
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
		// mm_checkheap(__LINE__);
    }

#ifdef NEXT_FIT
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp))) 
	rover = bp;
#endif
    return bp;
} 

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 *         splitted free block inherit old block's free list position
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    char *old_bp = bp;

    

    if ((csize - asize) >= (2*DSIZE)) {
    	/* allocate the requested block */ 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		/* split the block */
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize-asize, 0));
		PUT(FTRP(bp), PACK(csize-asize, 0));
		/* splitted blk inherit position */			
		put_prev_val(bp, prev_free_val(old_bp));
		put_next_val(bp, next_free_val(old_bp));
		/* point neighboring free blocks back */
		if (prev_free_val(bp))
			put_next_val(itop(prev_free_val(bp)), ptoi(bp));
		if (next_free_val(bp))
			put_prev_val(itop(next_free_val(bp)), ptoi(bp));
		if (old_bp == root) {
			root = bp;
		}
		// mm_checkheap(__LINE__);
    }
    else { 
    	/* delete from the free list */
    	deleteFree(bp);
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		/* root points to the next available free block */
		if (root == old_bp) {
			if ((root = get_next_free(root)))
				put_prev_val(root, 0);
		}
    }
}

/* 
 * find_fit - Find a fit for a block with asize bytes
 * first fit 
 * starts from the free list root
 */
static void *find_fit(size_t asize)
{

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
    char *bp;
	/* start from root until hit NULL ptr */
	for (bp = root; bp; bp = get_next_free(bp)) {
		if (GET_SIZE(HDRP(bp)) >= asize)
			return bp;
	}
    return NULL; /* No fit */
#endif
}

/*
 * delete a free block from the list
 */
static void deleteFree(void *bp) {
	unsigned int next_free = next_free_val(bp);
	unsigned int prev_free = prev_free_val(bp);

	// dbg_printf("BEFORE DELETE_FREE %p\n", bp);
	// printImg();

	if (prev_free) {
		/* bp's prev points to bp's next */
		put_next_val(itop(prev_free), next_free); 
	}
	if (next_free) {
		/* bp's next points to bp's prev */
		put_prev_val(itop(next_free), prev_free);
		/* root free block */
		if (bp == root) {
			root = get_next_free(bp);
		}
	}
	// dbg_printf("AFTER DELETE_FREE %p\n", bp);
	// printImg();
}

/*
 * insert a free block in the front of the list
 */
static void insertFree(void *bp) {
	// dbg_printf("BEFORE INSERT_FREE %p\n", bp);
	// printImg();	
	/* new 1st has NULL prev */ 
	put_prev_val(bp, 0); 

	/* root not existed */
	if (!root) {
		put_next_val(bp, 0);
	}
	/* the free'd blk was coalesced with a front block behind it */
	else if (root > (char *)(bp) && root < NEXT_BLKP(bp)) {
		put_next_val(bp, next_free_val(root));
		if ((next_free_val(bp)))
			put_prev_val(itop(next_free_val(bp)), ptoi(bp));
	}
	/* a normal free blk not coalesced with a front block before it */
	else if (bp != root){
		put_next_val(bp, ptoi(root));
		put_prev_val(root, ptoi(bp));
	}
	/* root points to 1st free block */
	root = bp;
	// mm_checkheap(__LINE__);
	// dbg_printf("AFTER INSERT_FREE %p\n", bp);
	// printImg();
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
/* given a free blk ptr, get next free blk ptr */
static char *get_next_free(void *bp) {
	return (next_free_val(bp)? itop(next_free_val(bp)) : NULL);
}
/* given a free blk ptr, get prev free blk ptr */
static char *get_prev_free(void *bp) {
	return (prev_free_val(bp)? itop(prev_free_val(bp)) : NULL);
}

/*
 * Heap consistency checker
 */ 

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
	char* hdrp;
	char* ftrp;
	char* prev_bp = NULL;
	char* bp;
	size_t countAll = 0, countFree = 0;
	size_t timer = 0;

	/* check heap start */
	if (!in_heap(heap_listp)) {
		dbg_printf("line %d: heap_listp not in heap!\n", lineno);
		exit(1);
	}
	/* check padding */
	if (GET(heap_base) != 0) {
		dbg_printf("line %d: intial padding wrong!\n", lineno);
		exit(1);
	}
	/* check epilogue and prologue */
	hdrp = HDRP(heap_listp);
	ftrp = FTRP(heap_listp);
	if ((GET_SIZE(hdrp) != DSIZE) 
		|| (GET_SIZE(ftrp) != DSIZE)) {
		dbg_printf("line %d: prologue size not correct!\n", lineno);
		dbg_printf("header size: %d\n", (GET_SIZE(hdrp)));
		dbg_printf("footer size: %d\n", (GET_SIZE(ftrp)));
		exit(1);
	}
	if ((!GET_ALLOC(hdrp)) || (!GET_ALLOC(ftrp))) {
		dbg_printf("line %d: prologue not allocated!\n", lineno);
		exit(1);
	}
	hdrp = HDRP(mem_heap_hi()+1);
	if (GET_SIZE(hdrp) != 0) {
		dbg_printf("in get_size\n");
		dbg_printf("line %d: epilogue size not 0!\n", lineno);
		dbg_printf("epilogue size: %u\n", GET_SIZE(hdrp));
		dbg_printf("heap size: %lu\n", mem_heapsize());
		exit(1);
	}
	if (GET_ALLOC(hdrp) != 1) {
		dbg_printf("in get alloc\n");
		dbg_printf("line %d: epilogue not allocated!\n", lineno);
		exit(1);
	}
	/* traverse through all blocks */
	bp = NEXT_BLKP(heap_listp);
	prev_bp = heap_listp;
	for (; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		hdrp = HDRP(bp);
		ftrp = FTRP(bp);
		/* check block address alignment */
		if (!aligned(bp)) {
			dbg_printf("line %d: blk not aligned\n", lineno);
			dbg_printf("blk at %p, blk size %u, alloc: %u", 
				        bp, GET_SIZE(hdrp), GET_ALLOC(hdrp));
			exit(1);
		}
		/* check heap boundaries */
		if (!in_heap(bp)) {
			dbg_printf("line %d: blk not in heap boundaries\n", lineno);
			dbg_printf("blk at %p:", bp);
			exit(1);
		}
		/* check block's header and footer */
		if (GET_SIZE(hdrp) < MIN_BLK_SIZE) {
			dbg_printf("line %d: blk at %p h, header size %u < MIN_BLK_SIZE\n", 
				        lineno, bp, GET_SIZE(hdrp));
			exit(1);
		}
		if (GET_SIZE(ftrp) < MIN_BLK_SIZE) {
			dbg_printf("line %d: blk at %p h, footer size %u < MIN_BLK_SIZE\n", 
			            lineno, bp, GET_SIZE(ftrp));
			exit(1);
		}
		if (GET_SIZE(hdrp) != GET_SIZE(ftrp)) {
			dbg_printf("line %d: blk at %p hdr ftr size inconsistent!\n", 
				        lineno, bp);
			dbg_printf("line %d: hdr size: %u, ftr size: %u", 
				        lineno, GET_SIZE(hdrp), GET_SIZE(ftrp));
			exit(1);
		}
		if (GET_ALLOC(hdrp) != GET_ALLOC(ftrp)) {
			dbg_printf("line %d: blk at %p hdr ftr alloc inconsistent!\n", 
				        lineno, bp);
			dbg_printf("line %d: hdr alloc: %u, ftr alloc: %u", 
				        lineno, GET_ALLOC(hdrp), GET_ALLOC(ftrp));
			exit(1);		
		}
		/* check coalescing */
		if ((GET_ALLOC(HDRP(prev_bp)) == 0) && GET_ALLOC(hdrp)) {
			dbg_printf("line %d: two consecutive free blokcs!\n", 
				        lineno);
			exit(1);
		}
	}
	/* check heap end */

	/* check  free list start */
	bp = root;
	for (; bp; bp = get_next_free(bp)) {
		/* next/previous pointers consistency */
		prev_bp = get_prev_free(bp);
		if ((prev_bp = get_prev_free(bp))) {
			if ((next_free_val(prev_bp) != ptoi(bp)) 
				|| (prev_free_val(bp) != ptoi(prev_bp))) {
				dbg_printf("line %d: next/prev pointers inconsistent!\n", 
					        lineno);
				dbg_printf("prev %p's next: %p, curr %p's prev: %p\n",
					 		prev_bp, itop(next_free_val(prev_bp)), 
					        bp,      itop(prev_free_val(bp)));
				printImg();
				exit(1);
			}
		}
		/* free list pointers in heap */
		if (!in_heap(bp)) {
			dbg_printf("line %d: free list ptr not in heap!\n", lineno);
		}
		/* infinite list something wrong */
		if (timer >= (1 << 28)) {
			dbg_printf("line %d: no ending node in the list!\n", lineno);
			exit(1);
		}
		timer++;
	}

	/* count free blocks */
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (GET_ALLOC(HDRP(bp)) == 0)
			countAll++;
	}
	for (bp = root; bp; bp = get_next_free(bp)) {
		countFree++;
	}
	if (countAll != countFree) {
		dbg_printf("line %d: free blokcs number inconsistent!\n", lineno);
		printImg();
		exit(1);
	}
	/* check free list end */
	/* get gcc to be quite */
	lineno = lineno;
}

static void printImg(void) {
	char *bp;
	
	dbg_printf("**********************************************************\n");
	dbg_printf("the heap image: [addr, size, alloc]\n");
	dbg_printf("[padding, %u, n/a] -> ", GET(heap_base)); 
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		dbg_printf("[%p, %u, %u] -> ", bp, GET_SIZE(HDRP(bp)), 
			        GET_ALLOC(HDRP(bp)));
	}
	dbg_printf("[%p, %u, %u]\n", bp, GET_SIZE(HDRP(bp)), 
			    GET_ALLOC(HDRP(bp)));

	dbg_printf("the free list image: [addr, size, alloc] (prev, next)\n");
	for (bp = root; bp; bp = get_next_free(bp)) {
		dbg_printf("[%p, %u, %u] (%p, %p) -> ", bp, GET_SIZE(HDRP(bp)),
			        GET_ALLOC(HDRP(bp)), get_prev_free(bp), get_next_free(bp));
	}
	dbg_printf("\n**********************************************************\n");
	return;
}