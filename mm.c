/* 
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP2e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"The JEDI",
	/* First member's full name */
	"Abhi Sapariya",
	/* First member's email address */
	"201401210@daiict.ac.in",
	/* Second member's full name (leave blank if none) */
	"Krishanu Konar",
	/* Second member's email address (leave blank if none) */
	"201401127@daiict.ac.in"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
//#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define NEXT_BLKP(bp)  ((void *)(bp) + GET_SIZE(HDRP(bp)))
//#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
#define PREV_BLKP(bp) ((void *)(bp) - GET_SIZE((void *)(bp) - DSIZE))

/* Global variables: */
static char *heap_listp=0; /* Pointer to first block */  

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp);

/*myMacros */
/*Pointer to get NEXT and PREVIOUS pointer of free_list*/
#define NEXT_PTR(p)  (*(char **)(p + WSIZE))
#define PREV_PTR(p)  (*(char **)(p))


/* myVariables */
// Pointer pointing to starting of explicit free list
static char* freeListPtr=0;

/* myMethods */
// Function prototypes for next_fit and best_fit
//static void *next_fit(size_t asize);
//static void *best_fit(size_t asize);

// Functions prototypes for adding and deleting free memory blocks in free_list
static void free_list_add(void* ptr);
static void free_list_delete(void* ptr);


/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{

	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(8 * WSIZE)) == NULL)
		return (-1);
	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);
	
	// Initialize freeListPtr to point to starting of free memory in heap
	freeListPtr=heap_listp;

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)	
		return (-1);
	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{	
	size_t oldsize,newsize;
	void *newptr;

	//If size is negative it means nothing, just return NULL
	if((int)size < 0) 
    	return NULL;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));

	oldsize=GET_SIZE(HDRP(ptr));
	newsize = size + (2 * WSIZE);					// newsize after adding header and footer to asked size

	/* Copy the old data. */

	//If the size needs to be decreased, shrink the block and return the same pointer
	if (newsize <= oldsize){
		
	   /*
		* AS MENTIONED IN THE PROJECT HANDOUT THE CODE SNIPPET BELOW SHRINKS THE OLD ALLOCATED BLOCK
		* SIZE TO THE REQUESTED NEW SIZE BY REMOVING EXTRA DATA i.e. (oldsize-newsize) AMOUNT OF DATA.
		* ON RUNNING CODE WITH THIS SNIPPET, THE FOLLOWING ERROR OCCURS 'mm_realloc did not preserve 
		* the data from old block' WHICH WILL ALWAYS HAPPEN IF WE SHRINK THE BLOCK.
		*/

		/*if(oldsize-newsize<=2*DSIZE){
			return ptr;
		}
		PUT(HDRP(ptr),PACK(newsize,1));
		PUT(FTRP(ptr),PACK(newsize,1));
		PUT(HDRP(NEXT_BLKP(ptr)),PACK(oldsize-newsize,1));
		PUT(FTRP((NEXT_BLKP(ptr)),PACK(oldsize-newsize,1));
		mm_free(NEXT_BLKP(ptr));
		free_list_add(NEXT_BLKP(ptr));*/
		
		return ptr;
	}
	else{
		size_t if_next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));		//check if next block is allocated
		size_t next_blk_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));		//size of next block
		size_t total_free_size = oldsize + next_blk_size;			//total free size of current and next block

		//combining current and next block if total_free_size is greater then or equal to new size
		if(!if_next_alloc && total_free_size>= newsize){
			free_list_delete(NEXT_BLKP(ptr));	
			PUT(HDRP(ptr),PACK(total_free_size,1));
			PUT(FTRP(ptr),PACK(total_free_size,1));
			return ptr;
		}
		//finding new size elsewhere in free_list and copy old data to new place
		else{
			newptr=mm_malloc(newsize);
			
			/* If realloc() fails the original block is left untouched  */
			if (newptr == NULL)
				return (NULL);

			place(newptr,newsize);
			memcpy(newptr,ptr,oldsize);
			mm_free(ptr);
			return newptr;
		}
	}
}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp) 
{
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp ; // prev_alloc will be true if previous block is allocated or its size is zero
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) {                 /* Case 1 */
		free_list_add(bp);							// adding free block in free_list
		return (bp);
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		free_list_delete(NEXT_BLKP(bp));			// next free block is deleted from free_list
		PUT(HDRP(bp), PACK(size, 0));				// updating the size of header and footer
		PUT(FTRP(bp), PACK(size, 0));
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		free_list_delete(PREV_BLKP(bp));			// previous free block is deleted from free_list
		PUT(FTRP(bp), PACK(size, 0));				// updating the size of header and footer
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	} else {                                        /* Case 4 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		free_list_delete(PREV_BLKP(bp));			// both free blocks are deleted from free_list
		free_list_delete(NEXT_BLKP(bp));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));	// updating the size of header and footer
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	free_list_add(bp);								// add newly coalesced block to free_list

	// only for best_fit and next_fit
	/*if ((freeListPtr > (char *)bp) && (freeListPtr < NEXT_BLKP(bp)))
		freeListPtr = bp;*/
	return (bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
	
	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *
find_fit(size_t asize)
{
	void *bp;

	/* Search for the first fit. */
	// traversing through the free_list until free block is found
	for (bp = freeListPtr; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_PTR(bp)) {
		if (asize <= GET_SIZE(HDRP(bp)))	//block of required size is found
			return (bp);
	}
	/* No fit was found. */
	return (NULL);
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */

/*static void *next_fit(size_t asize)
{
	char *temp=freeListPtr;
	for(;GET_SIZE(HDRP(freeListPtr)) > 0;freeListPtr=NEXT_BLKP(freeListPtr))
		if (!GET_ALLOC(HDRP(freeListPtr)) && asize <= GET_SIZE(HDRP(freeListPtr)))
			return freeListPtr;
	for(freeListPtr=heap_listp;freeListPtr<temp;freeListPtr=NEXT_BLKP(freeListPtr))
		if (!GET_ALLOC(HDRP(freeListPtr)) && asize <= GET_SIZE(HDRP(freeListPtr)))
			return freeListPtr;
	return NULL;
}*/

/*static void *best_fit(size_t asize)
{
	void *bp;
	int flag=0;
	unsigned int min;
	for(bp=heap_listp;GET_SIZE(HDRP(bp)) > 0;bp=NEXT_BLKP(bp))
	{
		if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
		{
			if(flag==0)
			{
				min=GET_SIZE(HDRP(bp));
				freeListPtr=bp;
				flag=1;
			}
			else
			{
				if(GET_SIZE(HDRP(bp))<min)
				{
					min=GET_SIZE(HDRP(bp));
					freeListPtr=bp;
				}
			}
		}
	}
	if(flag==1)
		return freeListPtr;
	return NULL;
}*/

static void
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   

	if ((csize - asize) >= (2 * DSIZE)) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		free_list_delete(bp);						// free block is deleted from free_list
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		coalesce(bp);
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		free_list_delete(bp);						// free block is deleted from free_list
	}
}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp) 
{

	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
	void*bp=freeListPtr;        
        while (NEXT_PTR(bp)!=NULL) {                       
            //checks if blocks in free_list are actually free
            if (GET_ALLOC(HDRP(bp)) == 1 || GET_ALLOC(FTRP(bp)) == 1){
                    printf("Encountered an allocated block in free list\n");
                    return;
            }                  
            bp  = NEXT_PTR(bp);
        }

    if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");

}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	bool halloc, falloc;
	size_t hsize, fsize;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}

/* myMethods */
// adds free block pointed by ptr to the free_list
static void free_list_add(void* ptr){
	NEXT_PTR(ptr)=freeListPtr;
	PREV_PTR(freeListPtr)=ptr;
	PREV_PTR(ptr)=NULL;
	freeListPtr=ptr;
}

// deletes free block pointed by ptr to the free_list
static void free_list_delete(void* ptr){
	if(PREV_PTR(ptr)==NULL)						//if ptr points to root of free_list
		freeListPtr=NEXT_PTR(ptr);
	else										//if ptr points to any arbitary block in free_list 
		NEXT_PTR(PREV_PTR(ptr))=NEXT_PTR(ptr);
	PREV_PTR(NEXT_PTR(ptr))=PREV_PTR(ptr);
}

/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
