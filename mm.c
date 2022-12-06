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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 // 더블워드, 8바이트 단위로 할당

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)   // 8바이트 단위로 할당할 용량 반환 함수

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // 8바이트를 나타냄 (보통 헤더 푸터 합쳐서 8바이트 추가됨으로 이거 더해서 사이즈 잡음)

/* Basic constants and macros */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)   /* Extend heap by amount (bytes) 2048바이트 */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))    // 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값 리턴

/* Read and write a word at address p */
#define GET(p)      (*(unsigned int *)(p))       // p가 참조하는 헤더 리턴
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // p가 가리키는 워드에 val 저장

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~0x7) // 헤더 사이즈만 리턴, 할당 비트 지움
#define GET_ALLOC(p)    (GET(p) & 0x1) // 할당 여부 리턴

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)    ((char *)(bp) - WSIZE)  // 헤더를 가리키는 포인터 리턴
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 풋터를 가리키는 포인터 리턴

/* Given block ptr bp, comupte address of next and previous blocks */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)) // 다음 블록 포인터 리턴
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)) // 이전 블록 포인터 리턴

/* 추가로 선언한 함수들 */
static void *heap_listp;
// static void *last_bp;       // 이 변수는 다른 파일에서 여러번 접근할 때도 계속 기존 값을 유지해야 하므로 static이 필요하다.
/* 
 * last_bp를 업데이트 해주는 경우는 총 3가지. 첫 init때 last_bp = heap_listp로 초기화해주는 과정.
 * 다음은 place로 블록을 할당해줄 때 bp가 바뀌므로 한번.
 * coalesce로 블록 합치는 과정에서 앞 블록과 합쳐질 경우 bp가 바뀌므로 한번.
*/

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
// static void *first_fit(size_t asize);
// static void *next_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){
        return -1;                                                             // heap_listp 에 힙의 바닥 주소(1번째 워드 주소)를 대입, 현재 brk -> 4 wsize
    }
    PUT(heap_listp, 0);                                                 // heap 첫 칸에 0 값 대입
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    // heap 2, 3번째 칸에 더블워드 사이즈 (8)와 할당(1) 합하여 대입
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));            // heap 4번째 칸에 사이즈 0 과 할당(1) 합하여 대입
    heap_listp += (2*WSIZE);                                        // heap_listp 에 heap 영역의 3번째 word를 가르키는 주소 대입

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }

    // last_bp = heap_listp;
    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) *WSIZE : words * WSIZE;    // 더블워드 정렬을 위해 홀수워드사이즈는 1 더해서 size 변수에 대입
    if ((long)(bp = mem_sbrk(size)) == -1){     // bp 에 old brk 대입 및 brk size 만큼 늘림
        return NULL;
    }

    /* Initialize free block header/footer and the epilogue header */   // 힙을 늘리면서 추가된 비할당 블록과 기존 가장 끝 비할당 블록 coalesce 전처리
    PUT(HDRP(bp), PACK(size, 0));   // 추가된 비할당 블록의 bp는 old brk이다. 그 블록에 비할당 정보 담는 과정
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 다음블록포인터로 이동 후 헤더포인터로 이동해 한칸짜리 에필로그 포인터에 값 담아줌

    /* Coalesce if the previous block was free */
    return coalesce(bp);    // 힙을 늘리면서 추가된 비할당 블록과 기존 가장 끝 비할당 블록 coalesce
}

 void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));   // 헤더에 할당정보 지우기
    PUT(FTRP(bp), PACK(size, 0));   // 푸터에 할당정보 지우기
    coalesce(bp);   // 전 후 블록과 연결
 }

 static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));     // 이전 블록의 푸터의 할당여부, 즉, 이전 블록 할당여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));     // 다음 블록 헤더의 할당여부, 즉, 다음 블록 할당여부
    size_t size = GET_SIZE(HDRP(bp));       // 현재 블록의 사이즈

    if (prev_alloc && next_alloc) {                                /* Case 1 : 전-할당 후-할당 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {                      /* Case 2 : 전-할당 후-비할 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {                      /* Case 3 : 전-비할 후-할당 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                                                         /* Case 4 : 전-비할 후-비할 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
 }


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * 
 */
void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0){
        return NULL;
    }
    if (size <= DSIZE){
        asize = 2 * DSIZE;
    }   else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);     // 헤더 푸터위한 dsize 더하고 dsize 정렬 맞게 올림처리하는 과정
    }
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);                       
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize){
    char *bp = (char*)heap_listp + DSIZE;

    while(1){
        if(!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= asize)){
            return bp;
        }
        else if(!GET_SIZE(HDRP(bp))){
            return NULL;
        }else{
            bp = NEXT_BLKP(bp);
        }
    }
}

static void place(void *bp, size_t asize){

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


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














