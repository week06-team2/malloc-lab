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
	"team2",
	/* First member's full name */
	"Taejun Kim",
	/* First member's email address */
	"xowns1016@gmail.com",
	/* Second member's full name (leave blank if none) */
	"",
	/* Second member's email address (leave blank if none) */
	""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define WSIZE 4 // Word, header, footer size
#define CHUNKSIZE (1 << 9)
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))							 // p가 가르키는 word의 값을 얻는다.
#define PUT(p, value) (*(unsigned int *)(p) = (value))			 // p가 가르키는 word의 값을 설정한다.
#define GET_SIZE(p) (GET(p) & ~0x7)								 // size를 리턴
#define GET_ALLOC(p) (GET(p) & 0x1)								 // 할당되어 있으면 1을 리턴, 할당되어 있지 않다면 0을 리턴
#define HDRP(bp) ((char *)(bp)-WSIZE)							 // 블록의 header 포인터 반환
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - ALIGNMENT) // 블록의 footer 포인터 반환
#define PRE_BLKP(bp) ((char *)(bp)-GET_SIZE((char *)(bp)-ALIGNMENT))
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp)-WSIZE))
static char *heap_listp;
char *search_listp;
// 현재 블록과 인접 가용 블록들과 통합하기
static void *coalesce(void *ptr)
{
	size_t prev_alloc = GET_ALLOC(HDRP(PRE_BLKP(ptr)));	 // 이전 블록의 할당 여부
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr))); // 다음 블록의 할당 여부
	size_t size = GET_SIZE(HDRP(ptr));					 // 현재 블록의 사이즈

	// Case 1. 이전 블록과 다음 블록이 모두 할당 상태
	if (prev_alloc && next_alloc)
		return ptr;
	// Case 2. 이전 블록은 할당, 다음 블록은 비할당 상태
	else if (prev_alloc && !next_alloc)
	{
		size += GET_SIZE(HDRP(NEXT_BLKP(ptr))); // 사이즈를 다음 블록의 사이즈 만큼 증가
		PUT(HDRP(ptr), PACK(size, 0));			// 현재 블록의 header 재설정
		PUT(FTRP(ptr), PACK(size, 0));			// 현재 블록의 footer 재설정
	}
	// Case 3. 이전 블록은 비할당, 다음 블록은 할당 상태
	else if (!prev_alloc && next_alloc)
	{
		size += GET_SIZE(HDRP(PRE_BLKP(ptr)));	 // 사이즈를 이전 블록의 사이즈 만큼 증가
		PUT(HDRP(PRE_BLKP(ptr)), PACK(size, 0)); // 이전 블록의 header 재설정
		PUT(FTRP(ptr), PACK(size, 0));			 // 현재 블록의 footer 재설정
		ptr = PRE_BLKP(ptr);					 // 현재 블록의 포인터를 이전 블록의 포인터로 설정
	}
	// Case 3. 이전 블록과 다음 블록 모두 비할당 상태
	else
	{
		size += GET_SIZE(HDRP(PRE_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr))); // 사이즈를 이전 블록과 다음 블록의 사이즈 만큼 증가
		PUT(HDRP(PRE_BLKP(ptr)), PACK(size, 0));								// 이전 블록의 header 재설정
		PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));								// 다음 블록의 footer 재설정
		ptr = PRE_BLKP(ptr);													// 현재 블록의 포인터를 이전 블록의 포인터로 설정
	}
	search_listp = ptr;
	return ptr;
}

// 힙 확장하기
static void *extend_heap(size_t words)
{
	char *bp;	 // 블록 포인터
	size_t size; // 힙을 확장할 size(바이트)

	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

	// mem_brk 재설정 하며 bp에 저장
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;
	PUT(HDRP(bp), PACK(size, 0));		  // extend_heap의 header 설정
	PUT(FTRP(bp), PACK(size, 0));		  // extend_heap의 footer 설정
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // new epliogue 블록의 header 설정
	return coalesce(bp);				  // 이전 블록 연결하기(가능하다면)
}
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) // 최초 힙 생성
{

	// 메모리 시스템에서 4워드를 가져와서 빈 가용 리스트를 생성하도록 초기화
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return -1;
	PUT(heap_listp, 0);								   // 정렬을 위한 padding
	PUT(heap_listp + (1 * WSIZE), PACK(ALIGNMENT, 1)); // prologue 블록의 header 설정
	PUT(heap_listp + (2 * WSIZE), PACK(ALIGNMENT, 1)); // prologue 블록의 footer 설정
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));		   // eplilogue 블록의 header 설정
	heap_listp += (2 * WSIZE);						   // heap_listp의 시작점(prologue 블록의 header)
	search_listp = heap_listp;
	// 힙 확장하기
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return -1;
	return 0;
}

// first_fit 방식으로 검색
static void *find_first_fit(size_t asize)
{
	size_t alloc, size;
	char *bp = heap_listp;
	while (1)
	{
		alloc = GET_ALLOC(HDRP(bp));
		size = GET_SIZE(HDRP(bp));
		// epliogue 블록에 도착(찾지 못함)
		if (!size)
			return NULL;
		// 찾을 경우
		else if (size >= asize && !alloc)
			return bp;
		// 다음 블럭으로 이동
		else
			bp = NEXT_BLKP(bp);
	}
}
// next_fit 방식으로 검색
static void *find_next_fit(size_t asize)
{
	size_t alloc, size;

	while (1)
	{
		alloc = GET_ALLOC(HDRP(search_listp));
		size = GET_SIZE(HDRP(search_listp));
		// epliogue 블록에 도착(찾지 못함)
		if (!size)
			return NULL;
		// 찾을 경우
		else if (size >= asize && !alloc)
			return search_listp;
		// 다음 블럭으로 이동
		else
			search_listp = NEXT_BLKP(search_listp);
	}
}
static void place(void *bp, size_t asize)
{
	void *old_fptr = FTRP(bp);			  // 현재 블록의 기존 footer
	size_t old_size = GET_SIZE(old_fptr); // 현재 블록의 기존 사이즈

	if (old_size > asize)
	{
		PUT(HDRP(bp), PACK(asize, 1));					  // 현재 블록의 header 재설정
		PUT(FTRP(bp), PACK(asize, 1));					  // 현재 블록의 새로운 footer 설정
		PUT(FTRP(bp) + WSIZE, PACK(old_size - asize, 0)); // 새로운 헤더 header 설정
		PUT(old_fptr, PACK(old_size - asize, 0));		  // 기존 footer 크기 변경
	}
	else
	{
		PUT(HDRP(bp), PACK(old_size, 1)); // 현재 블록의 header 재설정
		PUT(FTRP(bp), PACK(old_size, 1)); // 현재 블록의 새로운 footer 설정
	}
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
	char *bp;
	size_t extendsize;
	if (size == 0)
		return NULL;

	int newsize = ALIGN(size + SIZE_T_SIZE);

	// case 1. first-fit 방식
	// if ((bp = find_first_fit(newsize)) != NULL)
	// {
	//     place(bp, newsize);
	//     return bp;
	// }

	// free 블록을 찾을 경우
	// case 2. next-fit 방식
	if ((bp = find_next_fit(newsize)) != NULL)
	{
		place(bp, newsize);
		return bp;
	}
	// free 블록을 못찾을 경우
	extendsize = MAX(newsize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
		return NULL;
	place(bp, newsize);
	return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
	size_t size = GET_SIZE(HDRP(ptr)); // 현재 블록의 사이즈
	PUT(HDRP(ptr), PACK(size, 0));	   // 현재 블록의 header를 비할당으로 변경
	PUT(FTRP(ptr), PACK(size, 0));	   // 현재 블록의 footer를 비할당으로 변경
	coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
	void *oldptr = ptr; // 기존 블록의 포인터 저장
	void *newptr;
	void *nextptr;
	size_t oldSize;

	// ptr이 NULL인 경우
	if (ptr == NULL)
		return mm_malloc(size);
	// size가 0인 경우
	if (!size)
	{
		mm_free(ptr);
		return 0;
	}

	oldSize = GET_SIZE(HDRP(ptr));						 // 기존 블록의 사이즈
	size_t newSize = ALIGN(size + SIZE_T_SIZE);			 // 정렬된 사이즈
	int alloc = GET_ALLOC(HDRP(NEXT_BLKP(oldptr)));		 // 다음 블록의 할당 여부
	size_t nextSize = GET_SIZE(HDRP(NEXT_BLKP(oldptr))); // 다음 블록의 사이즈

	if (oldSize == newSize)
		return oldptr;

	else if (oldSize > newSize)
	{
		place(oldptr, newSize);
		if (!alloc)
			coalesce(NEXT_BLKP(oldptr));
		return oldptr;
	}

	else
	{
		if (alloc == 0 && nextSize + oldSize >= newSize)
		{
			oldSize += nextSize;				 // 사이즈를 다음 블록의 사이즈 만큼 증가
			PUT(HDRP(oldptr), PACK(oldSize, 0)); // 현재 블록의 header 재설정
			PUT(FTRP(oldptr), PACK(oldSize, 0)); // 현재 블록의 footer 재설정
			place(oldptr, newSize);
			search_listp = NEXT_BLKP(oldptr);
			return oldptr;
		}
		newptr = mm_malloc(size);
		if (newptr == NULL)
			return NULL;
		// 메모리 복사
		memcpy(newptr, oldptr, oldSize - ALIGNMENT);
		mm_free(oldptr);
		return newptr;
	}
}