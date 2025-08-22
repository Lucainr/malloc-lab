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
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

/* 상수 및 매크로 선언 */ 
#define WSIZE 4           // word와 header/footer 사이즈 (bytes)
#define DSIZE 8           // double word 사이즈 (bytes)
#define CHUNKSIZE (1<<12) // 확장 및 초기 자유(free) 블록 생성

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 블록 크기 정보와 할당 여부를 하나의 word(헤더)에 합쳐서 저장 */ 
#define PACK(size, alloc) ((size) | (alloc))            // 크기와 할당 비트를 통합해서 header와 footer에 저장할 수 있는 값을 return

/* 주소 p에 대한 워드 읽기 및 쓰기 */
#define GET(p)          (*(unsigned int *)(p))          // 인자 p가 참조하는 워드를 읽어서 return
#define PUT(p, val)     (*(unsigned int *)(p) = (val))  // p가 가리키는 워드에 val을 저장

// 주소 p에 저장된 헤더(word)에서, 블록의 크기(size)와 할당 여부(allocated)/비트를 return
#define GET_SIZE(p)  (GET(p) & ~0x7) // 각각 주소 p에 있는 header 또는 footer의 size와 할당 비트를 return
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 블록 포인터 bp(= payload 시작 주소)가 주어졌을 때, 그 블록의 header와 footer를 가리키는 포인터를 return */
#define HDRP(bp)     ((char *)(bp) - WSIZE)
#define FTRP(bp)     ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)  

/* 다음과 이전 블록의 블록 포인터를 각각 return */
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* heap의 시작 지점을 추적하는 포인터 (전역변수) */
static void *heap_listp;

static void place(void *bp, size_t asize) {
    // **최소 블록 크기는 16byte

    size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

// 묵시적 가용 리스트에서 first fit 검색
static void *find_fit(size_t asize) {
    
    // first fit 찾기
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL; // no fit
}

/*
 * 경계 태그 사용
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc) {
        return bp;
    }
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * 1) 힙이 초기화 될때
 * 2) mm_malloc이 적당한 맞춤 fit을 찾지 못했을 떄
 * 
 * 정렬을 유지하기 위해서 요청한 크기를 인접 2워드의 배수(8바이트)로 반올림하며
 * 그 후에 메모리 시스템으로부터 추가적인 힙 공간을 요청
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 정렬(alignment)을 유지하기 위해 짝수 개의 워드를 할당하라
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) {    // mem_sbrk()의 모든 호출은 Epilogue 블록의 header에 곧 이어서 더블워드 정렬된 메모리를 return
        return NULL;
    }

    // 빈 블록의 header와 footer를 초기화하고, 에필로그 헤더(epilogue header)도 설정
    PUT(HDRP(bp), PACK(size, 0));   // 이 header는 새 가용 블록의 header가 됨
    PUT(FTRP(bp), PACK(size, 0));   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 이 블록의 마지막 워드는 새 에필로그 블록의 header가 됨
    
    // 앞쪽(이전) 블록이 free 상태라면 현재 블록과 합쳐라(coalesce)
    return coalesce(bp); // 이전 heap이 가용 블럭으로 끝났다면, 두개의 가용 블럭을 통합하기 위해 coalesce 함수를 호출한다. 그리고 통합된 블록의 블록 포인터를 return
}

/*
 * mm_init - initialize the malloc package.
 * 최초 가용 블록으로 힙 생성하기
 */
int mm_init(void)
{
    // 힙 관리기를 시작할 때, 아무 블록도 없는 상태에서 기본 구조(프롤로그/에필로그)를 세팅하여 메모리 할당 준비를 끝내는 것.
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) {
        return 1;
    }

    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));  // 프롤로그 header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));  // 프롤로그 footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));      // 에필로그 header
    heap_listp += (2*WSIZE);

    // 빈 힙(heap)을 CHUNKSIZE 바이트만큼 확장해서 새로운 “free block”을 만든다
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;       // 조정된 블록 크기
    size_t extendsize;  // 적당한 블록이 없을 때 힙 확장 크기
    char *bp;

    // 불필요한 요청은 무시 
    if (size == 0){
        return NULL;
    }

    // 블록 크기를 조정해서 오버헤드와 정렬 요구사항까지 포함시키는 부분
    if (size <= DSIZE){
        asize = 2*DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    // 가용 리스트에서 요청한 크기를 담을 수 있는 적절한 블록을 찾는다.
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    // 할당기가 맞는 블록을 찾지 못했을때
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr) // ptr == bp
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
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - GET_SIZE(newptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}