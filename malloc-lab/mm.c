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
#include <stdint.h>  // SIZE_MAX 사용으로 추가

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Team 11",
    /* First member's full name */
    "Kim Hyung Wook",
    /* First member's email address */
    "ainrluca@gmail.com",
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

/* explicit free list의 최소 블록 크기(바이트)
 * header(4) + footer(4) + pred(8) + succ(8) = 24B = 3*DSIZE
 */
#define MINBLOCK (3*DSIZE)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 블록 크기 정보와 할당 여부를 하나의 word(헤더)에 합쳐서 저장 */ 
#define PACK(size, alloc) ((size) | (alloc))            // 크기와 할당 비트를 통합해서 header와 footer에 저장할 수 있는 값을 return

/* 주소 p에 대한 워드 읽기 및 쓰기 */
#define GET(p)          (*(unsigned int *)(p))          // 인자 p가 참조하는 워드를 읽어서 return
#define PUT(p, val)     (*(unsigned int *)(p) = (val))  // p가 가리키는 워드에 val을 저장

/* 포인터 크기(8바이트)에 맞게 저장할 때 사용 */
#define PUT_PTR(p, val) (*(void **)(p) = (void *)(val))

// 주소 p에 저장된 헤더(word)에서, 블록의 크기(size)와 할당 여부(allocated)/비트를 return
#define GET_SIZE(p)  (GET(p) & ~0x7) // 각각 주소 p에 있는 header 또는 footer의 size와 할당 비트를 return
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 블록 포인터 bp(= payload 시작 주소)가 주어졌을 때, 그 블록의 header와 footer를 가리키는 포인터를 return */
#define HDRP(bp)     ((char *)(bp) - WSIZE)
#define FTRP(bp)     ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)  

/* 다음과 이전 블록의 블록 포인터를 각각 return */
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* explicit free list */
#define PRED_FREEP(bp) (*(void **)(bp))                          // PRED는 payload 시작(8바이트)
#define SUCC_FREEP(bp) (*(void **)((char *)(bp) + DSIZE))        // SUCC는 payload에서 8바이트 뒤(총 16바이트 사용)

static char *heap_listp;

// 가용 리스트의 맨 앞 블록의 bp
static char *free_listp;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static void splice_free_block(void *bp); // 가용 리스트에서 제거
static void add_free_block(void *bp);    // 가용 리스트에 추가

/*
 * mm_init - initialize the malloc package.
 * 최초 가용 블록으로 힙 생성하기
 */
int mm_init(void)
{
    // 초기 힙 생성
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) // 4워드 크기의 최소 힙 생성
        return -1;
    PUT(heap_listp, 0);                             // 정렬 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  // 프롤로그 Header(8바이트, 할당)
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  // 프롤로그 Footer(8바이트, 할당)
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));      // 에필로그 Header(0바이트, 할당 플래그)
    free_listp = NULL;                              // 아직 가용 블록 없음 (첫 extend_heap에서 생성)

    // 힙을 CHUNKSIZE bytes로 확장
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
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

    // 블록 크기 조정: payload + (header+footer=8바이트)를 8의 배수로 정렬
    asize = ALIGN(size + 2*WSIZE);
    // pred/succ(각 8바이트)를 담기 위해 최소 24바이트(MINBLOCK) 보장
    if (asize < MINBLOCK) asize = MINBLOCK;

    // 가용 리스트에서 요청한 크기를 담을 수 있는 적절한 블록을 찾는다.
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);   // 할당
        return bp;          // 새로 할당된 블록의 포인터 리턴
    }

    // 할당기가 맞는 블록을 찾지 못했을때 힙 확장
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
void mm_free(void *bp)
{   
    // 해당 블록의 size를 알아내 header와 footer의 정보를 수정한다.
    size_t size = GET_SIZE(HDRP(bp));

    // header와 footer를 설정
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 만약 앞뒤의 블록이 가용 상태라면 연결한다.
    coalesce(bp);
}

// NOTE: copySize 계산은 보수 필요(GET_SIZE(HDRP(oldptr)) 기반)하지만
// 현 이슈(세그폴트)와 직접 관련 없으므로 여기서는 수정하지 않음.
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;  // 크기를 조절하고 싶은 힙의 시작 포인터
    void *newptr;        // 크기 조절 뒤의 새 힙의 시작 포인터
    size_t copySize;     // 복사할 힙의 크기
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;

    // payload만 복사(헤더/푸터 제외)
    copySize = GET_SIZE(HDRP(oldptr)) - 2*WSIZE;

    // 원래 메모리 크기보다 적은 크기를 realloc하면 크기에 맞는 메모리만 할당되고 나머지는 안 된다. 
    if (size < copySize)
      copySize = size;

    memcpy(newptr, oldptr, copySize);  // newptr에 oldptr를 시작으로 copySize만큼의 메모리 값을 복사한다.
    mm_free(oldptr);  // 기존의 힙을 반환한다.
    return newptr;
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
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;    // 2워드의 가장 가까운 배수로 반올림 (홀수면 1 더해서 곱함)
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
 * 경계 태그 사용 / LIFO(Last in First out)
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 할당 상태
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 할당 상태
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 블록 사이즈

    if (prev_alloc && next_alloc) // 모두 할당된 경우
    {
        add_free_block(bp); // free_list에 추가
        return bp;          // 블록의 포인터 반환
    }
    else if (prev_alloc && !next_alloc) // 다음 블록만 빈 경우
    {
        splice_free_block(NEXT_BLKP(bp)); // 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0)); // 다음 블록 푸터 재설정 (위에서 헤더를 재설정했으므로, FTRP(bp)는 합쳐질 다음 블록의 푸터가 됨)
    }
    else if (!prev_alloc && next_alloc) // 이전 블록만 빈 경우
    {
        splice_free_block(PREV_BLKP(bp)); // 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0));            // 현재 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    else // 이전 블록과 다음 블록 모두 빈 경우
    {
        splice_free_block(PREV_BLKP(bp)); // 이전 가용 블록을 free_list에서 제거
        splice_free_block(NEXT_BLKP(bp)); // 다음 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    add_free_block(bp); // 현재 병합한 가용 블록을 free_list에 추가
    return bp;          // 병합한 가용 블록의 포인터 반환
}

static void *find_fit(size_t asize) {
    // explicit free list에서 "베스트 핏"으로 탐색
    /*
    * free_listp부터 SUCC를 따라가며 asize 이상 담을 수 있는 블록 중
    * 가장 작은 블록을 선택. 완벽 일치(asize == bsize)면 즉시 반환.
    */
   void *bp = free_listp;
    void *best = NULL;
    size_t best_size = (size_t)-1;

    while (bp != NULL) {
        size_t bsize = GET_SIZE(HDRP(bp));
        if (bsize >= asize) {
            if (bsize == asize) return bp; // 완벽 일치
            if (bsize < best_size) { best_size = bsize; best = bp; }
        }
        bp = SUCC_FREEP(bp);
    }
    return best; // 없으면 NULL
}

static void place(void *bp, size_t asize) {

    size_t csize = GET_SIZE(HDRP(bp));  // 현재 블록의 크기

    // 선택된 가용 블록을 가용 리스트에서 제거
    splice_free_block(bp);  // free_listp에서 해당 블록을 제거

    // 남는 조각도 pred/succ(총 16B)를 담을 수 있어야 하므로 MINBLOCK(24B) 이상일 때만 분할
    if ((csize - asize) >= MINBLOCK) {
        // 앞 부분을 할당하고, 나머지를 새 가용 블록으로 남김
        PUT(HDRP(bp), PACK(asize, 1));  // 현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));

        void* next_bp = NEXT_BLKP(bp);  
        PUT(HDRP(next_bp), PACK((csize - asize), 0));   // 남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(next_bp), PACK((csize - asize), 0));
        add_free_block(next_bp); // 남은 블록을 free_list에 추가
    } else {
        // 통째로 할당
        PUT(HDRP(bp), PACK(csize, 1));  // 해당 블록 전부 사용
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 가용 리스트에서 bp에 해당하는 블록을 제거하는 함수 */
static void splice_free_block(void *bp) {
    /* 가용 리스트에서 bp를 안전하게 제거 */
    void *pred = PRED_FREEP(bp);
    void *succ = SUCC_FREEP(bp);

    if (pred != NULL) SUCC_FREEP(pred) = succ;
    else              free_listp = succ;   // bp가 루트였던 경우

    if (succ != NULL) PRED_FREEP(succ) = pred;

    // 제거된 노드의 링크 초기화(디버깅/안전성)
    PRED_FREEP(bp) = NULL;
    SUCC_FREEP(bp) = NULL;
}

/* 가용 리스트의 맨 앞에 현재 블록을 추가하는 함수 (LIFO) */
static void add_free_block(void *bp) {
    /* LIFO로 free_list 맨 앞에 삽입 */
    PRED_FREEP(bp) = NULL;
    SUCC_FREEP(bp) = free_listp;
    if (free_listp != NULL) PRED_FREEP(free_listp) = bp;
    free_listp = bp;
}
