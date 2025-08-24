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
    "team 11",
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
#define CHUNKSIZE (1<<12) // 확장 및 초기 기본 크기 (= 초기 빈 블록 크기)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 블록 크기 정보와 할당 여부를 하나의 word(헤더)에 합쳐서 저장 */ 
#define PACK(size, alloc) ((size) | (alloc))            // 크기와 할당 비트를 통합해서 header와 footer에 저장할 값

/* 주소 p에 대한 워드 읽기 및 쓰기 */
#define GET(p)          (*(unsigned int *)(p))          // 인자 p가 참조하는 워드를 읽어서 return (포인터라서 직접 역참조가 블가능 -> 타입 캐스팅)
#define PUT(p, val)     (*(unsigned int *)(p) = (val))  // p가 가리키는 워드에 val을 저장

// 주소 p에 저장된 헤더(word)에서, 블록의 크기(size)와 할당 여부(allocated)/비트를 return
#define GET_SIZE(p)  (GET(p) & ~0x7) // 각각 주소 p에 있는 header 또는 footer의 size와 할당 비트를 return
#define GET_ALLOC(p) (GET(p) & 0x1) // 할당 상태(allocated)

/* 블록 포인터 bp(= payload 시작 주소)가 주어졌을 때, 그 블록의 header와 footer를 가리키는 포인터를 return */
#define HDRP(bp)     ((char *)(bp) - WSIZE) // header 포인터
#define FTRP(bp)     ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // footer 포인터 (🚨header의 정보를 참조해서 가져오기 때문에, Header의 정보를 변경했다면 변경된 위치의 footer가 반환됨에 주의)

/* 다음과 이전 블록의 블록 포인터를 각각 return */
// 다음 블록의 포인터
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// 이전 블록의 포인터
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* heap의 시작 지점을 추적하는 포인터 (전역변수) */
static void *free_listp;

static void *last_searched = NULL;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static void place(void *bp, size_t asize) {
    // **최소 블록 크기는 16byte

    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if((csize - asize) >= (2*DSIZE)) {  // 차이가 최소 블록 크기 16보다 같거나 크면 분할
        PUT(HDRP(bp), PACK(asize, 1));  // 현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0)); // 남은 크기를 다음 블록에 할당 (가용 블록)
        PUT(FTRP(bp), PACK(csize-asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));  // 해당 블록 전부 사용
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
// 묵시적 가용 리스트에서 first fit 검색
static void *find_fit(size_t asize) {
    
    // first fit
    // for (void *bp = free_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    //     if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= asize)) {
    //         return bp;
    //     }
    // }
    // return NULL;

    // next fit
    // 힙 블록들을 NEXT_BLKP로 순회하는 next-fit
    void *bp;

    if (last_searched == NULL) {
        last_searched = free_listp; // 시작 위치 설정(프로로그 다음)
    }

    // 1) last_searched부터 에필로그(크기 0) 직전까지 스캔
    for (bp = last_searched; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= asize)) {
            last_searched = NEXT_BLKP(bp); // 다음 탐색 시작점 갱신
            return bp;
        }
    }

    // 2) 랩어라운드: 힙 시작(free_listp)부터 last_searched 직전까지 스캔
    for (bp = free_listp; bp < last_searched; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= asize)) {
            last_searched = NEXT_BLKP(bp);
            return bp;
        }
    }

    return NULL; // 적합 블록 없음

    // best fit
    // void *bp = free_listp;
    // void *best_fit = NULL;
    // size_t best_size = SIZE_MAX;
    
    // while (bp != NULL) {
    //     size_t block_size = GET_SIZE(HDRP(bp));
        
    //     if (block_size >= asize) {
    //         if (block_size == asize) {
    //             // 정확한 크기 - 즉시 반환
    //             return bp;
    //         }
            
    //         if (block_size < best_size) {
    //             best_fit = bp;
    //             best_size = block_size;
    //         }
    //     }
    //     bp = GET_SUCC(bp);
    // }
    // return best_fit;
}

/*
 * 경계 태그 사용
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 할당 상태
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 할당 상태
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 블록 사이즈

    if(prev_alloc && next_alloc) {  // 모두 할당된 경우
        return bp;
    }
    else if (prev_alloc && !next_alloc) {   // 다음 블록만 빈 경우
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));   // 현재 블록 header 재설정
        // 위에서 header를 재 설정했으므로, FTRP(bp)는 합쳐질 다음 블록의 footer가 됨
        PUT(FTRP(bp), PACK(size, 0));   // 다음 블록 footer 재설정
    }
    else if (!prev_alloc && next_alloc) {   // 이전 블록만 빈 경우
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));   // 이전 블록 header 재설정
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    // 현재 블록 footer 재설정
        bp = PREV_BLKP(bp); // 이전 블록의 시작점으로 포인터 변경
    }
    else {  // 이전 블록과 다음 블록 모두 빈 경우
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    // 이전 블록 header 재설정
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));    // 다음 블록 footer 재설정
        bp = PREV_BLKP(bp); // 이전 블록의 시작점으로 포인터 변경
    }
    return bp;  // 병합된 블록의 포인터 반환
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
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 2워드의 가장 가까운 배수로 반올림 (홀수면 1 더해서 곱함)

    // mem_sbrk()의 모든 호출은 Epilogue 블록의 header에 곧 이어서 더블워드 정렬된 메모리를 return
    if ((long)(bp = mem_sbrk(size)) == -1) {    // 힙 확장
        return NULL;
    }

    // 빈 블록의 header와 footer를 초기화하고, 에필로그 헤더(epilogue header)도 설정
    PUT(HDRP(bp), PACK(size, 0));   // 이 header는 새 가용 블록의 header가 됨(새 빈 블록 header 초기화)
    PUT(FTRP(bp), PACK(size, 0));   // 마찬가지로 새 빈 블록 footer 초기화
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 이 블록의 마지막 워드는 새 에필로그 블록의 header가 됨
    
    // 앞쪽(이전) 블록이 free 상태라면 현재 블록과 합쳐라(coalesce)
    return coalesce(bp); // 이전 heap이 가용 블럭으로 끝났다면, 두개의 가용 블럭을 통합(병합)하기 위해 coalesce 함수를 호출한다. 그리고 통합된 블록의 블록 포인터를 return
}

/*
 * mm_init - initialize the malloc package.
 * 최초 가용 블록으로 힙 생성하기
 */
int mm_init(void)
{
    // 힙 관리기를 시작할 때, 아무 블록도 없는 상태에서 기본 구조(프롤로그/에필로그)를 세팅하여 메모리 할당 준비를 끝내는 것.
    // 초기 힙 생성
    if ((free_listp = mem_sbrk(4*WSIZE)) == (void *)-1) { // 4워드 크기의 힙 생성
        return 1;
    }

    PUT(free_listp, 0);                           // 정렬 패딩
    PUT(free_listp + (1*WSIZE), PACK(DSIZE, 1));  // 프롤로그 header
    PUT(free_listp + (2*WSIZE), PACK(DSIZE, 1));  // 프롤로그 footer
    PUT(free_listp + (3*WSIZE), PACK(0, 1));      // 에필로그 header
    free_listp += (2*WSIZE);
    last_searched = free_listp; // next fit 시작 지점 설정

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
    size_t extendsize;  // 적당한 블록이 없을 때 확장할 힙 크기
    char *bp;

    // 잘못된 요청 분기
    if (size == 0){
        return NULL;
    }

    // 블록 크기를 조정해서 오버헤드와 정렬 요구사항까지 포함시키는 부분
    if (size <= DSIZE){     // 8바이트 이하이면
        asize = 2*DSIZE;    // 최소 블록 크기 16바이트 할당 (header 4, footer 4, 저장공간 8)
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); // 8의 배수로 반 올림 처리
    }

    // 가용 리스트에서 요청한 크기를 담을 수 있는 적절한 블록을 찾는다.
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);   // 할당
        return bp;          // 새로 할당된 블록의 포인터 리턴
    }

    // 할당기가 맞는 블록을 찾지 못했을때 힙을 확장
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
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    bp = coalesce(bp);
    last_searched = bp; // 해제 지점부터 다시 탐색하도록 설정
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{   
    /* 예외 처리 */
    if (ptr == NULL) // 포인터가 NULL인 경우 할당만 수행
        return mm_malloc(size);

    if (size <= 0) // size가 0인 경우 메모리 반환만 수행
    {
        mm_free(ptr);
        return 0;
    }

    /* 새 블록에 할당 */
    void *newptr = mm_malloc(size); // 새로 할당한 블록의 포인터
    if (newptr == NULL)
        return NULL; // 할당 실패

    /* 데이터 복사 */
    size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE; // payload만큼 복사
    if (size < copySize)                           // 기존 사이즈가 새 크기보다 더 크면
        copySize = size;                           // size로 크기 변경 (기존 메모리 블록보다 작은 크기에 할당하면, 일부 데이터만 복사)

    memcpy(newptr, ptr, copySize); // 새 블록으로 데이터 복사

    /* 기존 블록 반환 */
    mm_free(ptr);

    return newptr;
}