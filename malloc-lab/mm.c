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

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 블록 크기 정보와 할당 여부를 하나의 word(헤더)에 합쳐서 저장 */ 
#define PACK(size, alloc) ((size) | (alloc))            // 크기와 할당 비트를 통합해서 header와 footer에 저장할 수 있는 값을 return

/* 주소 p에 대한 워드 읽기 및 쓰기 */
#define GET(p)          (*(unsigned int *)(p))          // 인자 p가 참조하는 워드를 읽어서 return
#define PUT(p, val)     (*(unsigned int *)(p) = (unsigned int)(val))  // p가 가리키는 워드에 val을 저장

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
#define GET_SUCC(bp) (*(void **)((char *)(bp) + DSIZE)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)(bp))                   // 이전 가용 블록의 주소

// 가용 리스트의 맨 앞 블록의 bp
static char *free_listp;

// 마지막으로 검색한 위치를 저장하는 전역 변수
static void *last_searched = NULL;

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
  // 16 bytes만 할당: prologue(8) + epilogue(4) + padding(4)
    if ((free_listp = mem_sbrk(4*WSIZE)) == (void *)-1) {
        return -1;
    }

    PUT(free_listp, 0);                          // 패딩 (Alignment) padding
    PUT(free_listp + (1*WSIZE), PACK(DSIZE, 1)); // 프롤로그(Prologue) header
    PUT(free_listp + (2*WSIZE), PACK(DSIZE, 1)); // 프롤로그(Prologue) footer
    PUT(free_listp + (3*WSIZE), PACK(0, 1));     // 에필로그(Epilogue) header

    free_listp = NULL; // 초기에는 가용 블록이 없음

    // 첫 번째 가용 블록을 생성
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
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
    if (size <= DSIZE){ // 8byte 이하라면
        asize = 2*DSIZE;    // 최소 16바이트 (header 4 + footer 4 + payload 8)
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); // 8의 배수로 올림 처리
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

// NOTE: copySize 계산은 보수 필요(GET_SIZE(HDRP(oldptr)) 기반)하지만
// 현 이슈(세그폴트)와 직접 관련 없으므로 여기서는 수정하지 않음.
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

// 묵시적 가용 리스트에서 first fit 검색
static void *find_fit(size_t asize) {
    
    // first fit
    // void *bp = free_listp;
    // while (bp != NULL) {
    //     if (GET_SIZE(HDRP(bp)) >= asize) {
    //         return bp;
    //     }
    //     bp = GET_SUCC(bp);
    // }
    // return NULL;

    // next fit
    void *bp;
    void *start_bp = (last_searched != NULL) ? last_searched : free_listp;
    
    // start_bp부터 검색 시작
    bp = start_bp;
    do {
        if (bp != NULL && GET_SIZE(HDRP(bp)) >= asize) {
            last_searched = GET_SUCC(bp);  // 다음 검색을 위해 다음 위치 저장
            return bp;
        }
        
        if (bp != NULL) {
            bp = GET_SUCC(bp);
        }
        
        // 리스트 끝에 도달하면 처음부터 다시 시작
        if (bp == NULL) {
            bp = free_listp;
        }
        
    } while (bp != start_bp);  // 한 바퀴 돌면 종료
    
    return NULL;  // 적합한 블록을 찾지 못함

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

static void place(void *bp, size_t asize) {

    // 선택된 가용 블록을 가용 리스트에서 제거
    splice_free_block(bp);

    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        // 앞 부분을 할당하고, 나머지를 새 가용 블록으로 남김
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        void* next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK((csize - asize), 0));
        PUT(FTRP(next_bp), PACK((csize - asize), 0));
        add_free_block(next_bp); // 남은 블록을 free_list에 추가
    } else {
        // 통째로 할당
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 가용 리스트에서 bp에 해당하는 블록을 제거하는 함수 */
static void splice_free_block(void *bp) {
    void *pred = GET_PRED(bp);
    void *succ = GET_SUCC(bp);

    if (pred != NULL) { // 제거할 블록의 이전 블록이 있다면
        GET_SUCC(pred) = succ;
    } else { // 이전 블록이 없다면 (제거할 블록이 리스트의 맨 앞)
        free_listp = succ;
    }

    if (succ != NULL) { // 제거할 블록의 다음 블록이 있다면
        GET_PRED(succ) = pred;
    }
}


/* 가용 리스트의 맨 앞에 현재 블록을 추가하는 함수 (LIFO) */
static void add_free_block(void *bp) {
    GET_PRED(bp) = NULL;               // 새 루트의 PRED는 NULL
    GET_SUCC(bp) = free_listp;     // bp의 SUCC은 루트가 가리키던 블록
    if (free_listp != NULL)        // free list에 블록이 존재했을 경우만
        GET_PRED(free_listp) = bp; // 루트였던 블록의 PRED를 추가된 블록으로 연결
    free_listp = bp;               // 루트를 현재 블록으로 변경
}
