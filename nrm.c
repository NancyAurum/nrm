/////////////////////////////////// NRM ////////////////////////////////////////
///////////////////////////// NEW ARM ASSEMBLER ////////////////////////////////
////////////////////////// NANCY'S ARM ASSEMBLER ///////////////////////////////


/*

Public Domain (CC0) ARM Assembler.
Free as in actual freedom.
License: https://creativecommons.org/publicdomain/zero/1.0/

GOALS:
- ObjAsm compatibility
- Portability (across 32-bit CPUs)
- Simplicity
- Speed (for JIT use)




TODO:
- conditional [|] IF/THEN/ELSE/ENDIF
- WHILE/WEND
- macros (start with swinames)
- expressions
- ROUT and local labels, which are useful for macros
- handle |labels| and |variables|
- Consult ObjAsm if S bit should be generated with CMP, CMN, TST and TEQ
  also check what CMPS generates with ObjAsm
- STM/LDM can't have PC as a base or have empty {}
- STM/LDM after Arch >= 7 doesn't allow writeback into the register that appear in {}
- replace `strtol` with proper readers


NOTES:
- With 2-pass assembler there are two approaches:
  - 1st pass generates the code, while also storing label positions.
    2nd pass patches it.
  - 1st pass goes over the code, calculating label positions.
    2nd pass generates actual code.

- APCS versions:
  https://ext.3dodev.com/3DO/Portfolio_2.5/OnLineDoc/DevDocs/tktfldr/atsfldr/4atsb.html#XREF35590



CHEAT SHEET:

<Operation>{<cond>}{S} Rd, Rm, Rn

Data processing instruction format:
BitOffset/NBits: Name - Description
28/ 4: F  - if condition: see CND_* macros
25/ 3: C  - class: 0 = Rm is register
                   1 = Rm is immeidate
21/ 4: O  - operation code: see NRM_* macros
20/ 1: S  - set flags
16/ 4: Rn - 1st operand register
12/ 4: Rd - destination register
 0/12: Rm - 2nd operand register or immediate
            Register (C=0):
              0/4: Register
              4/1: ShiftSource
              5/2: ShiftType
                0 = LSL logical left
                1 = LSR logical right
                2 = ASR arithmetic right (sign bit handled)
                3 = ROR rotate right
              7/5: shift value
                Immediate (ShiftSource=0)
                  7/5 = immediate (0 to 31, i.e. 7 for LSL#7)
                Register (ShiftSource=1)
                  7/1 = should be 0 (1 switches to different instruction set)
                  8/4 = register
            Immediate (C=1):
              0/8: value
              8/4: rotate right amount
                   note: it is multiplied by 2
                   before use

RRX is a shorthand for `Operation RegA, RegB, ROR #0`

In 24-bit mode postfixing CMP/CMN/TST/TEQ with P sets Rd to 0xF = PSR
R15, beside PC, used to hold PSR, which later became CPSR.


LDR/STR with immediate offset:
  Pre-indexed instruction (possibly with write back)
    opcode{cond}{B} register,[base{index}]{!}
  Post-indexed instruction
    opcode{cond}{B}{T} register,[base]{,index}
  {T} if present the TRANS pin will be active.
      Used in supervisor mode to with user mode page translation.
      I.e. when doing unchecked and untranslated writes
      to a user supplied address.
      Note that T is invalid for preindexed addressing

28/ 4: F  - if {cond}: see CND_.* macros
25/ 3: C  - class: 2 = Rm is immediate
                   3 = Rm is register
24/ 1: P  - pre/post increment: 0 = post: add offset after transfer
                                1 = pre: add offset before transfer
23/ 1: U  - up/down: 0 = down: subtract offset from base
                     1 = up: add offset to base
22/ 1: B  - BYTE/WORD bit
21/ 1: W  - Write-back {!}:write new address into base register
            W=1 && P=0: LDRT/STRT operation (forced usermode MMU translation)
            W=1 && P=1: writeback without forced MMU translation
            P=0 && W=0: writeback without forced MMU translation
            P=1 && W=0: no writeback, no forced MMU translation
            load/store register with MMU translation
20/ 1: D  - direction: 0=STR, 1=LDR
16/ 4: Rn - base register
12/ 4: Rd - src/dst register
0 /12: Rm - offset
       Register (C=2), same format as with data processing opcodes
        0/4: Register
        4/1: ShiftSource
        5/2: ShiftType
          0 = LSL logical left
          1 = LSR logical right
          2 = ASR arithmetic right (sign bit handled)
          3 = ROR rotate right
        7/5: shift value
          Immediate (ShiftSource=0)
            7/5 = immediate (0 to 31, i.e. 7 for LSL#7)
          Register (ShiftSource=1)
            7/1 = should be 0 (1 turns it into an undefined opcode)
            8/4 = register
       Immediate (C=3)
         0/12: 12-bit immediate offset applied to base

Undefine opcode space (intended for VM or coprocessor use):
28/ 4: F  - if {cond}: see CND_.* macros
25/ 3: C  - class: 3
7 / 1: U  - signifies undefined opcode. All other bits are free to use

LDM/STM instruction format:
opcode{cond}type base{!}, {list}{^}
For example, STMNEDB
28/ 4: F  - if {cond}: see CND_.* macros
25/ 3: C  - class: always 4
24/ 1: P  - pre/post increment: 0 = post: add offset after transfer
                                1 = pre: add offset before transfer
23/ 1: U  - up/down: 0 = subtract offset from base
                     1 = add offset to base
22/ 1: S  - {^} = load PSR or force user mode
21/ 1: W  - Write-back {!}: write new address into base register
20/ 1: D  - direction: 0=STM, 1=LDM
16/ 4: Rn - base register
 0/15: Rs - registers to load store (i.e. the {list}).


B/BL branch instruction format:
28/ 4: F  - if condition: see CND_.* macros
25/ 3: C  - class: always 5
24/ 1: L  - Link: 0 = B, 1 = BL
 0/24: Im - Immediate Offset


Coprocessor/SWI instruction format:
28/ 4: F  - if condition: see CND_.* macros
25/ 3: C  - class: always 7
24/ 1: S  - 0=coprocessro, 1=SWI
0 /24: Op - Operation
       Immediate SWI number (S=1)
       Coprocessor operation (S=0)





*/

//////////////////////////// NRM CONFIGURATION /////////////////////////////////

#define NRM_STANDALONE


//////////////////////////// STANDARD INCLUDES /////////////////////////////////

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdarg.h>


/////////////////////////// OBSCURE INCLUDES ///////////////////////////////////

#define STB_DS_IMPLEMENTATION
#include "stb_ds.h"

//NOTE: SH tables by default expect user to do strdup

#define arrdup(xs) ((xs) ? \
     (void*)((uint8_t*)memcpy(malloc(sizeof(*stbds_header(xs)) \
                   + stbds_header(xs)->capacity*sizeof(xs[0])) \
           , stbds_header(xs) \
           ,(sizeof(*stbds_header(xs)) \
              + stbds_header(xs)->capacity*sizeof(xs[0])) \
           )+sizeof(*stbds_header(xs))) \
    : 0)


#define alen(a)   arrlen(a)
#define aput(a,v) arrput(a,v)
#define apop(a)   arrpop(a)
#define alast(a)  arrlast(a)
#define adup(a)   arrdup(a)



////////////////////////// GENERIC DECLARATION /////////////////////////////////

#define U8  uint8_t
#define U16 uint16_t
#define U32 uint32_t
#define S8  int8_t
#define S16 int16_t
#define S32 int
#define F32 float
#define F64 double
#define U64 uint64_t
#define S64 int64_t

#define PUTW(p,w) do {      \
  (p)[0] =  (w)     &0xFF;  \
  (p)[1] = ((w)>> 8)&0xFF;  \
  (p)[2] = ((w)>>16)&0xFF;  \
  (p)[3] =  (w)>>24;        \
  } while (0)


struct nrm_t;
typedef struct nrm_t nrm_t;


#define TCTX nrm_t
#define CTX TCTX *this
#define C (*this)
#define FLM (&this->flm)



/////////////////////////////// UTILITIES //////////////////////////////////////


//file end
#define ISFLE(x) ((x) == FLE)

#define ISWS(x) ((x) == ' ' || (x) == '\t')

#define SKPWS(p) while (ISWS(nx)) rd()
  
//locally defined terminating characater
#define ISTC(x) ((x) == tc)


static void upcase(char *d, char *s) {
  while ((*d++ = toupper(*s++)));
}


static char *_hidden_cat_(char *a0, ...) {
  char *a;
  va_list ap;
  int size = strlen(a0);
  va_start(ap, a0);
  for (;;) {
    a = va_arg(ap, char*);
    if (!a) break;
    size += strlen(a);
  }
  va_end(ap);
  size += 1;

  char *o = malloc(size);

  char *p = o;

  a = a0;
  while (*a) *p++ = *a++;

  va_start(ap, a0);
  for (;;) {
    a = va_arg(ap, char*);
    if (!a) break;
    while (*a) *p++ = *a++;
  }
  va_end(ap);

  *p++ = 0;

  return o;
}

#define cat(...) _hidden_cat_(__VA_ARGS__, 0)




////////////////////////// MEMORY MANAGEMENT ///////////////////////////////////


//local heap, allows evading malloc where possible
#define LHP(TSZ) char h_[TSZ]; char *hp_=h_, *he_ = h_+TSZ-1

//read characters by calling rd(), while tst(nx) is true
//assumes hp points to a temporary heap buffer and he points to its end
#define RDS(dst,tst) do {                              \
    dst = hp_;                                         \
    while (tst(nx)) {                                  \
      if (hp_ == he_) fatal("line is too long.");      \
      *hp_++ = rd();                                   \
    }                                                  \
    *hp_++ = 0;                                        \
  } while (0)






////////////////////////////////// URL /////////////////////////////////////////



typedef struct {
  char *dir;
  char *name;
  char *ext;
} url_t;

static url_t *url_parts(char *path) {
  int bufsz = strlen(path)+3;
  url_t *fn = malloc(sizeof(url_t)+bufsz);
  char *r = (char*)(fn+1);
  char *dir;
  char *name;
  char *ext;
  char *p, *q;
  int l;

  if ((p = strrchr(path, '/'))) {
    l = p-path + 1;
    dir = r;
    strncpy(dir, path, l);
    dir[l] = 0;
    p++;
    r += l+1;
  } else {
    p = path;
    dir = r;
    *r++ = 0;
  }
  if ((q = strrchr(p, '.'))) {
    l = q-p;
    name = r;
    strncpy(name, p, l);
    name[l] = 0;
    q++;
    r += l+1;

    ext = r;
    l = strlen(q);
    strcpy(ext, q);
  } else {
    ext = r;
    *r++ = 0;
    name = r;
    strcpy(name, p);
  }

  fn->dir = dir;
  fn->name = name;
  fn->ext = ext;

  return fn;
}


/////////////////////// FILE MANAGER DECLARATIONS //////////////////////////////

/*
RATIONALE:
- Portabily. 
- Flexibility.
- Speed.
- Parser housekeeping (row/column, names, etc..).
*/


//File end
#define FLE -1


/////////////////////////
// mfl_t.desc flags

//file's data array is owned by us and have to be freed
#define MFL_OWNED    0x001

//macro buffer
#define MFL_MACRO    0x002

//has an associated filesystem
#define MFL_FS       0x004

//the file won't be freed when nref hits 0
#define MFL_RETAIN   0x008

//root file
#define MFL_ROOT     0x010


struct flm_t;
typedef struct flm_t flm_t;

struct flp_t;
typedef struct flp_t flp_t;

struct mfl_t;
typedef struct mfl_t mfl_t;


struct mfl_t { //memory held file
  U32 desc;     //file description
  U8 *base;     //start of the data
  U32 size;     //length of the file
  char *name;   //name of the file
  url_t *url;   //path to the source
  int nrefs;    //number of references to this file
                //if it gets 0, we we can free it.
  mfl_t *ovrd;  //this entry overrides another in the file table
  flm_t *flm;   //associated file manager
};

struct flp_t { //file pointer
  U8 *ptr;        //current location inside the file
  U8 *end;        //end of the file
  U8 *line;       //start of the current line (used to calculate column)
  U32 row;        //line counter
  mfl_t *fl;      //the file handle
  //flp_t *prev;    //OBSOLETE: for reading files which include other files
                    //use nrm_t->fstack  instead,
                    //since one file can be opened several times
  U8 *shd;        // shadow copy
};


static mfl_t *new_mfl(char *name, U8 *base, U32 size) {
  mfl_t *f = malloc(sizeof(mfl_t));
  f->name = strdup(name);
  f->base = base;
  f->size = size;
  f->nrefs = 0;
  f->desc = 0;
  f->url = 0;
  f->ovrd = 0;
  return f;
}

static void del_mfl(mfl_t *f) {
  if (f->url) free(f->url);
  free(f->name);
  if (f->desc&MFL_OWNED) arrfree(f->base);
  free(f);
}

static flp_t *new_flp(mfl_t *f) {
  flp_t *fp = malloc(sizeof(flp_t));
  fp->fl = f;
  fp->ptr = f->base;
  fp->end = f->base + f->size;
  fp->line = fp->ptr;
  fp->row = 0;
  fp->shd = 0;
  return fp;
}

static void del_flp(flp_t *fp) {
  free(fp);
}

static void mfl_ref(mfl_t *f) {f->nrefs++;}
static void mfl_unref(mfl_t *f) {
  if (!(--f->nrefs || (f->desc&MFL_RETAIN))) del_mfl(f);
}


struct flm_t { //file manager
  flp_t flp;       //current file

  TCTX *ctx;

  struct { char *key; mfl_t *value; } *ft;  //file table

  //a stack of currently processed files (beside the flp)
  flp_t **fstack;
  
  flp_t *tflp_stack;

  char **paths; //include directories
};

typedef struct {
  int row;
  int col;
  char *macroname;
  char *filename;
} flmp_t;

static void flm_location(flm_t *this, flmp_t *p);
static void flm_conclude(flm_t *this);

static int nxF(flp_t *f) { return f->ptr==f->end ? FLE : *f->ptr; }

static int rdF(flp_t *f) {
  if (f->ptr == f->end) return FLE;
  U8 ch = *f->ptr++;
  if (f->shd) *f->shd++ = ch; //does a shadow copy
  if (f->ptr == f->end)  flm_conclude(f->fl->flm);
  else {
    if (ch == '\n') { f->row++; f->line = f->ptr; }
  }
  return ch;
}



#define cflp (&FLM->flp)

//next char peek
#define nx nxF(cflp)

//read char
#define rd() rdF(cflp)


//FIXME: the below macros will fail with windowed files

//these are for temporary redefining input
#define cflp_push(tflp) \
  aput(FLM->tflp_stack, *cflp); \
  cflp = *tflp;


#define cflp_pop() cflp = apop(FLM->tflp_stack)

#define cflp_shd(s) do { cflp->shd = s; } while (0)

//FIXME: handle unicode
#define FL_COL(f) ((f)->ptr - (f)->line)

#define cflp_saved() FLM->fstack[alen(FLM->fstack)-1]

#define cflp_save() do {*cflp_saved() = *cflp;} while (0)
#define cflp_load() do {*cflp = *cflp_saved();} while (0)

#define FLLOC(R,C,N,F) int R = (F)->row; int C = FL_COL(F); \
                       char *N = (F)->fl->name;

//////////////////////////// SYMBOL TABLE //////////////////////////////////////


//////////////////
// SYMBOL TYPES

//none
#define SYM_NON  0x00

//mnemonic
#define SYM_MNM  0x01

//macro
#define SYM_MCR  0x02

//register
#define SYM_REG  0x03

//macro constant
#define SYM_EQU  0x04

//macro constant
#define SYM_LBL  0x05

//ObjAsm apparently uses AREA as a synonym for namespace
typedef struct {
  char *name;

} area_t;


typedef union { //note that ARM word is 32bit, compared to x86's 16bit
  int i;
  U8  b; //byte
  U16 h; //half-word
  U32 w;
  U32 d; //dword
  U64 q; //qword
  S8  sb; //byte
  S16 sh; //half-word
  S32 sw;
  S32 sd; //dword
  S64 sq; //qword
  char *s;
} val_t;

typedef struct {
  char *name; //index inside the name table
  U32 desc; //description of the symbol
  val_t v; //value of the symbol
} sym_t;

typedef struct { char *key; sym_t *value; } *sym_tbl_t;


#define SYM_TYPE(s) ((s)->desc&0xff)


////////////////////// CONDITION CODES /////////////////////////////////////////

// Equal / Zero: Z == 1
#define NRM_EQ 0x0 

// Not Equal / Not Zero: Z = 0
#define NRM_NE 0x1

//HS/CS - Carry Set / Unsigned Higher or Same: C == 1
#define NRM_CS 0x2

//LO/CC - Carry Clear / Unsigned Lower: C == 0
#define NRM_CC 0x3

// Minus / Negative: N==1
#define NRM_MI 0x4

// Plus / Positive or Zero: N==0
#define NRM_PL 0x5

// Overflow Set: V==1
#define NRM_VS 0x6

// Overflow Clear: V==0
#define NRM_VC 0x7

// Unsigned Higher: C == 1 && Z == 0
#define NRM_HI 0x8

// Unsigned Lower or Same: C == 0 || Z == 1
#define NRM_LS 0x9

// Greater or Equal: N == V
#define NRM_GE 0xA

// Less Than: N != V
#define NRM_LT 0xB

// Greater Than: Z == 0 && N == V
#define NRM_GT 0xC

// Less or Equal: Z == 1 || N != V
#define NRM_LE 0xD 

// Always (unconditional)
#define NRM_AL 0xE

// Never (unconditionally false)
#define NRM_NV 0xF



//////////////////////////// OPERATION CODES ///////////////////////////////////

/////////////////////
// Legend:
//  Rd - destionation
//  Rn - 1st operand
//  Rm - 2nd operand

//Rd = Rn & Rm
#define NRM_AND (0x0<<21)

//Rd = Rn ^ Rm
#define NRM_EOR (0x1<<21)

//Rd = Rn - Rm
#define NRM_SUB (0x2<<21)

//Rd = Rm - Rn
#define NRM_RSB (0x3<<21)

//Rd = Rn + Rm
#define NRM_ADD (0x4<<21)

//Rd = Rn + Rm + C
#define NRM_ADC (0x5<<21)

//Rd = Rn - Rm - C
#define NRM_SBC (0x6<<21)

//Rd = Rm - Rn - C
#define NRM_RSC (0x7<<21)

//NZCV <- Rn & Rm
//S should be always 1
#define NRM_TST (0x8<<21)

//NZCV <- Rn ^ Rm 
//S should be always 1
#define NRM_TEQ (0x9<<21)

//NZCV <- Rn - Rm
//S should be always 1
#define NRM_CMP (0xA<<21)

//NZCV <- Rn + Rm (compare negated)
//S should be always 1
#define NRM_CMN (0xB<<21)

//Rd = Rn | Rm
#define NRM_ORR (0xC<<21)

//Rd = Rm (Rn is ignored)
#define NRM_MOV (0xD<<21)

//Rd = Rn & ~Rm (bit clear)
#define NRM_BIC (0xE<<21)

//Rd = ~Rm (Rn is ignored)
#define NRM_MVN (0xF<<21)

//store
#define NRM_STR (0x2<<25)

//load
#define NRM_LDR ((0x2<<25)|NRM_STLD_LD)

//store
#define NRM_STM (0x4<<25)

//load
#define NRM_LDM ((0x4<<25)|NRM_STLD_LD)

//branch
#define NRM_B   (0x5<<25)

//branch and link
#define NRM_BL  ((0x5<<25)|(1<<24))

//software interrupt
#define NRM_SWI  ((0x7<<25)|(1<<24))





//for S suffixed opcodes
#define NRM_S (1<<20)

#define NRM_L (1<<24)

//immediate operand
#define NRM_I (1<<25)


//load flag for ST/LD opcode
#define NRM_STLD_LD (1<<20)


//save incremented offset back after ST/LD
#define NRM_WRITEBACK (1<<21)

//preicrement Rn (base register), before STR/LDR
#define NRM_PRE (1<<24)

//increment up
#define NRM_UP (1<<23)

#define NRM_STLD_BYTE (1<<22)

#define NRM_STLD_TRANS (NRM_WRITEBACK|1)

//that is for exiting service mode
#define NRM_LOAD_PSR_FORCE_USER_MODE (1<<22)

#define NRM_NONE  0xFFFFFFFF
#define NRM_ERROR 0xFFFFFFFE
#define NRM_EOF   0xFFFFFFFD


//data processing register
#define NRM_CLS_DPR    0x0

//data processing immediate
#define NRM_CLS_DPI    0x1

//load/store immediate offset
#define NRM_CLS_STLDI  0x2

//load/store register offset
#define NRM_CLS_STLDR  0x3

//load/store multiple
#define NRM_CLS_STLDM  0x4

//branch
#define NRM_CLS_B_BL   0x5

#define NRM_CLS_SWI    0x7

#define NRM_CND(dsc) ((dsc)>>28)
#define NRM_OPC(dsc) ((dsc)&(0xF<<21))

#define NRM_IS_CTDP(x) ((x)==NRM_CMP || (x)==NRM_CMN || \
                        (x)==NRM_TST || (x)==NRM_TEQ)

#define NRM_IS_MOV(x) ((x)==NRM_MOV || (x)==NRM_MVN)

//instruction class
#define NRM_CLS(dsc) (((dsc)>>25)&7)

#define NRM_IS_DP(x) (NRM_CLS(x) == NRM_CLS_DPR || NRM_CLS(x) == NRM_CLS_DPI)

#define NRM_IS_STLD(x) \
  (NRM_CLS(x) == NRM_CLS_STLDI || NRM_CLS(x) == NRM_CLS_STLDR)

#define NRM_IS_BRANCH(x) (NRM_CLS(x) == NRM_CLS_B_BL)

#define NRM_IS_STLDM(x) (NRM_CLS(x) == NRM_CLS_STLDM)





/////////////////////////// BIT MANIPULATION ///////////////////////////////////


static U32 nrm_ror(U32 x, U32 n) { //32bit rotate right
	return (x >> n) | (x << (32 - n));
}

static U32 nrm_rol(U32 x, U32 n) { //32bit rotate left
  return (x << n) | (x >> (32 - n));
}


#define NRM_BAD_IMM 0xFFFFFFFF


U32 nrm_enc_imm(U32 imm) { //encode immediate as a RORed value
  U32 v = imm;
  for (U32 s = 0; s < 31; s += 2) {
    v = nrm_rol(imm, s);
    if (v < 256) {
      //printf("v=%d s=%d\n", v, s);
      return v | (s<<7) | NRM_I;
    }
  }
  return NRM_BAD_IMM;
}

U32 nrm_dec_imm(U32 opcode) {//decode immediate given ARM opcode
	U32 v = opcode & 0xff;
	U32 r = ((opcode >> 8) & 0xf) << 1;
	return nrm_ror(v, r);
}



//////////////////////////// GLOBAL DATA ///////////////////////////////////////

typedef struct {
  char *key;
  int32_t value;
} ki_t; //key to integer value

typedef struct {
  char *key;
  U32 value;
} ku_t; //key to integer value

static ki_t base_regs[] = {
  { "r0", 0},{ "r1", 1},{ "r2", 2},{ "r3", 3},
  { "r4", 4},{ "r5", 5},{ "r6", 6},{ "r7", 7},
  { "r8", 8},{ "r9", 9},{"r10",10},{"r11",11},
  {"r12",12},{"r13",13},{"r14",14},{"r15",15},
  { "R0", 0},{ "R1", 1},{ "R2", 2},{ "R3", 3},
  { "R4", 4},{ "R5", 5},{ "R6", 6},{ "R7", 7},
  { "R8", 8},{ "R9", 9},{"R10",10},{"R11",11},
  {"R12",12},{"R13",13},{"R14",14},{"R15",15},
  { "sp",13},{ "SP",13},{ "lr",14},{ "LR",14},
  { "pc",15},{ "PC",15},
  {0,0}
};

static ki_t apcs_regs[] = { //RISC OS C ABI
  //objasm v3.27 apparently only includes the lower case names
  {"a1", 0}, {"a2", 1}, {"a3", 2}, {"a4", 3},
  {"v1", 4}, {"v2", 5}, {"v3", 6}, {"v4", 7},
  {"v8", 8}, {"v6", 9}, {"sl",10}, {"fp",11},
  {"ip",12}, {"sp",13}, {"lr",14}, {"pc",15},
  {0,0}
};

static ku_t cnds[] = {
  {"EQ", NRM_EQ}, {"NE", NRM_NE}, {"CS", NRM_CS}, {"CC", NRM_CC},
  {"MI", NRM_MI}, {"PL", NRM_PL}, {"VS", NRM_VS}, {"VC", NRM_VC},
  {"HI", NRM_HI}, {"LS", NRM_LS}, {"GE", NRM_GE}, {"LT", NRM_LT},
  {"GT", NRM_GT}, {"LE", NRM_LE}, {"AL", NRM_AL}, {"NV", NRM_NV},
  {"HS", NRM_CS}, {"LO", NRM_CC},
  {0,0}
};


static ku_t opcs[] = {
  {"AND", NRM_AND}, {"EOR", NRM_EOR}, {"SUB", NRM_SUB}, {"RSB", NRM_RSB},
  {"ADD", NRM_ADD}, {"ADC", NRM_ADC}, {"SBC", NRM_SBC}, {"RSC", NRM_RSC},
  {"TST", NRM_TST|NRM_S}, {"TEQ", NRM_TEQ|NRM_S},
  {"CMP", NRM_CMP|NRM_S}, {"CMN", NRM_CMN|NRM_S},
  {"ORR", NRM_ORR}, {"MOV", NRM_MOV}, {"BIC", NRM_BIC}, {"MVN", NRM_MVN},
  {"LDR", NRM_LDR}, {"STR", NRM_STR},
  
  {"LDM", NRM_LDM}, {"STM", NRM_STM},
  {"B"  , NRM_B  }, {"BL" , NRM_BL },
  {"SWI", NRM_SWI},
  {0,0}
};


#define NRM_S_LSL   0
#define NRM_S_LSR   1
#define NRM_S_ASR   2
#define NRM_S_ROR   3
#define NRM_S_RRX   4
#define NRM_S_NIL   5

static ku_t sfts[] = {
  {"LSL", NRM_S_LSL}, {"ASL", NRM_S_LSL},
  {"LSR", NRM_S_LSR}, {"ASR", NRM_S_ASR},
  {"ROR", NRM_S_ROR}, {"RRX", NRM_S_RRX},
  {0,0}
};

enum { NRM_D_FIRST_DRC=0,
  NRM_D_ASSERT,
  NRM_D_OPT, NRM_D_TTL, NRM_D_SUBT,
  NRM_D_ORG, NRM_D_LTORG, NRM_D_AREA, NRM_D_ENTRY, NRM_D_ROUT,
  NRM_D_END, NRM_D_KEEP, NRM_D_GET, NRM_D_INCLUDE,
  NRM_D_IMPORT, NRM_D_EXPORT,
  NRM_D_EQU,
  NRM_D_GBLA, NRM_D_GBLL, NRM_D_GBLS,
  NRM_D_LCLA, NRM_D_LCLL, NRM_D_LCLS,
  NRM_D_SETA, NRM_D_SETL, NRM_D_SETS,
  NRM_D_RN, NRM_D_FN, NRM_D_CP, NRM_D_CN,
  NRM_D_DCB, NRM_D_DCW, NRM_D_DCD, NRM_D_DCZ, NRM_D_DCFS, NRM_D_DCFD,
  NRM_D_ALIGN, NRM_D_SMORG, NRM_D_RESERVE,
  NRM_D_NOFP, NRM_D_RLIST,
  NRM_D_IF, NRM_D_ELSE, NRM_D_ENDIF,
  NRM_D_WHILE, NRM_D_WEND,
  NRM_D_MACRO, NRM_D_MEND, NRM_D_MEXIT,
  NRM_D_LAST_DRC
};


static ku_t dcts[] = { //assembler directives
  {"ASSERT", NRM_D_ASSERT},{"!", NRM_D_ASSERT},
  {"OPT", NRM_D_OPT}, {"TTL", NRM_D_TTL}, {"SUBT", NRM_D_SUBT}, 
  {"ORG", NRM_D_ORG}, //{"ABS", NRM_D_ORG}, /*in ObjAsm ABS is synonym for ORG*/
  {"LTORG", NRM_D_LTORG},
  {"AREA", NRM_D_AREA}, {"ENTRY", NRM_D_ENTRY}, {"ROUT", NRM_D_ROUT},
  {"END", NRM_D_END},  {"KEEP", NRM_D_KEEP},
  {"GET", NRM_D_GET}, {"INCLUDE", NRM_D_INCLUDE},
  {"IMPORT", NRM_D_IMPORT}, {"EXPORT", NRM_D_EXPORT},
  {"*", NRM_D_EQU}, {"EQU", NRM_D_EQU},
  {"GBLA", NRM_D_GBLA}, {"GBLL", NRM_D_GBLL}, {"GBLS", NRM_D_GBLS},
  {"LCLA", NRM_D_LCLA}, {"LCLL", NRM_D_LCLL}, {"LCLS", NRM_D_LCLS},
  {"SETA", NRM_D_SETA}, {"SETL", NRM_D_SETL}, {"SETS", NRM_D_SETS},
  {"RN", NRM_D_RN}, {"FN", NRM_D_FN}, {"CP", NRM_D_CP},{"CN", NRM_D_CN},
  {"DCB", NRM_D_DCB}, {"DCW", NRM_D_DCW}, {"DCD", NRM_D_DCD},
  {"=", NRM_D_DCB}, {"&", NRM_D_DCD}, {"%", NRM_D_DCZ},
  {"DCFS", NRM_D_DCB}, {"DCFD", NRM_D_DCFD}, 
  {"ALIGN", NRM_D_ALIGN}, {"^", NRM_D_SMORG}, {"#", NRM_D_RESERVE},
  {"NOFP", NRM_D_NOFP}, {"RLIST", NRM_D_NOFP}, 
  {"IF", NRM_D_IF}, {"ELSE", NRM_D_ELSE}, {"ENDIF", NRM_D_ENDIF}, 
  {"[", NRM_D_IF}, {"|", NRM_D_ELSE}, {"]", NRM_D_ENDIF},
  {"WHILE", NRM_D_WHILE}, {"WEND", NRM_D_WEND}, 
  {"MACRO", NRM_D_MACRO}, {"MEND", NRM_D_MEND}, {"MEXIT", NRM_D_MEXIT},
  {0,0}
};

#define NRM_BV_FALSE    0x01
#define NRM_BV_TRUE     0x02
#define NRM_BV_PC       0x03
#define NRM_BV_VAR      0x04
#define NRM_BV_OPT      0x05
#define NRM_BV_CONFIG   0x06
#define NRM_BV_ENDIAN   0x07
#define NRM_BV_INVALID  0x08

static ku_t blts[] = { //builtin variables
  {"{FALSE}", NRM_BV_FALSE}, {"{TRUE}", NRM_BV_TRUE},
  {"{PC}", NRM_BV_PC}, {".", NRM_BV_PC},
  {"{VAR}", NRM_BV_VAR}, {"@", NRM_BV_VAR},
  {"{OPT}", NRM_BV_OPT},
  {"{CONFIG}", NRM_BV_CONFIG}, {"{ENDIAN}", NRM_BV_ENDIAN},
  {0,0}
};


static int nrm_globals_ready = 0;


#define NRM_BAD_OPCODE 0xFFFFFFFF


static ku_t *opcm = NULL; // opcode mnemonic map
static ku_t *sftm = NULL; // shift operations map
static ku_t *cndm = NULL; // condition mnemonic map
static ku_t *dctm = NULL; // directive map
static ku_t *bltm = NULL; // builtin variable map

static void nrm_init_globals() {
  shdefault(opcm,NRM_BAD_OPCODE);
  for (ku_t *o = opcs; o->key; o++) shput(opcm, o->key, o->value);

  shdefault(cndm,NRM_BAD_OPCODE);
  for (ku_t *o = cnds; o->key; o++) shput(opcm, o->key, o->value<<28);


  shdefault(sftm,NRM_S_NIL);
  for (ku_t *o = sfts; o->key; o++) shput(sftm, o->key, o->value);


  for (ku_t *o = dcts; o->key; o++) shput(dctm, o->key, o->value);
  for (ku_t *o = blts; o->key; o++) shput(bltm, o->key, o->value);

  nrm_globals_ready = 1;
}

////////////////////////////// NRM STATE ///////////////////////////////////////

// Options for the nrm_init
typedef struct {
  //ARGUMENTS
  char **paths; //paths to search for files
  U32 flags;
  void *user; //user provided handle
              //available to callbacks through ncm_user
  
  //CALLBACKS provided by user
  
  //called when a fatal error has occured
  void (*fatal)(void *ncm, char *macro
                   ,char *file, int row, int col, char *description);

  //checks is a file exists (using in include)
  int (*exists)(void *ncm, char *filename);

  //reads entire file, storing its size at the *size pointer
  uint8_t *(*get)(void *ncm, U32 *size, char *filename);
} nrm_opt_t;

typedef struct { //represents expression delayed for the 2nd pass
  U32 pc;
  char *expr;
  char *name;
  int row;
  int col;
} dld_t;


struct nrm_t { // NRM's state
  flm_t flm;       //file manager
  nrm_opt_t opt;   //user specified options
  sym_tbl_t st;    //symbol map
  sym_t **sl;      //symbol list
  int pass;        //assembler's pass
  U8 *out;         //where output is currently being written
  dld_t *dld;      //list of delayed expressions
  U32 pc;          //have to maintain a separate one
                   //because out could be broken into parts
  int dldi;
};




///////////////////////////// NRM ERROR ////////////////////////////////////////


//FIXME: when fatal error happens, the nrm_t should be freed
static void fatalF(CTX, char *fmt, ...) {
  if (!C.opt.fatal) exit(-1);
  flmp_t p;
  flm_location(FLM, &p);

  va_list ap;
  va_start(ap, fmt);
  int l = vsnprintf(NULL, 0, fmt, ap);
  va_end(ap);
  char *s = (char*)malloc(l+1);

  va_start(ap, fmt);
  vsprintf(s, fmt, ap);
  va_end(ap);
  C.opt.fatal(this, p.macroname, p.filename, p.row, p.col, s);

  exit(-1);
}

#define fatal(...) fatalF(this, __VA_ARGS__)





///////////////////////////// FILE MANAGER /////////////////////////////////////

static mfl_t *mfl_open(CTX, char *filename) {
  U32 size;
  U8 *data = C.opt.get(this, &size, filename);
  if (!data) return 0;
  mfl_t *f = new_mfl(filename, data, size);
  f->url = url_parts(f->name);
  f->desc |= MFL_OWNED|MFL_FS;
  f->desc |= MFL_RETAIN; //as of now we retain everything, due to filetable
  return f;
}


static void flm_deinit(flm_t *this) {
  for (int i = 0; i < alen(this->fstack); i++) {
    flp_t *fp = this->fstack[i];
    fp->fl = 0;
    del_flp(fp);
  }
  arrfree(this->fstack);

  for (int i = 0; i < shlen(this->ft); i++) {
    mfl_t *next = this->ft[i].value;
    do {
      mfl_t *f = next;
      next = f->ovrd;
      del_mfl(f);
    } while (next);
  }

  shfree(this->ft);
}



static flp_t *flm_cur_flp(flm_t *this) {
  int nfiles = alen(this->fstack);
  for (int i =  nfiles-1; i >= 0; i--) {
    flp_t *p = this->fstack[i];
    if (p->fl->desc&MFL_FS) return p;
  }
  return 0;
}


//resolves a relative filename
static char *flm_resolve(flm_t *this, char *rel_name) {
  char *tmprel_name = 0;
  char *tmpname = 0;
  int nonlocal = 0;
  if (*rel_name == '<') {
    nonlocal = 1;
    rel_name++;
  }
  flp_t *cfp = flm_cur_flp(this);
  char **ps = this->paths;
  if (!ps) return 0;
  url_t *url = url_parts(rel_name);
  if (!*url->ext) {
    tmprel_name = cat(rel_name, ".h");
    rel_name = tmprel_name;
  }
  free(url);
  for (int i = -1; i < 0 || *ps; i++) {
    char *folder;
    if (i == -1) {
      if (nonlocal || !cfp) {
        continue;
      }
      folder = cfp->fl->url->dir; //try current dir
    } else {
      folder = *ps;
      ps++;
    }
    tmpname = cat(folder, rel_name);
    if (C.ctx->opt.exists(this,tmpname)) break;
    free(tmpname);
    tmpname = 0;
  }
  if (tmprel_name) free(tmprel_name);
  return tmpname;
}


static void flm_location(flm_t *this, flmp_t *p) {
  p->filename = 0;
  p->macroname = 0;
  p->row = 0;
  p->col = 0;
  for (int i = alen(C.fstack)-1; i >= 0; i--) {
    flp_t *fp = C.fstack[i];
    if (fp->fl->desc & MFL_MACRO) {
      if (!p->macroname) p->macroname = fp->fl->name;
    } else {
      if (!p->filename) {
        p->filename = fp->fl->name;
        p->row = fp->row;
        p->col = FL_COL(fp);
      }
    }
  }
  
  if (!p->filename) p->filename = "<none>";
}

static void flm_push(flm_t *this, mfl_t *f) {
  mfl_ref(f);
  U8 *shd = 0;
  if (alen(C.fstack)) {
    *alast(C.fstack) = C.flp;
    shd = C.flp.shd;
  }
  flp_t *fp = new_flp(f);
  aput(C.fstack, fp);
  C.flp = *fp;
  C.flp.shd = shd;
}

//include counter for each encountered file
static ku_t *flm_incnts = NULL;

static void flm_minclude(flm_t *this, char *name, U8 *base, U32 size, U32 flags)
{
  if (!flm_incnts) {
    shdefault(flm_incnts,0);
    sh_new_arena(flm_incnts);
  }
  shput(flm_incnts, name, shget(flm_incnts,name)+1);
  mfl_t *f = new_mfl(name, base, size);
  f->desc |= flags;
  f->flm = this;
  flm_push(this, f);
}

static void flm_conclude(flm_t *this) {
  U8 *shd = C.flp.shd;
  if (C.flp.fl->desc&MFL_ROOT) return; // can't pop root
  flp_t *fp = apop(C.fstack);
  C.flp = *alast(C.fstack);
  C.flp.shd = shd;
  mfl_t *f = fp->fl;
  if (f->ovrd) shput(C.ft, f->name, f->ovrd); //uncover old entry
  del_flp(fp);
  mfl_unref(f);
}



static void flm_include(flm_t *this, char *rel_name) {
  char *resolved_name = 0;
  char *filename;
  if (alen(C.fstack)) resolved_name = flm_resolve(this, rel_name);
  if (resolved_name) filename = resolved_name;
  else filename = rel_name; //consider it being absolute name

  mfl_t *f = shget(this->ft,filename);
  if (f) {
    flm_push(this, f);
    return;
  }
  
  f = mfl_open(C.ctx, filename);
  if (!f) fatalF(C.ctx, "Couldn't read `%s`", filename);

  f->flm = this;

  shput(C.ft, f->name, f);
  flm_push(this, f);


  if (resolved_name) free(resolved_name);
}


static void flm_init(flm_t *this, TCTX *ctx) {
  memset(this, 0, sizeof(flm_t));
  this->ctx = ctx;
  sh_new_arena(this->ft); //copies keys to internal store
  this->paths = ctx->opt.paths;
  flm_minclude(this, "", "", 0, MFL_ROOT);
}


////////////////////////////// NRM SYMBOL //////////////////////////////////////


static sym_t *nrm_sref(CTX, char *name) {
  sym_t *s = shget(C.st, name);
  if (!s) {
    s = malloc(sizeof(sym_t));
    s->desc = SYM_NON;
    s->name = strdup(name);
    memset(s, 0, sizeof(sym_t));
    shput(C.st, name, s);
    aput(C.sl, s);
  }
  return s;
}




////////////////////////////// NRM INIT ////////////////////////////////////////


void nrm_opt_init(nrm_opt_t *o) {
  memset(o, 0, sizeof(nrm_opt_t));
}


//assign's name to a register indexed by index
void nrm_name_reg(CTX, char *name, int index) {
  sym_t *s = nrm_sref(this,name);
  s->desc = SYM_REG;
  s->v.w = index;
}


void nrm_init(CTX, nrm_opt_t *opt) {
  if (!nrm_globals_ready) nrm_init_globals();

  memset(this, 0, sizeof(nrm_t));

  if (opt) memcpy(&C.opt, opt, sizeof(nrm_opt_t));
  else nrm_opt_init(&C.opt);

  sh_new_arena(C.st);
  flm_init(&this->flm, this);

  for (ki_t *rn = base_regs; rn->key; rn++) {
    nrm_name_reg(this, rn->key, rn->value);
  }
}

static nrm_t *new_nrm(nrm_opt_t *opt) {
  nrm_t *this = malloc(sizeof(nrm_t));
  nrm_init(this, opt);
  return this;
}

static void del_nrm(CTX) {
  flm_deinit(&this->flm);
  free(this);
}


void nrm_cstr(CTX, char *cstr) {
  flm_minclude(&this->flm, "<cstr>", cstr, strlen(cstr), 0);
}



////////////////////////// NRM OPERATIONS //////////////////////////////////////


typedef struct { //parsed instruction
  U32 dsc; //binary description of the instruction
} nrm_nst_t;


//is end of stream, line feed or comment

#define ISNL(x) (ISFLE(x) || (x)=='\n')
#define ISNLC(x) (ISNL(x) || (x)==';')

//is argument end
#define ISWSNLC(x) (ISNLC(x) || ISWS(x))
#define ISAE(x) (ISWSNLC(x) || (x) == ',')
#define SKPAE(p) do { if (nx == ',') {rd(); SKPWS();} } while(0)



static char *get_dec(CTX) {
  char *r = NULL;
  while (isdigit(nx)) aput(r, rd());
  aput(r,0);
  return r;
}

static char *get_hex(CTX) {
  char *r = NULL;
  while (isxdigit(nx)) aput(r, rd());
  aput(r,0);
  return r;
}


#define NRM_ARG_SYM  0
#define NRM_ARG_IMM  1
#define NRM_ARG_REG  2
#define NRM_ARG_LST  3
#define NRM_ARG_ADR  4
#define NRM_ARG_SFT  5
//register set
#define NRM_ARG_RES  6

#define NRM_SFT_REG  (1<<4)


typedef struct {
  char *s; //readed string
  int desc;
  val_t v;
} nrm_arg_t;

static int issymchr(int c) {
  return isalnum(c) || c == '_';
}

        
#define READ_NUM(name,base)                                 \
  S32 name;                                                 \
  {SKPWS();                                                 \
  char *tmp_;                                               \
  int sign = 0;                                             \
  if (nx == '-') {sign=1; rd();}                            \
  if (base==10) RDS(tmp_,isdigit); else RDS(tmp_,isxdigit); \
  if (!tmp_[0]) fatal("number expected");                   \
  name = strtol(tmp_, 0, base);                         \
  if (sign) name = -name;}


static U32 parse_stldm_type(U32 dsc, char *m) {
  if (m[0]=='I') {
    dsc |= NRM_UP;
    if (m[1]=='B') dsc |= NRM_PRE;
    else if (m[1]!='A') dsc = NRM_BAD_OPCODE;
  } else if (m[0]=='D') {
    if (m[1]=='B') dsc |= NRM_PRE;
    else if (m[1]!='A') dsc = NRM_BAD_OPCODE;
  } else {
    if (dsc & NRM_STLD_LD) {
      /* LDMFD=LDMIA, LDMFA=LDMDA, LDMED=LDMIB, LDMEA=LDMDB */
      if (m[0]=='F') {
        if (m[1]=='D') dsc |= NRM_UP;
        else if (m[1]!='A') dsc = NRM_BAD_OPCODE;
      } else if (m[0]=='E') {
        dsc |= NRM_PRE;
        if (m[1]=='D') dsc |= NRM_UP;
        else if (m[1]!='A') dsc = NRM_BAD_OPCODE;
      } else {
        dsc = NRM_BAD_OPCODE;
      }
    } else {
      /* STMFD=STMDB, STMFA=STMIB, STMED=STMDA, STMEA=STMIA */
      if (m[0]=='F') {
        dsc |= NRM_PRE;
        if (m[1]=='A') dsc |= NRM_UP;
        else if (m[1]!='D') dsc = NRM_BAD_OPCODE;
      } else if (m[0]=='E') {
        if (m[1]=='A') dsc |= NRM_UP;
        else if (m[1]!='D') dsc = NRM_BAD_OPCODE;
      } else {
        dsc = NRM_BAD_OPCODE;
      }
    }
  }
  return dsc;
}

#define MAX_MM_LEN 7

static U32 parse_mnemonic(CTX, char *mm) {
  U32 dsc;
  char m[8], t[8];

  int l = 0;
  while ((m[l] = toupper(mm[l])))
    if (++l == MAX_MM_LEN) return NRM_BAD_OPCODE;

  switch (l) {
  case 1: case 2: case 3:
    dsc = shget(opcm, m);
    if (dsc != NRM_BAD_OPCODE) {
      if (NRM_IS_STLDM(dsc))
        return NRM_BAD_OPCODE; //add a switch defaulting to dsc |= NRM_UP;
      return dsc | (NRM_AL<<28);
    }
    if (l == 3 && m[0] == 'B') {
      dsc = shget(cndm, m+1);
      if (dsc != NRM_BAD_OPCODE) {
        dsc |= NRM_B;
        return dsc;
      }
    }
    break;

  case 4:
    strncpy(t, m, 3);
    t[3] = 0;
    dsc = shget(opcm, t);
    if (dsc == NRM_BAD_OPCODE) return dsc;
    if (m[3] == 'S') {
      if (!NRM_IS_DP(dsc)) return NRM_BAD_OPCODE;
      dsc |= NRM_S;
    } else if (m[0] == 'B' && m[1] == 'L') { //BLCC
      dsc = shget(cndm, m+2);
      dsc |= NRM_BL;
      return dsc;
    } else if (m[3] == 'B') { //LDRB/STRB
      if (!NRM_IS_STLD(dsc)) return NRM_BAD_OPCODE;
      dsc |= NRM_STLD_BYTE;
    } else if (m[3] == 'T') { //LDRT/STRT
      if (!NRM_IS_STLD(dsc)) return NRM_BAD_OPCODE;
      dsc |= NRM_STLD_TRANS;
    } else if (m[3] == 'P') { //CMPP/CMNP/TSTP/TEQP
      U32 opc = NRM_OPC(dsc);
      if (!NRM_IS_CTDP(opc)) return NRM_BAD_OPCODE;
      dsc |= (0xF<<12);
    } else {
      return NRM_BAD_OPCODE;
    }
    dsc |= NRM_AL<<28;
    break;


  case 5:
    strncpy(t, m, 3);
    t[3] = 0;
    dsc = shget(opcm, t) | (NRM_AL<<28);
    if (NRM_IS_STLDM(dsc)) return parse_stldm_type(dsc,m+3);
    if (m[3] == 'B' && m[4] == 'T' && NRM_IS_STLD(dsc)) {
      dsc |= NRM_STLD_BYTE|NRM_STLD_TRANS;
    } else {
      dsc |= shget(cndm, m+3);
    }
    break;


  case 6:
    strncpy(t, m, 3);
    t[3] = 0;
    dsc = shget(opcm, m);
    strncpy(t, m+3, 2);
    dsc |= shget(cndm, t);
    if (NRM_IS_DP(dsc)) { //ADDEQS, etc..
      if (m[5] != 'S') return NRM_BAD_OPCODE;
      dsc |= NRM_S;
    } else if (NRM_IS_STLD(dsc)) { //LDREQB, erc..
      if (m[5] == 'B') dsc |= NRM_STLD_BYTE;
      else if (m[5] == 'T') dsc |= NRM_STLD_TRANS;
      else return NRM_BAD_OPCODE;
    } else {
      return NRM_BAD_OPCODE;
    }
    break;


  case 7:
    strncpy(t, m, 3);
    t[3] = 0;
    dsc = shget(opcm, t);
    if (NRM_IS_STLDM(dsc)) { //STMLOIA, etc..
      strncpy(t, m+3, 2);
      dsc |= shget(cndm, t);
      dsc = parse_stldm_type(dsc,m+5);
    } else if (NRM_IS_STLD(dsc)) { //LDRVCBT, etc..
      if (m[5] != 'B' && m[6] != 'T') return NRM_BAD_OPCODE;
      dsc |= NRM_STLD_BYTE|NRM_STLD_TRANS;
    } else {
      return NRM_BAD_OPCODE;
    }
    strncpy(t, m+3, 2);
    dsc |= shget(cndm, t);
    break;


  default:
    dsc = NRM_BAD_OPCODE;
  }

  return dsc;
}

void nrm_skip_comment(CTX) {
  while (!ISNLC(nx) || nx == ';') rd();
  if (nx == '\n') rd();
}

void nrm_skip_till_eol(CTX) {
  while (!ISNL(nx)) rd();
  if (nx == '\n') rd();
}

static void nrm_set_label(CTX, char *l, U32 pc) {
  sym_t *s = nrm_sref(this,l);
  s->desc = SYM_LBL;
  s->v.w = pc;
}


static void nrm_outw(CTX, U32 w) {
  uint8_t *out = C.out;
  aput(out, w&0xFF);
  aput(out, (w>>8)&0xFF);
  aput(out, (w>>16)&0xFF);
  aput(out, w>>24);
  C.out = out;
}

static void nrm_do_expr(CTX) { //processes single expression
  LHP(256); //temporary area for parsing mnemonic and args
  char shd[512]; //shadow copy of this input line
  char *m, *l;
  nrm_arg_t as[5];
  int n = 0; //nargs
  
  cflp_save();
  cflp_shd(shd);

read_label:

  //ObjAsm labels variables always begin at the start of a line,
  //everything else gets indented.
  if (ISWS(nx)) {
    l = "";
    SKPWS();
  } else if (nx == ';') {
    nrm_skip_comment(this);
    goto read_label;
  } else { 
    RDS(l,!ISWSNLC); SKPWS();
  }

read_mnemonic:
  if (nx == '\n') {
    rd();
    if (*l) {
      SKPWS();
      goto read_mnemonic;
    }
    goto read_label;
  }
  
  if (ISFLE(nx)) {
    if (*l) nrm_set_label(this, l, alen(C.out));
    return;
  }

  RDS(m,!ISWSNLC); SKPWS();
  
  //fprintf(stderr, "%s\n", m);

  U32 dsc = parse_mnemonic(this, m);
  //U32 dsc = shget(opctbl, m);
  if (dsc == NRM_BAD_OPCODE) {
    int dct = shget(dctm, m);
    U32 pc = alen(C.out);
    if (!dct) fatal("unknown operation `%s`", m);
    if (dct == NRM_D_EQU) { //these are akin to argless C99 macros
      if (!*l) fatal("EQU without a label.");
      char *v;
      RDS(v,!ISNLC);
      if (nx == '\n') rd();
      sym_t *s = nrm_sref(this,l);
      s->desc = SYM_EQU;
      s->v.s = strdup(v);
      *l = 0; //consume label
    } else if (dct == NRM_D_AREA) {
      nrm_skip_till_eol(this); //ignored for now
    } else if (dct == NRM_D_ENTRY) {
      nrm_skip_till_eol(this); //for now we assume 1st opcode to be entry
    } else if (dct == NRM_D_DCB) {
      if (nx == '\"') {
        rd();
        for (;;) { //FIXME: implement option of C escapes
          int ch = rd();
          if (ch == FLE) fatal("EOF in string");
          if (ch == '\"') {
            aput(C.out, 0);
            break;
          }
          aput(C.out, ch);
        }
      } else if (isdigit(nx)) {
        READ_NUM(v,10);
        if ((U32)v > 255) fatal("DCB value is invalid");
        aput(C.out, v);
      } else {
        fatal("DCB value is invalid");
      }
    } else if (dct == NRM_D_DCD) {
      if (nx == '&') {
        rd();
        READ_NUM(v,16);
        nrm_outw(this, v);
        nrm_skip_till_eol(this);
      } else {
        fatal("DCD value is invalid");
      }
    } else if (dct == NRM_D_ALIGN) { //FIXME: implement optional arguments
      while (alen(C.out)&0x3) aput(C.out, 0);
    } else if (dct == NRM_D_END) {
      nrm_skip_till_eol(this);
    } else{
      fatal("directive `%s` is unimplemented", m);
    }
    if (*l) nrm_set_label(this, l, pc);
    return; //it is possible we got END
  }

  if (*l) nrm_set_label(this, l, alen(C.out));

  U32 cls = NRM_CLS(dsc);

  //fprintf(stderr, "%x\n", dsc);

  int bo = 0; //opening bracket
  int bd = 0; //bracket depth
  int bs = -1; //bracket start
  int be = -1; //bracket end
  int wb = 0; //write-back
  int nr = 0; //negative register
  for (; !ISNLC(nx) && n < 5; n++) {
    int c;
    cflp_save(); //save file position for error reporting
    nrm_arg_t *a = &as[n];
arg_retry:
    c = nx;
    if (isalpha(c)) {
      int shtype;
      RDS(a->s,issymchr);
      //a->v.s
      sym_t *sym = shget(C.st, a->s);

      if (sym) {
        if (sym->desc == SYM_REG) {
          a->desc = NRM_ARG_REG;
          a->v.w = sym->v.w;
        } else if (sym->desc == SYM_EQU) {
          flm_minclude(&this->flm, "<EQU>", sym->v.s, strlen(sym->v.s), 0);
          goto arg_retry;
        } else if (sym->desc == SYM_LBL) {
          a->desc = NRM_ARG_IMM;
          U32 v = sym->v.w;
          if (cls != NRM_CLS_DPR && cls != NRM_CLS_DPI) {
            if (cls == NRM_CLS_STLDI) bo = '[';
            a->v.sw = v;
          } else {
            a->v.w = nrm_enc_imm(v);
            if (a->v.w == NRM_BAD_IMM) fatal("can't encode `%d`", v);
          }
        } else {
          fatal("`%s` is unexpected", a->s);
        }
      } else if ((shtype = shget(sftm, a->s)) != NRM_S_NIL) {
        int base = 10;
        char s[4];
        strncpy(s, a->s, 3);
        s[3] = 0;
        upcase(s,s);

        a->desc = NRM_ARG_SFT;

        SKPWS();
        if (shtype == NRM_S_RRX) {
          a->v.w = 0;
        } else if (nx == '#' || nx == '&' || ISWS(nx)) {
          if (nx == '#')  {
            rd();
          }
          if (nx == '&')  {
            base = 16;
          }
          READ_NUM(v,base)
          if (v > 31) fatal("shift value `%d` is larger than 31", v);
          a->v.w = (v<<7) | (shtype<<5);
        } else if (isalpha(c)) {
          RDS(a->s,issymchr);
          sym_t *sym = shget(C.st, a->s);
          if (!sym || sym->desc != SYM_REG) {
             fatal("`%s` is unexpected", a->s);
          }
          a->v.w = (sym->v.w<<8)|NRM_SFT_REG;
        } else {
          fatal("operand %d is invalid", n);
        }
      } else {
        if (C.pass == 0) {
          dld_t dld;
          FLLOC(row,col,name,cflp_saved());
          dld.row = row; dld.col = col; dld.name = strdup(name);
          dld.pc = alen(C.out);
          nrm_skip_till_eol(this); //ignored for now
          *cflp->shd = 0;
          cflp->shd = 0;
          dld.expr = strdup(shd);
          aput(C.dld,dld);
          aput(C.out,0); aput(C.out,0); aput(C.out,0); aput(C.out,0);
          return;
        } else {
          fatal("symbol `%s` is undefined", a->s);
        }
      }
    } else if (c == '#') {
      int base = 10;
      rd();
      SKPWS();
      if (nx == '\"') {
        int tc = rd();
        RDS(a->s,!ISTC);
        rd();
        if (strlen(a->s)>1)
          fatal("char literal #\"%s\" is too big", a->s);
        a->v.w = a->s[0]; //assume ASCII
      } else {
        if (nx == '&') {
read_hex_imm:
          base = 16;
          rd();
        }
        a->desc = NRM_ARG_IMM;
        READ_NUM(v,base);
        if (cls != NRM_CLS_DPR && cls != NRM_CLS_DPI) {
          if (cls == NRM_CLS_STLDI) bo = '[';
          a->v.sw = v;
        } else {
          a->v.w = nrm_enc_imm(v);
          if (a->v.w == NRM_BAD_IMM) fatal("can't encode `%d`", v);
        }
      }
      
    } else if (c == '&') {
      goto read_hex_imm;
    } else if (c == '=') {
      fatal("implement `=` reading.");
    } else if (c == '|') {
      fatal("implement `|` reading.");
    } else if (c == '[') {
      if (bo) fatal("unexpected `%c`", c);
      rd();
      bo = c;
      bd++;
      bs = n;
      n--;
    } else if (c == ']') {
      rd();
      if (bo!='[') fatal("unexpected `%c`",c);
      be = n;
      bd--;
      n--;
    } else if (c == '-') {
      if (cls != NRM_CLS_STLDI) fatal("unexpected `%c`",c);
      rd();
      nr = n;
      n--;
    } else if (c == '!') {
      if (cls != NRM_CLS_STLDI && cls != NRM_CLS_STLDM)
        fatal("unexpected `%c`",c);
      rd();
      wb = n;
      n--;
    } else if (c == '{') {
      if (cls != NRM_CLS_STLDM) fatal("unexpected `%c`",c);
      rd();
      U32 regs = 0;
      int prev = -1;
      int interp = 0;
      SKPWS();
      for (;;) {
        int c = nx;
        if (isalpha(c)) {
          RDS(a->s,issymchr);
          sym_t *sym = shget(C.st, a->s);
          if (!sym || sym->desc != SYM_REG) fatal("`%s` is unexpected", a->s);
          if (interp) {
            interp = 0;
            int a = prev;
            int b = sym->v.w;
            if (a > b) {
              int t = b;
              b = a-1;
              a = t-1;
            }
            while (a++ < b) regs |= 1<<a;
            prev = sym->v.w;
          } else {
            prev = sym->v.w;
            regs |= 1<<prev;
          }
        } else if (c == '-') {
          rd();
          interp = 1;
        } else if (c == ',') {
          rd();
        } else if (c == '}') {
          rd();
          break;
        } else {
          fatal("unexpected `%c`",c);
        }
      }
      SKPWS();
      if (nx == '^') {
        rd();
        regs |= NRM_LOAD_PSR_FORCE_USER_MODE;
      }
      as[n].desc = NRM_ARG_RES;
      as[n].v.w = regs;
    } else {
      fatal("operand %d is invalid", n);
    }
    SKPWS();
    SKPAE();
  }
  if (n > 4) fatal("too many operands"); //too many args

  if (bo) {
    if (bd) fatal("unclosed `%c`", bo);
    int bn = be-bs;
    if (n == 0 || (bn > 1 && be != n)) fatal("invalid `%c` specification", bo);
  }



  //skip comment till EOL
  if (nx == ';') nrm_skip_comment(this);

  //printf("l=%s m=%s a=%s b=%s c=%s d=%s\n", l, m,a,b,c,d);

  switch (cls) {
  case NRM_CLS_DPR: case NRM_CLS_DPI:
    //should we allow partially encoded opcodes
    //if (n != 2)  fatal("too %s operands", n > 2 ? "many" : "little");
    U32 opc = NRM_OPC(dsc);

    if (NRM_IS_CTDP(opc) || NRM_IS_MOV(opc)) {
      if (n < 2) fatal("too little operands");
      if (n > 3) fatal("too many operands");
      if (as[0].desc != NRM_ARG_REG) fatal("operand 0 is invalid");

      if (NRM_IS_CTDP(opc)) dsc |= as[0].v.w<<16;
      else dsc |= as[0].v.w<<12;
      if (as[1].desc == NRM_ARG_REG) dsc |= as[1].v.w;
      else if (as[1].desc == NRM_ARG_IMM) dsc |= as[1].v.w;
      else fatal("operand 1 is invalid");
      if (n > 2) {
        if (as[2].desc == NRM_ARG_SFT && as[1].desc == NRM_ARG_REG) {
          dsc |= as[2].v.w;
        } else {
          fatal("operand 2 is invalid");
        }
      }
    } else {
      if (n < 3) fatal("too little operands");
      if (n > 4) fatal("too many operands");

      if (as[0].desc != NRM_ARG_REG) fatal("operand 0 is invalid");
      dsc |= as[0].v.w<<12; //dst register
 
      if (as[1].desc != NRM_ARG_REG) fatal("operand 1 is invalid");
      dsc |= as[1].v.w<<16; //1st operand

      if (as[2].desc == NRM_ARG_REG) dsc |= as[2].v.w;
      else if (as[2].desc == NRM_ARG_SFT) dsc |= as[2].v.w;
      else fatal("operand 2 is invalid");
    }

    break;


  case NRM_CLS_STLDI: //NRM_CLS_STLDR can't occur before this switch
    if (n < 2) fatal("too little operands");
    if (n > 4) fatal("too many operands");
    if (wb && (wb != n || n == 2)) fatal("unexpected `%c`",'!');
    if (as[0].desc != NRM_ARG_REG) fatal("operand 0 is invalid");
    int trans = 0;
    if (dsc&0x1) {
      trans = 1;
      dsc ^= 1;
    }
    dsc |= as[0].v.w<<12;
    
    if (bo != '[')  fatal("missing [...] base");
    if (as[1].desc == NRM_ARG_REG) {
      dsc |= as[1].v.w<<16; //base register
    } else if (as[1].desc == NRM_ARG_IMM) {
      if (n > 2) { fatal("offset is invalid"); }
      dsc |= 15<<16; //pc relative addressing
      S32 sw = (S32)as[1].v.w - (S32)this->pc - 8;
      if (sw >= 0) dsc |= NRM_UP;
      else sw = -sw;
      dsc |= sw;
    } else {
      fatal("base register is invalid");
    }

    if (n == 2) {
      dsc |= NRM_UP; //FIXME: should we really add these?
                     //consult objasm output
      if (!trans) dsc |= NRM_PRE;
    } else {
      if (as[2].desc == NRM_ARG_IMM) {
        S32 sw = as[1].v.w;
        if (sw >= 0) dsc |= NRM_UP;
        else sw = -sw;
        dsc |= sw;
      } else if (as[2].desc == NRM_ARG_REG) {
        dsc |= (NRM_CLS_STLDR<<25);
        dsc |= as[2].v.w;
        if (nr && nr == 2) nr = 0;
        else dsc |= NRM_UP;
      } else {
        fatal("offset is invalid");
      }

      if (wb) dsc |= NRM_WRITEBACK;
      if (be == n) if (!trans) dsc |= NRM_PRE;
      else {
        if (wb && wb != be) fatal("unexpected `%c`",'!');
      }

      if (n > 3) {
        if (as[3].desc == NRM_ARG_SFT && as[2].desc == NRM_ARG_REG) {
          dsc |= as[3].v.w;
        } else {
          fatal("operand 2 is invalid");
        }
      }
    }

    if (nr) fatal("unexpected `%c`",'-'); //placed somewhere randomly
    break;


  case NRM_CLS_STLDM:
    if (n != 2) fatal("too %s operands", n > 2 ? "many" : "little");
    if (wb) {
      if (wb != 1) fatal("unexpected `%c`",'!');
      dsc |= NRM_WRITEBACK;
    }

    if (as[0].desc == NRM_ARG_REG) dsc |= as[0].v.w<<16; //base register
    else fatal("base register is invalid");

    if (as[1].desc == NRM_ARG_RES) dsc |= as[1].v.w; //base register
    else fatal("register set is invalid");

    break;

  case NRM_CLS_B_BL:
    if (n != 1) fatal("too %s operands", n > 1 ? "many" : "little");
    if (as[0].desc != NRM_ARG_IMM) fatal("immediate expected");
    U32 a = as[0].v.w;
    if (a & 0x3) fatal("unaligned destination");
    //ARM branches are PC relative and word-aligned
    dsc |= ((a - this->pc - 8)&0x3FFFFFF)>>2;
    break;

  case NRM_CLS_SWI:
    if (n != 1) fatal("too %s operands", n > 1 ? "many" : "little");
    if (as[0].desc != NRM_ARG_IMM) fatal("immediate expected");
#define MAX_SWI_INDEX 0xFFFFFF
    if (as[0].v.w > MAX_SWI_INDEX)
      fatal("SWI number is larger than %d", MAX_SWI_INDEX);
    dsc |= as[0].v.w;
    break;

  default:
    fatal("operation `%s` is unimplemented", m);
    break;
  }

do_output:
  nrm_outw(this, dsc);
}


static uint8_t *nrm_do(CTX) {
  C.pass = 0;
  C.out = 0;
  while (!ISFLE(nx)) {
    this->pc = alen(this->out);
    nrm_do_expr(this);
    if (nx == '\n') rd();
  }
  U8 *r = C.out;
  C.out = 0;

  C.pass++;

  for (int i = 0; i < alen(C.dld); i++) {
    C.dldi = i;
    flm_minclude(&this->flm, C.dld[i].name, C.dld[i].expr
                ,strlen(C.dld[i].expr), 0);
    U32 spc = alen(C.out);
    this->pc = C.dld[i].pc;
    nrm_do_expr(this);
    U32 dpc = C.dld[i].pc;
    while (spc < alen(C.out)) r[dpc++] = C.out[spc++]; //patch it
  }
  arrfree(C.out);
  C.out = 0;
  return r;
}

void nrm_include(CTX, char *filename) {
  flm_include(&C.flm, filename);
}


/////////////////////// NRM PROCESSING LOOP ////////////////////////////////////


static uint8_t *nrm_do_cstr(nrm_opt_t *opt, char *cstr) {
  nrm_t *nrm = new_nrm(opt);
  nrm_cstr(nrm, cstr);
  uint8_t *r = nrm_do(nrm);
  del_nrm(nrm);
  return r;
}

static uint8_t *nrm_do_file(nrm_opt_t *opt, char *filename) {
  nrm_t *nrm = new_nrm(opt);
  nrm_include(nrm, filename);
  uint8_t *r = nrm_do(nrm);
  del_nrm(nrm);
  return r;
}

/////////////////////////// STANDALONE /////////////////////////////////////////

#ifdef NRM_STANDALONE


//////////////////////////// ncu_file.h ////////////////////////////////////////


#define FILE_SIZE_ERROR 0xFFFFFFFF
static uint32_t fileSize(char *filename) {
  FILE *fp = fopen(filename, "rb");
  if (!fp) return FILE_SIZE_ERROR;
  fseek(fp, 0L, SEEK_END);
  uint32_t sz = ftell(fp);
  fclose(fp);
  return sz;
}

static uint8_t *fileGet(uint32_t *rsize, char *filename) {
  uint32_t sz = fileSize(filename);
  if (sz == FILE_SIZE_ERROR) return 0;
  FILE *fp = fopen(filename, "rb");
  if (!fp) return 0;
  *rsize = sz;
  uint8_t *p = 0;
  arrsetlen(p, sz+1);
  p[sz] = 0;
  fread(p, 1, sz, fp);
  fclose(fp);
  return p;
}

static int fileSet(char *filename, uint8_t *data, uint32_t size) {
  FILE *fp = fopen(filename, "wb");
  if (!fp) return 0;
  fwrite(data, 1, size, fp);
  fclose(fp);
  return 1;
}

static int fileExist(char *filename) {
  FILE *fp = fopen(filename, "rb");
  if (!fp) return 0;
  fclose(fp);
  return 1;
}


//////////////////////////////// MAIN //////////////////////////////////////////

#define XD_NO 0x80

static void xd(uint8_t *p, int n, uint32_t s, uint32_t opt) {
  int i;
  int ll = (opt&0xFF);
  int j = 0;
  if (!(opt&XD_NO)) printf("%06x: ", s);
  for (i = 0; i < n; i++) {
    printf("%02X", p[i]);
    if (++j == ll || i+1 == n) {
      printf("\n");
      if (!(opt&XD_NO) && i+1 != n) printf("%06x: ", s+i+1);
      j = 0;
    } else {
      printf(" ");
    }

  }
}

static void cbFatal(void *ncm, char *macro
                        ,char *file, int row, int col, char *text) {
  fprintf(stderr, "%s:%d:%d\n", file, row+1, col+1);
  if (macro)
    fprintf(stderr, "  During macro expansion `%s`\n", macro);
  fprintf(stderr, "  Fatal: %s\n", text);
  exit(-1);
}

static uint8_t *cbGet(void *handle, uint32_t *rsize, char *filename) {
  return fileGet(rsize, filename);
}

static int cbExists(void *handle, char *filename) {
  return fileExist(filename);
}

static void p(char *s) {
  printf("%s\n", s);
}

void usage() {
  p("NRM 0.1 New ARM Assembler by Nancy Sadkov (public domain CC0 version)");
  p("");
  p("Usage:      nrm [keyword arguments] sourcefile objectfile");

  //FIXME: implement rest of the ObJAsm options below
#if 0
  p("            nrm [keyword arguments] -o objectfile sourcefile");
  p("Keyword options (upper case shows allowable abbreviation):");
  p("");
  p("-Help                   Output this infomation");
  p("-LIST <file>            Create a listing file:");
  p("  -NOTerse                Terse flag off                (default on)");
  p("  -Width <n>              Listing page width            (default 79)");
  p("  -Length <n>             Listing page length           (default 66)");
  p("  -Xref                   List X-ref info on symbols    (default off)");
  p("-VIA <file>             Read in extra comm line arguments from <file>");
  p("-ERRors <file>          Write error output to file");
  p("-LIttleend              Assemble code for little-endian memory");
  p("-BIgend                 Assemble code for big-endian memory");
  p("-Apcs NONE|3<quals>     Specify variany of APCS in use (in any)");
  p("-Depend <file>          Write 'make' source file dependency information to <file>");
  p("-ThrowBack              Support error processing by Desktop Tools & compliant tools");
  p("-DeskTop                Set the work directory for the assembler as <dir>");
  p("-Esc                    Enable C-style escape sequences (eg '\n', '\t')");
  p("-UpperCase              Recognise instruction mnemonics in upper case only");
  p("-I <dir>[,<dir>]        Include <dir>s on the source file search path");
  p("-CPU <target-cpu>       Set the target ARM core type");
  p("-PreDefine <directive>  Pre-execute a SET{A|L|S} directive");
  p("-G                      Output ASD debugging tables");
  p("-NOCache                Turn off source caching         (default on)");
  p("-MaxCache <n>           Set maximum source cache size   (default 8MB)");
  p("-ABSolute               Accept AAsm source code");
  p("-NOWarn                 Disable all warning messages");
  p("");
  p("");
  p("-FRom, -TO, -Print      Supported for backward compatibility");
  p("-Quit                   Recognised for backward compatibility, but ignored");
#endif

  exit(0);
}





#if 0
//the below struct is for reference header only
//dont cast/memcpy it as is, since we want this code
//to work on big endian machines
typedef struct {
/*00*/U32 bl_decompress; //NOP if the image is not compressed.
/*04*/U32 bl_relocate;   //NOP if the image is not self-relocating.
/*08*/U32 bl_init;       //NOP if the image has none.
/*0C*/U32 entry;         //either BL to entry or an offset for non executables
                         //Non-executable AIF uses an offset, not BL
/*10*/U32 swi_os_exit;   //...last ditch in case of return.
/*14*/U32 ro_sz;         //Includes header size if executable AIF;
                         //excludes headser size if non-executable AIF.
/*18*/U32 rw_sz;         //Exact size - a multiple of 4 bytes
/*1C*/U32 debug_sz;      //Exact size - a multiple of 4 bytes
/*20*/U32 zero_sz;       //`.bss` section size, cleared by bl_init
                         //a multiple of 4 bytes
/*24*/U32 debug_type;    //0, 1, 2, or 3
/*28*/U32 base;          //Address the image (code) was linked at. 
                         //typically 0x8000
/*2C*/U32 workspace;     //Min work space - in bytes - to be reserved
                         //preallocates heap
/*30*/U32 mode;          //Address mode: 26/32 + 3 flag bytes
                         //LS byte contains 26 or 32;
                         //bit 8 set when using a separate data base.
/*34*/U32 data_base;     //Address the image data was linked at.
/*38*/U32 reserved0;     //set to 0
/*3C*/U32 reserved1;     //set to 0
/*40*/U32 bl_debug_init; //NOP if unused.
/*44*/U32 init[15];      //init code; typically zeroes zero_sz bytes of bss 
} aifhdr_t;
#endif



#define AIF_RO_SZ  0x14

#define AIF_HDR_SZ 0x80
//basic header which just transfers control to the code below it
static uint8_t nrm_aif_header[AIF_HDR_SZ] = {
  0x00, 0x00, 0xA0, 0xE1,
  0x00, 0x00, 0xA0, 0xE1,
  0x00, 0x00, 0xA0, 0xE1,
  0x1B, 0x00, 0x00, 0xEB,
  0x11, 0x00, 0x00, 0xEF,
  0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x00, 0x80, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x1A, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0xA0, 0xE1,
  0x0F, 0xC0, 0x4E, 0xE0,
  0x0C, 0xC0, 0x8F, 0xE0,
  0x0F, 0x00, 0x9C, 0xE9,
  0x10, 0xC0, 0x4C, 0xE2,
  0x30, 0x20, 0x9C, 0xE5,
  0x01, 0x0C, 0x12, 0xE3,
  0x34, 0xC0, 0x9C, 0x15,
  0x00, 0xC0, 0x8C, 0x00,
  0x01, 0xC0, 0x8C, 0xE0,
  0x00, 0x00, 0xA0, 0xE3,
  0x00, 0x00, 0x53, 0xE3,
  0x0E, 0xF0, 0xA0, 0xD1,
  0x04, 0x00, 0x8C, 0xE4,
  0x04, 0x30, 0x53, 0xE2,
  0xFB, 0xFF, 0xFF, 0xEA
};


int nrm_dump_aif(char *filename, uint8_t *r, uint32_t len) {
  uint8_t h[AIF_HDR_SZ];
  memcpy(h, nrm_aif_header, AIF_HDR_SZ);
  PUTW(h+AIF_RO_SZ,len+AIF_HDR_SZ);
  FILE *f = fopen(filename, "wb");
  if (!f) return -1;
  fwrite(h, 1, AIF_HDR_SZ, f);  
  fwrite(r, 1, len, f);
  fclose(f);
  return 0;
}

static void b2c(uint8_t *p, int n) {
  int i;
  int j = 0;
  printf("  ");
  for (i = 0; i < n; i++) {
    printf("0x%02X", p[i]);
    if (++j == 4 || i+1 == n) {
      printf(",\n");
      printf("  ");
      j = 0;
    } else {
      printf(", ");
    }
  }
  printf("\n");
}

int main(int argc, char **argv) {
  nrm_opt_t o;
  nrm_opt_init(&o);
  o.fatal = cbFatal;
  o.exists = cbExists;
  o.get = cbGet;


#if 0
  uint32_t fsz;
  uint8_t *p = fileGet(&fsz, argv[2]);
  b2c(p, 0x80);
  exit(-1);
#endif

  //printf("%s,%s\n", argv[1], argv[2]);



#if 1
  if (argc != 3) usage();

  uint8_t *r = nrm_do_file(&o, argv[1]);
  //xd(r, alen(r), 0x8080, 4);
  if (nrm_dump_aif(argv[2], r, alen(r))) {
    fprintf(stderr, "Couldn't creare `%s`\n", argv[2]);
    exit(-1);
  }
  arrfree(r);

#else
  uint8_t *r = nrm_do_cstr(&o, "lbl  mov r3, #123\n  b lbl");
  xd(r, alen(r), 0, 4);
#endif
  return 0;
}


#endif /*NRM_STANDALONE*/
