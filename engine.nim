# The Salewski Chess Engine
# v 0.2 -- 24-AUG-2022
# (C) 2015 - 2032 Dr. Stefan Salewski
# All rights reserved.
#
# Developed from scratch, based on the fundamental ideas of alpha-beta-prunning only.
# The move generation is based on old ideas of precalculation, similar as it was used
# in early GNU-Chess engines in the late 1980's.
#
# TODO:
# create a real GUI
# avoid global variables, make board a parameter of abeta()
# make transposition table size configurable?
# make aggression configurable
# make aggression depending on winning/loosing
# add optional random noise

from std/sequtils import keepIf, anyIt
from std/strutils import toLowerAscii
from std/times import cpuTime, Duration, initDuration, inNanoSeconds
import std/[monotimes, sets, tables, hashes]

var # variables for statistics
  TablePut: int
  TableCol: int
  ABCall: int
  ScoreHashSucc: int
  FloorHashSucc: int
  HashSucc: int
  NullMoveSucc1: int
  NullMoveSucc2: int
  ReEvalSkip: int
  MaxDeltaLen: int

template debugEcho(x: varargs[string, `$`]) =
  when defined(salewskiChessDebug):
    echo(x)

template debugInc(a: var int) =
  when compileOption("assertions"):
    inc(a)

proc resetStatistics =
  TablePut = 0
  TableCol = 0
  ABCall = 0
  ScoreHashSucc = 0
  FloorHashSucc = 0
  HashSucc = 0
  NullMoveSucc1 = 0
  NullMoveSucc2 = 0
  ReEvalSkip = 0
  MaxDeltaLen = 0

proc writeStatistics =
  echo "ABCall: ", ABCall
  echo "ScoreHashSucc: ", ScoreHashSucc
  echo "FloorHashSucc: ", FloorHashSucc
  echo "HashSucc: ", HashSucc
  echo "TablePut: ", TablePut
  echo "TableCol: ", TableCol
  echo "NullMoveSucc1: ", NullMoveSucc1
  echo "NullMoveSucc2: ", NullMoveSucc2
  echo "ReEvalSkip: ", ReEvalSkip
  echo "MaxDeltaLen: ", MaxDeltaLen

var ENDG = false
var CutTime: MonoTime
var StartTime: MonoTime

proc `:=`(x: var int8; v: int): int {.inline, noinit.} =
  x = v.int8
  result = v

type
  BitBuffer192 = array[32, byte]
  # BitBuffer192 = array[24, byte]

const
  MaxDepth = 15 # other values should work as well

const
  VoidID = 0
  PawnID = 1
  KnightID = 2
  BishopID = 3
  RookID = 4
  QueenID = 5
  KingID = 6
  WPawn = PawnID
  WKnight = KnightID
  WBishop = BishopID
  WRook = RookID
  WQueen = QueenID
  WKing = KingID
  BPawn = -PawnID
  BKnight = -KnightID
  BBishop = -BishopID
  BRook = -RookID
  BQueen = -QueenID
  BKing = -KingID

const
  Forward = 8
  Sideward = 1
  S = Forward
  O = Sideward
  N = -S
  W = -O
  NO = N + O
  SO = S + O
  NW = N + W
  SW = S + W

  PawnDirsWhite = [Forward - Sideward, Forward + Sideward, Forward, Forward + Forward]
  BishopDirs = [NO, SO, NW, SW]
  RookDirs = [N, O, S, W]
  KnightDirs = [N + NO, N + NW, W + NW, W + SW, O + NO, O + SO, S + SO, S + SW]
  KingDirs = [N, O, S, W, NO, SO, NW, SW] # KingDirs = BishopDirs + RookDirs

  #Agility = [0, 4, 6, 5, 3, 2, 1] # Pawn .. King, how often is that piece used in smart average game play.

const # we try to keep all the values small to fit in two bytes
  AB_Inf = 32000 # more than the summed value of all pieces
  VoidValue = 0
  PawnValue = 100
  KnightValue = 300
  BishopValue = 300
  RookValue = 500
  QueenValue = 900
  KingValue* = 18000 # more than the summed value of all other pieces
  KingValueDiv2* = KingValue div 2
  SureCheckmate* = KingValue div 2 # still more than the summed value of all other pieces, but less than value of a king

  FigureValue: array[0 .. KingID, int] = [VoidValue, PawnValue, KnightValue, BishopValue, RookValue, QueenValue, KingValue]

const
  Setup = [
    WRook, WKnight, WBishop, WKing, WQueen, WBishop, WKnight, WRook,
    WPawn, WPawn, WPawn, WPawn, WPawn, WPawn, WPawn, WPawn,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    BPawn, BPawn, BPawn, BPawn, BPawn, BPawn, BPawn, BPawn,
    BRook, BKnight, BBishop, BKing, BQueen, BBishop, BKnight, BRook]

# the traditional row and column designators -- B prefix for Board
const BA = 7
const BB = 6
const BC = 5
const BD = 4
const BE = 3
const BF = 2
const BG = 1
const BH = 0
const B1 = 0
const B2 = 1
const B3 = 2
const B4 = 3
const B5 = 4
const B6 = 5
const B7 = 6
const B8 = 7

const PosRange = 0 .. 63

type
  Color = enum Black = -1, White = 1
  ColorIndex = 0 .. 1
  Position = 0 .. 63
  Col = 0 .. 7
  Row = 0 .. 7
  FigureID = int
  Board* = array[Position, FigureID]
  Freedom = array[-KingID .. KingID, array[Position, int]] # VoidID..KingID; Maybe we should call it happyness

const
  WR0 = 0
  WK3 = 3
  WR7 = 7
  BR56 = 56
  BK59 = 59
  BR63 = 63

type
  ChessSquare = range[0 .. 63]
  ChessSquares = set[ChessSquare]
  HasMoved = set[ChessSquare]
  PawnMarch = array[-4 .. 32, ChessSquares]

type
  Gnu = tuple # move precalculation is based on old gnuchess ideas...
    pos: int
    nxtDirIdx: int

  Path = array[Position, array[Position, Gnu]]

const
  IgnoreMarkerLowInt16 = low(int16)
  InvalidScore = low(int16)
  LowestScore = -high(int16) # allows inverting the sign

type
  State = enum
    playing, stalemate, checkmate, noValidMove, canCaptureKing

type
  KK = tuple # source figure, destination figure, source index, destination index
    s: int16 # score
    sf: int8
    df: int8
    si: int8
    di: int8
    evalDepth: int8
    promoteTo: int8 # we may use this to indicate pawn to queen/knight promotion

  KKS = seq[KK]

assert(sizeof(KK) == 8)

type
  Guide1 = tuple # size is 5 byte -- not that nice
    s: int16
    si: int8
    di: int8
    promoteTo: int8

  Guide2 = tuple
    s: int16

  HashLine1 = array[0 .. MaxDepth, Guide1]
  HashLine2 = array[0 .. MaxDepth, Guide2]

  HashResult = tuple
    score: HashLine1 # exact values
    floor: HashLine2 # lower bounds
    kks: KKS
    kksHigh: int
    pri: int
    kingPos: int
    popCnt: int
    control: ChessSquares
    state: State
    inCheck: bool

  TTE = tuple
    res: HashResult
    key: BitBuffer192

template `>=!`(a: var SomeNumber; b: SomeNumber) =
  if a < b: a = b

const
  TTESize = 1024 * 1024 * 2 # must be a power of 2
  TTTry = 5

var tt = newSeq[TTE](TTESize)
var history = initCountTable[BitBuffer192]()

proc clear[T](s: var seq[T]) {.inline.} = s.setLen(0)

template umod8(i: typed): untyped = i and 7

template udiv8(i: typed): untyped = i shr 3

proc odd(i: int): bool {.inline.} = (i and 1) != 0

proc even(i: int): bool {.inline.} = (i and 1) == 0

proc sign(x: int): int {.inline.} =
  (x > 0).int - (x < 0).int

proc sameSign(a, b: int): bool {.inline.} =
  (a xor b) >= 0

proc sqr(i: int): int {.inline.} = i * i

template isAPawn(i: typed): bool = (i == WPawn or i == BPawn) # avoid use of abs()

template isAKing(i: typed): bool = (i == WKing or i == BKing)

proc colIdx(c: Color): ColorIndex {.inline.} = (c.int + 1) shr 1 # div 2

proc isWhite(c: Color): bool {.inline.} = c == White

proc isBlack(c: Color): bool {.inline.} = c == Black

proc oppColor(c: Color): Color {.inline.} = (-c.int).Color

proc col(p: Position): Col {.inline.} = umod8(p) # p mod 8

proc row(p: Position): Row {.inline.} = udiv8(p) # p div 8

proc baseRow(p: Position): bool {.inline.} = p < 8 or p > 55 # row(p) == 0 or row(p) == 7

proc rowsToGo(p: Position; c: Color): int {.inline.} =
  if c == Black: row(p) else: 7 - row(p)

proc getTTE(key: BitBuffer192; res: var HashResult): int {.inline.} =
  assert(tt.len == TTESize)
  let h0 = key.hash
  for i in 0 .. TTTry:
    let h = (h0 +% i) and (TTESize - 1)
    if tt[h].key == key:
      res = tt[h].res
      return h
  return -1

proc putTTE(key: BitBuffer192; res: var HashResult; pri: int; hashPos = -1) {.inline.} =
  assert(tt.len == TTESize)
  debugInc(TablePut)
  if hashPos >= 0:
    res.pri = pri
    tt[hashPos].res = res
    return
  let h0 = key.hash
  for i in 0 .. TTTry:
    let h = (h0 +% i) and (TTESize - 1)
    if tt[h].res.pri < pri:
      res.pri = pri
      tt[h].res = res
      tt[h].key = key
      return
  debugInc(TableCol)

proc genHashResultAllZeroConst: HashLine1 {.inline.} =
  for i in result.low .. result.high:
    result[i].s = InvalidScore

const
  HashResultAllZero = genHashResultAllZeroConst()

proc initHR(hr: var HashResult) {.inline.} =
  hr.score = HashResultAllZero
  for el in mitems(hr.floor):
    el.s = InvalidScore
  hr.state = playing

var # we use global data for now
  board: Board
  hasMoved: HasMoved
  pawnMarch: PawnMarch
  freedom: Freedom
  pawnPath: array[ColorIndex, Path]
  knightPath: Path
  bishopPath: Path
  rookPath: Path
  kingPath: Path
  pjm = -1

const # unicode font chars
  Figures: array[-6 .. 6, string] = ["\xe2\x99\x9A", "\xe2\x99\x9B", "\xe2\x99\x9C", "\xe2\x99\x9D", "\xe2\x99\x9E",
    "\xe2\x99\x9F", "-", "\xe2\x99\x99", "\xe2\x99\x98", "\xe2\x99\x97", "\xe2\x99\x96", "\xe2\x99\x95", "\xe2\x99\x94"]

proc p(b: Board) =
  for i, c in b:
    stdout.write(Figures[c])
    if (i + 1) mod 8 == 0: echo ""

proc isVoidAt(p: Position): bool {.inline.} = board[p] == VoidID

proc isAPawnAt(p: Position): bool {.inline.} = board[p].sqr == PawnID

proc isAKingAt(p: Position): bool {.inline.} = board[p].sqr == KingID * KingID

proc check =
  var p: int
  for i in board:
    if i != VoidID:
      inc(p)
  assert(p <= 32)

proc simpleWriteToBitBuffer(c: Color): BitBuffer192 {.inline.} =
  assert(sizeof(result) == 32)
  var empty: uint8 = KingID
  if c == Black: # encode the color of active player in empty squares
    empty = 15
  for i in countdown(31, 0):
    var a = (board[i] + KingID).byte # a non negative value now, so we can use bit masking
    var b = (board[i + 32] + KingID).byte
    if a == KingID:
      a = empty
    if b == KingID:
      b = empty
    assert(a >= 0 and a <= 15)
    assert(b >= 0 and b <= 15)
    result[i] = (a shl 4) or b

# experimental compression
proc muchFasterWriteToBitBuffer(c: Color): BitBuffer192 {.inline.} =
  const
    L: array[-KingID .. KingID, int8] = [6.int8, 6, 5, 5, 5, 3, 1, 3, 5, 5, 5, 6, 6]
    Code: array[-KingID .. KingID, int8] = [0b111100.int8, 0b111101, 0b11000, 0b11001, 0b11010, 0b100, 0b0, 0b101, 0b11011, 0b11100, 0b11101, 0b111110, 0b111111]
  var collector: array[4 * 8, int8]
  var buf: int64
  var shift = 0
  var bpos = 0
  var bp = 0
  assert(sizeof(result) == 24) # 24 byte size should be enough
  for i in 0 .. 3:
    bp = i
    for j in 0 .. 7:
      let f = board[bp]; inc(bp, 8)
      let newbits: int64 = Code[f]
      buf = buf or (newbits shl shift)
      shift += L[f]
    cast[var int64](addr(collector[bpos])) = buf
    assert bpos + 8 <= 32
    bpos += shift shr 3 # div 8
    var r = shift and (not 7)
    buf = buf shr r
    shift -= r
    bp = i + 4
    for j in 0 .. 7:
      let f = board[bp]; inc(bp, 8)
      let newbits: int64 = Code[f]
      buf = buf or (newbits shl shift)
      shift += L[f]
    cast[var int64](addr(collector[bpos])) = buf
    assert bpos + 8 <= 32
    bpos += shift shr 3 # div 8
    r = shift and (not 7)
    buf = buf shr r
    shift -= r
  result = cast[ptr typeof(result)](addr collector)[]
  assert(result[22] == 0)
  assert(result[23] == 0)
  result[23] = c.byte

proc encodeBoard(c: Color): BitBuffer192 {.inline.} =
  result = simpleWriteToBitBuffer(c)
  # result = muchFasterWriteToBitBuffer(c)

proc offBoard64(dst: int): bool {.inline.} = dst < Board.low or dst > Board.high

# do we not cross the border of the board when figure is moved in a regular way
proc moveIsValid(src: Position; dst: int): bool {.inline.} =
  not offBoard64(dst) and (col(src) - col(dst)).abs <= 1

proc knightMoveIsValid(src: Position; dst: int): bool {.inline.} =
  not offBoard64(dst) and (col(src) - col(dst)).abs <= 2

proc pawnMoveIsValid(c: Color; src, dst: int): bool {.inline.} =
  result = moveIsValid(src, dst)
  if result and (src - dst).abs == 16:
    result = if c.isWhite: row(src) == B2 else: row(src) == B7

proc initRook {.inline.} =
  for src in PosRange:
    var i = 0
    for d in RookDirs:
      var pos = src
      while true:
        var dst = pos + d
        if not moveIsValid(pos, dst): break
        rookPath[src][i].pos = if pos == src: -dst else: dst # mark start pos for this dir
        inc(i)
        pos = dst
    var nxtDirStart = i # index of the last terminal node
    rookPath[src][i].pos = -1 # terminator
    while i > 0:
      dec(i)
      rookPath[src][i].nxtDirIdx = nxtDirStart
      if rookPath[src][i].pos < 0:
        nxtDirStart = i
        rookPath[src][i].pos *= -1

proc initBishop {.inline.} =
  for src in PosRange:
    var i = 0
    for d in BishopDirs:
      var pos = src
      while true:
        var dst = pos + d
        if not moveIsValid(pos, dst): break
        bishopPath[src][i].pos = if pos == src: -dst else: dst
        inc(i)
        pos = dst
    var nxtDirStart = i
    bishopPath[src][i].pos = -1
    freedom[WBishop][src] = (i - 10) * 4 # range -12..12 # abs val is big enough, so exchange of a
    freedom[WQueen][src] = (i - 10) * 4 # range -12..12 # pawn for very good position may occur
    freedom[BBishop][src] = (i - 10) * 4
    freedom[BQueen][src] = (i - 10) * 4
    while i > 0:
      dec(i)
      bishopPath[src][i].nxtDirIdx = nxtDirStart
      if bishopPath[src][i].pos < 0:
        nxtDirStart = i
        bishopPath[src][i].pos *= -1

proc initKnight {.inline.} =
  for src in PosRange:
    var i = 0
    for d in KnightDirs:
      if knightMoveIsValid(src, src + d):
        knightPath[src][i].pos = src + d
        knightPath[src][i].nxtDirIdx = i + 1 # not really needed
        inc(i)
    knightPath[src][i].pos = -1
    freedom[WKnight][src] = (i - 5) * 4 # range -12..12
    freedom[BKnight][src] = (i - 5) * 4

proc initKing {.inline.} =
  for src in PosRange:
    var i = 0
    for d in KingDirs:
      if moveIsValid(src, src + d):
        kingPath[src][i].pos = src + d
        kingPath[src][i].nxtDirIdx = i + 1
        inc(i)
    kingPath[src][i].pos = -1
    if src == 0 or src == 7 or src == 56 or src == 63:
      freedom[WKing][src] = -16
      freedom[BKing][src] = -16

# the first two moves are possible captures or -1 if at the border of the board
proc initPawn(color: Color) =
  for src in PosRange:
    var i = 0
    for d in PawnDirsWhite:
      pawnPath[color.colIdx][src][i].pos =
        if pawnMoveIsValid(color, src, src + d * color.int): src + d * color.int else: -1
      pawnPath[color.colIdx][src][i].nxtDirIdx = i + 1 # not really needed
      inc(i)
    pawnPath[color.colIdx][src][i].pos = -1

# delete seq entries with score s == IgnoreMarkerLowInt16
proc fastDelInvalid(a: var seq[KK]) {.inline.} =
  var i = a.low
  while i < a.len and a[i].s != IgnoreMarkerLowInt16:
    inc(i)
  var j = i # j is the source index
  while j < a.len:
    if a[j].s != IgnoreMarkerLowInt16:
      a[i] = a[j]
      inc(i)
    inc(j)
  a.setLen(a.len - (j - i))

proc ixsort(a: var seq[KK]; high: int = high(a)) {.inline.} =
  for i in 1 .. high:
    let x = a[i]
    var j = i - 1
    while j >= 0 and a[j].s < x.s:
      a[j + 1] = a[j]
      dec(j)
    a[j + 1] = x
  when compileOption("assertions"):
    var h = a
  a.fastDelInvalid # we can delete them, or just skip them
  when compileOption("assertions"):
    keepIf(h, proc(el: KK): bool = el.s != low(int16))
    assert(a == h)

proc isSorted(a: seq[KK]; high: int = high(a)): bool {.inline.} =
  var i = high
  while i > 0 and a[i].s <= a[i - 1].s:
    dec(i)
  return i <= 0

proc isSorted2(a: seq[KK]; low: int = low(a); high: int = high(a)): bool {.inline.} =
  var i = high
  while i > low and a[i].s <= a[i - 1].s:
    dec(i)
  return i <= low

proc capture(kk: KK): bool {.inline.} = kk.sf * kk.df < 0

proc valid(kk: KK): bool {.inline.} = kk.sf * kk.df <= 0

# caution, this is used for inCheck() test too.
proc wanted(kk: KK): bool {.inline.} = kk.sf * kk.df < (kk.s > 0).int

proc walkRook(kk: KK; s: var KKS) {.inline.} =
  var i: int
  var kk = kk
  while (kk.di := rookPath[kk.si][i].pos) >= 0:
    if (kk.df := board[kk.di]) == 0:
      inc(i)
    else:
      i = rookPath[kk.si][i].nxtDirIdx
    if wanted(kk): s.add kk

proc walkBishop(kk: KK; s: var KKS) {.inline.} =
  var i: int
  var kk = kk
  while (kk.di := bishopPath[kk.si][i].pos) >= 0:
    if (kk.df := board[kk.di]) == 0:
      inc(i)
    else:
      i = bishopPath[kk.si][i].nxtDirIdx
    if wanted(kk): s.add kk

proc walkKing(kk: KK; s: var KKS) {.inline.} =
  var kk = kk
  for i in 0 .. 7:
    if (kk.di := kingPath[kk.si][i].pos) < 0: break
    kk.df = board[kk.di].int8
    if wanted(kk):
      s.add kk

proc walkKnight(kk: KK; s: var KKS) {.inline.} =
  var kk = kk
  for i in 0 .. 7:
    if (kk.di := knightPath[kk.si][i].pos) < 0: break
    kk.df = board[kk.di].int8
    if wanted(kk):
      s.add kk

# now we generate all possible ep captures -- before performing the actual move, we have to check eppos value
proc walkPawn(kk: KK; s: var KKS; eppos = -1) {.inline.} =
  var kk = kk
  let colIdx = (kk.sf + 1) div 2
  for i in 0 .. 1:
    if (kk.di := pawnPath[colIdx][kk.si][i].pos) >= 0:
      kk.df = board[kk.di].int8
      var c: Color
      if kk.sf == WPawn: c = White else: c = Black
      assert c == Color(kk.sf)
      if rowsToGo(kk.si, c) == 3 and kk.df == VoidID and board[kk.di + kk.sf * 8] == -kk.sf: # possible ep capture
        s.add kk
      elif capture(kk):
        if baseRow(kk.di):
          kk.promoteTo = kk.sf * KnightID
          s.add kk
          kk.promoteTo = kk.sf * QueenID
          s.add kk
        else:
          s.add kk
  if kk.s >= 0:
    for i in 2 .. 3:
      if (kk.di := pawnPath[colIdx][kk.si][i].pos) >= 0:
        if (kk.df := board[kk.di]) == 0:
          if baseRow(kk.di):
            kk.promoteTo = kk.sf * KnightID
            s.add kk
            kk.promoteTo = kk.sf * QueenID
            s.add kk
          else:
            s.add kk
        else: break

type
  Move = tuple
    src: int
    dst: int
    score: int
    control: ChessSquares
    promoteTo: int
    state: State

# result is for White
proc plainEvaluateBoard: int {.inline.} =
  for p, f in board: # if f != VoidID -- does not increase performance
    result += (FigureValue[f.abs] + freedom[f][p]) * sign(f)

discard """
https://chessprogramming.wikispaces.com/Alpha-Beta
int alphaBeta( int alpha, int beta, int depthleft ) {
   if( depthleft == 0 ) return quiesce( alpha, beta );
   for ( all moves) {
      score = -alphaBeta( -beta, -alpha, depthleft - 1 );
      if( score >= beta )
         return beta; // fail hard beta-cutoff
      if( score > alpha )
         alpha = score; // alpha acts like max in MiniMax
   }
   return alpha;
}
"""
proc inCheck(si: int; col: Color): bool =
  var
    kk: KK
    s = newSeqOfCap[KK](8)
  kk.si = si.int8
  kk.sf = sign(col.int).int8
  assert kk.sf == col.int
  kk.s = -1 # only captures
  s.clear
  walkBishop(kk, s)
  if anyIt(s, it.df.abs == BishopID or it.df.abs == QueenID): return true
  s.clear
  walkRook(kk, s)
  if anyIt(s, it.df.abs == RookID or it.df.abs == QueenID): return true
  s.clear
  walkKnight(kk, s)
  if anyIt(s, it.df.abs == KnightID): return true
  s.clear
  walkPawn(kk, s)
  if anyIt(s, it.df.abs == PawnID): return true
  s.clear
  walkKing(kk, s)
  return anyIt(s, it.df.abs == KingID)

proc kingPos(c: Color): Position {.inline.} =
  let k = KingID * c.int
  for i, f in board:
    if f == k:
      return i

#const QD0 = 0
const
  VRatio = 8

  SelectedExtend = false # depth extend based on source and destination pieces
  CaptureExtend = false # depth extend for captures
  EqualCaptureExtend = false # depth extend for captures of pieces with similar value
  LargerCaptureExtend = false # i.e. pawn captures knight
  PawnMarchExtend = false # successive pawn moves of a single pawn, to gain nconversion to queen
  CheckExtend = false # depth extend when we are in check (only supported for first 3 plys)
  NoExtendsAtAll = true # avoid depth entends for now

proc m2Str*(si, di: Position): string

# for endgame, to get a correct value for "moves to mate"
# "moves to mate" is calculated from score and value of cup counter
proc `+-?`(a, b: int): int {.inline.} =
  if a > KingValueDiv2:
    result = a + b
  elif a < -KingValueDiv2:
    result = a - b
  else:
    result = a

# color: White or Black, color of active player
# vdepth: search depth, as a multiply of VRatio
# vdepth is the virtual search depth, it is a multiple of real search depth to allow a more
# fine grained search depth extension.
# vdepth starts with a multiple of VRatio (n * VRation + VRatio div 2), and generally decreases by
# VRatio for each recursive call of abeta(). For special very important moves it may decrease less,
# i.e. if we are in check. Real depth is always vdepth div VRatio.
# vdepth may even increase in rare cases!
# cup: plain recursion depth counter counting upwards starting at zero, depth indication
# alpha0, beta: the search window for prunning
# oldListLen: estimation of the number of moves that the opponent can do
# eppos: if not -1, it indicates the position of the en pasant square
# for en passant capture, i.e. after pawn move e2 e4 eppos is e3.
# Result: Currently we return a value object. We may change that to a reference type, that
# would allow changing moves and displaying whole move sequences. Maybe a bit slower.
# Board: Currently we use a global board variable, but we may change that to pass
# the board as first parameter as in OOP style. By using a non var board parameter,
# we can avoid reseting the state -- we have to test the performace.
#
proc abeta(color: Color; vdepth, cup, alpha0, beta, oldListlen, eppos: int): Move =
  assert(alpha0 < beta)
  debugInc(ABCall)
  assert(MaxDepth == 15)
  assert(VRatio == 8)
  var depth0 = min(max(vdepth div VRatio, 0), MaxDepth) # starting at depth0 == 0 we do only captures
  assert(cup >= 0)
  assert(depth0 >= 0)
  assert(sizeof(KK) == 8)
  assert(oldListLen >= 0)
  assert(eppos in -1 .. 63)

  var
    hashRes: HashResult
    sdi, ddi: array[7, int]
    neppos: int
    vdepthInc: int
    evalCnt: int
    alpha: int = alpha0
    validMoveFound: bool # = false

  when compileOption("assertions"):
    var back = board # test board integrity

  result.state = noValidMove
  let vdepth = vdepth - VRatio
  let encodedBoard = encodeBoard(color)
  let hashPos = getTTE(encodedBoard, hashRes)
  if hashPos >= 0: # we have the list of moves, and maybe the exact score, or a possible beta cutoff
    debugInc(HashSucc)
    for i in countdown(MaxDepth, depth0):
      if hashRes.score[i].s != InvalidScore: # we have the exact score, so return it
        if i == depth0 or hashRes.score[i].s.abs < KingValueDiv2 or hashRes.score[i].s.abs >= KingValue:
          # use of deeper knowledge in endgame can give wrong moves to mate reports
          # or generate repeated moves.
          result.score = hashRes.score[i].s +-? -cup
          result.src = hashRes.score[i].si # these details are currently only needed for cup == 0
          result.dst = hashRes.score[i].di
          result.promoteTo = hashRes.score[i].promoteTo
          result.state = hashRes.state
          debugInc(ScoreHashSucc)
        elif hashRes.score[i].s +-? -cup >= beta: # at least we can use the score for a beta cutoff
          result.score = beta
        return
      if hashRes.floor[i].s +-? -cup >= beta: # a beta cutoff
        result.score = beta
        debugInc(FloorHashSucc)
        return
    tt[hashPos].res.pri >=! depth0 # avoid that this entry in tt is overwritten by recursive abeta() calls!
  else: # we have to create the move list
    initHR(hashRes)

  when false: # possible, but makes not much sense
    if hashPos < 0 and depth0 > 3: # fast movelist ordering
      discard abeta(color, vdepth - 2 * VRatio, cup, alpha0, beta, oldListLen, -1)
      hashPos = getTTE(encodedBoard, hashRes)

  var evaluation: int = LowestScore
  if depth0 == 0: # null move estimation for quiescence search
    evaluation = plainEvaluateBoard() * color.int
    if evaluation >= beta + 64: # +64 for max. difference in number of possible moves of both sides
      result.score = beta
      debugInc(NullMoveSucc1)
      return

  if hashPos < 0: # generate the move list, including possible castlings and en passant moves
    var s = newSeqOfCap[KK](63)
    var kk: KK
    kk.s = 1 # generate all moves, not only capures
    for si, sf in board: # source index, source figure
      if sf != VoidID:
        inc(hashRes.popCnt)
      if sf * color.int <= 0:
        continue
      kk.si = si
      kk.sf = sf.int8
      case sf.abs:
        of PawnID: walkPawn(kk, s)
        of KnightID: walkKnight(kk, s)
        of BishopID: walkBishop(kk, s)
        of RookID: walkRook(kk, s)
        of QueenID: walkBishop(kk, s); walkRook(kk, s)
        of KingID: walkKing(kk, s); hashRes.kingpos = kk.si
        else: discard

    assert(hashRes.popCnt <= 32) # for regular games
    if cup < 3:
      hashRes.inCheck = inCheck(hashRes.kingpos, color) # this field is optional information

    for el in s:
      if not isAPawn(el.sf) or (el.si - el.di).odd:
        hashRes.control.incl(el.di) # attacked positions

    kk.df = VoidID # for all 4 types of castling
    if color == White and board[3] == WKing: # and 3 notin hasMoved and 0 notin hasMoved:
      if board[0] == WRook and board[1] == VoidID and board[2] == VoidID:
        kk.di = 1
        kk.si = 3
        kk.sf = WKing
        s.add(kk)
      if board[7] == WRook and board[4] == VoidID and board[5] == VoidID and board[6] == VoidID:
        kk.di = 5
        kk.si = 3
        kk.sf = WKing
        s.add(kk)

    if color == Black and board[59] == BKing: # and 59 notin hasMoved and 56 notin hasMoved:
      if board[56] == BRook and board[57] == VoidID and board[58] == VoidID:
        kk.di = 57
        kk.si = 59
        kk.sf = BKing
        s.add(kk)
      if board[63] == BRook and board[60] == VoidID and board[61] == VoidID and board[62] == VoidID:
        kk.di = 61
        kk.si = 59
        kk.sf = BKing
        s.add(kk)

    for el in mitems(s): # guessed ratings of the moves
      el.evalDepth = -1 # mark as unevaluated
      when compileOption("assertions"):
        if baseRow(el.di) and isAPawn(el.sf):
          assert(el.promoteTo.abs in [KnightID, QueenID])
        else:
          assert(el.promoteTo == 0)
      el.s = (FigureValue[el.promoteTo.abs] + FigureValue[el.df.abs] + freedom[el.sf][el.di] - freedom[el.sf][el.si]).int16
    s.ixsort
    assert(s.isSorted)
    hashRes.kks = s

  if depth0 == 0: # # more detailed null move estimation for quiescence search
    evaluation += (hashRes.kks.len - oldListlen) # we may do a more fine grained board control evaluation?
    when compileOption("assertions"):
      MaxDeltaLen >=! (hashRes.kks.len - oldListlen).abs
    if evaluation >= beta:
      result.score = beta
      debugInc(NullMoveSucc2)
      return
    alpha >=! evaluation

  result.control = hashRes.control
  hashRes.kksHigh = -1 # the number of newly evaluated positions, we sort only this range.

  result.score = evaluation # LowestScore for depth0 > 0
  assert(depth0 == 0 or result.score == LowestScore)
  assert(hashRes.score[depth0].s == InvalidScore)

  for el in mitems(hashRes.kks):
    if el.s == IgnoreMarkerLowInt16:
      assert(false) # we actually delete invalid entries, so nothing to skip
      continue
    assert(el.s != IgnoreMarkerLowInt16)
    assert(board[el.si] != VoidID)
    hashRes.kksHigh += 1 # the number of up to date positions, which we have to sort later
    if depth0 == 0 and el.df == VoidID: # skip non-captures in quiescence search
      continue
    if cup == 0:
      debugEcho ":", (getMonoTime() - StartTime).inNanoSeconds.float / 1e9 , " ", hashRes.kks.len
      if evalCnt > 1 and getMonoTime() > CutTime:
        debugEcho "break", evalCnt, " ", hashRes.kksHigh
        break

    var m: Move
    if el.evalDepth >= depth0:# this move was already evaluated, but was not good enough, no beta cutoff
      validMoveFound = true # list contains only valid moves, as we delete or skip the invalid ones
      debugInc(ReEvalSkip)
      m.score = (el.s +-? -cup).int16
      assert(m.score < beta)
    else: # do new evaluation
      evalCnt += 1 # number of newly evaluated moves
      let isAPawnelsf = isAPawn(el.sf)
      let isAKingelsf = isAKing(el.sf)
      let elsieldi = el.si - el.di
      let littleCastling = isAKingelsf and elsieldi == 2 # castling candidates
      let bigCastling = isAKingelsf and elsieldi == -3
      let enPassant = isAPawnelsf and el.df == VoidID and elsieldi.odd # move is an eP capture candidate

      if littleCastling and (el.si in hasMoved or el.si - 3 in hasMoved): # we always generate castling moves but
        continue

      if bigCastling and (el.si in hasMoved or el.si + 4 in hasMoved): # skip them when not allowed.
        continue

      if enPassant and el.di != eppos: # skip en pasant move
        continue

      # does such extents make any sense? We can do it, but we have to be careful and test.
      when SelectedExtend:
        if not ENDG: # makes no sense in endgame
          sdi = [0, 0, 0, 0, 0, 0, 2] # source figure depth increase # increase depth when king is moved
          ddi = [0, 0, 2, 2, 2, 2, 0] # destination figure depth increase # increase depth for capture

      when CaptureExtend or EqualCaptureExtend or LargerCaptureExtend:
        if el.df != VoidID:
          when CaptureExtend:
            vdepthInc = 2
          when EqualCaptureExtend or LargerCaptureExtend:
            let immediateGain = FigureValue[el.df.abs] - FigureValue[el.sf.abs]
            when LargerCaptureExtend:
              if immediateGain > PawnValue:
                vdepthInc = 4
            when EqualCapureExtend:
              if immediateGain.abs < 10:
                vdepthInc = 2

      when PawnMarchExtend:
        if isAPawnelsf and hashRes.popCnt < 32 - 6:
          let rowsToGo = rowsToGo(el.si, color)
          pawnMarch[cup].incl(el.di)
          if el.si in pawnMarch[cup - 2]: # pawn just moved to this location
            assert(rowsToGo < 7)
            if rowsToGo == 6 and (elsieldi == 8 or elsieldi == -8):
              discard # last was one step from base row
            elif hashRes.popCnt < 32 - 12:
              vdepthInc = 4
            else:
              vdepthInc = 2

      when CheckExtend:
        if hashRes.inCheck:
          vdepthInc = 2

      when NoExtendsAtAll:
        vdepthInc = 0

      if ENDG: # better no extents in endgame
        vdepthInc = 0

      if isAKing(el.df):
        result.state = canCaptureKing # the other result fields are not really used/needed
        result.score = KingValue# + 1 # or high(int16)
        hashRes.state = canCaptureKing
        hashRes.score[MaxDepth].s = result.score.int16 # MaxDepth, as it is the final score
        assert(hashPos < 0) # once stored, we just retrieve it
        putTTE(encodedBoard, hashRes, depth0, hashPos) # store this for a fast return next time
        return

      board[el.si] = VoidID # the basic movement
      board[el.di] = el.sf

      let hmback = hasMoved # backup
      hasMoved.incl(el.si) # may be a king or rook move, so castling is forbidden
      if littleCastling: # small rochade
        board[el.di + 1] = board[el.di - 1]
        board[el.di - 1] = VoidID
        hasMoved.incl(el.di - 1)
      elif bigCastling: # big rochade
        board[el.di - 1] = board[el.di + 2]
        board[el.di + 2] = VoidID
        hasMoved.incl(el.di + 2)
      elif enPassant:
        board[el.di - color.int * 8] = VoidID
      elif isAPawnelsf and baseRow(el.di):
        board[el.di] = el.promoteTo

      let pawnJump = isAPawnelsf and (elsieldi == 16 or elsieldi == -16)
      if pawnJump:
        neppos = (el.si + el.di) /% 2 # fast unsigned div
      else:
        neppos = -1

      # if isAPawnelsf or el.df != VoidID: # handle draw by repetitions. As rep. test is a bit expensive, we do not
      if cup > 5 or hashRes.popCnt > 20 or isAPawnelsf or el.df != VoidID: # test dense populated board or deeper plys.
        m = abeta(color.oppColor, vdepth + vdepthInc + sdi[el.sf.abs] + ddi[el.df.abs], cup + 1, -beta, -alpha, hashRes.kks.len, neppos)
      else: # deal with repetive positions
        let newState = encodeBoard(color) # this is the new board state after a piece is moved
        if history[newState] >= 2: # this will be the third repetition, so draw can be requested
          m.score = 0 # draw
        else:
          history.inc(newState)
          m = abeta(color.oppColor, vdepth + vdepthInc + sdi[el.sf.abs] + ddi[el.df.abs], cup + 1, -beta, -alpha, hashRes.kks.len, neppos)
          history.inc(newState, -1)

      m.score *= -1
      if m.state == canCaptureKing:
        el.s = IgnoreMarkerLowInt16 # mark for deletion
      else:
        validMoveFound = true
        el.s = (m.score +-? cup).int16
        if m.score > alpha and m.score < beta: # otherwise our abeta() call did a beta cutoff, so we have no real score
          el.evalDepth = depth0.int8
        else:
          el.evalDepth = -1 # mark as unevaluated

      hasMoved = hmback # reset board state
      pawnMarch[cup].excl(el.di)
      board[el.di] = el.df
      board[el.si] = el.sf
      if enPassant:
        board[el.di - color.int * 8] = -el.sf

      if littleCastling: # small rochade
        board[el.di - 1] = board[el.di + 1]
        board[el.di + 1] = VoidID
        # hasMoved.excl(el.di - 1) # use backup instead
        if m.control * {el.si.ChessSquare, (el.si - 1).ChessSquare, el.di.ChessSquare} != {}:
          el.s = IgnoreMarkerLowInt16 # mark for deletion or ignore
          continue # was illegal, so ignore
      elif bigCastling: # big rochade
        board[el.di + 2] = board[el.di - 1]
        board[el.di - 1] = VoidID
        # hasMoved.excl(el.di + 2)
        if m.control * {el.si.ChessSquare, (el.si + 1).ChessSquare, el.di.ChessSquare} != {}:
          el.s = IgnoreMarkerLowInt16
          continue # was illegal, so ignore

      if m.score >= beta:
        # assert(isSorted2(hashRes.kks, hashRes.kksHigh + 1, hashRes.kks.high)) # no, can be more than one partition
        hashRes.kks.ixsort(hashRes.kksHigh)
        assert(hashRes.floor[depth0].s < m.score) # always true, due to beta cutoff test at top of proc
        hashRes.floor[depth0].s = (m.score +-? cup).int16
        putTTE(encodedBoard, hashRes, depth0, hashpos)
        result.score = beta
        return

    alpha >=! m.score
    if m.score > result.score:
      result.score = m.score
      result.src = el.si
      result.dst = el.di
      result.promoteTo = el.promoteTo

  if depth0 > 0 and not validMoveFound:
    if inCheck(hashRes.kingpos, color):
      result.state = checkMate
      result.score = -KingValue + cup - 1
    else:
      result.score = 0
      result.state = staleMate
  else:
    result.state = playing

  assert(hashRes.score[depth0].s == InvalidScore)
  #assert(hashRes.kksHigh == hashRes.kks.high) # not always, due to CutTime break for cup == 0
  hashRes.kks.ixsort(hashRes.kksHigh)
  if result.score > alpha0 or result.state == checkMate or result.state == staleMate: # otherwise our abeta() call did a beta cutoff, so we have no real score
    assert(depth0 == 0 or alpha > alpha0 or result.state == checkMate or result.state == staleMate)
    hashRes.score[depth0].s = (result.score +-? cup).int16
    hashRes.score[depth0].si = result.src.int8
    hashRes.score[depth0].di = result.dst.int8
  hashRes.state = result.state
  putTTE(encodedBoard, hashRes, depth0, hashPos)
  when compileOption("assertions"):
    assert(back == board)

proc str2BoardPos(s: string): Position =
  assert(s.len == 2)
  let s0 = s[0].toLowerAscii
  let s1 = s[1]
  assert(s0 in {'a' .. 'h'})
  assert(s1 in {'1' .. '8'})
  let c = 7 - (s0.ord - 'a'.ord)
  let r = s1.ord - '1'.ord
  result = c + r * 8

proc checkMateIn(score: int): int =
  if score > KingValueDiv2:
    KingValue - score
  else:
    -1

var debugList = newSeq[string]()

proc alphabeta(color: Color; depth: int; epPos: int): Move =
  CutTime = getMonoTime() + initDuration(seconds = 1, milliseconds = 700)
  StartTime = getMonoTime()
  resetStatistics()
  result = abeta(color, depth * VRatio + VRatio div 2, 0, -AB_Inf, AB_Inf, 20, epPos)
  when defined(salewskiChessDebug):
    writeStatistics()
    echo result

type Flag* {.pure.} = enum
  plain, capture, ep, promotion, procap

proc moveToStr*(si, di: Position; flag: Flag): string

proc doMove*(p0, p1: Position; silent = false): Flag =
  if not isVoidAt(p1): result = Flag.capture
  if not silent:
    hasMoved.incl(p0)
    pjm = -1
    if isAPawnAt(p0) and (p0 - p1).abs == 16:
      pjm = (p0 + p1) div 2
  if (p1 - p0).abs == 2 and isAKingAt(p0):
    if col(p1) == 1:
      board[p0 - 1] = board[p0 - 3]
      board[p0 - 3] = VoidID
    else:
      board[p0 + 1] = board[p0 + 4]
      board[p0 + 4] = VoidID
  elif baseRow(p1) and isAPawnAt(p0):
    board[p0] *= QueenID
    result = if result == Flag.capture: Flag.procap else: Flag.promotion
  elif isAPawnAt(p0) and isVoidAt(p1) and (p1 - p0).odd:
    result = Flag.ep
    board[p1 - board[p0] * 8] = VoidID
  board[p1] = board[p0]
  board[p0] = VoidID
  if not silent:
    if isAPawnAt(p1) or result != Flag.plain:
      history = initCountTable[BitBuffer192]()
    else:
      let newState = encodeBoard(sign(board[p1]).Color)
      history.inc(newState)
  when defined(salewskiChessDebug):
    if not silent:
      debugList.add(moveToStr(p0, p1, result))
      echo "--"
      for el in debugList: echo el

proc tag*(si: int): KKS =
  var kk: KK
  kk.sf = board[si].int8
  let color = sign(kk.sf).Color
  kk.si = si.int8
  kk.s = 1 # generate all moves, not only captures
  var s = newSeqOfCap[KK](32)
  case kk.sf.abs:
    of PawnID: walkPawn(kk, s)
    of KnightID: walkKnight(kk, s)
    of BishopID: walkBishop(kk, s)
    of RookID: walkRook(kk, s)
    of QueenID: walkBishop(kk, s); walkRook(kk, s)
    of KingID: walkKing(kk, s)
    else: discard
  if si == 3 or si == 3 + 7 * 8:
    const # king, void, void, void, rook, kingDelta, rookDelta
      Q = [[3, 2, 1, 1, 0, -2, 2], [3, 4, 5, 6, 7, 2, -3]]
    let
      k = WKing * color.int
      r = WRook * color.int
    for i in 0..1: # castlings both sides
      var q = Q[i]
      if color == Black:
        for j in 0..4:
          q[j] += 7 * 8
      if board[q[0]] == k and board[q[1]] == 0 and board[q[2]] == 0 and board[q[3]] == 0 and board[q[4]] == r and
        q[0] notin hasMoved and q[4] notin hasMoved:
        if not (inCheck(q[1], color) or inCheck(q[2], color)):
          kk.di = (q[0] + q[5]).int8
          s.add kk
  let backup = board
  for el in s.mitems:
    discard doMove(si, el.di, silent = true)
    if inCheck(kingPos(color), color): el.s = 0
    board = backup
  keepIf(s, proc(el: KK): bool = el.s != 0)
  return s

proc moveIsValid*(si, di: int): bool {.inline.} =
  sign(board[si]).Color == White and anyIt(tag(si), it.di == di)

const
  FigStr = ["  ", "  ", "N_", "B_", "R_", "Q_", "K_"]

proc colStr(c: Col): char {.inline.} = char('H'.int - c.int)

proc rowStr(c: Col): char {.inline.} = char('1'.int + c.int)

proc getBoard*: Board {.inline.} =
  result = board

# call this after doMove()
proc moveToStr*(si, di: Position; flag: Flag): string =
  when true: # moveIsValid(si, di): # avoid unnecessary expensive test
    if board[di].abs == KingID and (di - si).abs == 2:
      result = if col(di) == 1: "o-o" else: "o-o-o"
    else:
      result = FigStr[board[di].abs]
      result.add(colStr(col(si)))
      result.add(rowStr(row(si)))
      result.add(if flag == Flag.capture or flag == Flag.procap: 'x' else: '-')
      result.add(colStr(col(di)))
      result.add(rowStr(row(di)))
      if flag == Flag.ep or flag == Flag.procap:
        result.add(" e.p.")
    if inCheck(kingPos((-sign(board[di])).Color), (-sign(board[di])).Color):
      result.add(" +")
  else:
    result = "invalid move"

proc m2Str*(si, di: Position): string =
  var flag: Flag
  if not isVoidAt(di):
    flag = Flag.capture
  if baseRow(di) and isAPawnAt(si):
    flag = if flag == Flag.capture: Flag.procap else: Flag.promotion
  elif isAPawnAt(si) and isVoidAt(di) and (di - si).odd:
    flag = Flag.ep
  when true: # moveIsValid(si, di): # avoid unnecessary expensive test
    if board[di].abs == KingID and (di - si).abs == 2:
      result = if col(di) == 1: "o-o" else: "o-o-o"
    else:
      result = FigStr[board[si].abs]
      result.add(colStr(col(si)))
      result.add(rowStr(row(si)))
      result.add(if flag == Flag.capture or flag == Flag.procap: 'x' else: '-')
      result.add(colStr(col(di)))
      result.add(rowStr(row(di)))
      if flag == Flag.ep or flag == Flag.procap:
        result.add(" e.p.")
    # works only after doing the move
    #if inCheck(kingPos((-sign(board[di])).Color), (-sign(board[di])).Color):
    #  result.add(" +")
  else:
    result = "invalid move"

# Endgame = no pawns, weaker side has no queen, no rook and not two bishops.
proc setupEndgame: bool {.inline.} =
  var
    p: array[-KingID..KingID, int]
    h: array[-1..1, int] # total number of pieces
    b: array[-1..1, int] # single bishop position
  for i, f in board:
    p[f] += 1
    h[sign(f)] += 1
    if f.abs == BishopID: b[sign(f)] = i
  if p[WPawn] + p[BPawn] > 0: return
  if h[-1] > 3 or h[1] > 3: return
  for i in BKing .. WKing:
    for j in PosRange: freedom[i][j] = 0
  for s in [-1, 1]: # black, white -- set the hunting matrix for opposite king
    if p[QueenID * s] + p[RookID * s] == 0 and p[BishopID * s] + p[KnightID * s] < 2:
      continue # of course with only two knights it is hard, but one may try.
    let oppKing = -s * KingID
    for i in PosRange:
      if p[QueenID * s] + p[RookID * s] == 0 and p[BishopID * s] < 2: # chase to selected corner
        if col(b[s]).odd != row(b[s]).odd:
          freedom[oppKing][i] = -(row(i) - col(i)).sqr # sqr may be better than abs when both sites are
        else: # struggling, i.e. K + B + B vs K + B
          freedom[oppKing][i] = -(row(i) + col(i) - 7).sqr
      else: # chase to border and/or arbitrary corner
        freedom[oppKing][i] = -((2 * row(i) - 7).abs + (2 * col(i) - 7).abs div 2).sqr
    #if s == -1: echo "White King" else: echo "Black King"
    #for i, f in board:
    #  if i mod 8 == 0: echo("")
    #  write(stdout, $freedom[oppKing][i]); write(stdout, " ");
    #echo ""
  return true

proc reply*: Move =
  const
    Time = 1.3 # seconds
  var
    hashRes: HashResult
    alpha = -AB_Inf
    beta = AB_inf
    depth = 0

  let startTime = cpuTime()
  if setupEndgame():
    if not ENDG:
      ENDG = true
  debugEcho GC_getStatistics()
  for el in mitems(tt): el.res.pri = low(int)
  while depth < MaxDepth:
    inc(depth)
    debugEcho "Depth: ", depth
    result = alphabeta(Black, depth, pjm)
    debugEcho result.score
    debugEcho "score: ", result.score, "(", result.src, "-", result.dst, ")"
    if result.score.abs > SureCheckmate:
      break
    if cpuTime() - startTime > Time:
      debugEcho "Time: ", cpuTime() - startTime
      break

proc setBoard(f: FigureID; c, r: Position) = board[c + r * 8] = f

proc setBoard(f: FigureID; s: string) =
  assert(s.len == 2)
  assert(f.abs <= KingID)
  let s0 = s[0].toLowerAscii
  let s1 = s[1]
  assert(s0 in {'a' .. 'h'})
  assert(s1 in {'1' .. '8'})
  let c = 7 - (s0.ord - 'a'.ord)
  let r = s1.ord - '1'.ord
  board[c + r * 8] = f

proc print =
  for p, f in board:
    if p mod 8 == 0:
      echo ""
    if f >= 0:
      write(stdout, ' ')
    write(stdout, $f & "|" & $p & ' ')
    if p < 10: echo ' '
  echo ""

initPawn(White)
initPawn(Black)
initBishop()
initKnight()
initKing()
initRook()
board = Setup

when defined(salewskiChessDebug):
  print()

#setBoard(BKing, BC, B4)
#setBoard(WKing, BD, B5)
#setBoard(BBishop, BD, B4)
#setBoard(BKnight, BD, B3)
#setBoard(WKnight, BA, B2)
#setBoard(WBishop, BG, B3)

when false:
  setBoard(BKing, BC, B3)
  setBoard(WKing, BA, B1)
  setBoard(BBishop, BC, B2)
  setBoard(BPawn, BE, B6)

when false:
  setBoard(BKing, BC, B3)
  setBoard(WKing, BA, B1)
  setBoard(BKnight, BC, B2)
  setBoard(BBishop, BE, B5)
  
when false:
  setBoard(BKing, BC, B3)
  setBoard(WKing, BA, B1)
  setBoard(BBishop, BC, B2)
  setBoard(BBishop, BE, B5)

when false:
  setBoard(BKing, BC, B4)
  setBoard(WKing, BC, B3)
  setBoard(BKnight, BD, B4)
  setBoard(BBishop, BD, B3)

when false:
  setBoard(BKing, BD, B3)
  setBoard(WKing, BD, B5)
  #setBoard(BQueen, BE, B3)
  setBoard(BQueen, "E3")
#setBoard(BBishop, BD, B3)

when false:
  setBoard(BKing, BD, B5)
  setBoard(WKing, BC, B7)
  setBoard(BQueen, "E8")

when false:
  setBoard(BKing, BC, B4)
  setBoard(WKing, BD, B6)
  setBoard(BQueen, "E8")

when false:
  setBoard(BKing, BC, B4)
  setBoard(WKing, BC, B7)
  #setBoard(BQueen, BE, B3)
  setBoard(BQueen, "E3")

when false:
  setBoard(BKing, BD, B3)
  setBoard(WKing, BD, B5)
  setBoard(BQueen, "E3")

