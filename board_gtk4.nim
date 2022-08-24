# minimal GTK4 test app for the salewski chess engine
# v0.1 2022-AUG-24

import gintro/[gtk4, gdk4, glib, gio, gobject, pango, cairo, pangocairo]
from engine import Board, getBoard, doMove, reply, tag, moveToStr, moveIsValid, Flag, KingValue, KingValueDiv2

const # unicode font chars
  Figures: array[-6 .. 6, string] = ["\xe2\x99\x9A", "\xe2\x99\x9B", "\xe2\x99\x9C", "\xe2\x99\x9D", "\xe2\x99\x9E", "\xe2\x99\x9F", "",
    "\xe2\x99\x99", "\xe2\x99\x98", "\xe2\x99\x97", "\xe2\x99\x96", "\xe2\x99\x95", "\xe2\x99\x94"]

type State = enum
  U0, U1

type
  ChessBoard = ref object of DrawingArea
    gesture: Gesture

proc rot180(b: Board): Board {.inline, noinit.} =
  for i, f in b:
    result[63 - i] = f

var
  tagged: Board
  state: State
  ButtonHandler_ID: culong

proc drawIt(cr: cairo.Context; widget: Widget)  =
  const
    Font = "Sans 64"
  var
    w, h: int
    width = getAllocatedWidth(widget)
    height = getAllocatedHeight(widget)
    w8 = width div 8
    h8 = height div 8
    board = rot180(getBoard())
    layout: pango.Layout
    desc: pango.FontDescription
  for i, t in tagged:
    var h: float
    case t
      of 2:
        h = 0.1
      of 1:
        h = 0.2
      else:
        h = 0
    if i mod 2 != (i div 8) mod 2:
      cr.setSource(0.9, 0.9, 0.9 - h, 1)
    else:
      cr.setSource(1, 1, 1 - h, 1)
    cr.rectangle(float((i mod 8) * w8), float((i div 8) * h8), w8.float, h8.float)
    cr.fill
  layout = createLayout(cr)
  desc = newFontDescription(Font)
  desc.absoluteSize = (min(width, height) div 8 * pango.Scale).float
  layout.setFontDescription(desc)
  for i, f in board:
    if tagged[i] < 0:
      cr.setSource(0, 0, 0, 0.5)
    else:
      cr.setSource(0, 0, 0, 1)
    layout.setText(Figures[f], -1)
    cr.updateLayout(layout)
    layout.getSize(w, h)
    cr.moveTo(float((i mod 8) * w8 + w8 div 2 - w div 2 div pango.Scale), float((i div 8) * h8 + h8 div 2 - h div 2 div pango.Scale))
    cr.showLayout(layout)

proc idleFunc(widget: ChessBoard): bool =
  signalHandlerBlock(widget.gesture, ButtonHandler_ID)
  var msg: string
  var m = reply()
  for i in mitems(tagged): i = 0
  tagged[63 - m.src] = 2
  tagged[63 - m.dst] = 2
  var flag = doMove(m.src, m.dst)
  msg = moveToStr(m.src, m.dst, flag) & " (score: " & $m.score & ")"
  if m.score == KingValue:
    msg &= " Checkmate, game terminated!"
  elif m.score > KingValueDiv2:
    msg &= " Checkmate in " & $((KingValue - m.score) div 2)
  Window(widget.getRootWidget).title = msg
  let cursor = newCursorFromName("default")
  setCursor(widget, cursor)
  widget.queueDraw
  if m.score != KingValue:
    signalHandlerUnblock(widget.gesture, ButtonHandler_ID)
  return SOURCE_REMOVE

proc pressed(gesture: GestureClick; n_press: int; xf, yf: float; widget: ChessBoard) =
  var
    p0 {.global.} = -1
    p1, x, y: int
    window = Window(widget.getRootWidget)
  for i in mitems(tagged): i = 0
  x =  int(xf) div (widget.getAllocatedWidth div 8)
  y = int(yf) div (widget.getAllocatedHeight div 8)
  if state == State.U0:
    p0 = 63 - (x + y * 8)
    for i in tag(p0):
      tagged[63 - i.di] = 1
    tagged[63 - p0] = -1
  elif state == State.U1:
    p1 = 63 - (x + y * 8)
    if p0 == p1 or not moveIsValid(p0, p1):
      if p0 != p1: window.title= "invalid move, ignored."
      tagged[63 - p0] = 0
      tagged[63 - p1] = 0
      queueDraw(widget)
      state = State.U0
      return
    var flag = doMove(p0, p1)
    tagged[63 - p0] = 2
    tagged[63 - p1] = 2
    window.title = moveToStr(p0, p1, flag) & " ... one moment please, reply is:"
    let cursor = newCursorFromName("not-allowed")
    setCursor(widget, cursor)
    idleAdd(idleFunc, widget)
  if state == State.U1:
    state = State.U0
  else:
    inc(state)
  queueDraw(widget)
  return

proc onDrawEvent(widget: DrawingArea; cr: cairo.Context; width, height: int) =
  drawIt(cr, widget)

proc activate(app: Application) =
  let window = newApplicationWindow(app)
  let darea = newDrawingArea(ChessBoard)
  let press: GestureClick = newGestureClick()
  darea.gesture = press
  press.setButton(gdk4.BUTTON_PRIMARY)
  darea.addController(press)
  ButtonHandler_ID = press.connect("pressed", pressed, darea)
  window.setChild(darea)
  darea.setDrawFunc(onDrawEvent)
  window.setDefaultSize(800, 800)
  window.title = "Tiny chess engine demo, GTK4 GUI with Unicode chess pieces, coded from scratch in Nim"
  window.show

proc main =
  let app = newApplication("org.gtk.example")
  app.connect("activate", activate)
  discard run(app)

main()

