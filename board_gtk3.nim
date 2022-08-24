# minimal GTK3 test app for the salewski chess engine
# v0.1 2022-AUG-24

import gintro/[gtk, gdk, glib, gio, gobject, pango, cairo, pangocairo]
from engine import Board, getBoard, doMove, reply, tag, moveToStr, moveIsValid, Flag, KingValue, KingValueDiv2

const # unicode font chars
  Figures: array[-6..6, string] = ["\xe2\x99\x9A", "\xe2\x99\x9B", "\xe2\x99\x9C", "\xe2\x99\x9D", "\xe2\x99\x9E", "\xe2\x99\x9F", "",
    "\xe2\x99\x99", "\xe2\x99\x98", "\xe2\x99\x97", "\xe2\x99\x96", "\xe2\x99\x95", "\xe2\x99\x94"]

type State = enum
  U0, U1

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

proc idleFunc(widget: Widget): bool =
  signalHandlerBlock(widget, ButtonHandler_ID)
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
  gtk.Window(widget.toplevel).title = msg
  let display: Display = gdk.getDefaultDisplay()
  let cursor = newCursorFromName(display, "default")
  setCursor(widget.window, cursor)
  widget.window.invalidateRect()
  if m.score != KingValue:
    signalHandlerUnblock(widget, ButtonHandler_ID)
  return SOURCE_REMOVE

proc onButtonPressEvent(widget: DrawingArea; event: EventButton): bool =
  var
    p0 {.global.} = -1
    p1, x, y: int
    xf, yf: float
  for i in mitems(tagged): i = 0
  doassert(getCoords(event, xf, yf))
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
      if p0 != p1: gtk.Window(widget.toplevel).title= "invalid move, ignored."
      tagged[63 - p0] = 0
      tagged[63 - p1] = 0
      widget.window.invalidateRect()
      state = State.U0
      return gdk.EVENT_PROPAGATE
    var flag = doMove(p0, p1)
    tagged[63 - p0] = 2
    tagged[63 - p1] = 2
    gtk.Window(widget.toplevel).title = moveToStr(p0, p1, flag) & " ... one moment please, reply is:"
    let display: Display = gdk.getDefaultDisplay()
    let cursor = newCursorFromName(display, "not-allowed")
    setCursor(widget.window, cursor)
    idleAdd(idleFunc, widget)
  if state == State.U1:
    state = State.U0
  else:
    inc(state)
  widget.window.invalidateRect()
  return gdk.EVENT_PROPAGATE

proc onDrawEvent(widget: DrawingArea; cr: cairo.Context): bool=
  drawIt(cr, widget)
  return gdk.EVENT_PROPAGATE

proc activate(app: Application) =
  let window = newApplicationWindow(app)
  let darea = newDrawingArea()
  darea.addEvents({EventFlag.buttonPress})
  window.add(darea)
  connect(darea, "draw", onDrawEvent)
  ButtonHandler_ID = connect(darea, "button-press-event", onButtonPressEvent)
  window.position = WindowPosition.center
  window.setDefaultSize(800, 800)
  window.title = "Tiny chess engine demo, GTK3 GUI with Unicode chess pieces, coded from scratch in Nim"
  window.showAll

proc main =
  let app = newApplication("org.gtk.example")
  app.connect("activate", activate)
  discard run(app)

main()

