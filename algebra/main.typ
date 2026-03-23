#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/theorion:0.4.1": *
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/biceps:0.0.1": *
#import "@preview/quick-maths:0.2.1": shorthands
#import "@preview/wordometer:0.1.5": word-count, total-words
#import "@preview/cetz:0.4.2": draw

#show: word-count

#show: shorthands.with(
  ($|-$, math.tack),
  ($|=$, math.tack.double),
)
#import cosmos.rainbow: *
#show: show-theorion
// #set par.line(numbering: it => text(fill: gray, [#it]))
#set page(numbering: "1 of 1")
#set heading(numbering: "1.1.1.1")
#set math.equation(numbering: "(1)")
#show link: this => underline(text(this, fill: blue))

#set page(width: 8.5in, height: 11in)
// #set page(width: 8.5in, height: 205in)
// #set page(margin: (right: 3.0in))

#let opp(x) = $#x^sans("op")$
#let fwd = $sans("fwd")$
#let bwd = $sans("bwd")$
#let Set = $bold("Set")$
#let FinSet = $bold("FinSet")$
#let Hom = $bold("Hom")$
#let CC = $cal(C)$
#let PP = $cal(P)$
#let natrec = $sans("natrec")$
#let id = $sans("id")$
#let rev = $sans("rev")$
#let inl = $sans("inl")$
#let inr = $sans("inr")$
#let inv = $sans("inv")$
#let Ob = $sans("Ob")$
#let head = $sans("head")$
#let Prop = $sans("Prop")$
#let tail = $sans("tail")$
#let fst = $sans("fst")$
#let snd = $sans("snd")$
#let KK = $bold(sans("K"))$
#let DA = $sans("DA")$
#let oDA = $sans("oDA")$
#let mDA = $sans("mDA")$
#let rDA = $sans("rDA")$
#let Init = $sans("Init")$
#let Term = $sans("Term")$
#let TODO = text(fill: red, $bold(sans("TODO"))$)

#let (exercise-counter, exercise-box, exercise, show-exercise) = make-frame(
  "exercise",
  "Exercise",
  counter: none,
  inherited-levels: 2,
  inherited-from: heading,
  render: (prefix: none, title: "", full-title: auto, body) => [#strong[#full-title.]#sym.space#emph(body)],
)
#show: show-exercise

#align(center, [
  #heading(numbering: none, text(size: 1.5em)[Algebras and automata])

  Michael Zhang
])



= Automata

= Exercises

Here is a table of some of the exercises that have been distributed throughout the explainer.

#outline(title: none, target: figure.where(kind: "exercise"))

#bibliography("zotero.bib", style: "chicago-author-date")