#import "@preview/ctheorems:1.1.3": *
#import "@preview/curryst:0.6.0": prooftree, rule

#let env(head, bodyfmt: body => body, ..style) = thmbox(
  "theorem",
  head,
  base: none,
  titlefmt: strong,
  namefmt: name => [(#name)],
  separator: [.#h(0.4em)],
  bodyfmt: bodyfmt,
  padding: (top: 0em, bottom: 0em),
  width: 100%,
  breakable: false,
  ..style,
)
#let claim = (
  bodyfmt: body => emph(body),
  stroke: (left: 1.2pt + luma(40)),
  inset: (left: 0.9em, y: 0.5em),
  radius: 0pt,
)
#let theorem = env("Theorem", ..claim)
#let lemma = env("Lemma", ..claim)
#let proposition = env("Proposition", ..claim)
#let corollary = env("Corollary", ..claim)
#let definition = env("Definition", inset: (x: 0em, y: 0.4em))
#let remark = env("Remark", stroke: (left: 0.6pt + luma(150)), inset: (left: 0.9em, y: 0.4em), radius: 0pt)
#let example = env("Example", stroke: (left: 0.6pt + luma(150)), inset: (left: 0.9em, y: 0.4em), radius: 0pt)
#let judgement(name, form, body) = block(width: 100%, breakable: true, above: 2.4em, below: 2.4em)[
  #box(stroke: 0.5pt, inset: (x: 0.45em, y: 0.35em), baseline: 0.35em)[#form #h(0.6em) (#name)]
  #v(0.2em)
  #body
]
#let aside(title, body) = box(stroke: 0.5pt + luma(140), inset: 0.6em, radius: 2pt)[
  #set align(start)
  #smallcaps(title)
  #body
]
#let given(premise, body) = block(
  width: 100%,
  breakable: true,
  stroke: (left: 1pt + luma(60)),
  inset: (left: 0.9em, y: 0.4em),
  above: 1.4em,
  below: 1.4em,
)[
  #premise
  #body
]
#let proof = thmproof("proof", "Proof", titlefmt: emph, separator: [.#h(0.4em)], inset: (x: 0em, y: 0.3em))

#let report(title: none, author: none, body) = {
  set document(title: title, author: author)
  set page(paper: "a4", margin: 2.5cm, numbering: "1")
  set text(font: "New Computer Modern", size: 11pt)
  show math.equation: set text(font: "New Computer Modern Math")
  set par(justify: true, leading: 0.62em, spacing: 1.1em)
  show math.equation.where(block: true): set block(spacing: 1em)
  set heading(numbering: "1.1")
  show heading: it => {
    let size = if it.level == 1 { 1em } else { 0.8em }
    let number = if it.numbering == none { none } else { counter(heading).display(it.numbering) }
    block(above: if it.level == 1 { 2.4em } else { 1.8em }, below: 1.1em, sticky: true)[
      #set text(size: size, weight: "bold")
      #if number != none { box(width: 1.6em, number) }#it.body
    ]
  }
  show: thmrules.with(qed-symbol: $square$)
  if title != [] and title != none {
    align(center, text(size: 1.6em, weight: "bold", title))
  }
  body
}

#let rules(column-gutter: 2em, row-gutter: 2.4em, ..items) = layout(size => {
  set text(top-edge: "bounds", bottom-edge: "bounds")
  let boxes = items
    .pos()
    .map(it => if type(it) == dictionary {
      if it.name != none { it.name = smallcaps(it.name) }
      prooftree(it)
    } else { it })
  let rows = ((),)
  let gap = column-gutter.to-absolute()
  let used = 0pt
  for b in boxes {
    let w = measure(b).width
    if rows.last().len() > 0 and used + gap + w > size.width {
      rows.push(())
      used = 0pt
    }
    if rows.last().len() > 0 { used += gap }
    used += w
    rows.last().push(b)
  }
  stack(dir: ttb, spacing: row-gutter, ..rows.map(row => grid(
    columns: (1fr,) + row.map(_ => (auto, 1fr)).flatten(),
    column-gutter: 0pt,
    align: bottom,
    [], ..row.map(b => (b, [])).flatten(),
  )))
})
