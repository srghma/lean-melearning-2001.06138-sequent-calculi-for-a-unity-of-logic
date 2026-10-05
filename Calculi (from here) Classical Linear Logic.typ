#import "@preview/curryst:0.6.0": rule, prooftree

#set page(width: auto, height: auto, margin: (x: 2cm, y: 1.5cm), paper: "a4")
#set text(font: "Linux Libertine", size: 10.5pt)

// Notation shortcuts
#let tensor = sym.times.o
#let par = sym.amp.inv
#let with = sym.amp
#let plus = sym.plus.o
#let oc = $!$
#let wn = $?$
#let arrowtriangle = $⇾$ // \rightarrowtriangle

// Prettified rule label helper
#let rname(s) = text(size: 0.78em, smallcaps(s))

// Proof rule helper:
// In Curryst, `rule(..premises, concl)` puts premises on TOP and conclusion on BOTTOM.
#let pt(
  concl,
  premises: (),
  left: none,
  right: none,
  ill: false, // Set to true to highlight ILL rules in blue
) = {
  let c = if ill { blue } else { black }
  let prems = if type(premises) == array { premises } else { (premises,) }
  box(
    text(fill: c,
      prooftree(
        stroke: c,
        rule(
          ..prems,
          concl,
          label: if left != none { rname(left) } else { none },
          name: if right != none { text(size: 0.75em, right) } else { none },
        )
      )
    )
  )
}

Formulas $A, B$ of _classical linear logic (CLL)_ are defined by
$
  A, B := X | X^bot | top | bot | 1 | 0 | A tensor B | A par B | A with B | A plus B | oc A | wn A
$
where $X$ ranges over propositional variables.

#v(0.5em)
*Definition 1* (LLK for CLL). \
The sequent calculus *LLK* for CLL consists of the axioms and the rules displayed in @fig-llk.
#v(0.5em)

#figure(
  caption: [Sequent calculus *LLK* for CLL],
  grid(
    columns: (auto, auto),
    column-gutter: 4em,
    row-gutter: 2.2em,
    align: center + horizon,

    // Row 1: Exchange
    pt($Delta, A', A, Delta' tack Gamma$,
      premises: ($Delta, A, A', Delta' tack Gamma$,),
      left: [(XL)],
      ill: true),
    pt($Delta tack Gamma, B', B, Gamma'$,
      premises: ($Delta tack Gamma, B, B', Gamma'$,),
      left: [(XR)]),

    // Row 2: Weakening
    pt($Delta, oc A tack Gamma$,
      premises: ($Delta tack Gamma$,),
      left: [($!$W)],
      ill: true),
    pt($Delta tack wn B, Gamma$,
      premises: ($Delta tack Gamma$,),
      left: [($?$W)]),

    // Row 3: Contraction
    pt($Delta, oc A tack Gamma$,
      premises: ($Delta, oc A, oc A tack Gamma$,),
      left: [($!$C)],
      ill: true),
    pt($Delta tack wn B, Gamma$,
      premises: ($Delta tack wn B, wn B, Gamma$,),
      left: [($?$C)]),

    // Row 4: Dereliction
    pt($Delta, oc A tack Gamma$,
      premises: ($Delta, A tack Gamma$,),
      left: [($!$D)],
      ill: true),
    pt($Delta tack wn B, Gamma$,
      premises: ($Delta tack B, Gamma$,),
      left: [($?$D)]),

    // Row 5: Promotion / Storage
    pt($oc Delta, wn A tack wn Gamma$,
      premises: ($oc Delta, A tack wn Gamma$,),
      left: [($? upright("L")^(!?)$)]),
    pt($oc Delta tack oc B, wn Gamma$,
      premises: ($oc Delta tack B, wn Gamma$,),
      left: [($! upright("R")^(!?)$)],
      ill: true),

    // Row 6: Identity & Cut
    pt($A tack A$,
      premises: (),
      left: [(Id)],
      ill: true),
    pt($Delta, Delta' tack Gamma, Gamma'$,
      premises: ($Delta tack B, Gamma$, $Delta', B tack Gamma'$),
      left: [(Cut)],
      ill: true),

    // Row 7: Multiplicative Units (0L & 1R)
    pt($Delta, 0 tack Gamma$,
      premises: (),
      left: [(0L)]),
    pt($Delta tack 1, Gamma$,
      premises: (),
      left: [(1R)]),

    // Row 8: Additive Truth (Top)
    pt($Delta, top tack Gamma$,
      premises: ($Delta tack Gamma$,),
      left: [($top$L)],
      ill: true),
    pt($tack top$,
      premises: (),
      left: [($top$R)],
      ill: true),

    // Row 9: Additive / Multiplicative False (Bottom)
    pt($bot tack$,
      premises: (),
      left: [($bot$L)]),
    pt($Delta tack bot, Gamma$,
      premises: ($Delta tack Gamma$,),
      left: [($bot$R)]),

    // Row 10: Multiplicative Conjunction (Tensor)
    pt($Delta, A_1 tensor A_2 tack Gamma$,
      premises: ($Delta, A_1, A_2 tack Gamma$,),
      left: [($tensor$L)],
      ill: true),
    pt($Delta_1, Delta_2 tack B_1 tensor B_2, Gamma_1, Gamma_2$,
      premises: ($Delta_1 tack B_1, Gamma_1$, $Delta_2 tack B_2, Gamma_2$),
      left: [($tensor$R)],
      ill: true),

    // Row 11: Additive Conjunction (With)
    pt($Delta, A_1 with A_2 tack Gamma$,
      premises: ($Delta, A_i tack Gamma$,),
      left: [($with$L$#sub[i]$)],
      right: [($i in overline(2)$)],
      ill: true),
    pt($Delta tack B_1 with B_2, Gamma$,
      premises: ($Delta tack B_1, Gamma$, $Delta tack B_2, Gamma$),
      left: [($with$R)],
      ill: true),

    // Row 12: Multiplicative Disjunction (Par)
    pt($Delta_1, Delta_2, A_1 par A_2 tack Gamma_1, Gamma_2$,
      premises: ($Delta_1, A_1 tack Gamma_1$, $Delta_2, A_2 tack Gamma_2$),
      left: [($par$L)]),
    pt($Delta tack B_1 par B_2, Gamma$,
      premises: ($Delta tack B_1, B_2, Gamma$,),
      left: [($par$R)]),

    // Row 13: Additive Disjunction (Plus)
    pt($Delta, A_1 plus A_2 tack Gamma$,
      premises: ($Delta, A_1 tack Gamma$, $Delta, A_2 tack Gamma$),
      left: [($plus$L)],
      ill: true),
    pt($Delta tack B_1 plus B_2, Gamma$,
      premises: ($Delta tack B_i, Gamma$,),
      left: [($plus$R$#sub[i]$)],
      right: [($i in overline(2)$)],
      ill: true),

    // Row 14: Linear Negation
    pt($Delta, B^bot tack Gamma$,
      premises: ($Delta tack B, Gamma$,),
      left: [($(\_)^bot upright("L")$)]),
    pt($Delta tack A^bot, Gamma$,
      premises: ($Delta, A tack Gamma$,),
      left: [($(\_)^bot upright("R")$)]),
  )
) <fig-llk>

#v(0.8em)

*Definition 2* (LLJ for ILL). <DefLLJ> \
The sequent calculus *LLJ* for ILL consists of the
axioms and the rules of *LLK* on exchange, identity,
cut, top $top$, tensor $tensor$, with $with$, plus $plus$
and of-course $oc$ that contain only intuitionistic sequents,
as well as the following rules on up-linear implication:

#v(0.4em)
#align(center)[
  #grid(
    columns: (auto, auto),
    column-gutter: 4em,
    align: center + horizon,

    pt($Delta, Gamma, A arrowtriangle B tack C$,
      premises: ($Delta tack A$, $Gamma, B tack C$),
      left: [($arrowtriangle$L)],
      ill: true),

    pt($Delta tack A arrowtriangle B$,
      premises: ($Delta, A tack B$,),
      left: [($arrowtriangle$R)],
      ill: true),
  )
]
