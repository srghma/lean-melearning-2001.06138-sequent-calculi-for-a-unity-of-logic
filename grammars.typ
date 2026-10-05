#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

#set page(paper: "a4", margin: (x: 1.8cm, y: 2cm))
#set text(font: "Linux Libertine", size: 10pt)

// --- Mathematical Notation & Connectives ---
#let tensor = sym.times.o
#let par = sym.amp.inv
#let with = sym.amp
#let plus = sym.plus.o
#let oc = $!$
#let wn = $?$
#let arrowtriangle = $⇾$                     // \rightarrowtriangle (up-linear implication, U+21FE)
#let cneg = sym.tilde                        // Classical negation ~
#let ineg = sym.star                         // Intuitionistic negation (-)^\star
#let lneg = $bot$                            // Linear negation (-)^\bot
#let uplneg = sym.not                        // Up-linear negation \neg
#let clneg = sym.star                        // Classical linear negation subscript \star
#let cimp = $arrow.r.triple$                 // Classical implication \Rrightarrow (⇛)
#let iimp = $arrow.r.double$                 // Intuitionistic implication \Rightarrow (⇒)
#let limp = $multimap$                       // Linear implication \multimap (⊸)
#let climp = $arrow.r.loop$                  // Classical linear implication \looparrowright (↬)
#let tt = $upright("tt")$
#let ff = $upright("ff")$

// Maps/Functors with placeholder notation: (_)! and (_)?
#let map-oc = $(text("_"))_!$
#let map-wn = $(text("_"))_?$

// Helper for edge labels: Title + optional conceptual note + Lean Formula Function + Lean Calculus Function
#let fn-lbl(title, note: none, f: none, c: none) = [
  #text(weight: "medium", size: 0.82em)[#title]
  #if note != none [ \ #text(size: 0.72em, style: "italic", fill: gray.darken(40%))[#note] ]
  #if f != none [ \ #text(size: 0.62em, fill: rgb("#1d4ed8"))[f: #raw(f)] ]
  #if c != none [ \ #text(size: 0.62em, fill: rgb("#047857"))[c: #raw(c)] ]
]

#align(center)[
  #text(size: 1.35em, weight: "bold")[Commutative Unity of Logic: Grammars & Transformations] \
  #text(size: 1.0em, style: "italic")[Extracted from "Sequent calculi for a unity of logic" by Norihiro Yamada \
    Annotated with Lean 4 formalisation declarations (`RequestProject/Logics`)]
]

#v(0.8em)

= 1. Formal Grammars of the Logics

The paper establishes relationships among standard logics (CL, IL, CLL, ILL) and three novel extensions ($text("ILL")^e$, $text("IL")^e$, and $text("CLL")^-$) without polarities:

#grid(
  columns: (1fr, 1fr),
  gutter: 1.5em,
  [
    *Classical Logic (CL)* --- `CL.Formula`
    $ A, B := X | tt | ff | A and B | A or B | A cimp B $
    where $cneg A := A cimp ff$ (`CL.Formula.neg`).

    #v(0.3em)
    *Intuitionistic Logic (IL)* --- `IL.Formula`
    $ A, B := X | top | ff | A with B | A or B | A iimp B $
    where $A^ineg := A iimp ff$ (`IL.Formula.neg`).

    #v(0.3em)
    *Classical Linear Logic (CLL)* --- `CLL.Formula`
    $
      A, B := & X | X^lneg | top | bot | 1 | 0 | A tensor B \
              & | A par B | A with B | A plus B | oc A | wn A
    $
    where $A limp B := A^lneg par B$ (`CLL.Formula.lneg`).

    #v(0.3em)
    *Intuitionistic Linear Logic (ILL)* --- `ILL.Formula`
    $ A, B := X | top | A tensor B | A with B | A plus B | A arrowtriangle B | oc A $
  ],
  [
    *Intuitionistic Linear Logic Extended ($text("ILL")^(e)_(iota \/ rho)$)* --- `ILLe.Formula`
    $
      A, B := & X | top | bot | 1 | 0 | A tensor B | A par B \
              & | A with B | A plus B | uplneg A | oc A | wn A
    $
    where $A arrowtriangle B := uplneg A par B$ (`ILLe.Formula.limp`).

    #v(0.3em)
    *Intuitionistic Logic Extended ($text("IL")^e$)* --- `ILe.Formula`
    $ A, B := X | top | ff | A with B | A or B | A iimp B | wn A $
    where $A^ineg := A iimp ff$ (`ILe.Formula.neg`).

    #v(0.3em)
    *Classical Linear Logic Negative ($text("CLL")^-$)* --- `CLLneg.Formula`
    $ A, B := X | tt | bot | A and B | A plus B | A climp B | oc A $
    where $A_clneg := A climp bot$ (`CLLneg.Formula.neg`).
  ],
)

#v(1.2em)
= 2. The Three Unity-of-Logic Diagrams

== Diagram 1: The Naive / Target Commutative Square (§2.2)
The traditional dichotomy sought between linearity and non-linearity (horizontal) and intuitionisity and classicality (vertical). This diagram fails to commute in existing literature because classical linear negation $(-)^bot$ imposes definitional De Morgan symmetries and polarities absent from IL and CL.

#v(0.3em)
#align(center)[
  #fletcher.diagram(
    node-inset: 8pt,
    spacing: (58mm, 22mm),

    node((0, 0), [*ILL* \ #text(size: 0.72em, fill: gray.darken(30%))[`ILL.LLJ`]]),
    node((1, 0), [*IL* \ #text(size: 0.72em, fill: gray.darken(30%))[`IL.LJ`]]),
    node((0, 1), [*CLL* \ #text(size: 0.72em, fill: gray.darken(30%))[`CLL.LLK`]]),
    node((1, 1), [*CL* \ #text(size: 0.72em, fill: gray.darken(30%))[`CL.LK`]]),

    // Horizontal arrows
    edge((0, 0), (1, 0), "->", fn-lbl([unlinearisation], f: "IL.girard (←)", c: "IL.LJ.toILC (←)"), label-side: left),
    edge((0, 1), (1, 1), "->", fn-lbl([unlinearisation], note: [non-commutative]), label-side: right),

    // Vertical arrows
    edge((0, 0), (0, 1), "->", fn-lbl([classicalisation], note: [adds polarities & $(-)^bot$]), label-side: right),
    edge((1, 0), (1, 1), "->", fn-lbl([classicalisation], note: [e.g. negative transl.]), label-side: left),
  )
]

#v(1.2em)
== Diagram 2: Commutative Unity of Logic via $text("ILL")^(e)_iota$ (§1.3 Theorem)
By replacing $text("CLL")$ with $text("CLL")^-$ (which discards involutive linear negation and polarities) and using conservative extensions $text("ILL")^(e)_iota$ and $text("IL")^e$, the operations of unlinearisation #map-oc and classicalisation #map-wn commute modulo rule permutation.

#v(0.3em)
#align(center)[
  #fletcher.diagram(
    node-inset: 8pt,
    spacing: (64mm, 25mm),

    node((0, 0), [*ILL* \ #text(size: 0.72em, fill: gray.darken(30%))[`ILL.LLJ`]]),
    node((1, 0), [*IL* \ #text(size: 0.72em, fill: gray.darken(30%))[`IL.LJ`]]),
    node((0, 1), [$bold(text("ILL")^(e)_iota)$ \ #text(size: 0.72em, fill: purple.darken(30%))[`ILLe.ILC true`]]),
    node((1, 1), [$bold(text("IL")^e)$ \ #text(size: 0.72em, fill: blue.darken(30%))[`ILe.INC`]]),
    node((0, 2), [$bold(text("CLL")^-)$ \ #text(size: 0.72em, fill: red.darken(30%))[`CLLneg.CLC`]]),
    node((1, 2), [*CL* \ #text(size: 0.72em, fill: gray.darken(30%))[`CL.LK`]]),

    // Top embeddings
    edge(
      (0, 0),
      (1, 0),
      "->",
      fn-lbl([Girard's translation], f: "IL.girard / IL.girardE (←)", c: "IL.LJ.toILC (←)"),
      label-side: left,
    ),
    edge(
      (0, 0),
      (0, 1),
      "hook'->",
      fn-lbl([conservative extension], f: "ILL.embed (↓)", c: "ILL.LLJ.toILC true (↓)"),
      label-side: right,
    ),
    edge(
      (1, 0),
      (1, 1),
      "hook'->",
      fn-lbl([conservative extension], f: "IL.embed (↓)", c: "IL.LJm.toINC (↓)"),
      label-side: left,
    ),

    // Middle transformations
    edge(
      (0, 1),
      (1, 1),
      "->",
      fn-lbl([unlinearisation #map-oc], f: "ILe.T (←)", c: "ILe.INC.toILC (←)"),
      label-side: right,
    ),
    edge(
      (0, 1),
      (0, 2),
      "->",
      fn-lbl([classicalisation #map-wn], f: "CLLneg.T (↑)", c: "CLLneg.CLC.toILC (↑)"),
      label-side: right,
    ),
    edge(
      (1, 1),
      (1, 2),
      "->",
      fn-lbl([classicalisation #map-wn], f: "CL.Twn (↑)", c: "CL.LK.toINC (↑)"),
      label-side: left,
    ),

    // Bottom transformation
    edge(
      (0, 2),
      (1, 2),
      "->",
      fn-lbl([unlinearisation #map-oc], f: "CL.Tbang (←)", c: "CL.LK.toCLC (←)"),
      label-side: right,
    ),
  )
]

#v(1.2em)
== Diagram 3: Fully Conservative Unity of Logic via $text("ILL")^(e)_rho$ (§1.3 Corollary & §3.5 Figure 5)
Restricting proof derivations to _tractable_ cuts yields the substructural system $text("ILL")^(e)_rho$ (embodied by sequent calculus $bold("ILC")_rho$), which restores cut-elimination. Consequently, all embeddings and transformations become strictly *conservative* at the provability level.

#v(0.3em)
#align(center)[
  #fletcher.diagram(
    node-inset: 8pt,
    spacing: (64mm, 25mm),

    node((0, 0), [*ILL* \ #text(size: 0.72em, fill: gray.darken(30%))[`ILL.LLJ`]]),
    node((1, 0), [*IL* \ #text(size: 0.72em, fill: gray.darken(30%))[`IL.LJ`]]),
    node((0, 1), [$bold(text("ILL")^(e)_rho)$ \ #text(size: 0.72em, fill: blue.darken(30%))[`ILLe.ILC false`]]),
    node((1, 1), [$bold(text("IL")^e)$ \ #text(size: 0.72em, fill: blue.darken(30%))[`ILe.INC`]]),
    node((0, 2), [$bold(text("CLL")^-)$ \ #text(size: 0.72em, fill: red.darken(30%))[`CLLneg.CLC`]]),
    node((1, 2), [*CL* \ #text(size: 0.72em, fill: gray.darken(30%))[`CL.LK`]]),

    // Row 0 to 1: Conservative extensions
    edge(
      (0, 0),
      (1, 0),
      "->",
      fn-lbl([Girard's translation], f: "IL.girard (←)", c: "IL.LJ.toLLJ_of_conservative (←)"),
      label-side: left,
    ),
    edge(
      (0, 0),
      (0, 1),
      "hook'->",
      fn-lbl([conservative extension], f: "ILL.embed (↓)", c: "ILL.LLJ.toILC false (↓)"),
      label-side: right,
    ),
    edge(
      (1, 0),
      (1, 1),
      "hook'->",
      fn-lbl([conservative extension], f: "IL.embed (↓)", c: "IL.incConservativeMin"),
      label-side: left,
    ),

    // Row 1 to 2: Conservative classicalisation & unlinearisation
    edge(
      (0, 1),
      (1, 1),
      "->",
      fn-lbl([unlinearisation #map-oc], f: "ILe.T (←)", c: "ILe.INC.toILC (←)"),
      label-side: right,
    ),
    edge(
      (0, 1),
      (0, 2),
      "->",
      fn-lbl([classicalisation #map-wn], f: "CLLneg.T (↑)", c: "CLLneg.CLC.toILC (↑)"),
      label-side: right,
    ),
    edge(
      (1, 1),
      (1, 2),
      "->",
      fn-lbl([classicalisation #map-wn], f: "CL.Twn (↑)", c: "CL.LK.toINC (↑)"),
      label-side: left,
    ),

    // Bottom edge
    edge(
      (0, 2),
      (1, 2),
      "->",
      fn-lbl([unlinearisation #map-oc], f: "CL.Tbang (←)", c: "CL.LK.toCLC (←)"),
      label-side: right,
    ),
  )
]

#v(1.2em)
= 3. Explicit Grammar Mappings Across the Functors

The arrows in the diagrams correspond to inductive formula translations that embed each logic into $text("ILL")^(e)_rho$:

#table(
  columns: (auto, 1fr, 1fr, 1.25fr),
  inset: 6pt,
  align: (center + horizon, left, left, left),
  stroke: 0.5pt + gray,
  fill: (x, y) => if y == 0 { rgb("f0f4f8") } else if calc.even(y) { rgb("fafafa") } else { none },

  [*Connective*],
  [*Unlinearisation* $scr(T)_!$ \ #text(size: 0.72em)[`ILe.T` : $text("IL")^e -> text("ILL")^e$]],
  [*Classicalisation* $scr(T)_?$ \ #text(size: 0.72em)[`CL.Twn` : $text("CL") -> text("IL")^e$]],
  [*Composition* $scr(T)_(!?)$ \ #text(size: 0.72em)[`CL.Tbangwn` : $text("CL") -> text("ILL")^e$]],

  [Truth], [$scr(T)_!(top) = top$], [$scr(T)_?(tt) = wn top$], [$scr(T)_(!?)(tt) = wn top$],

  [Falsity], [$scr(T)_!(ff) = oc bot$], [$scr(T)_?(ff) = ff$], [$scr(T)_(!?)(ff) = oc bot$],

  [Conjunction],
  [$scr(T)_!(A with B) = scr(T)_!(A) with scr(T)_!(B)$],
  [$scr(T)_?(A and B) = wn scr(T)_?(A) with wn scr(T)_?(B)$],
  [$scr(T)_(!?)(A and B) = wn scr(T)_(!?)(A) with wn scr(T)_(!?)(B)$],

  [Disjunction],
  [$scr(T)_!(A or B) = oc scr(T)_!(A) plus oc scr(T)_!(B)$],
  [$scr(T)_?(A or B) = scr(T)_?(A) or scr(T)_?(B)$],
  [$scr(T)_(!?)(A or B) = oc scr(T)_(!?)(A) plus oc scr(T)_(!?)(B)$],

  [Implication],
  [$scr(T)_!(A iimp B) = oc scr(T)_!(A) arrowtriangle scr(T)_!(B)$],
  [$scr(T)_?(A cimp B) = scr(T)_?(A) iimp wn scr(T)_?(B)$],
  [$scr(T)_(!?)(A cimp B) = oc scr(T)_(!?)(A) arrowtriangle wn scr(T)_(!?)(B)$],

  [Modalities], [$scr(T)_!(wn A) = wn scr(T)_!(A)$], [---], [---],
)

#v(0.6em)
#rect(width: 100%, stroke: 0.5pt + blue.darken(20%), fill: rgb("f4f8ff"), inset: 8pt, radius: 4pt)[
  *Key Insight from Yamada (2026) and Lean Verification (`Diagram.lean`):*
  - *Non-linearity* is the _implicit_ placement of $oc$ on antecedent formulas (`Unlinearisation bang C`).
  - *Classicality* is the _implicit_ placement of $wn$ on succedent formulas (`Classicalisation wn C`).
  - Dual translations: `CL.Tbang` unlinearises $text("CL") -> text("CLL")^-$, and `CLLneg.T` classicalises $text("CLL")^- -> text("ILL")^e$.
  - Commutativity on formulas is proved by `CL.Tbangwn_eq_Twnbang` ($scr(T)_(!?) = scr(T)_(?!)$).
  - Commutativity on sequents is proved by `CL.LK.routes_agree`, showing both routes from `CL.LK` yield identical provable sequents in `ILLe.ILC true` (`CL.LK.toILC_viaILe` and `CL.LK.toILC_viaCLLneg`).
]

#v(1.5em)

= 4. Grand Unified Diagram: Joining All Logics, Calculi, and Translations

The diagram below synthesizes all 8 formal systems, formula embeddings (`f:`), and sequent calculus provability maps (`c:`):
- *Columns 1 & 2 (Right)*: Form the strictly conservative, cut-eliminable unity of logic (Diagram 3), where unlinearisation #map-oc and classicalisation #map-wn commute cleanly.
- *Column 0 (Left)*: Houses the unconstrained/polarized systems: $bold(text("ILL")^(e)_iota)$ (`ILLe.ILC true`, cut-elimination fails) and standard $bold(text("CLL"))$ (`CLL.LLK`, with polarities and involutive negation).
- *Horizontal bridges*: Explicitly split $bold(text("ILL")^(e)_rho)$ and $bold(text("ILL")^(e)_iota)$, showing the substructural cut restriction and the polarity removal ($bold(text("CLL")) arrow.dashed bold(text("CLL"))^-$).

#v(0.6em)
#align(center)[
  #fletcher.diagram(
    spacing: (48mm, 28mm),

    // --- Row 0: Intuitionistic Logics ---
    node((1, 0), [*ILL* \ #text(size: 0.72em, fill: gray.darken(30%))[`ILL.LLJ` \ `ILL.Formula`]]),
    node((2, 0), [*IL* \ #text(size: 0.72em, fill: gray.darken(30%))[`IL.LJ` / `IL.LJm` \ `IL.Formula`]]),

    // --- Row 1: Extended Logics (Split: ILL^e_iota on left, ILL^e_rho in center) ---
    node((0, 1), [$bold(text("ILL")^(e)_iota)$ \ #text(
        size: 0.72em,
        fill: purple.darken(30%),
      )[`ILLe.ILC true` \ `ILLe.Formula`]]),
    node((1, 1), [$bold(text("ILL")^(e)_rho)$ \ #text(
        size: 0.72em,
        fill: blue.darken(30%),
      )[`ILLe.ILC false` \ `ILLe.Formula`]]),
    node((2, 1), [$bold(text("IL")^e)$ \ #text(size: 0.72em, fill: blue.darken(30%))[`ILe.INC` \ `ILe.Formula`]]),

    // --- Row 2: Classical Logics (CLL on left, CLL^- in center, CL on right) ---
    node((0, 2), [*CLL* \ #text(size: 0.72em, fill: gray.darken(30%))[`CLL.LLK` \ `CLL.Formula`]]),
    node((1, 2), [$bold(text("CLL")^-)$ \ #text(size: 0.72em, fill: red.darken(30%))[`CLLneg.CLC` \ `CLLneg.Formula`]]),
    node((2, 2), [*CL* \ #text(size: 0.72em, fill: gray.darken(30%))[`CL.LK` \ `CL.Formula`]]),

    // --- Core Commutative Ladder (Columns 1 & 2) ---
    // Top: Girard's translation
    edge(
      (1, 0),
      (2, 0),
      "->",
      fn-lbl([Girard's translation], f: "IL.girard / IL.girardE (←)", c: "IL.LJ.toILC (←)"),
      label-side: left,
    ),

    // Inclusions to extended layer
    edge(
      (1, 0),
      (1, 1),
      "hook'->",
      fn-lbl([conservative extension], f: "ILL.embed (↓)", c: "ILL.LLJ.toILC false (↓)"),
      label-side: right,
    ),
    edge(
      (2, 0),
      (2, 1),
      "hook'->",
      fn-lbl([conservative extension], f: "IL.embed (↓)", c: "IL.LJm.toINC (↓)"),
      label-side: left,
    ),

    // Middle row unlinearisation
    edge(
      (1, 1),
      (2, 1),
      "->",
      fn-lbl([unlinearisation #map-oc], f: "ILe.T (←)", c: "ILe.INC.toILC (←)"),
      label-side: right,
    ),

    // Extended to classical layer
    edge(
      (1, 1),
      (1, 2),
      "->",
      fn-lbl([classicalisation #map-wn], f: "CLLneg.T (↑)", c: "CLLneg.CLC.toILC (↑)"),
      label-side: right,
    ),
    edge(
      (2, 1),
      (2, 2),
      "->",
      fn-lbl([classicalisation #map-wn], f: "CL.Twn (↑)", c: "CL.LK.toINC (↑)"),
      label-side: left,
    ),

    // Bottom row unlinearisation
    edge(
      (1, 2),
      (2, 2),
      "->",
      fn-lbl([unlinearisation #map-oc], f: "CL.Tbang (←)", c: "CL.LK.toCLC (←)"),
      label-side: right,
    ),

    // --- Connections to Split ILL^e_iota (Diagram 2) ---
    // Substructural inclusion between ILL^e_rho and ILL^e_iota
    edge(
      (1, 1),
      (0, 1),
      "hook->",
      fn-lbl([substructural inclusion], note: [pure cut restriction], f: "ILC false ⊆ ILC true"),
      label-side: right,
    ),

    // Conservative extension ILL -> ILL^e_iota
    edge(
      (1, 0),
      (0, 1),
      "hook'->",
      fn-lbl([conservative ext.], f: "ILL.embed (↓)", c: "ILL.LLJ.toILC true (↓)"),
      label-side: right,
    ),

    // Classicalisation ILL^e_iota -> CLL^-
    edge(
      (0, 1),
      (1, 2),
      "->",
      fn-lbl([classicalisation #map-wn], f: "CLLneg.T (↑)", c: "CLLneg.CLC.toILC (↑)"),
      label-side: left,
    ),

    // --- Connections to Traditional CLL (Diagram 1) ---
    // Transition from CLL to CLL^- (discarding polarities, label below arrow)
    edge(
      (0, 2),
      (1, 2),
      "..>",
      stroke: (paint: red.darken(25%), thickness: 0.9pt),
      fn-lbl([discard polarities], note: [removes $(-)^bot$ De Morgan], c: "CLL.LLK ⟹ CLC"),
      label-side: right,
    ),

    // Relationship between CLL and ILL^e_iota (unpolarising negation)
    edge(
      (0, 2),
      (0, 1),
      "-->",
      stroke: (paint: gray.darken(30%), dash: "dashed"),
      fn-lbl([unpolarised negation], note: [replaces $(-)^bot$ with ¬], f: "CLL.Formula = ILLe.Formula"),
      label-side: left,
    ),
  )
]
