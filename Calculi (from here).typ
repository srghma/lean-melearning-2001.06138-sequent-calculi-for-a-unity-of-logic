#set page(
  paper: "a4",
  margin: (top: 2.2cm, bottom: 2.2cm, left: 2.2cm, right: 2.2cm),
  numbering: "1",
)
#set text(font: "New Computer Modern", size: 10pt)
#set par(leading: 0.55em, justify: true, first-line-indent: 0pt)

#set heading(numbering: "1")

#show heading.where(level: 1): it => {
  v(0.4em)
  text(size: 14pt, weight: "bold", it)
  v(0.6em)
}

// Linear Logic Symbols
#let tensor = symbol("⊗")
#let oplus  = symbol("⊕")
#let par    = symbol("⅋")


= Classical Sequent Calculus ($bold("LK")$)

*Formulas:*
$ A, B ::= X | "tt" | "ff" | A and B | A or B | A => B wide (tilde.op A := A => "ff") $

*Identity and Cut:*
$
"" / (A tack.r A) quad ("id")
wide
(Delta tack.r B, Gamma quad B, Delta' tack.r Gamma') / (Delta, Delta' tack.r Gamma, Gamma') quad ("cut")
$

*Structural Rules:*
$
(Delta tack.r Gamma) / (A, Delta tack.r Gamma) quad ("weak"_L)
wide
(Delta tack.r Gamma) / (Delta tack.r B, Gamma) quad ("weak"_R)
$

$
(A, A, Delta tack.r Gamma) / (A, Delta tack.r Gamma) quad ("contr"_L)
wide
(Delta tack.r B, B, Gamma) / (Delta tack.r B, Gamma) quad ("contr"_R)
$

*Truth and Falsity Constants:*
$
(Delta tack.r Gamma) / ("tt", Delta tack.r Gamma) quad ("tt"_L)
wide
"" / (tack.r "tt") quad ("tt"_R)
$

$
"" / ("ff" tack.r) quad ("ff"_L)
wide
(Delta tack.r Gamma) / (Delta tack.r "ff", Gamma) quad ("ff"_R)
$

*Conjunction:*
$
(A_1, Delta tack.r Gamma) / (A_1 and A_2, Delta tack.r Gamma) quad (and_(L 1))
wide
(A_2, Delta tack.r Gamma) / (A_1 and A_2, Delta tack.r Gamma) quad (and_(L 2))
$

$
(Delta tack.r B_1, Gamma quad Delta tack.r B_2, Gamma) / (Delta tack.r B_1 and B_2, Gamma) quad (and_R)
$

*Disjunction:*
$
(A_1, Delta tack.r Gamma quad A_2, Delta tack.r Gamma) / (A_1 or A_2, Delta tack.r Gamma) quad (or_L)
$

$
(Delta tack.r B_1, Gamma) / (Delta tack.r B_1 or B_2, Gamma) quad (or_(R 1))
wide
(Delta tack.r B_2, Gamma) / (Delta tack.r B_1 or B_2, Gamma) quad (or_(R 2))
$

*Implication:*
$
(Delta tack.r A, Gamma quad B, Delta tack.r Gamma) / (A => B, Delta tack.r Gamma) quad (=>_L)
wide
(A, Delta tack.r B, Gamma) / (Delta tack.r A => B, Gamma) quad (=>_R)
$

---

= Intuitionistic Sequent Calculus ($bold("LJ")$)

_Here $gamma$ denotes at most one right-hand formula (`Option (Formula α)`): either empty or a single formula $C$._

*Formulas:*
$ A, B ::= X | top | "ff" | A \& B | A or B | A => B wide (A^star := A => "ff") $

*Identity and Cut:*
$
"" / (A tack.r A) quad ("id")
wide
(Delta tack.r B quad B, Delta' tack.r gamma) / (Delta, Delta' tack.r gamma) quad ("cut")
$

*Structural Rules:*
$
(Delta tack.r gamma) / (A, Delta tack.r gamma) quad ("weak"_L)
wide
(A, A, Delta tack.r gamma) / (A, Delta tack.r gamma) quad ("contr"_L)
$

*Truth and Falsity Constants:*
$
(Delta tack.r gamma) / (top, Delta tack.r gamma) quad (top_L)
wide
"" / (tack.r top) quad (top_R)
$

$
"" / ("ff" tack.r) quad ("ff"_L)
wide
(Delta tack.r) / (Delta tack.r "ff") quad ("ff"_R)
$

*Conjunction (& / with):*
$
(A_1, Delta tack.r gamma) / (A_1 \& A_2, Delta tack.r gamma) quad (\&_(L 1))
wide
(A_2, Delta tack.r gamma) / (A_1 \& A_2, Delta tack.r gamma) quad (\&_(L 2))
$

$
(Delta tack.r B_1 quad Delta tack.r B_2) / (Delta tack.r B_1 \& B_2) quad (\&_R)
$

*Disjunction:*
$
(A_1, Delta tack.r gamma quad A_2, Delta tack.r gamma) / (A_1 or A_2, Delta tack.r gamma) quad (or_L)
$

$
(Delta tack.r B_1) / (Delta tack.r B_1 or B_2) quad (or_(R 1))
wide
(Delta tack.r B_2) / (Delta tack.r B_1 or B_2) quad (or_(R 2))
$

*Implication:*
$
(Delta tack.r A quad B, Delta tack.r gamma) / (A => B, Delta tack.r gamma) quad (=>_L)
wide
(A, Delta tack.r B) / (Delta tack.r A => B) quad (=>_R)
$


// #import "@preview/curryst:0.3.0": rule, proof-tree

// #proof-tree(
//   rule(
//     name: "cut",
//     $Delta, Delta' tack.r Gamma, Gamma'$,
//     $Delta tack.r B, Gamma$,
//     $B, Delta' tack.r Gamma'$
//   )
// )

// #proof-tree(
//   rule(
//     name: $=>_L$,
//     $A => B, Delta tack.r gamma$,
//     $Delta tack.r A$,
//     $B, Delta tack.r gamma$
//   )
// )