module

public import Mathlib

/-!
# The six formal languages

Formal languages (grammars of formulas) of the six logics in the commutative diagram:

```
ILL      ──Girard's translation──▶  IL
 │ (conservative extension)          │ (conservative extension)
ILLᵉ_ι   ──unlinearisation (_)_!──▶  ILᵉ
 │ classicalisation (_)_?            │ classicalisation (_)_?
CLL⁻     ──unlinearisation (_)_!──▶  CL
```

### Chapter / Paper Mapping (ArXivSequentCalculi.tex)
* Diagram & Main Results: **Section 1.3** (PDF pages 3–5).
* `CL.Formula`: **Section 2.1, Definition 2.2** (PDF page 8).
* `IL.Formula`: **Section 2.1, Definition 2.5** (PDF page 8).
* `ILL.Formula`: **Section 2.2, Definition 2.10** (PDF page 10).
* `ILLe.Formula`: **Section 3.1, Definition 3.2** (PDF page 13).
* `CLL.Formula`: **Section 2.2, Definition 2.10** (PDF page 10).
* `ILe.Formula`: **Section 3.2, Definition 3.11** (PDF page 20).
* `CLLneg.Formula`: **Section 3.3, Definition 3.19** (PDF page 25).

Throughout, `α` is the type of propositional variables.

Notational conventions follow the paper: in the linear logics, `⊤` is the unit of
tensor `⊗` and `1` is the unit of with `&` (i.e. the traditional notations are swapped, Notation 2.9, PDF page 10).
-/

@[expose] public section

universe u

/-- Formulas of classical logic (CL) — **Paper Section 2.1, Definition 2.2** (PDF page 8):
`A, B ::= X | tt | ff | A ∧ B | A ∨ B | A ⇛ B`. -/
inductive CL.Formula (α : Type u) : Type u
  | var : α → CL.Formula α
  /-- classical truth `tt` -/
  | tt : CL.Formula α
  /-- non-linear falsity `ff` -/
  | ff : CL.Formula α
  /-- classical conjunction `∧` -/
  | conj : CL.Formula α → CL.Formula α → CL.Formula α
  /-- non-linear disjunction `∨` -/
  | disj : CL.Formula α → CL.Formula α → CL.Formula α
  /-- classical implication `⇛` -/
  | imp : CL.Formula α → CL.Formula α → CL.Formula α
  deriving DecidableEq

/-- Classical negation `∼ A := A ⇛ ff` — **Paper Section 2.1, Definition 2.2** (PDF page 8). -/
def CL.Formula.neg {α : Type u} (A : CL.Formula α) : CL.Formula α := .imp A .ff

/-- Formulas of intuitionistic logic (IL) — **Paper Section 2.1, Definition 2.5** (PDF page 8):
`A, B ::= X | ⊤ | ff | A & B | A ∨ B | A ⇒ B`. -/
inductive IL.Formula (α : Type u) : Type u
  | var : α → IL.Formula α
  /-- intuitionistic truth (top) `⊤` -/
  | top : IL.Formula α
  /-- non-linear falsity `ff` -/
  | ff : IL.Formula α
  /-- intuitionistic conjunction (with) `&` -/
  | with : IL.Formula α → IL.Formula α → IL.Formula α
  /-- non-linear disjunction `∨` -/
  | disj : IL.Formula α → IL.Formula α → IL.Formula α
  /-- intuitionistic implication `⇒` -/
  | imp : IL.Formula α → IL.Formula α → IL.Formula α
  deriving DecidableEq

/-- Intuitionistic negation `A⋆ := A ⇒ ff` — **Paper Section 2.1, Definition 2.5** (PDF page 8). -/
def IL.Formula.neg {α : Type u} (A : IL.Formula α) : IL.Formula α := .imp A .ff

/-- Formulas of intuitionistic linear logic (ILL) — **Paper Section 2.2, Definition 2.10** (PDF page 10):
`A, B ::= X | ⊤ | A ⊗ B | A & B | A ⊕ B | A ⊸ B | !A`
(here `⊤` is the unit of `⊗`, and `⊸` is the *up-linear implication*). -/
inductive ILL.Formula (α : Type u) : Type u
  | var : α → ILL.Formula α
  /-- top `⊤` (unit of tensor) -/
  | top : ILL.Formula α
  /-- tensor `⊗` -/
  | tensor : ILL.Formula α → ILL.Formula α → ILL.Formula α
  /-- with `&` -/
  | with : ILL.Formula α → ILL.Formula α → ILL.Formula α
  /-- plus `⊕` -/
  | plus : ILL.Formula α → ILL.Formula α → ILL.Formula α
  /-- up-linear implication `⊸` -/
  | limp : ILL.Formula α → ILL.Formula α → ILL.Formula α
  /-- of-course `!` -/
  | bang : ILL.Formula α → ILL.Formula α
  deriving DecidableEq

/-- Formulas of intuitionistic linear logic (ι-)extended (ILLᵉ, ILLᵉ_ι) —
**Paper Section 3.1, Definition 3.2** (PDF page 13); both logics share this formal language:
`A, B ::= X | ⊤ | ⊥ | 1 | 0 | A ⊗ B | A ⅋ B | A & B | A ⊕ B | ¬A | !A | ?A`
where `¬` is the *up-linear negation*. -/
inductive ILLe.Formula (α : Type u) : Type u
  | var : α → ILLe.Formula α
  /-- top `⊤` (unit of tensor) -/
  | top : ILLe.Formula α
  /-- bottom `⊥` (unit of par) -/
  | bot : ILLe.Formula α
  /-- one `1` (unit of with) -/
  | one : ILLe.Formula α
  /-- zero `0` (unit of plus) -/
  | zero : ILLe.Formula α
  /-- tensor `⊗` -/
  | tensor : ILLe.Formula α → ILLe.Formula α → ILLe.Formula α
  /-- par `⅋` -/
  | par : ILLe.Formula α → ILLe.Formula α → ILLe.Formula α
  /-- with `&` -/
  | with : ILLe.Formula α → ILLe.Formula α → ILLe.Formula α
  /-- plus `⊕` -/
  | plus : ILLe.Formula α → ILLe.Formula α → ILLe.Formula α
  /-- up-linear negation `¬` -/
  | neg : ILLe.Formula α → ILLe.Formula α
  /-- of-course `!` -/
  | bang : ILLe.Formula α → ILLe.Formula α
  /-- why-not `?` -/
  | wn : ILLe.Formula α → ILLe.Formula α
  deriving DecidableEq

/-- Up-linear implication in ILLᵉ: `A ⊸ B := ¬A ⅋ B` —
**Paper Section 3.1, Definition 3.2** (PDF page 13). -/
def ILLe.Formula.limp {α : Type u} (A B : ILLe.Formula α) : ILLe.Formula α :=
  .par (.neg A) B

/-!
## CLL.Formula — Formulas of Classical Linear Logic (CLL)

The formula language of CLL is **identical** to `ILLe.Formula`:
```
A, B ::= X | ⊤ | ⊥ | 1 | 0 | A ⊗ B | A ⅋ B | A & B | A ⊕ B | ¬A | !A | ?A
```
Linear negation `¬` plays the role of `(—)⊥`, so `X⊥ = ¬(var X)`.
The formula type `CLL.Formula α` is therefore defined as an abbreviation for `ILLe.Formula α`.
-/

/-- Formulas of Classical Linear Logic (CLL) — **Paper Section 2.2, Definition 2.10** (PDF page 10):
`A, B ::= X | ⊤ | ⊥ | 1 | 0 | A ⊗ B | A ⅋ B | A & B | A ⊕ B | A⊥ | !A | ?A`.
The formula language coincides with `ILLe.Formula α`. We provide `CLL.Formula` as a type alias. -/
abbrev CLL.Formula (α : Type u) := ILLe.Formula α

/-- Linear negation in CLL: `A⊥ := ¬A` (the `neg` constructor of `ILLe.Formula`). -/
abbrev CLL.Formula.lneg {α : Type u} (A : CLL.Formula α) : CLL.Formula α := .neg A

/-- Formulas of intuitionistic logic extended (ILᵉ) —
**Paper Section 3.2, Definition 3.11** (PDF page 20):
`A, B ::= X | ⊤ | ff | A & B | A ∨ B | A ⇒ B | ?A`. -/
inductive ILe.Formula (α : Type u) : Type u
  | var : α → ILe.Formula α
  /-- top `⊤` -/
  | top : ILe.Formula α
  /-- falsity `ff` -/
  | ff : ILe.Formula α
  /-- with `&` -/
  | with : ILe.Formula α → ILe.Formula α → ILe.Formula α
  /-- disjunction `∨` -/
  | disj : ILe.Formula α → ILe.Formula α → ILe.Formula α
  /-- intuitionistic implication `⇒` -/
  | imp : ILe.Formula α → ILe.Formula α → ILe.Formula α
  /-- why-not `?` -/
  | wn : ILe.Formula α → ILe.Formula α
  deriving DecidableEq

/-- Intuitionistic negation in ILᵉ: `A⋆ := A ⇒ ff` —
**Paper Section 3.2, Definition 3.11** (PDF page 20). -/
def ILe.Formula.neg {α : Type u} (A : ILe.Formula α) : ILe.Formula α := .imp A .ff

/-- Formulas of classical linear logic negative (CLL⁻) —
**Paper Section 3.3, Definition 3.19** (PDF page 25):
`A, B ::= X | tt | ⊥ | A ∧ B | A ⊕ B | A ↬ B | !A`. -/
inductive CLLneg.Formula (α : Type u) : Type u
  | var : α → CLLneg.Formula α
  /-- truth `tt` -/
  | tt : CLLneg.Formula α
  /-- bottom `⊥` -/
  | bot : CLLneg.Formula α
  /-- conjunction `∧` -/
  | conj : CLLneg.Formula α → CLLneg.Formula α → CLLneg.Formula α
  /-- plus `⊕` -/
  | plus : CLLneg.Formula α → CLLneg.Formula α → CLLneg.Formula α
  /-- classical linear implication `↬` -/
  | imp : CLLneg.Formula α → CLLneg.Formula α → CLLneg.Formula α
  /-- of-course `!` -/
  | bang : CLLneg.Formula α → CLLneg.Formula α
  deriving DecidableEq

/-- Classical linear negation in CLL⁻: `A⋆ := A ↬ ⊥` —
**Paper Section 3.3, Definition 3.19** (PDF page 25). -/
def CLLneg.Formula.neg {α : Type u} (A : CLLneg.Formula α) : CLLneg.Formula α := .imp A .bot

/-- Turn an optional formula (the right-hand side of an intuitionistic sequent) into a
multiset with at most one element. -/
def optMs {β : Type u} : Option β → Multiset β
  | none => 0
  | some b => {b}

@[simp] lemma optMs_none {β : Type u} : optMs (none : Option β) = 0 := rfl
@[simp] lemma optMs_some {β : Type u} (b : β) : optMs (some b) = {b} := rfl

lemma optMs_map {β γ : Type u} (f : β → γ) (o : Option β) :
    (optMs o).map f = optMs (o.map f) := by
  cases o <;> simp [optMs]

/-- Turn an optional formula (the right-hand side of an intuitionistic sequent) into a
finset with at most one element. -/
def optFinset {β : Type u} : Option β → Finset β
  | none => ∅
  | some b => {b}

@[simp] lemma optFinset_none {β : Type u} : optFinset (none : Option β) = ∅ := rfl
@[simp] lemma optFinset_some {β : Type u} (b : β) : optFinset (some b) = {b} := rfl

lemma optFinset_map {β γ : Type u} [DecidableEq γ] (f : β → γ) (o : Option β) :
    (optFinset o).image f = optFinset (o.map f) := by
  cases o <;> simp [optFinset]

end
