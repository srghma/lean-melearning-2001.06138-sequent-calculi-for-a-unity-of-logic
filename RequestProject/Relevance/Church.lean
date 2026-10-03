module

public import Mathlib

/-!
# Relevance logic: Church's weak theory of implication

The *implicational fragment* `R→` of relevance logic, in the form in which it was introduced
by Alonzo Church, *The weak theory of implication* (1951). Church's motivating requirement is
exactly the "use" criterion of relevance logic: a formula may only be listed among the
premises of a deduction if it is *actually used* in the deduction. In proof-theoretic terms
this forbids weakening (thinning) while keeping contraction.

Church's Hilbert-style system has modus ponens as its only rule and four axiom schemes:

* `I`: `A → A`                                   (identity)
* `B`: `(A → B) → ((C → A) → (C → B))`           (prefixing)
* `C`: `(A → (B → C)) → (B → (A → C))`           (permutation)
* `W`: `(A → (A → B)) → (A → B)`                 (contraction)

The weakening axiom `K`: `A → (B → A)` of intuitionistic/classical logic is deliberately
absent (see `Relevance.not_thm_K`).

We also formalise Church's notion of a *deduction from hypotheses in which every hypothesis
is used* (`Relevance.Deriv`), keeping track of the hypotheses as a multiset.
-/

@[expose] public section

universe u

/-- Formulas of the implicational relevance logic `R→`: `A, B ::= X | A → B`. -/
inductive Relevance.Formula (α : Type u) : Type u
  | var : α → Relevance.Formula α
  /-- relevant implication `→` -/
  | imp : Relevance.Formula α → Relevance.Formula α → Relevance.Formula α
  deriving DecidableEq

namespace Relevance

variable {α : Type u}

open Formula

/-- Theorems of Church's Hilbert-style system for `R→` (axioms `I`, `B`, `C`, `W` and the
rule of modus ponens). -/
inductive Thm : Formula α → Prop
  /-- axiom `I`: `A → A` -/
  | axI (A : Formula α) : Thm (imp A A)
  /-- axiom `B`: `(A → B) → ((C → A) → (C → B))` -/
  | axB (A B C : Formula α) : Thm (imp (imp A B) (imp (imp C A) (imp C B)))
  /-- axiom `C`: `(A → (B → C)) → (B → (A → C))` -/
  | axC (A B C : Formula α) : Thm (imp (imp A (imp B C)) (imp B (imp A C)))
  /-- axiom `W`: `(A → (A → B)) → (A → B)` -/
  | axW (A B : Formula α) : Thm (imp (imp A (imp A B)) (imp A B))
  /-- modus ponens -/
  | mp {A B : Formula α} : Thm (imp A B) → Thm A → Thm B

/-- Church's *deductions from hypotheses in which every hypothesis is used*:
`Deriv Γ A` means that `A` is deducible from the multiset of hypotheses `Γ`, each
hypothesis (with its multiplicity) being actually used. Hypotheses may be used more than
once (contraction), but no unused hypothesis may be added (no weakening). -/
inductive Deriv : Multiset (Formula α) → Formula α → Prop
  /-- a hypothesis `A` deduces `A` -/
  | hyp (A : Formula α) : Deriv {A} A
  /-- theorems are deducible from no hypotheses -/
  | thm {A : Formula α} : Thm A → Deriv 0 A
  /-- modus ponens, collecting the hypotheses of both premises -/
  | mp {Γ Γ' : Multiset (Formula α)} {A B : Formula α} :
      Deriv Γ (imp A B) → Deriv Γ' A → Deriv (Γ + Γ') B
  /-- a hypothesis used twice need only be listed once -/
  | contr {Γ : Multiset (Formula α)} {A B : Formula α} :
      Deriv (A ::ₘ A ::ₘ Γ) B → Deriv (A ::ₘ Γ) B

/-! ## Derived theorems and rules of Church's system -/

namespace Thm

/-- prefixing as a rule -/
theorem pre {A B : Formula α} (C : Formula α) (h : Thm (imp A B)) :
    Thm (imp (imp C A) (imp C B)) :=
  mp (axB A B C) h

/-- permutation as a rule -/
theorem perm {A B C : Formula α} (h : Thm (imp A (imp B C))) : Thm (imp B (imp A C)) :=
  mp (axC A B C) h

/-- suffixing: `(A → B) → ((B → C) → (A → C))` -/
theorem suf (A B C : Formula α) : Thm (imp (imp A B) (imp (imp B C) (imp A C))) :=
  perm (axB B C A)

/-- transitivity as a rule -/
theorem trans {A B C : Formula α} (h₁ : Thm (imp A B)) (h₂ : Thm (imp B C)) :
    Thm (imp A C) :=
  mp (pre A h₂) h₁

/-- assertion: `A → ((A → B) → B)` -/
theorem assertion (A B : Formula α) : Thm (imp A (imp (imp A B) B)) :=
  perm (axI (imp A B))

end Thm

/-! ## Curried implications `A₁ → (A₂ → ⋯ → (Aₙ → B))` -/

/-- `curry [A₁, …, Aₙ] B = A₁ → (A₂ → ⋯ → (Aₙ → B))`. -/
def curry : List (Formula α) → Formula α → Formula α
  | [], B => B
  | A :: L, B => imp A (curry L B)

@[simp] lemma curry_nil (B : Formula α) : curry [] B = B := rfl
@[simp] lemma curry_cons (A : Formula α) (L : List (Formula α)) (B : Formula α) :
    curry (A :: L) B = imp A (curry L B) := rfl

lemma curry_append (L L' : List (Formula α)) (B : Formula α) :
    curry (L ++ L') B = curry L (curry L' B) := by
  induction L with
  | nil => rfl
  | cons A L ih => simp [ih]

namespace Thm

/-- iterated prefixing: `X → Y` gives `(L ⇒ X) → (L ⇒ Y)`. -/
theorem curry_mono (L : List (Formula α)) {X Y : Formula α} (h : Thm (imp X Y)) :
    Thm (imp (curry L X) (curry L Y)) := by
  induction L with
  | nil => exact h
  | cons A L ih => exact pre A ih

/-- the order of the antecedents does not matter -/
theorem curry_perm {L L' : List (Formula α)} (hp : L.Perm L') (B : Formula α) :
    Thm (imp (curry L B) (curry L' B)) := by
  induction hp with
  | nil => exact axI B
  | cons x _ ih => exact pre x ih
  | swap x y L => exact axC y x (curry L B)
  | trans _ _ ih₁ ih₂ => exact trans ih₁ ih₂

/-- `(L ⇒ A) → ((A → Y) → (L ⇒ Y))` -/
theorem curry_suf (L : List (Formula α)) (A Y : Formula α) :
    Thm (imp (curry L A) (imp (imp A Y) (curry L Y))) := by
  induction L with
  | nil => exact assertion A Y
  | cons D L ih => exact trans (pre D ih) (axC D (imp A Y) (curry L Y))

end Thm

end Relevance

end
