module

public import RequestProject.Relevance.Sequent

/-!
# Weakening is not valid in relevance logic

We use the three-element *Sugihara matrix* to show that `R→` really forbids weakening:

* `Relevance.not_thm_K`: the weakening axiom `K`, `A → (B → A)`, is not a theorem of
  Church's system (for distinct variables `A`, `B`);
* `Relevance.Deriv.weakening_fails`: one may not add an unused hypothesis: `p → p` is
  deducible from no hypotheses, but not from the (unused) hypothesis `q`;
* `Relevance.LR.weakening_not_admissible`: likewise, the weakening rule is not admissible in
  the sequent calculus **LR→**.

The Sugihara matrix has the values `-1, 0, 1` (encoded as `0, 1, 2 : Fin 3`), designated
values `0, 1`, and `a → b = max(-a, b)` if `a ≤ b`, `min(-a, b)` otherwise.
-/

@[expose] public section

universe u

namespace Relevance

variable {α : Type u}

open Formula

/-- Implication of the three-element Sugihara matrix on `{-1, 0, 1}`, encoded as
`0, 1, 2 : Fin 3`. -/
def sugiharaImp : Fin 3 → Fin 3 → Fin 3
  | 0, _ => 2
  | 1, 0 => 0
  | 1, 1 => 1
  | 1, 2 => 2
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 2

/-- Evaluation of a formula in the Sugihara matrix under a valuation `v`. -/
def sugiharaEval (v : α → Fin 3) : Formula α → Fin 3
  | var x => v x
  | imp A B => sugiharaImp (sugiharaEval v A) (sugiharaEval v B)

/-- Soundness of Church's system for the Sugihara matrix: every theorem takes a designated
value (`0` or `1`, i.e. `1 ≤ ·` in the encoding) under every valuation. -/
theorem Thm.sugihara_sound {A : Formula α} (h : Thm A) (v : α → Fin 3) :
    1 ≤ sugiharaEval v A := by
  induction h with
  | axI A =>
    simp only [sugiharaEval]; generalize sugiharaEval v A = a; revert a; decide
  | axB A B C =>
    simp only [sugiharaEval]
    generalize sugiharaEval v A = a; generalize sugiharaEval v B = b
    generalize sugiharaEval v C = c; revert a b c; decide
  | axC A B C =>
    simp only [sugiharaEval]
    generalize sugiharaEval v A = a; generalize sugiharaEval v B = b
    generalize sugiharaEval v C = c; revert a b c; decide
  | axW A B =>
    simp only [sugiharaEval]
    generalize sugiharaEval v A = a; generalize sugiharaEval v B = b; revert a b; decide
  | @mp A B _ _ ih₁ ih₂ =>
    simp only [sugiharaEval] at ih₁
    revert ih₁ ih₂
    generalize sugiharaEval v A = a; generalize sugiharaEval v B = b; revert a b; decide

/-- **Weakening is not a theorem**: for distinct variables `p`, `q`, the axiom `K`
`p → (q → p)` is not a theorem of Church's system for `R→`. -/
theorem not_thm_K {p q : α} (hpq : p ≠ q) : ¬ Thm (imp (var p) (imp (var q) (var p))) := by
  classical
  intro h
  have := h.sugihara_sound (fun x => if x = p then 1 else 2)
  simp [sugiharaEval, hpq.symm, sugiharaImp] at this

/-- `q → (p → p)` is not a theorem for distinct variables `p`, `q`. -/
theorem not_thm_weak_id {p q : α} (hpq : p ≠ q) : ¬ Thm (imp (var q) (imp (var p) (var p))) := by
  classical
  intro h
  have := h.sugihara_sound (fun x => if x = p then 1 else 2)
  simp [sugiharaEval, hpq.symm, sugiharaImp] at this

/-- **Unused hypotheses are forbidden.** `p → p` is deducible (from no hypotheses), but it is
not deducible from the hypothesis `q` (with `q` distinct from `p`), since `q` would not be
used. -/
theorem Deriv.weakening_fails {p q : α} (hpq : p ≠ q) :
    Deriv 0 (imp (var p) (var p)) ∧ ¬ Deriv {var q} (imp (var p) (var p)) := by
  refine ⟨Deriv.thm (Thm.axI _), fun h => not_thm_weak_id hpq ?_⟩
  rw [← Deriv.nil_iff_thm, ← Deriv.deduction]
  simpa using h

/-- The weakening rule is not admissible in **LR→**: `⊢ p → p` is provable but
`q ⊢ p → p` is not (for distinct variables `p`, `q`). -/
theorem LR.weakening_not_admissible {p q : α} (hpq : p ≠ q) :
    LR 0 (imp (var p) (var p)) ∧ ¬ LR {var q} (imp (var p) (var p)) := by
  simpa only [Deriv.iff_LR] using Deriv.weakening_fails hpq

/-- `K` is not provable in **LR→**. -/
theorem LR.not_K {p q : α} (hpq : p ≠ q) : ¬ LR 0 (imp (var p) (imp (var q) (var p))) := by
  rw [LR.nil_iff_thm]; exact not_thm_K hpq

end Relevance

end
