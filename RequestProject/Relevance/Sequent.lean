module

public import RequestProject.Relevance.Church

/-!
# A sequent calculus for `R→` and the relevant deduction theorem

The sequent calculus **LR→** for the implicational relevance logic `R→`: it is the
implicational fragment of Gentzen's **LJ** *without the weakening rule* (but with
contraction). Contexts are multisets, which absorbs exchange.

Main results:

* `Relevance.LR.iff_thm`: a sequent `A₁, …, Aₙ ⊢ C` is provable in **LR→** iff
  `A₁ → (⋯ → (Aₙ → C))` is a theorem of Church's system; in particular
  `Relevance.LR.nil_iff_thm`: `⊢ A` is provable iff `A` is a theorem of Church's system.
* `Relevance.Deriv.iff_LR`: Church's deductions in which every hypothesis is used are exactly
  the provable sequents of **LR→**.
* `Relevance.Deriv.deduction`: Church's *relevant deduction theorem*: if `B` is deducible
  from `Γ, A` with every hypothesis (in particular `A`) used, then `A → B` is deducible
  from `Γ`, and conversely.
-/

@[expose] public section

universe u

/-- Close an equality of multisets (possibly built from lists) by normalising to sums of
singletons and using commutativity. -/
macro "rms_eq" : tactic =>
  `(tactic| (simp only [← Multiset.coe_add, ← Multiset.cons_coe, Multiset.coe_toList,
      Multiset.insert_eq_cons, ← Multiset.singleton_add, add_zero, zero_add,
      Multiset.coe_nil] <;> abel))

namespace Relevance

variable {α : Type u}

open Formula

/-- The sequent calculus **LR→** for `R→`: `LR Δ C` means that `Δ ⊢ C` is provable. There is
no weakening rule: every formula of `Δ` must be used. -/
inductive LR : Multiset (Formula α) → Formula α → Prop
  | id (A : Formula α) : LR {A} A
  /-- contraction -/
  | contr {Δ : Multiset (Formula α)} {A C : Formula α} : LR (A ::ₘ A ::ₘ Δ) C → LR (A ::ₘ Δ) C
  | cut {Δ Δ' : Multiset (Formula α)} {B C : Formula α} :
      LR Δ B → LR (B ::ₘ Δ') C → LR (Δ + Δ') C
  /-- `→L`, with the contexts of the two premises joined -/
  | impL {Δ Δ' : Multiset (Formula α)} {A B C : Formula α} :
      LR Δ A → LR (B ::ₘ Δ') C → LR (imp A B ::ₘ (Δ + Δ')) C
  /-- `→R` -/
  | impR {Δ : Multiset (Formula α)} {A B : Formula α} : LR (A ::ₘ Δ) B → LR Δ (imp A B)

namespace LR

theorem cast {Δ Δ' : Multiset (Formula α)} {C : Formula α} (h : LR Δ C) (e : Δ = Δ') :
    LR Δ' C := e ▸ h

/-- modus ponens is admissible in **LR→** -/
theorem mp {Δ Δ' : Multiset (Formula α)} {A B : Formula α} (h₁ : LR Δ (imp A B))
    (h₂ : LR Δ' A) : LR (Δ + Δ') B := by
  have h₃ : LR (imp A B ::ₘ (Δ' + 0)) B := impL h₂ (id B)
  simpa using cut h₁ h₃

/-- `→R` is invertible -/
theorem impR_inv {Δ : Multiset (Formula α)} {A B : Formula α} (h : LR Δ (imp A B)) :
    LR (A ::ₘ Δ) B :=
  (mp h (id A)).cast (by rms_eq)

/-- Church's axioms are provable in **LR→**, hence every theorem of Church's system. -/
theorem of_thm {A : Formula α} (h : Thm A) : LR 0 A := by
  induction h with
  | axI A => exact impR (id A)
  | axB A B C =>
    have h1 : LR (imp A B ::ₘ ({A} + 0)) B := impL (id A) (id B)
    have h2 : LR (imp C A ::ₘ ({C} + {imp A B})) B :=
      impL (id C) (h1.cast (by rms_eq))
    exact impR (impR (impR (h2.cast (by rms_eq))))
  | axC A B C =>
    have h1 : LR (imp B C ::ₘ ({B} + 0)) C := impL (id B) (id C)
    have h2 : LR (imp A (imp B C) ::ₘ ({A} + {B})) C :=
      impL (id A) (h1.cast (by simp))
    exact impR (impR (impR (h2.cast (by rms_eq))))
  | axW A B =>
    have h1 : LR (imp A B ::ₘ ({A} + 0)) B := impL (id A) (id B)
    have h2 : LR (imp A (imp A B) ::ₘ ({A} + {A})) B :=
      impL (id A) (h1.cast (by simp))
    exact impR (impR (contr (h2.cast (by rms_eq))))
  | mp _ _ ih₁ ih₂ => simpa using mp ih₁ ih₂

/-- From `Δ ⊢ L ⇒ C` to `Δ, L ⊢ C`. -/
theorem of_curry {Δ : Multiset (Formula α)} {C : Formula α} (L : List (Formula α))
    (h : LR Δ (curry L C)) : LR (Δ + (L : Multiset (Formula α))) C := by
  induction L generalizing Δ with
  | nil => simpa using h
  | cons A L ih => exact (ih (impR_inv h)).cast (by rms_eq)

private theorem thm_transfer {L L' : List (Formula α)} {C : Formula α}
    (e : (L : Multiset (Formula α)) = L') (h : Thm (curry L C)) : Thm (curry L' C) :=
  Thm.mp (Thm.curry_perm (Multiset.coe_eq_coe.mp e) C) h

/-- Soundness of **LR→** with respect to Church's system: a provable sequent
`A₁, …, Aₙ ⊢ C` gives the theorem `A₁ → (⋯ → (Aₙ → C))`, for any listing of the context. -/
theorem toThm {Δ : Multiset (Formula α)} {C : Formula α} (h : LR Δ C) :
    ∀ L : List (Formula α), (L : Multiset (Formula α)) = Δ → Thm (curry L C) := by
  induction h with
  | id A =>
    intro L hL
    obtain rfl : L = [A] := by simpa using hL
    exact Thm.axI A
  | @contr Δ A C _ ih =>
    intro L hL
    have := ih (A :: A :: Δ.toList) (by rms_eq)
    exact thm_transfer (L := A :: Δ.toList) (by rw [hL]; rms_eq) (Thm.mp (Thm.axW _ _) this)
  | @cut Δ Δ' B C _ _ ih₁ ih₂ =>
    intro L hL
    have h₁ := ih₁ Δ.toList (by simp)
    have h₂ := ih₂ (B :: Δ'.toList) (by rms_eq)
    have := Thm.mp (Thm.curry_mono Δ.toList h₂) h₁
    rw [← curry_append] at this
    exact thm_transfer (by rw [hL]; rms_eq) this
  | @impL Δ Δ' A B C _ _ ih₁ ih₂ =>
    intro L hL
    have h₁ := ih₁ Δ.toList (by simp)
    have h₂ := ih₂ (B :: Δ'.toList) (by rms_eq)
    have h₃ := Thm.trans (Thm.pre A h₂)
      (Thm.mp (Thm.curry_suf Δ.toList A (curry Δ'.toList C)) h₁)
    rw [← curry_append] at h₃
    exact thm_transfer (L := imp A B :: (Δ.toList ++ Δ'.toList)) (by rw [hL]; rms_eq) h₃
  | @impR Δ A B _ ih =>
    intro L hL
    have := ih (A :: Δ.toList) (by rms_eq)
    have h' : Thm (curry (Δ.toList ++ [A]) B) :=
      thm_transfer (L := A :: Δ.toList) (by rw [Multiset.coe_eq_coe]; exact (List.perm_append_singleton A _).symm) this
    rw [curry_append] at h'
    exact thm_transfer (by rw [hL]; rms_eq) h'

/-- **LR→** and Church's system agree: `A₁, …, Aₙ ⊢ C` is provable iff
`A₁ → (⋯ → (Aₙ → C))` is a theorem. -/
theorem iff_thm (L : List (Formula α)) (C : Formula α) :
    LR (L : Multiset (Formula α)) C ↔ Thm (curry L C) :=
  ⟨fun h => h.toThm L rfl, fun h => (of_curry L (of_thm h)).cast (by simp)⟩

/-- `⊢ A` is provable in **LR→** iff `A` is a theorem of Church's system. -/
theorem nil_iff_thm (A : Formula α) : LR 0 A ↔ Thm A := iff_thm [] A

end LR

namespace Deriv

theorem cast {Γ Γ' : Multiset (Formula α)} {C : Formula α} (h : Deriv Γ C) (e : Γ = Γ') :
    Deriv Γ' C := e ▸ h

theorem toLR {Γ : Multiset (Formula α)} {A : Formula α} (h : Deriv Γ A) : LR Γ A := by
  induction h with
  | hyp A => exact LR.id A
  | thm h => exact LR.of_thm h
  | mp _ _ ih₁ ih₂ => exact LR.mp ih₁ ih₂
  | contr _ ih => exact LR.contr ih

private theorem of_curry {Γ : Multiset (Formula α)} {C : Formula α} (L : List (Formula α))
    (h : Deriv Γ (curry L C)) : Deriv (Γ + (L : Multiset (Formula α))) C := by
  induction L generalizing Γ with
  | nil => simpa using h
  | cons A L ih => exact (ih (mp h (hyp A))).cast (by rms_eq)

theorem ofLR {Γ : Multiset (Formula α)} {A : Formula α} (h : LR Γ A) : Deriv Γ A :=
  (of_curry Γ.toList (thm (h.toThm Γ.toList (by simp)))).cast (by simp)

/-- Church's deductions in which every hypothesis is used coincide with the provable
sequents of **LR→**. -/
theorem iff_LR (Γ : Multiset (Formula α)) (A : Formula α) : Deriv Γ A ↔ LR Γ A :=
  ⟨toLR, ofLR⟩

/-- A formula is deducible from no hypotheses iff it is a theorem. -/
theorem nil_iff_thm (A : Formula α) : Deriv 0 A ↔ Thm A := by
  rw [iff_LR, LR.nil_iff_thm]

/-- **Church's relevant deduction theorem.** `B` is deducible from the hypotheses `Γ, A`
(all of them, in particular `A`, being used) iff `A → B` is deducible from `Γ`. -/
theorem deduction (Γ : Multiset (Formula α)) (A B : Formula α) :
    Deriv (A ::ₘ Γ) B ↔ Deriv Γ (imp A B) :=
  ⟨fun h => ofLR (LR.impR h.toLR), fun h => (mp h (hyp A)).cast (by rms_eq)⟩

end Deriv

end Relevance

end
