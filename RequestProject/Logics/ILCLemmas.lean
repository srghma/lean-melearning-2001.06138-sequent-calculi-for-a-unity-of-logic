module

public import RequestProject.Logics.Util

/-!
# Structural lemmas for ILC / ILC_ι
-/

@[expose] public section

universe u

variable {α : Type u}

namespace ILLe.ILC

open Formula

variable {ι : Bool}

lemma cast' {Δ Γ Δ' Γ' : Multiset (Formula α)} (h : ILC ι Δ Γ) (h₁ : Δ = Δ') (h₂ : Γ = Γ') :
    ILC ι Δ' Γ' := h₁ ▸ h₂ ▸ h

/-- Contraction of a whole multiset of `!`-formulas on the left. -/
lemma bangC_ctx (Θ : Multiset (Formula α)) :
    ∀ {Δ Γ : Multiset (Formula α)}, ILC ι (Θ.map bang + Θ.map bang + Δ) Γ →
      ILC ι (Θ.map bang + Δ) Γ := by
  induction Θ using Multiset.induction_on with
  | empty => intro Δ Γ h; simpa using h
  | cons a Θ ih =>
    intro Δ Γ h
    have h' : ILC ι (bang a ::ₘ bang a ::ₘ (Θ.map bang + Θ.map bang + Δ)) Γ := h.cast' (by
      simp only [Multiset.map_cons, Multiset.cons_add, Multiset.add_cons]) rfl
    have := ih (Δ := bang a ::ₘ Δ) ((bangC h').cast' (by simp [Multiset.add_cons]) rfl)
    exact this.cast' (by simp [Multiset.add_cons]) rfl

/-- Contraction of a whole multiset of `?`-formulas on the right. -/
lemma wnC_ctx (Γ : Multiset (Formula α)) :
    ∀ {Δ Ξ : Multiset (Formula α)}, ILC ι Δ (Γ.map wn + Γ.map wn + Ξ) →
      ILC ι Δ (Γ.map wn + Ξ) := by
  induction Γ using Multiset.induction_on with
  | empty => intro Δ Ξ h; simpa using h
  | cons a Γ ih =>
    intro Δ Ξ h
    have h' : ILC ι Δ (wn a ::ₘ wn a ::ₘ (Γ.map wn + Γ.map wn + Ξ)) := h.cast' rfl (by
      simp only [Multiset.map_cons, Multiset.cons_add, Multiset.add_cons])
    have := ih (Ξ := wn a ::ₘ Ξ) ((wnC h').cast' rfl (by simp [Multiset.add_cons]))
    exact this.cast' rfl (by simp [Multiset.add_cons])

/-- `!(A₁ & A₂) ⊢ !Aᵢ` (for `i = 1`). -/
lemma bang_with_fst (A₁ A₂ : Formula α) : ILC ι {bang («with» A₁ A₂)} {bang A₁} := by
  have h1 := withL₁ (ι := ι) (Δ := 0) (Γ := {A₁}) A₂ (id A₁)
  have h2 := bangD (Δ := 0) h1
  exact (bangR (Δ := {«with» A₁ A₂}) (Γ := 0) (h2.cast' (by ms_eq) (by ms_eq))).cast'
    (by ms_eq) (by ms_eq)

/-- `!(A₁ & A₂) ⊢ !Aᵢ` (for `i = 2`). -/
lemma bang_with_snd (A₁ A₂ : Formula α) : ILC ι {bang («with» A₁ A₂)} {bang A₂} := by
  have h1 := withL₂ (ι := ι) (Δ := 0) (Γ := {A₂}) A₁ (id A₂)
  have h2 := bangD (Δ := 0) h1
  exact (bangR (Δ := {«with» A₁ A₂}) (Γ := 0) (h2.cast' (by ms_eq) (by ms_eq))).cast'
    (by ms_eq) (by ms_eq)

/-- Cutting against a sequent `{C} ⊢ {D}` replaces `D` by `C` on the left. -/
lemma cut_left {Δ Γ : Multiset (Formula α)} {C D : Formula α} (h₁ : ILC ι {C} {D})
    (h₂ : ILC ι (D ::ₘ Δ) Γ) : ILC ι (C ::ₘ Δ) Γ :=
  (cut (Γ := 0) (h₁.cast' rfl (by ms_eq)) h₂).cast' (by ms_eq) (by ms_eq)

/-- Cutting against a sequent `{C} ⊢ {D}` replaces `C` by `D` on the right. -/
lemma cut_right {Δ Γ : Multiset (Formula α)} {C D : Formula α} (h₁ : ILC ι Δ (C ::ₘ Γ))
    (h₂ : ILC ι {C} {D}) : ILC ι Δ (D ::ₘ Γ) :=
  (cut (Δ' := 0) h₁ (h₂.cast' (by ms_eq) rfl)).cast' (by ms_eq) (by ms_eq)

/-- The rule `!&L`: `!Δ, !Aᵢ ⊢ Γ` / `!Δ, !(A₁ & A₂) ⊢ Γ`, derived by a cut. -/
lemma bangWithL₁ {Δ Γ : Multiset (Formula α)} {A₁ : Formula α} (A₂ : Formula α)
    (h : ILC ι (bang A₁ ::ₘ Δ) Γ) : ILC ι (bang («with» A₁ A₂) ::ₘ Δ) Γ :=
  cut_left (bang_with_fst A₁ A₂) h

/-- The rule `!&L` for the second component. -/
lemma bangWithL₂ {Δ Γ : Multiset (Formula α)} {A₂ : Formula α} (A₁ : Formula α)
    (h : ILC ι (bang A₂ ::ₘ Δ) Γ) : ILC ι (bang («with» A₁ A₂) ::ₘ Δ) Γ :=
  cut_left (bang_with_snd A₁ A₂) h

/-- The rule `!⊸L`: from `!Θ ⊢ A, ?Ξ` and `!Δ, !B ⊢ Γ` derive
`!Δ, !Θ, !(!A ⊸ B) ⊢ Γ, ?Ξ`. -/
lemma bangLimpL {Δ Θ Γ Ξ : Multiset (Formula α)} {A B : Formula α}
    (h₁ : ILC ι (bang B ::ₘ Δ) Γ) (h₂ : ILC ι (Θ.map bang) (A ::ₘ Ξ.map wn)) :
    ILC ι (bang (limp (bang A) B) ::ₘ (Δ + Θ.map bang)) (Γ + Ξ.map wn) := by
  have s1 := bangR h₂
  have s2 := negL s1
  have s3 := parL (Δ₂ := 0) (Γ₂ := {B}) s2 (id B)
  have s4 := bangD s3
  have s5 := bangR (Δ := limp (bang A) B ::ₘ Θ) (Γ := Ξ) (s4.cast' (by simp [limp]) (by ms_eq))
  exact (cut s5 h₁).cast' (by simp [add_comm]) (by ms_eq)

end ILLe.ILC

end
