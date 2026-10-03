module

public import RequestProject.Logics.Util

/-!
# Unlinearisation `CLL⁻ ⟶ CL`: the translation `𝒯_!` of LK into CLC

**Paper Section 3.3, Lemma 3.22** (`Translation 𝒯_! of LK into CLC`, PDF p. 26):
Every provable sequent `Δ ⊢ Γ` of **LK** is translated to the provable sequent
`!𝒯_!(Δ) ⊢ 𝒯_!(Γ)` of **CLC**, i.e. to a provable sequent of the unlinearisation `CLC_!`.
-/

@[expose] public section

universe u

variable {α : Type u}

namespace CLLneg.CLC

open Formula

lemma cast' {Δ Γ Δ' Γ' : Multiset (Formula α)} (h : CLC Δ Γ) (h₁ : Δ = Δ') (h₂ : Γ = Γ') :
    CLC Δ' Γ' := h₁ ▸ h₂ ▸ h

/-- Contraction of a whole multiset of `!`-formulas on the left. -/
lemma bangC_ctx (Θ : Multiset (Formula α)) :
    ∀ {Δ Γ : Multiset (Formula α)}, CLC (Θ.map bang + Θ.map bang + Δ) Γ →
      CLC (Θ.map bang + Δ) Γ := by
  induction Θ using Multiset.induction_on with
  | empty => intro Δ Γ h; simpa using h
  | cons a Θ ih =>
    intro Δ Γ h
    have h' : CLC (bang a ::ₘ bang a ::ₘ (Θ.map bang + Θ.map bang + Δ)) Γ := h.cast' (by
      simp only [Multiset.map_cons, Multiset.cons_add, Multiset.add_cons]) rfl
    have := ih (Δ := bang a ::ₘ Δ) ((bangC h').cast' (by simp [Multiset.add_cons]) rfl)
    exact this.cast' (by simp [Multiset.add_cons]) rfl

/-- Contraction of a whole multiset on the right. -/
lemma contrR_ctx (Γ : Multiset (Formula α)) :
    ∀ {Δ Ξ : Multiset (Formula α)}, CLC Δ (Γ + Γ + Ξ) → CLC Δ (Γ + Ξ) := by
  induction Γ using Multiset.induction_on with
  | empty => intro Δ Ξ h; simpa using h
  | cons a Γ ih =>
    intro Δ Ξ h
    have h' : CLC Δ (a ::ₘ a ::ₘ (Γ + Γ + Ξ)) := h.cast' rfl (by
      simp only [Multiset.cons_add, Multiset.add_cons])
    have := ih (Ξ := a ::ₘ Ξ) ((contrR h').cast' rfl (by simp [Multiset.add_cons]))
    exact this.cast' rfl (by simp [Multiset.add_cons])

end CLLneg.CLC

namespace CL

open CLLneg

lemma map_bang_Tbang (Δ : Multiset (CL.Formula α)) :
    (Δ.map Tbang).map CLLneg.Formula.bang = Δ.map (fun A => .bang (Tbang A)) := by
  simp only [Multiset.map_map]; rfl

/-- **Translation `𝒯_!` of LK into CLC** (unlinearisation `CLL⁻ ⟶ CL`) —
**Paper Section 3.3, Lemma 3.22** (`Translation 𝒯_! of LK into CLC`, PDF p. 26):
if `Δ ⊢ Γ` is provable in **LK**, then `!𝒯_!(Δ) ⊢ 𝒯_!(Γ)` is provable in **CLC**. -/
theorem LK.toCLC {Δ Γ : Multiset (CL.Formula α)} (h : LK Δ Γ) :
    Unlinearisation CLLneg.Formula.bang CLC (Δ.map Tbang) (Γ.map Tbang) := by
  unfold Unlinearisation
  induction h with
  | weakL A _ ih => msimpa using CLC.bangW (Tbang A) ih
  | weakR B _ ih => msimpa using CLC.weakR (Tbang B) ih
  | contrL _ ih => msimpa using CLC.bangC (by msimpa using ih)
  | contrR _ ih => msimpa using CLC.contrR (by msimpa using ih)
  | id A => exact (CLC.bangD (Δ := 0) (CLC.id (Tbang A))).cast' (by ms_eq) (by ms_eq)
  | @cut Δ Γ Δ' Γ' B _ _ ih₁ ih₂ =>
    msimpa using CLC.cut (Δ := Δ.map Tbang) (Δ' := Δ'.map Tbang) (by msimpa using ih₁)
      (by msimpa using ih₂)
  | @ttL Δ Γ _ ih => msimpa [Tbang] using CLC.bangD (Δ := Δ.map Tbang) (CLC.ttL ih)
  | ttR => exact CLC.ttR.cast' (by simp) (by simp [Tbang])
  | ffL =>
    exact (CLC.bangD (Δ := 0) (CLC.bangD (Δ := 0) CLC.botL)).cast' (by ms_eq) (by simp)
  | ffR _ ih => msimpa [Tbang] using CLC.weakR _ ih
  | @conjL₁ Δ Γ A₁ A₂ _ ih =>
    have k := CLC.bangD (Δ := 0) (CLC.conjL₁ (Δ := 0) (Tbang A₂)
      ((CLC.id (Tbang A₁)).cast' (by ms_eq) rfl))
    have := CLC.cut (Δ := {CLLneg.Formula.conj (Tbang A₁) (Tbang A₂)}) (Γ := 0) (Δ' := Δ.map Tbang)
      (k.cast' (by ms_eq) (by ms_eq)) (by msimpa using ih)
    exact this.cast' (by simp [Tbang]) (by simp)
  | @conjL₂ Δ Γ A₂ A₁ _ ih =>
    have k := CLC.bangD (Δ := 0) (CLC.conjL₂ (Δ := 0) (Tbang A₁)
      ((CLC.id (Tbang A₂)).cast' (by ms_eq) rfl))
    have := CLC.cut (Δ := {CLLneg.Formula.conj (Tbang A₁) (Tbang A₂)}) (Γ := 0) (Δ' := Δ.map Tbang)
      (k.cast' (by ms_eq) (by ms_eq)) (by msimpa using ih)
    exact this.cast' (by simp [Tbang]) (by simp)
  | conjR _ _ ih₁ ih₂ =>
    msimpa [Tbang] using CLC.conjR (by msimpa using ih₁) (by msimpa using ih₂)
  | @disjL Δ Γ A₁ A₂ _ _ ih₁ ih₂ =>
    msimpa [Tbang] using CLC.bangD (Δ := Δ.map Tbang)
      (CLC.plusL (by msimpa using ih₁) (by msimpa using ih₂))
  | @disjR₁ Δ Γ B₁ B₂ _ ih =>
    msimpa [Tbang] using CLC.plusR₁ (.bang (Tbang B₂))
      (CLC.bangR (Δ := Δ.map Tbang) (by msimpa using ih))
  | @disjR₂ Δ Γ B₂ B₁ _ ih =>
    msimpa [Tbang] using CLC.plusR₂ (.bang (Tbang B₁))
      (CLC.bangR (Δ := Δ.map Tbang) (by msimpa using ih))
  | @impL Δ Γ A B _ _ ih₁ ih₂ =>
    -- `!(!A ↬ B) ⊢ !A ↬ !B`
    have k1 := CLC.impL (Δ := 0) (Γ := {Tbang B}) (Θ := {.bang (Tbang A)}) (Ξ := 0)
      (A := .bang (Tbang A)) (B := Tbang B) ((CLC.id _).cast' (by ms_eq) rfl)
      ((CLC.id _).cast' rfl (by ms_eq))
    have k2 := CLC.bangR (Δ := CLLneg.Formula.imp (.bang (Tbang A)) (Tbang B) ::ₘ {Tbang A})
      (Γ := 0) (B := Tbang B)
      (k1.cast' (by ms_eq) (by ms_eq))
    have k3 := CLC.impR (Δ := {CLLneg.Formula.imp (.bang (Tbang A)) (Tbang B)}) (Γ := 0)
      (A := .bang (Tbang A)) (B := .bang (Tbang B))
      (k2.cast' (by ms_eq) rfl)
    -- `!Δ, !(!A ↬ !B) ⊢ Γ`
    have m1 := CLC.impL (Δ := Δ.map Tbang) (Θ := (Δ.map Tbang).map .bang) (Ξ := Γ.map Tbang)
      (A := .bang (Tbang A)) (B := .bang (Tbang B)) (by msimpa using ih₂)
      (CLC.bangR (Δ := Δ.map Tbang) (by msimpa using ih₁))
    have m2 := CLC.contrR_ctx (Γ.map Tbang) (Ξ := 0) (CLC.bangC_ctx (Δ.map Tbang)
      (Δ := {CLLneg.Formula.bang (.imp (.bang (Tbang A)) (.bang (Tbang B)))})
      (m1.cast' (by ms_eq) (by ms_eq)))
    have := CLC.cut (Δ' := Δ.map Tbang) k3 (m2.cast' (by ms_eq) (by ms_eq))
    exact this.cast' (by simp only [Multiset.map_cons, Tbang]; ms_eq) (by ms_eq)
  | @impR Δ Γ A B _ ih =>
    msimpa [Tbang] using CLC.impR (Δ := Δ.map Tbang) (by msimpa using ih)

end CL

end
