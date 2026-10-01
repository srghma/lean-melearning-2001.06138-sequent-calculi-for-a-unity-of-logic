module

public import RequestProject.Logics.ILCLemmas

/-!
# Unlinearisation `ILLᵉ_ι ⟶ ILᵉ`: the translation `𝒯_!` of INC into ILC_ι

Every provable sequent `Δ ⊢ Γ` of **INC** is translated to the provable sequent
`!𝒯_!(Δ) ⊢ 𝒯_!(Γ)` of **ILC_ι**, i.e. to a provable sequent of the unlinearisation
`(ILC_ι)_!`.
-/

@[expose] public section

universe u

variable {α : Type u}

namespace ILe

open ILLe

lemma map_wn_T (Γ : Multiset (ILe.Formula α)) :
    (Γ.map ILe.Formula.wn).map T = (Γ.map T).map ILLe.Formula.wn := by
  simp only [Multiset.map_map]; rfl

/-- **Translation `𝒯_!` of INC into ILC_ι** (unlinearisation `ILLᵉ_ι ⟶ ILᵉ`): if `Δ ⊢ Γ`
is provable in **INC**, then `!𝒯_!(Δ) ⊢ 𝒯_!(Γ)` is provable in **ILC_ι**. -/
theorem INC.toILC {Δ Γ : Multiset (ILe.Formula α)} (h : INC Δ Γ) :
    Unlinearisation ILLe.Formula.bang (ILC true) (Δ.map T) (Γ.map T) := by
  unfold Unlinearisation
  induction h with
  | weakL A _ ih => msimpa using ILC.bangW (T A) ih
  | wnW B _ ih => msimpa [T] using ILC.wnW (T B) ih
  | contrL _ ih => msimpa using ILC.bangC (by msimpa using ih)
  | wnC _ ih => msimpa [T] using ILC.wnC (by msimpa [T] using ih)
  | wnD _ ih => msimpa [T] using ILC.wnD (by msimpa [T] using ih)
  | @wnL Δ Γ A _ ih =>
    have := ILC.bangWnL (Δ := Δ.map T) (Γ := Γ.map T) (A := T A) rfl
      (by rw [← map_wn_T]; msimpa using ih)
    rw [map_wn_T]; msimpa [T] using this
  | id A => exact (ILC.bangD (Δ := 0) (ILC.id (T A))).cast' (by ms_eq) (by ms_eq)
  | @cut Δ Γ Δ' Γ' B _ _ ih₁ ih₂ =>
    have l := ILC.bangR (Δ := Δ.map T) (Γ := Γ.map T) (by rw [← map_wn_T]; msimpa [T] using ih₁)
    have r := ILC.bangWnL (Δ := Δ'.map T) (Γ := Γ'.map T) (A := T B) rfl
      (by rw [← map_wn_T]; msimpa using ih₂)
    have := ILC.cut l r
    simp only [Multiset.map_add, map_wn_T]; msimpa using this
  | topL _ ih => msimpa [T] using ILC.bangD (ILC.topL ih)
  | topR => msimpa [T] using (ILC.topR (ι := true) (α := α))
  | ffL =>
    exact (ILC.bangD (Δ := 0) (ILC.bangD (Δ := 0) ILC.botL)).cast' (by ms_eq) (by simp)
  | @ffR Δ Γ _ ih =>
    have := ILC.bangR (Δ := Δ.map T) (Γ := Γ.map T) (ILC.botR (by rw [← map_wn_T]; exact ih))
    rw [Multiset.map_cons, map_wn_T]; msimpa [T] using this
  | withL₁ A₂ _ ih => msimpa [T] using ILC.bangWithL₁ (T A₂) (by msimpa using ih)
  | withL₂ A₁ _ ih => msimpa [T] using ILC.bangWithL₂ (T A₁) (by msimpa using ih)
  | @withR Δ Γ B₁ B₂ _ _ ih₁ ih₂ =>
    have := ILC.withR (by msimpa using ih₁) (by msimpa using ih₂)
    msimpa [T] using this
  | disjL _ _ ih₁ ih₂ =>
    msimpa [T] using ILC.bangD (ILC.plusL (by msimpa using ih₁) (by msimpa using ih₂))
  | @disjR₁ Δ Γ B₁ B₂ _ ih =>
    have := ILC.bangR (Δ := Δ.map T) (Γ := Γ.map T) (by rw [← map_wn_T]; msimpa using ih)
    rw [Multiset.map_cons, map_wn_T]; msimpa [T] using ILC.plusR₁ (.bang (T B₂)) this
  | @disjR₂ Δ Γ B₂ B₁ _ ih =>
    have := ILC.bangR (Δ := Δ.map T) (Γ := Γ.map T) (by rw [← map_wn_T]; msimpa using ih)
    rw [Multiset.map_cons, map_wn_T]; msimpa [T] using ILC.plusR₂ (.bang (T B₁)) this
  | @impL Δ Γ Θ Ξ A B _ _ ih₁ ih₂ =>
    have := ILC.bangLimpL (Θ := Θ.map T) (Ξ := Ξ.map T) (by msimpa using ih₁)
      (by rw [← map_wn_T]; msimpa using ih₂)
    rw [Multiset.map_add, map_wn_T]; msimpa [T] using this
  | @impR Δ Γ A B _ ih =>
    have := ILC.parR (ILC.negR (by msimpa using ih))
    msimpa [T, ILLe.Formula.limp] using this

end ILe

end
