module

public import RequestProject.Logics.ILCLemmas

/-!
# Classicalisation `ILLᵉ_ι ⟶ CLL⁻`: the translation `𝒯_?` of CLC into ILC_ι

Every provable sequent `Δ ⊢ Γ` of **CLC** is translated to the provable sequent
`𝒯_?(Δ) ⊢ ?𝒯_?(Γ)` of **ILC_ι**, i.e. to a provable sequent of the classicalisation
`(ILC_ι)_?`.
-/

@[expose] public section

universe u

variable {α : Type u}

namespace CLLneg

open ILLe

lemma map_bang_T (Δ : Multiset (CLLneg.Formula α)) :
    (Δ.map CLLneg.Formula.bang).map T = (Δ.map T).map ILLe.Formula.bang := by
  simp only [Multiset.map_map]; rfl

/-- **Translation `𝒯_?` of CLC into ILC_ι** (classicalisation `ILLᵉ_ι ⟶ CLL⁻`): if `Δ ⊢ Γ`
is provable in **CLC**, then `𝒯_?(Δ) ⊢ ?𝒯_?(Γ)` is provable in **ILC_ι**. -/
theorem CLC.toILC {Δ Γ : Multiset (CLLneg.Formula α)} (h : CLC Δ Γ) :
    Classicalisation ILLe.Formula.wn (ILC true) (Δ.map T) (Γ.map T) := by
  unfold Classicalisation
  induction h with
  | bangW A _ ih => msimpa [T] using ILC.bangW (T A) ih
  | weakR B _ ih => msimpa using ILC.wnW (T B) ih
  | bangC _ ih => msimpa [T] using ILC.bangC (by msimpa [T] using ih)
  | contrR _ ih => msimpa using ILC.wnC (by msimpa using ih)
  | bangD _ ih => msimpa [T] using ILC.bangD (by msimpa using ih)
  | @bangR Δ Γ B _ ih =>
    have := ILC.wnBangR (Δ := Δ.map T) (Γ := Γ.map T) (B := T B) rfl
      (by rw [← map_bang_T]; msimpa using ih)
    rw [map_bang_T]; msimpa [T] using this
  | id A => exact (ILC.wnD (Γ := 0) (ILC.id (T A))).cast' (by ms_eq) (by ms_eq)
  | @cut Δ Γ Δ' Γ' B _ _ ih₁ ih₂ =>
    have l := ILC.wnBangR (Δ := Δ.map T) (Γ := Γ.map T) (B := T B) rfl
      (by rw [← map_bang_T]; msimpa using ih₁)
    have r := ILC.wnL (Δ := Δ'.map T) (Γ := Γ'.map T) (A := .bang (T B))
      (by rw [← map_bang_T]; msimpa [T] using ih₂)
    have := ILC.cut l r
    simp only [Multiset.map_add, map_bang_T]; msimpa using this
  | @ttL Δ Γ _ ih =>
    have := ILC.wnL (Δ := Δ.map T) (Γ := Γ.map T) (A := .top)
      (ILC.topL (by rw [← map_bang_T]; msimpa using ih))
    rw [Multiset.map_cons, map_bang_T]; msimpa [T] using this
  | ttR =>
    exact (ILC.wnD (Γ := 0) (ILC.wnD (Γ := 0) ILC.topR)).cast' (by simp) (by simp [T])
  | botL => exact (ILC.botL).cast' (by simp [T]) (by simp)
  | botR _ ih => msimpa [T] using ILC.wnW .bot ih
  | @conjL₁ Δ Γ A₁ A₂ _ ih =>
    have := ILC.withL₁ (.wn (T A₂)) (ILC.wnL (Δ := Δ.map T) (Γ := Γ.map T) (A := T A₁)
      (by rw [← map_bang_T]; msimpa using ih))
    rw [Multiset.map_cons, map_bang_T]; msimpa [T] using this
  | @conjL₂ Δ Γ A₂ A₁ _ ih =>
    have := ILC.withL₂ (.wn (T A₁)) (ILC.wnL (Δ := Δ.map T) (Γ := Γ.map T) (A := T A₂)
      (by rw [← map_bang_T]; msimpa using ih))
    rw [Multiset.map_cons, map_bang_T]; msimpa [T] using this
  | conjR _ _ ih₁ ih₂ =>
    msimpa [T] using ILC.wnD (ILC.withR (Γ := Multiset.map ILLe.Formula.wn (Multiset.map T _))
      (by msimpa using ih₁) (by msimpa using ih₂))
  | plusL _ _ ih₁ ih₂ =>
    msimpa [T] using ILC.plusL (by msimpa using ih₁) (by msimpa using ih₂)
  | @plusR₁ Δ Γ B₁ B₂ _ ih =>
    have k := ILC.wnL (ι := true) (Δ := 0) (Γ := {.plus (T B₁) (T B₂)}) (A := T B₁)
      ((ILC.wnD (Γ := 0) (ILC.plusR₁ (Γ := 0) (T B₂) (ILC.id (T B₁)))).cast' (by ms_eq)
        (by ms_eq))
    msimpa [T] using ILC.cut_right (by msimpa using ih) (k.cast' (by ms_eq) (by ms_eq))
  | @plusR₂ Δ Γ B₂ B₁ _ ih =>
    have k := ILC.wnL (ι := true) (Δ := 0) (Γ := {.plus (T B₁) (T B₂)}) (A := T B₂)
      ((ILC.wnD (Γ := 0) (ILC.plusR₂ (Γ := 0) (T B₁) (ILC.id (T B₂)))).cast' (by ms_eq)
        (by ms_eq))
    msimpa [T] using ILC.cut_right (by msimpa using ih) (k.cast' (by ms_eq) (by ms_eq))
  | @impL Δ Γ Θ Ξ A B _ _ ih₁ ih₂ =>
    -- `!(A ⊸ ?B), ?A ⊢ ?B`
    have k1 := ILC.negL (ι := true) (Δ := {T A}) (Γ := 0) (B := T A)
      ((ILC.id (T A)).cast' rfl (by ms_eq))
    have k2 := ILC.parL (Δ₂ := 0) (Γ₂ := {.wn (T B)}) k1 (ILC.id (.wn (T B)))
    have k3 := ILC.bangD k2
    have k4 := ILC.wnL (Δ := {ILLe.Formula.limp (T A) (.wn (T B))}) (Γ := {T B}) (A := T A)
      (k3.cast' (by simp only [ILLe.Formula.limp]; ms_eq) (by ms_eq))
    have c1 := ILC.cut (by msimpa using ih₂) k4
    have r := ILC.wnL (Δ := Δ.map T) (Γ := Γ.map T) (A := T B)
      (by rw [← map_bang_T]; msimpa using ih₁)
    have c2 := ILC.cut (c1.cast' rfl (by rw [add_comm]; ms_eq)) r
    simp only [Multiset.map_add, Multiset.map_cons, map_bang_T]
    exact c2.cast' (by simp only [T]; ms_eq) (by ms_eq)
  | impR _ ih =>
    msimpa [T, ILLe.Formula.limp] using ILC.wnD (ILC.parR (ILC.negR (by msimpa using ih)))

end CLLneg

end
