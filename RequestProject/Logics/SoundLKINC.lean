module

public import RequestProject.Logics.Util

/-!
# Classicalisation `ILᵉ ⟶ CL`: the translation `𝒯_?` of LK into INC

Every provable sequent `Δ ⊢ Γ` of **LK** is translated to the provable sequent
`𝒯_?(Δ) ⊢ ?𝒯_?(Γ)` of **INC**, i.e. to a provable sequent of the classicalisation `INC_?`.
-/

@[expose] public section

universe u

variable {α : Type u}

namespace ILe.INC

open Formula

lemma cast' {Δ Γ Δ' Γ' : Multiset (Formula α)} (h : INC Δ Γ) (h₁ : Δ = Δ') (h₂ : Γ = Γ') :
    INC Δ' Γ' := h₁ ▸ h₂ ▸ h

/-- Contraction of a whole multiset on the left. -/
lemma contrL_ctx (Θ : Multiset (Formula α)) :
    ∀ {Δ Γ : Multiset (Formula α)}, INC (Θ + Θ + Δ) Γ → INC (Θ + Δ) Γ := by
  induction Θ using Multiset.induction_on with
  | empty => intro Δ Γ h; simpa using h
  | cons a Θ ih =>
    intro Δ Γ h
    have h' : INC (a ::ₘ a ::ₘ (Θ + Θ + Δ)) Γ := h.cast' (by
      simp only [Multiset.cons_add, Multiset.add_cons]) rfl
    have := ih (Δ := a ::ₘ Δ) ((contrL h').cast' (by simp [Multiset.add_cons]) rfl)
    exact this.cast' (by simp [Multiset.add_cons]) rfl

/-- Contraction of a whole multiset of `?`-formulas on the right. -/
lemma wnC_ctx (Γ : Multiset (Formula α)) :
    ∀ {Δ Ξ : Multiset (Formula α)}, INC Δ (Γ.map wn + Γ.map wn + Ξ) → INC Δ (Γ.map wn + Ξ) := by
  induction Γ using Multiset.induction_on with
  | empty => intro Δ Ξ h; simpa using h
  | cons a Γ ih =>
    intro Δ Ξ h
    have h' : INC Δ (wn a ::ₘ wn a ::ₘ (Γ.map wn + Γ.map wn + Ξ)) := h.cast' rfl (by
      simp only [Multiset.map_cons, Multiset.cons_add, Multiset.add_cons])
    have := ih (Ξ := wn a ::ₘ Ξ) ((wnC h').cast' rfl (by simp [Multiset.add_cons]))
    exact this.cast' rfl (by simp [Multiset.add_cons])

end ILe.INC

namespace CL

open ILe


/-- **Translation `𝒯_?` of LK into INC** (classicalisation `ILᵉ ⟶ CL`): if `Δ ⊢ Γ` is
provable in **LK**, then `𝒯_?(Δ) ⊢ ?𝒯_?(Γ)` is provable in **INC**. -/
theorem LK.toINC {Δ Γ : Multiset (CL.Formula α)} (h : LK Δ Γ) :
    Classicalisation ILe.Formula.wn INC (Δ.map Twn) (Γ.map Twn) := by
  unfold Classicalisation
  induction h with
  | weakL A _ ih => msimpa [Twn] using INC.weakL _ ih
  | weakR B _ ih => msimpa [Twn] using INC.wnW _ ih
  | contrL _ ih => msimpa [Twn] using INC.contrL (by msimpa [Twn] using ih)
  | contrR _ ih => msimpa [Twn] using INC.wnC (by msimpa [Twn] using ih)
  | id A => msimpa [Twn] using INC.wnD (Γ := 0) (by msimpa [Twn] using INC.id (Twn A))
  | cut _ _ ih₁ ih₂ =>
    msimpa [Twn] using INC.cut (Γ := Multiset.map Twn _) (by msimpa [Twn] using ih₁) (by msimpa [Twn] using ih₂)
  | ttL _ ih =>
    msimpa [Twn] using INC.wnL (Γ := Multiset.map Twn _) (INC.topL ih)
  | ttR =>
    msimpa [Twn] using INC.wnD (Γ := 0) (INC.wnD (Γ := 0) INC.topR)
  | ffL => msimpa [Twn] using INC.ffL
  | ffR _ ih => msimpa [Twn] using INC.wnW _ ih
  | conjL₁ A₂ _ ih =>
    msimpa [Twn] using INC.withL₁ (.wn (Twn A₂))
      (INC.wnL (Γ := Multiset.map Twn _) (by msimpa [Twn] using ih))
  | conjL₂ A₁ _ ih =>
    msimpa [Twn] using INC.withL₂ (.wn (Twn A₁))
      (INC.wnL (Γ := Multiset.map Twn _) (by msimpa [Twn] using ih))
  | conjR _ _ ih₁ ih₂ =>
    msimpa [Twn] using INC.wnD (INC.withR (Γ := Multiset.map Twn _)
      (by msimpa [Twn] using ih₁) (by msimpa [Twn] using ih₂))
  | disjL _ _ ih₁ ih₂ =>
    msimpa [Twn] using INC.disjL (by msimpa [Twn] using ih₁) (by msimpa [Twn] using ih₂)
  | @disjR₁ Δ Γ B₁ B₂ _ ih =>
    have key : INC {Twn B₁} {.wn (Twn (Formula.disj B₁ B₂))} :=
      INC.wnD (Γ := 0) (by msimpa [Twn] using INC.disjR₁ (Γ := 0) (Twn B₂) (INC.id (Twn B₁)))
    have := INC.cut (Γ := Γ.map Twn) (Γ' := {Twn (Formula.disj B₁ B₂)}) (by msimpa [Twn] using ih)
      (by msimpa [Twn] using key)
    exact this.cast' (by simp) (by simp [add_comm])
  | @disjR₂ Δ Γ B₂ B₁ _ ih =>
    have key : INC {Twn B₂} {.wn (Twn (Formula.disj B₁ B₂))} :=
      INC.wnD (Γ := 0) (by msimpa [Twn] using INC.disjR₂ (Γ := 0) (Twn B₁) (INC.id (Twn B₂)))
    have := INC.cut (Γ := Γ.map Twn) (Γ' := {Twn (Formula.disj B₁ B₂)}) (by msimpa [Twn] using ih)
      (by msimpa [Twn] using key)
    exact this.cast' (by simp) (by simp [add_comm])
  | @impL Δ Γ A B _ _ ih₁ ih₂ =>
    -- `A ⇒ ?B ⊢ ?(?A ⇒ ?B)`
    have s1 := INC.impL (Δ := 0) (Γ := {ILe.Formula.wn (Twn B)}) (Θ := {Twn A}) (Ξ := 0)
      (A := Twn A) (B := .wn (Twn B)) (INC.id _) (INC.id _)
    have s2 := INC.wnL (Δ := {ILe.Formula.imp (Twn A) (.wn (Twn B))}) (Γ := {Twn B})
      (A := Twn A) (s1.cast' (by ms_eq) (by ms_eq))
    have s3 := INC.impR (Γ := 0) (s2.cast' rfl (by ms_eq))
    have key := INC.wnD s3
    -- `Δ, ?A ⇒ ?B ⊢ ?Γ`
    have t1 := INC.wnL (Δ := Δ.map Twn) (Γ := Γ.map Twn) (A := Twn B) (by msimpa [Twn] using ih₂)
    have t2 := INC.impL (A := .wn (Twn A)) (Ξ := Γ.map Twn) t1 (by msimpa [Twn] using ih₁)
    have t3 := INC.wnC_ctx (Γ.map Twn) (Ξ := 0) (INC.contrL_ctx (Δ.map Twn)
      (Δ := {ILe.Formula.imp (.wn (Twn A)) (.wn (Twn B))}) (t2.cast' (by ms_eq) (by ms_eq)))
    have := INC.cut (Γ := 0) (Γ' := Γ.map Twn) key (t3.cast' (by ms_eq) (by ms_eq))
    exact this.cast' (by simp [Twn]) (by simp)
  | impR _ ih =>
    msimpa [Twn] using INC.wnD (INC.impR (Γ := Multiset.map Twn _) (by msimpa [Twn] using ih))

end CL

end
