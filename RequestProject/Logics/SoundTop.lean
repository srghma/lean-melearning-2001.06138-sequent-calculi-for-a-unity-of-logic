module

public import RequestProject.Logics.ILCLemmas

/-!
# The top row of the diagram: ILL ⊆ ILLᵉ(_ι) and Girard's translation of LJ

* `ILL.LLJ.toILC`: every sequent provable in **LLJ** is provable in **ILC** and in **ILC_ι**
  (the "extension" half of the conservative extension ILL ↪ ILLᵉ_ι).
* `IL.LJ.toILC`: Girard's translation (in its total form `IL.girardE`, with `ff ↦ 0`)
  sends every sequent `Δ ⊢ C` provable in **LJ** to a sequent `!Δ° ⊢ C°` provable in **ILC**
  (an empty succedent being read as `0`)
  (hence also in **ILC_ι**); i.e. to a provable sequent of the unlinearisation.
-/

@[expose] public section

universe u

variable {α : Type u}

namespace ILL

open ILLe

lemma map_bang_embed (Δ : Multiset (ILL.Formula α)) :
    (Δ.map ILL.Formula.bang).map embed = (Δ.map embed).map ILLe.Formula.bang := by
  simp only [Multiset.map_map]; rfl

/-- **ILL ⊆ ILLᵉ(_ι)** — **Paper Section 3.1, Corollary 3.7** (`ILC(ι) as a conservative extension of LLJ`, PDF p. 16):
every sequent provable in **LLJ** is provable in **ILC** / **ILC_ι**
(for any value of the flag `ι`). -/
theorem LLJ.toILC
    (ι : Bool)
    {Δ : Multiset (ILL.Formula α)}
    {C : Option (ILL.Formula α)}
    (h : LLJ Δ C) :
    ILC ι (Δ.map embed) (optMs (C.map embed)) := by
  induction h with
  | id A => exact (ILC.id (embed A)).cast' (by simp) (by simp)
  | cut _ _ ih₁ ih₂ =>
    exact (ILC.cut (Γ := 0) ih₁ (by msimpa using ih₂)).cast'
      (by simp) (by simp)
  | topL _ ih => msimpa [embed] using ILC.topL ih
  | topR => exact ILC.topR.cast' (by simp) (by simp [embed])
  | tensorL _ ih => msimpa [embed] using ILC.tensorL (by msimpa using ih)
  | tensorR _ _ ih₁ ih₂ =>
    exact (ILC.tensorR (Γ₁ := 0) (Γ₂ := 0) ih₁
      ih₂).cast' (by simp) (by simp [embed])
  | withL₁ A₂ _ ih => msimpa [embed] using ILC.withL₁ (embed A₂) (by msimpa using ih)
  | withL₂ A₁ _ ih => msimpa [embed] using ILC.withL₂ (embed A₁) (by msimpa using ih)
  | withR _ _ ih₁ ih₂ =>
    exact (ILC.withR (Γ := 0) ih₁
      ih₂).cast' rfl (by simp [embed])
  | plusL _ _ ih₁ ih₂ =>
    msimpa [embed] using ILC.plusL (by msimpa using ih₁) (by msimpa using ih₂)
  | plusR₁ B₂ _ ih =>
    exact (ILC.plusR₁ (Γ := 0) (embed B₂) ih).cast' rfl (by simp [embed])
  | plusR₂ B₁ _ ih =>
    exact (ILC.plusR₂ (Γ := 0) (embed B₁) ih).cast' rfl (by simp [embed])
  | bangW A _ ih => msimpa [embed] using ILC.bangW (embed A) ih
  | bangC _ ih => msimpa [embed] using ILC.bangC (by msimpa [embed] using ih)
  | bangD _ ih => msimpa [embed] using ILC.bangD (by msimpa [embed] using ih)
  | @bangR Δ B _ ih =>
    have := ILC.bangR (Δ := Δ.map embed) (Γ := 0) (ih.cast' (map_bang_embed Δ) rfl)
    exact this.cast' (map_bang_embed Δ).symm (by simp [embed])
  | @limpL Δ Γ C A B _ _ ih₁ ih₂ =>
    have := ILC.parL (ILC.negL (Γ := 0) ih₁) (by msimpa using ih₂)
    exact this.cast' (by simp [embed, ILLe.Formula.limp]) (by simp)
  | @limpR Δ A B _ ih =>
    have := ILC.parR (Γ := 0) (ILC.negR ((by msimpa using ih : ILC ι _ {embed B}).cast' rfl
      (by ms_eq)))
    exact this.cast' rfl (by simp [embed, ILLe.Formula.limp])

end ILL

namespace IL

open ILLe

@[simp] lemma girardE_var (x : α) : girardE (.var x : IL.Formula α) = .var x := rfl
@[simp] lemma girardE_top : girardE (.top : IL.Formula α) = .top := rfl
@[simp] lemma girardE_ff : girardE (.ff : IL.Formula α) = .zero := rfl
@[simp] lemma girardE_with (A B : IL.Formula α) :
    girardE (.with A B) = .with (girardE A) (girardE B) := rfl
@[simp] lemma girardE_disj (A B : IL.Formula α) :
    girardE (.disj A B) = .plus (.bang (girardE A)) (.bang (girardE B)) := rfl
@[simp] lemma girardE_imp (A B : IL.Formula α) :
    girardE (.imp A B) = ILLe.Formula.limp (.bang (girardE A)) (girardE B) := rfl
@[simp] lemma girardS_none : girardS (none : Option (IL.Formula α)) = .zero := rfl
@[simp] lemma girardS_some (A : IL.Formula α) : girardS (some A) = girardE A := rfl

/-- **Girard's translation of LJ** (unlinearisation, top row): if `Δ ⊢ C` is provable in
**LJ** (full intuitionistic logic, with ex falso), then `!Δ° ⊢ C°` is provable in **ILC**
(and in **ILC_ι**), where `(_)°` is Girard's translation `IL.girardE`
(`ff ↦ 0`, `A ∨ B ↦ !A° ⊕ !B°`, `A ⇒ B ↦ !A° ⊸ B°`) and an empty succedent is read as `0`. -/
theorem LJ.toILC (ι : Bool) {Δ : Multiset (IL.Formula α)} {C : Option (IL.Formula α)}
    (h : LJ Δ C) : ILC ι ((Δ.map girardE).map .bang) {girardS C} := by
  induction h with
  | weakL A _ ih => msimpa using ILC.bangW (girardE A) ih
  | contrL _ ih => msimpa using ILC.bangC (by msimpa using ih)
  | @weakR Δ B _ ih =>
    exact (ILC.cut (Γ := 0) ih (ILC.zeroL 0 {girardE B})).cast'
      (by simp) (by simp)
  | id A => exact (ILC.bangD (Δ := 0) (ILC.id (girardE A))).cast' (by ms_eq) (by simp)
  | @cut Δ Δ' C B _ _ ih₁ ih₂ =>
    have l := ILC.bangR (Δ := Δ.map girardE) (Γ := 0) ih₁
    exact (ILC.cut l (by msimpa using ih₂)).cast' (by simp) (by simp)
  | topL _ ih => msimpa using ILC.bangD (ILC.topL ih)
  | topR => exact ILC.topR.cast' (by simp) (by simp)
  | ffL => exact (ILC.bangD (Δ := 0) (ILC.zeroL 0 {.zero})).cast' (by ms_eq) (by simp)
  | ffR _ ih => exact ih
  | withL₁ A₂ _ ih => msimpa using ILC.bangWithL₁ (girardE A₂) (by msimpa using ih)
  | withL₂ A₁ _ ih => msimpa using ILC.bangWithL₂ (girardE A₁) (by msimpa using ih)
  | withR _ _ ih₁ ih₂ =>
    exact (ILC.withR (Γ := 0) ih₁ ih₂).cast' rfl
      (by simp)
  | disjL _ _ ih₁ ih₂ =>
    msimpa using ILC.bangD (ILC.plusL (by msimpa using ih₁) (by msimpa using ih₂))
  | @disjR₁ Δ B₁ B₂ _ ih =>
    have := ILC.bangR (Δ := Δ.map girardE) (Γ := 0) ih
    exact (ILC.plusR₁ (.bang (girardE B₂)) this).cast' rfl (by simp)
  | @disjR₂ Δ B₂ B₁ _ ih =>
    have := ILC.bangR (Δ := Δ.map girardE) (Γ := 0) ih
    exact (ILC.plusR₂ (.bang (girardE B₁)) this).cast' rfl (by simp)
  | @impL Δ C A B _ _ ih₁ ih₂ =>
    have := ILC.bangLimpL (Θ := Δ.map girardE) (Ξ := 0) (A := girardE A)
      (by msimpa using ih₂) ih₁
    have := ILC.bangC_ctx (Δ.map girardE)
      (Δ := {ILLe.Formula.bang (.limp (.bang (girardE A)) (girardE B))})
      (this.cast' (by ms_eq) rfl)
    exact this.cast' (by simp only [Multiset.map_cons, girardE_imp]; ms_eq) (by simp)
  | @impR Δ A B _ ih =>
    have := ILC.parR (Γ := 0) (ILC.negR ((by msimpa using ih :
      ILC ι _ {girardE B}).cast' rfl (by ms_eq)))
    exact this.cast' rfl (by simp [ILLe.Formula.limp])

end IL

end
