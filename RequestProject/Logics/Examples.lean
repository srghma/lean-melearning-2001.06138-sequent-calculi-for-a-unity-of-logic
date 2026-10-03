module

public import RequestProject.Logics.Diagram

/-!
# Sanity-check examples

* The law of excluded middle `⊢ ∼A ∨ A` is provable in **LK** —
  **Paper Section 2.1**, PDF p. 8 (explicit proof tree);
  its translation `⊢ ?𝒯(∼A ∨ A)` is provable in **ILC_ι** (**Section 1.3**, PDF p. 5).
* The sequent `!?A ⊢ ?!A` is provable in **ILC_ι** —
  **Paper Section 3.1, Definition 3.4** (weakly distributive rules, PDF p. 13);
  and **Appendix A** (Axiom Dist: `!?A ⊢ ?!A`, PDF p. 38).
-/

@[expose] public section

universe u

variable {α : Type u}

/-- The law of excluded middle `⊢ ∼A ∨ A` in **LK** —
**Paper Section 2.1**, PDF p. 8 (the explicit derivation in LK). -/
theorem CL.LK.lem (A : CL.Formula α) : CL.LK 0 {.disj A.neg A} := by
  have h1 : CL.LK (A ::ₘ 0) (.ff ::ₘ {A}) := CL.LK.ffR (CL.LK.id A)
  have h2 := CL.LK.impR h1
  have h3 := CL.LK.disjR₁ A h2
  have h4 : CL.LK 0 (A ::ₘ {.disj A.neg A}) := by
    have e : (CL.Formula.disj (.imp A .ff) A ::ₘ {A} : Multiset (CL.Formula α)) =
        A ::ₘ {.disj A.neg A} := by
      simp only [CL.Formula.neg]; ms_eq
    exact e ▸ h3
  exact CL.LK.contrR (CL.LK.disjR₂ A.neg h4)

/-- The translation of the law of excluded middle through the diagram: `⊢ ?𝒯(∼A ∨ A)` is
provable in **ILC_ι** — **Paper Section 1.3**, PDF p. 5. -/
example (A : CL.Formula α) :
    ILLe.ILC true 0 {.wn (CL.Tbangwn (.disj A.neg A))} := by
  simpa using CL.LK.toILC_viaILe (CL.LK.lem A)

/-- `!?A ⊢ ?!A` is provable in **ILC_ι** (using the weakly distributive rule `?!R^{!?}`) —
**Paper Section 3.1, Definition 3.4** (weakly distributive rules, PDF p. 13);
**Appendix A** (Axiom Dist: `!?A ⊢ ?!A`, PDF p. 38). -/
theorem ILLe.ILC.bang_wn_le_wn_bang (A : ILLe.Formula α) :
    ILLe.ILC true {.bang (.wn A)} {.wn (.bang A)} := by
  have h1 := ILLe.ILC.bangD (ι := true) (Δ := 0) (ILLe.ILC.id (.wn A))
  exact (ILLe.ILC.wnBangR (Δ := {.wn A}) (Γ := 0) (B := A) rfl (h1.cast' (by simp) (by simp))).cast'
    (by simp) (by simp)

end
