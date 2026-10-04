module

public import RequestProject.Relevance.Sugihara
public import RequestProject.Logics.Calculi

/-!
# Relevance logic inside intuitionistic and classical logic

Relevant implication is read as intuitionistic implication `⇒` (resp. classical
implication `⇛`):

* `Relevance.LR.toLJ`: every sequent provable in **LR→** is provable in **LJ** (for IL);
* `Relevance.LR.toLK`: every sequent provable in **LR→** is provable in **LK** (for CL);
* `Relevance.toIL_not_conservative` / `Relevance.toCL_not_conservative`: these maps are not
  conservative: the weakening axiom `K` becomes provable in **LJ** / **LK**, but it is not
  provable in **LR→**.
-/

@[expose] public section

universe u

namespace Relevance

variable {α : Type u}

open Formula

/-- Reading relevant implication as intuitionistic implication. -/
def Formula.toIL : Formula α → IL.Formula α
  | var x => .var x
  | imp A B => .imp A.toIL B.toIL

/-- Reading relevant implication as classical implication. -/
def Formula.toCL : Formula α → CL.Formula α
  | var x => .var x
  | imp A B => .imp A.toCL B.toCL

private lemma LJ.weaken [DecidableEq α] {Δ : Finset (IL.Formula α)} {C : Option (IL.Formula α)}
    (h : IL.LJ Δ C) (Δ' : Finset (IL.Formula α)) : IL.LJ (Δ ∪ Δ') C := by
  induction Δ' using Finset.induction_on with
  | empty => simpa using h
  | insert a s _ ih =>
    rw [Finset.union_insert]
    exact IL.LJ.weakL a ih

private lemma LK.weaken [DecidableEq α] {Δ Γ : Finset (CL.Formula α)}
    (h : CL.LK Δ Γ) (Δ' : Finset (CL.Formula α)) : CL.LK (Δ ∪ Δ') Γ := by
  induction Δ' using Finset.induction_on with
  | empty => simpa using h
  | insert a s _ ih =>
    rw [Finset.union_insert]
    exact CL.LK.weakL a ih

private lemma LK.weakenR [DecidableEq α] {Δ Γ : Finset (CL.Formula α)}
    (h : CL.LK Δ Γ) (Γ' : Finset (CL.Formula α)) : CL.LK Δ (Γ ∪ Γ') := by
  induction Γ' using Finset.induction_on with
  | empty => simpa using h
  | insert b s _ ih =>
    rw [Finset.union_insert]
    exact CL.LK.weakR b ih

/-- **LR→** embeds into **LJ**. -/
theorem LR.toLJ [DecidableEq α] {Δ : Multiset (Formula α)} {C : Formula α} (h : LR Δ C) :
    IL.LJ (Δ.map Formula.toIL).toFinset (some C.toIL) := by
  induction h with
  | id A => simpa using IL.LJ.id A.toIL
  | contr _ ih =>
    simpa only [Multiset.map_cons, Multiset.toFinset_cons, Finset.insert_idem] using ih
  | @cut Δ Δ' B C _ _ ih₁ ih₂ =>
    have hcut := IL.LJ.cut (Δ' := (Multiset.map Formula.toIL Δ').toFinset) ih₁ (by simpa using ih₂)
    simpa [Multiset.toFinset_add] using hcut
  | @impL Δ Δ' A B C _ _ ih₁ ih₂ =>
    have h₁ : IL.LJ ((Δ.map Formula.toIL).toFinset ∪ (Δ'.map Formula.toIL).toFinset) (some A.toIL) :=
      LJ.weaken ih₁ _
    have h₂ : IL.LJ (B.toIL ::ᵢ ((Δ.map Formula.toIL).toFinset ∪ (Δ'.map Formula.toIL).toFinset)) (some C.toIL) := by
      have := LJ.weaken (by simpa using ih₂) (Δ.map Formula.toIL).toFinset
      rw [Finset.insert_union, Finset.union_comm (Multiset.map toIL Δ').toFinset] at this
      exact this
    have h₃ := IL.LJ.impL h₁ h₂
    simpa [Formula.toIL, Multiset.toFinset_add] using h₃
  | impR _ ih => exact IL.LJ.impR (by simpa using ih)

/-- **LR→** embeds into **LK**. -/
theorem LR.toLK [DecidableEq α] {Δ : Multiset (Formula α)} {C : Formula α} (h : LR Δ C) :
    CL.LK (Δ.map Formula.toCL).toFinset {C.toCL} := by
  induction h with
  | id A => simpa using CL.LK.id A.toCL
  | contr _ ih =>
    simpa only [Multiset.map_cons, Multiset.toFinset_cons, Finset.insert_idem] using ih
  | @cut Δ Δ' B C _ _ ih₁ ih₂ =>
    have hcut := CL.LK.cut (Γ := ∅) (Δ' := (Δ'.map Formula.toCL).toFinset) (Γ' := {C.toCL})
      (by simpa using ih₁) (by simpa using ih₂)
    simpa [Multiset.toFinset_add] using hcut
  | @impL Δ Δ' A B C _ _ ih₁ ih₂ =>
    have h₁ : CL.LK ((Δ.map Formula.toCL).toFinset ∪ (Δ'.map Formula.toCL).toFinset) (A.toCL ::ᵢ {C.toCL}) := by
      have key := LK.weaken (LK.weakenR ih₁ {C.toCL}) (Δ'.map Formula.toCL).toFinset
      have e : ({A.toCL} ∪ {C.toCL} : Finset (CL.Formula α)) = A.toCL ::ᵢ {C.toCL} := by
        ext; simp
      rwa [e] at key
    have h₂ : CL.LK (B.toCL ::ᵢ ((Δ.map Formula.toCL).toFinset ∪ (Δ'.map Formula.toCL).toFinset)) {C.toCL} := by
      have := LK.weaken (by simpa using ih₂) (Δ.map Formula.toCL).toFinset
      rw [Finset.insert_union, Finset.union_comm (Multiset.map toCL Δ').toFinset] at this
      exact this
    have h₃ := CL.LK.impL h₁ h₂
    simpa [Formula.toCL, Multiset.toFinset_add] using h₃
  | impR _ ih =>
    have := CL.LK.impR (Γ := ∅) (by simpa using ih)
    simpa using this

/-- The embedding into **LJ** is not conservative: the image of the weakening axiom `K` is
provable in **LJ** but `K` is not provable in **LR→**. -/
theorem toIL_not_conservative [DecidableEq α] {p q : α} (hpq : p ≠ q) :
    IL.LJ ∅ (some (imp (var p) (imp (var q) (var p))).toIL) ∧
      ¬ LR 0 (imp (var p) (imp (var q) (var p))) := by
  refine ⟨?_, LR.not_K hpq⟩
  have h : IL.LJ (IL.Formula.var q ::ᵢ {IL.Formula.var p}) (some (IL.Formula.var p)) :=
    IL.LJ.weakL _ (IL.LJ.id _)
  exact IL.LJ.impR (IL.LJ.impR h)

/-- The embedding into **LK** is not conservative: the image of the weakening axiom `K` is
provable in **LK** but `K` is not provable in **LR→**. -/
theorem toCL_not_conservative [DecidableEq α] {p q : α} (hpq : p ≠ q) :
    CL.LK ∅ {(imp (var p) (imp (var q) (var p))).toCL} ∧
      ¬ LR 0 (imp (var p) (imp (var q) (var p))) := by
  refine ⟨?_, LR.not_K hpq⟩
  have h : CL.LK (CL.Formula.var q ::ᵢ {CL.Formula.var p}) {CL.Formula.var p} :=
    CL.LK.weakL _ (CL.LK.id _)
  exact CL.LK.impR (Γ := ∅) (CL.LK.impR (Γ := ∅) h)

end Relevance

end
