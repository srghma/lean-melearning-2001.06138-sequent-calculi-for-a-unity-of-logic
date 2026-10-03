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

private theorem LJ.weaken {Δ : Multiset (IL.Formula α)} {C : Option (IL.Formula α)}
    (h : IL.LJ Δ C) (Δ' : Multiset (IL.Formula α)) : IL.LJ (Δ' + Δ) C := by
  induction Δ' using Multiset.induction with
  | empty => simpa using h
  | cons A Δ' ih => simpa using IL.LJ.weakL A ih

private theorem LK.weaken {Δ Γ : Multiset (CL.Formula α)}
    (h : CL.LK Δ Γ) (Δ' : Multiset (CL.Formula α)) : CL.LK (Δ' + Δ) Γ := by
  induction Δ' using Multiset.induction with
  | empty => simpa using h
  | cons A Δ' ih => simpa using CL.LK.weakL A ih

/-- **LR→** embeds into **LJ**. -/
theorem LR.toLJ {Δ : Multiset (Formula α)} {C : Formula α} (h : LR Δ C) :
    IL.LJ (Δ.map Formula.toIL) (some C.toIL) := by
  induction h with
  | id A => simpa using IL.LJ.id A.toIL
  | contr _ ih => simpa using IL.LJ.contrL (by simpa using ih)
  | cut _ _ ih₁ ih₂ => simpa using IL.LJ.cut ih₁ (by simpa using ih₂)
  | @impL Δ Δ' A B C _ _ ih₁ ih₂ =>
    have h₁ : IL.LJ (Δ.map Formula.toIL + Δ'.map Formula.toIL) (some A.toIL) := by
      rw [add_comm]; exact LJ.weaken ih₁ _
    have h₂ : IL.LJ (Δ.map Formula.toIL + (B.toIL ::ₘ Δ'.map Formula.toIL)) (some C.toIL) :=
      LJ.weaken (by simpa using ih₂) _
    have h₃ := IL.LJ.impL h₁ (by simpa only [Multiset.add_cons] using h₂)
    simpa [Formula.toIL, add_comm] using h₃
  | impR _ ih => exact IL.LJ.impR (by simpa using ih)

/-- **LR→** embeds into **LK**. -/
theorem LR.toLK {Δ : Multiset (Formula α)} {C : Formula α} (h : LR Δ C) :
    CL.LK (Δ.map Formula.toCL) {C.toCL} := by
  induction h with
  | id A => simpa using CL.LK.id A.toCL
  | contr _ ih => simpa using CL.LK.contrL (by simpa using ih)
  | cut _ _ ih₁ ih₂ =>
    simpa using CL.LK.cut (Γ := 0) (by simpa using ih₁) (by simpa using ih₂)
  | @impL Δ Δ' A B C _ _ ih₁ ih₂ =>
    have h₁ : CL.LK (Δ.map Formula.toCL + Δ'.map Formula.toCL) (A.toCL ::ₘ {C.toCL}) := by
      have e : (C.toCL ::ₘ {A.toCL} : Multiset (CL.Formula α)) = A.toCL ::ₘ {C.toCL} :=
        Multiset.cons_swap _ _ _
      rw [add_comm, ← e]; exact CL.LK.weakR _ (LK.weaken ih₁ _)
    have h₂ : CL.LK (Δ.map Formula.toCL + (B.toCL ::ₘ Δ'.map Formula.toCL)) {C.toCL} :=
      LK.weaken (by simpa using ih₂) _
    have h₃ := CL.LK.impL h₁ (by simpa only [Multiset.add_cons] using h₂)
    simpa [Formula.toCL, add_comm] using h₃
  | impR _ ih => exact CL.LK.impR (Γ := 0) (by simpa using ih)

/-- The embedding into **LJ** is not conservative: the image of the weakening axiom `K` is
provable in **LJ** but `K` is not provable in **LR→**. -/
theorem toIL_not_conservative {p q : α} (hpq : p ≠ q) :
    IL.LJ 0 (some (imp (var p) (imp (var q) (var p))).toIL) ∧
      ¬ LR 0 (imp (var p) (imp (var q) (var p))) := by
  refine ⟨?_, LR.not_K hpq⟩
  have h : IL.LJ (.var q ::ₘ {.var p}) (some (.var p)) := IL.LJ.weakL _ (IL.LJ.id _)
  exact IL.LJ.impR (IL.LJ.impR (by simpa [Multiset.cons_swap] using h))

/-- The embedding into **LK** is not conservative: the image of the weakening axiom `K` is
provable in **LK** but `K` is not provable in **LR→**. -/
theorem toCL_not_conservative {p q : α} (hpq : p ≠ q) :
    CL.LK 0 {(imp (var p) (imp (var q) (var p))).toCL} ∧
      ¬ LR 0 (imp (var p) (imp (var q) (var p))) := by
  refine ⟨?_, LR.not_K hpq⟩
  have h : CL.LK (.var q ::ₘ {.var p}) {.var p} := CL.LK.weakL _ (CL.LK.id _)
  exact CL.LK.impR (Γ := 0) (CL.LK.impR (Γ := 0) (by simpa [Multiset.cons_swap] using h))

end Relevance

end
