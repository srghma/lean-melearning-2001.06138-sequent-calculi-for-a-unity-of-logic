module

public import RequestProject.Logics.SoundLKINC
public import RequestProject.Logics.SoundINCILC
public import RequestProject.Logics.SoundLKCLC
public import RequestProject.Logics.SoundCLCILC
public import RequestProject.Logics.SoundTop

/-!
# The commutative diagram of the six logics

```
ILL      ──Girard's translation──▶  IL
 │ (conservative extension)          │ (conservative extension)
ILLᵉ_ι   ──unlinearisation (_)_!──▶  ILᵉ
 │ classicalisation (_)_?            │ classicalisation (_)_?
CLL⁻     ──unlinearisation (_)_!──▶  CL
```

This file assembles the translations proved in the other files:

* the two routes from **LK** to **ILC_ι** (through **INC** and through **CLC**) send every
  provable sequent `Δ ⊢ Γ` of CL to the *same* provable sequent `!𝒯(Δ) ⊢ ?𝒯(Γ)` of ILLᵉ_ι
  (`CL.LK.toILC_viaILe`, `CL.LK.toILC_viaCLLneg`, `CL.LK.routes_agree`);
* the conservativity statements of the vertical top arrows are recorded as propositions
  (`ILL.ILCConservative`, `IL.INCConservative`); the "extension" halves are proved
  (`ILL.LLJ.toILC`); the conservativity halves rely on cut-elimination and are *not* proved
  here;
* assuming the conservativity of ILC(_ι) over LLJ, Girard's translation is sound from **LJ**
  to **LLJ** (`IL.LJ.toLLJ_of_conservative`).
-/

@[expose] public section

universe u

variable {α : Type u}

namespace CL

open ILLe

/-- **Route through ILᵉ** (classicalisation then unlinearisation, `𝒯_{!?} = 𝒯_! ∘ 𝒯_?`) —
**Paper Section 3.2, Corollary 3.18** (`Translation 𝒯_{!?} of LK into ILC_ι`, PDF p. 25):
if `Δ ⊢ Γ` is provable in **LK** then `!𝒯_{!?}(Δ) ⊢ ?𝒯_{!?}(Γ)` is provable in **ILC_ι**. -/
theorem LK.toILC_viaILe {Δ Γ : Multiset (CL.Formula α)} (h : LK Δ Γ) :
    ILC true ((Δ.map Tbangwn).map .bang) ((Γ.map Tbangwn).map .wn) := by
  have h1 := ILe.INC.toILC (LK.toINC h)
  unfold Unlinearisation at h1
  rw [ILe.map_wn_T] at h1
  simpa only [Multiset.map_map, Function.comp_def, Tbangwn] using h1

/-- **Route through CLL⁻** (unlinearisation then classicalisation, `𝒯_{?!} = 𝒯_? ∘ 𝒯_!`) —
**Paper Section 3.3, Corollary 3.25** (`Translation 𝒯_{?!} of LK into ILC_ι`, PDF p. 29):
if `Δ ⊢ Γ` is provable in **LK** then `!𝒯_{?!}(Δ) ⊢ ?𝒯_{?!}(Γ)` is provable in **ILC_ι**. -/
theorem LK.toILC_viaCLLneg {Δ Γ : Multiset (CL.Formula α)} (h : LK Δ Γ) :
    ILC true ((Δ.map Twnbang).map .bang) ((Γ.map Twnbang).map .wn) := by
  have h1 := CLLneg.CLC.toILC (LK.toCLC h)
  unfold Classicalisation at h1
  rw [CLLneg.map_bang_T] at h1
  simpa only [Multiset.map_map, Function.comp_def, Twnbang] using h1

/-- **Commutativity of the lower square** (sequents) —
**Paper Section 3.4, Theorem 3.26** (`Commutative unity of logic`, PDF p. 29):
the two routes CL → ILᵉ → ILLᵉ_ι and CL → CLL⁻ → ILLᵉ_ι translate every sequent `Δ ⊢ Γ`
of CL into literally the same sequent `!𝒯(Δ) ⊢ ?𝒯(Γ)` of ILLᵉ_ι. -/
theorem LK.routes_agree (Δ Γ : Multiset (CL.Formula α)) :
    ((Δ.map Tbangwn).map ILLe.Formula.bang, (Γ.map Tbangwn).map ILLe.Formula.wn) =
      ((Δ.map Twnbang).map ILLe.Formula.bang, (Γ.map Twnbang).map ILLe.Formula.wn) := by
  have : (Tbangwn : CL.Formula α → ILLe.Formula α) = Twnbang := funext Tbangwn_eq_Twnbang
  rw [this]

end CL

/-! ## Conservativity of the vertical top arrows (statements) -/

namespace ILL

/-- The statement that **ILC** (`ι = false`) / **ILC_ι** (`ι = true`) is a *conservative
extension* of **LLJ** — **Paper Section 3.1, Corollary 3.7** (`ILC(ι) as a conservative extension of LLJ`, PDF p. 16):
a sequent of ILL formulas is provable in **LLJ** iff it is provable in **ILC(_ι)**, and every
sequent of ILL formulas provable in **ILC(_ι)** has at most one formula on the right.
(The direction LLJ ⟹ ILC(_ι) is `ILL.LLJ.toILC`; the converse relies on cut-elimination
and is not proved here.) -/
def ILCConservative (ι : Bool) : Prop :=
  (∀ (Δ : Multiset (ILL.Formula α)) (C : Option (ILL.Formula α)),
      LLJ Δ C ↔ ILLe.ILC ι (Δ.map embed) (optMs (C.map embed))) ∧
  (∀ Δ Γ : Multiset (ILL.Formula α), ILLe.ILC ι (Δ.map embed) (Γ.map embed) → Γ.card ≤ 1)

end ILL

namespace IL

/-- The statement that **INC** is a *conservative extension* of **LJ** —
**Paper Section 3.2, Corollary 3.14** (`INC as a conservative extension of LJ`, PDF p. 20):
a sequent of IL formulas is provable in **LJ** iff it is provable in **INC**, and every
sequent of IL formulas provable in **INC** has at most one formula on the right.
(Not proved here: both directions use cut-elimination.) -/
def INCConservative : Prop :=
  (∀ (Δ : Multiset (IL.Formula α)) (C : Option (IL.Formula α)),
      LJ Δ C ↔ ILe.INC (Δ.map embed) (optMs (C.map embed))) ∧
  (∀ Δ Γ : Multiset (IL.Formula α), ILe.INC (Δ.map embed) (Γ.map embed) → Γ.card ≤ 1)

lemma map_girardE_of_rel {Δ : Multiset (IL.Formula α)} {Δ' : Multiset (ILL.Formula α)}
    (h : Multiset.Rel (fun A B => girard A = some B) Δ Δ') :
    Δ.map girardE = Δ'.map ILL.embed := by
  induction h with
  | zero => rfl
  | cons hab _ ih =>
    rw [Multiset.map_cons, Multiset.map_cons, ih, embed_girard hab]; rfl

/-- **Girard's translation of LJ into LLJ** (top arrow), conditional on the conservativity of
ILC(_ι) over LLJ — **Paper Section 1.3** (PDF p. 3–5), **Section 3.5, Corollary 3.37** (PDF p. 35):
let `Δ ⊢ C` be provable in **LJ**, where all formulas are `ff`-free, and let `Δ'`, `C'` be their
Girard translations. Then `!Δ' ⊢ C'` is provable in **LLJ**. -/
theorem LJ.toLLJ_of_conservative (ι : Bool) (hcons : ILL.ILCConservative (α := α) ι)
    {Δ : Multiset (IL.Formula α)} {C : Option (IL.Formula α)} (h : LJ Δ C)
    {Δ' : Multiset (ILL.Formula α)} {C' : Option (ILL.Formula α)}
    (hΔ : Multiset.Rel (fun A B => girard A = some B) Δ Δ')
    (hC : Option.Rel (fun A B => girard A = some B) C C') :
    ILL.LLJ (Δ'.map .bang) C' := by
  rw [hcons.1]
  have h1 := LJ.toILC ι h
  have e1 : (Δ'.map ILL.Formula.bang).map ILL.embed = (Δ.map girardE).map .bang := by
    rw [map_girardE_of_rel hΔ, Multiset.map_map, Multiset.map_map]; rfl
  have e2 : C'.map ILL.embed = C.map girardE := by
    cases hC with
    | none => rfl
    | some hab => simp [embed_girard hab, girardE]
  rw [e1, e2]
  exact h1

end IL

end
