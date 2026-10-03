module

public import RequestProject.Logics.SoundLKINC
public import RequestProject.Logics.SoundINCILC
public import RequestProject.Logics.SoundLKCLC
public import RequestProject.Logics.SoundCLCILC
public import RequestProject.Logics.SoundTop
public import RequestProject.Semantics.Heyting

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
  (`ILL.ILCConservative`, `IL.INCConservative`); the "extension" half of the left one is proved
  (`ILL.LLJ.toILC`), while its conservativity half relies on cut-elimination and is *not*
  proved here;
* since **LJ** is full intuitionistic logic (with ex falso `ff ⊢ B`), while **INC** has no
  ex falso (`ILe.INC.not_exfalso`), **INC is not a conservative extension of LJ**
  (`IL.not_INCConservative`); over minimal logic **LJᵐ** (the explicit rule figure of LJ in
  the source) the statement `IL.INCConservativeMin` holds, and is proved in
  `RequestProject/Logics/INCConservative.lean` (`IL.incConservativeMin`), so the right-hand
  column of the diagram is consistent when **IL** is presented by **LJᵐ**;
* assuming the conservativity of ILC(_ι) over LLJ, Girard's translation is sound from **LJ**
  to **LLJ** (`IL.LJ.toLLJ_of_conservative`).
-/

@[expose] public section

universe u

variable {α : Type u}

namespace CL

open ILLe

/-- **Route through ILᵉ** (classicalisation then unlinearisation, `𝒯_{!?} = 𝒯_! ∘ 𝒯_?`) —
**Paper Section 3.2, Corollary 3.18** (PDF p. 25); **Section 3.4, Theorem 3.26** (PDF p. 29):
if `Δ ⊢ Γ` is provable in **LK** then `!𝒯_{!?}(Δ) ⊢ ?𝒯_{!?}(Γ)` is provable in **ILC_ι**. -/
theorem LK.toILC_viaILe {Δ Γ : Multiset (CL.Formula α)} (h : LK Δ Γ) :
    ILC true ((Δ.map Tbangwn).map .bang) ((Γ.map Tbangwn).map .wn) := by
  have h1 := ILe.INC.toILC (LK.toINC h)
  unfold Unlinearisation at h1
  rw [ILe.map_wn_T] at h1
  simpa only [Multiset.map_map, Function.comp_def, Tbangwn] using h1

/-- **Route through CLL⁻** (unlinearisation then classicalisation, `𝒯_{?!} = 𝒯_? ∘ 𝒯_!`) —
**Paper Section 3.3, Corollary 3.25** (PDF p. 29); **Section 3.4, Theorem 3.26** (PDF p. 29):
if `Δ ⊢ Γ` is provable in **LK** then `!𝒯_{?!}(Δ) ⊢ ?𝒯_{?!}(Γ)` is provable in **ILC_ι**. -/
theorem LK.toILC_viaCLLneg {Δ Γ : Multiset (CL.Formula α)} (h : LK Δ Γ) :
    ILC true ((Δ.map Twnbang).map .bang) ((Γ.map Twnbang).map .wn) := by
  have h1 := CLLneg.CLC.toILC (LK.toCLC h)
  unfold Classicalisation at h1
  rw [CLLneg.map_bang_T] at h1
  simpa only [Multiset.map_map, Function.comp_def, Twnbang] using h1

/-- **Commutativity of the lower square** (sequents) —
**Paper Section 3.4, Theorem 3.26** (`Commutative unity of logic`, PDF p. 29):
the two routes CL → ILᵉ → ILLᵉ_ι and CL → CLL⁻ → ILLᵉ_ι translate every sequent `Δ ⊢ Γ` of CL
into literally the same sequent `!𝒯(Δ) ⊢ ?𝒯(Γ)` of ILLᵉ_ι. -/
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
(The direction LLJ ⟹ ILC(_ι) is `ILL.LLJ.toILC`; the converse relies on cut-elimination and is not proved here.) -/
def ILCConservative (ι : Bool) : Prop :=
  (∀ (Δ : Multiset (ILL.Formula α)) (C : Option (ILL.Formula α)),
      LLJ Δ C ↔ ILLe.ILC ι (Δ.map embed) (optMs (C.map embed))) ∧
  (∀ Δ Γ : Multiset (ILL.Formula α), ILLe.ILC ι (Δ.map embed) (Γ.map embed) → Γ.card ≤ 1)

end ILL

namespace IL

/-- The statement that **INC** is a *conservative extension* of **LJ** —
**Paper Section 3.2, Corollary 3.14** (`INC as a conservative extension of LJ`, PDF p. 20):
a sequent of IL formulas is provable in **LJ** iff it is provable in **INC**, and every sequent of IL formulas
provable in **INC** has at most one formula on the right.

Now that **LJ** is full intuitionistic logic (with ex falso), this statement is **false**:
see `IL.not_INCConservative`. -/
def INCConservative : Prop :=
  (∀ (Δ : Multiset (IL.Formula α)) (C : Option (IL.Formula α)),
      LJ Δ C ↔ ILe.INC (Δ.map embed) (optMs (C.map embed))) ∧
  (∀ Δ Γ : Multiset (IL.Formula α), ILe.INC (Δ.map embed) (Γ.map embed) → Γ.card ≤ 1)

/-- The conservativity statement of **INC** over *minimal* logic **LJᵐ** (`IL.LJm`, LJ without
right weakening, the explicit rule figure of LJ in the source): the same as `INCConservative`
with `IL.LJm` in place of `IL.LJ`. This is the form of the statement compatible with the
counter-model of `IL.not_INCConservative`. It is proved as `IL.incConservativeMin` in
`RequestProject/Logics/INCConservative.lean`, by semantic arguments that avoid
cut-elimination. -/
def INCConservativeMin : Prop :=
  (∀ (Δ : Multiset (IL.Formula α)) (C : Option (IL.Formula α)),
      LJm Δ C ↔ ILe.INC (Δ.map embed) (optMs (C.map embed))) ∧
  (∀ Δ Γ : Multiset (IL.Formula α), ILe.INC (Δ.map embed) (Γ.map embed) → Γ.card ≤ 1)

/-- **Ex falso** is provable in **LJ**: `ff ⊢ B`. -/
theorem LJ.exfalso (B : IL.Formula α) : LJ {.ff} (some B) := LJ.weakR B LJ.ffL

end IL

namespace ILe

/-- A three-valued-style reading of ILᵉ formulas used to show that **INC** has no ex falso:
`ff` and every `?A` are read as *true*, the other connectives classically. -/
private def Formula.evT (v : α → Prop) : Formula α → Prop
  | .var x => v x
  | .top => True
  | .ff => True
  | .with A B => A.evT v ∧ B.evT v
  | .disj A B => A.evT v ∨ B.evT v
  | .imp A B => A.evT v → B.evT v
  | .wn _ => True

/-- Validity of `Δ ⊢ Γ` for this reading: if all of `Δ` hold, then `Γ` is empty or one of its
formulas holds. -/
private def ValidT (v : α → Prop) (Δ Γ : Multiset (Formula α)) : Prop :=
  (∀ A ∈ Δ, A.evT v) → Γ = 0 ∨ ∃ B ∈ Γ, B.evT v

/-- A succedent consisting of `?`-formulas (possibly empty) is always satisfied. -/
private lemma validT_wn (v : α → Prop) (Γ : Multiset (Formula α)) :
    Γ.map Formula.wn = 0 ∨ ∃ B ∈ Γ.map Formula.wn, B.evT v := by
  rcases Multiset.empty_or_exists_mem Γ with rfl | ⟨b, hb⟩
  · simp
  · exact Or.inr ⟨.wn b, Multiset.mem_map_of_mem _ hb, trivial⟩

private theorem INC.soundT (v : α → Prop) {Δ Γ : Multiset (Formula α)} (h : INC Δ Γ) :
    ValidT v Δ Γ := by
  unfold ValidT
  induction h with
  | weakL A _ ih => exact fun hΔ => ih fun B hB => hΔ B (Multiset.mem_cons_of_mem hB)
  | wnW B _ _ => exact fun _ => Or.inr ⟨.wn B, Multiset.mem_cons_self _ _, trivial⟩
  | contrL _ ih =>
    intro hΔ; apply ih; intro B hB
    simp only [Multiset.mem_cons] at hB hΔ
    rcases hB with rfl | rfl | hB
    · exact hΔ _ (Or.inl rfl)
    · exact hΔ _ (Or.inl rfl)
    · exact hΔ _ (Or.inr hB)
  | wnC _ _ => exact fun _ => Or.inr ⟨.wn _, Multiset.mem_cons_self _ _, trivial⟩
  | wnD _ _ => exact fun _ => Or.inr ⟨.wn _, Multiset.mem_cons_self _ _, trivial⟩
  | @wnL Δ Γ A _ _ =>
    intro _
    exact validT_wn v Γ
  | id A => exact fun hΔ => Or.inr ⟨A, Multiset.mem_singleton_self _, hΔ A (by simp)⟩
  | @cut Δ Γ Δ' Γ' B _ _ _ _ =>
    intro _
    simpa [← Multiset.map_add] using validT_wn v (Γ + Γ')
  | topL _ ih =>
    intro hΔ; apply ih; intro B hB; exact hΔ B (Multiset.mem_cons_of_mem hB)
  | topR => exact fun _ => Or.inr ⟨.top, by simp, trivial⟩
  | ffL => exact fun _ => Or.inl rfl
  | ffR _ _ => exact fun _ => Or.inr ⟨.ff, Multiset.mem_cons_self _ _, trivial⟩
  | @withL₁ Δ Γ A₁ A₂ _ ih =>
    intro hΔ; apply ih; intro B hB
    simp only [Multiset.mem_cons] at hB hΔ
    rcases hB with rfl | hB
    · exact (hΔ _ (Or.inl rfl)).1
    · exact hΔ _ (Or.inr hB)
  | @withL₂ Δ Γ A₂ A₁ _ ih =>
    intro hΔ; apply ih; intro B hB
    simp only [Multiset.mem_cons] at hB hΔ
    rcases hB with rfl | hB
    · exact (hΔ _ (Or.inl rfl)).2
    · exact hΔ _ (Or.inr hB)
  | @withR Δ Γ B₁ B₂ _ _ ih₁ ih₂ =>
    intro hΔ
    rcases Multiset.empty_or_exists_mem Γ with rfl | ⟨b, hb⟩
    · simp only [Multiset.map_zero, Multiset.cons_zero, Multiset.singleton_ne_zero,
        Multiset.mem_singleton, exists_eq_left, false_or] at ih₁ ih₂ ⊢
      exact ⟨ih₁ hΔ, ih₂ hΔ⟩
    · exact Or.inr ⟨.wn b, Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem _ hb), trivial⟩
  | @disjL Δ Γ A₁ A₂ _ _ ih₁ ih₂ =>
    intro hΔ
    simp only [Multiset.mem_cons] at hΔ
    rcases hΔ _ (Or.inl rfl) with h | h
    · apply ih₁; intro B hB
      simp only [Multiset.mem_cons] at hB
      rcases hB with rfl | hB
      · exact h
      · exact hΔ _ (Or.inr hB)
    · apply ih₂; intro B hB
      simp only [Multiset.mem_cons] at hB
      rcases hB with rfl | hB
      · exact h
      · exact hΔ _ (Or.inr hB)
  | @disjR₁ Δ Γ B₁ B₂ _ ih =>
    intro hΔ
    rcases ih hΔ with h | ⟨B, hB, hB'⟩
    · simp at h
    · simp only [Multiset.mem_cons] at hB
      rcases hB with rfl | hB
      · exact Or.inr ⟨_, Multiset.mem_cons_self _ _, Or.inl hB'⟩
      · exact Or.inr ⟨B, Multiset.mem_cons_of_mem hB, hB'⟩
  | @disjR₂ Δ Γ B₂ B₁ _ ih =>
    intro hΔ
    rcases ih hΔ with h | ⟨B, hB, hB'⟩
    · simp at h
    · simp only [Multiset.mem_cons] at hB
      rcases hB with rfl | hB
      · exact Or.inr ⟨_, Multiset.mem_cons_self _ _, Or.inr hB'⟩
      · exact Or.inr ⟨B, Multiset.mem_cons_of_mem hB, hB'⟩
  | @impL Δ Γ Θ Ξ A B _ _ ih₁ ih₂ =>
    intro hΔ
    simp only [Multiset.mem_cons, Multiset.mem_add] at hΔ
    rcases Multiset.empty_or_exists_mem Ξ with rfl | ⟨b, hb⟩
    · simp only [Multiset.map_zero, add_zero, Multiset.cons_zero, Multiset.singleton_ne_zero,
        Multiset.mem_singleton, exists_eq_left, false_or] at ih₂ ⊢
      have hA := ih₂ fun C hC => hΔ C (Or.inr (Or.inr hC))
      apply ih₁; intro C hC
      simp only [Multiset.mem_cons] at hC
      rcases hC with rfl | hC
      · exact hΔ _ (Or.inl rfl) hA
      · exact hΔ C (Or.inr (Or.inl hC))
    · exact Or.inr ⟨.wn b, Multiset.mem_add.2 (Or.inr (Multiset.mem_map_of_mem _ hb)), trivial⟩
  | @impR Δ Γ A B _ ih =>
    intro hΔ
    rcases Multiset.empty_or_exists_mem Γ with rfl | ⟨b, hb⟩
    · simp only [Multiset.map_zero, Multiset.cons_zero, Multiset.singleton_ne_zero,
        Multiset.mem_singleton, exists_eq_left, false_or] at ih ⊢
      intro hA
      apply ih; intro C hC
      simp only [Multiset.mem_cons] at hC
      rcases hC with rfl | hC
      · exact hA
      · exact hΔ C hC
    · exact Or.inr ⟨.wn b, Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem _ hb), trivial⟩

/-- **INC has no ex falso**: `ff ⊢ X` is not provable in **INC** (for a variable `X`). -/
theorem INC.not_exfalso (x : α) : ¬ INC {.ff} {.var x} := by
  intro h
  have := INC.soundT (fun _ => False) h (by simp [Formula.evT])
  simp [Formula.evT] at this

end ILe

namespace IL

/-- **INC is not a conservative extension of LJ** (with ex falso): `ff ⊢ X` is provable in
**LJ** but its image is not provable in **INC**. -/
theorem not_INCConservative (x : α) : ¬ INCConservative (α := α) := by
  intro h
  have := (h.1 {.ff} (some (.var x))).1 (LJ.exfalso _)
  exact ILe.INC.not_exfalso x (by simpa [embed] using this)

lemma map_girardE_of_rel {Δ : Multiset (IL.Formula α)} {Δ' : Multiset (ILL.Formula α)}
    (h : Multiset.Rel (fun A B => girard A = some B) Δ Δ') :
    Δ.map girardE = Δ'.map ILL.embed := by
  induction h with
  | zero => rfl
  | cons hab _ ih =>
    rw [Multiset.map_cons, Multiset.map_cons, ih, embed_girard_eq_girardE hab]

/-- An `ff`-free formula is true under the valuation sending every variable to `⊤`. -/
lemma eval_top_of_girard {A : IL.Formula α} {B : ILL.Formula α} (h : girard A = some B) :
    A.eval (fun _ => (⊤ : Bool)) = ⊤ := by
  induction A generalizing B with
  | var x => rfl
  | top => rfl
  | ff => simp [girard] at h
  | «with» A₁ A₂ ih₁ ih₂ =>
    simp only [girard, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨B₁, h₁, B₂, h₂, rfl⟩ := h
    have e₁ := ih₁ h₁; have e₂ := ih₂ h₂
    simp only [Formula.eval, Formula.evalG] at *
    rw [e₁, e₂]; rfl
  | disj A₁ A₂ ih₁ ih₂ =>
    simp only [girard, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨B₁, h₁, B₂, h₂, rfl⟩ := h
    have e₁ := ih₁ h₁
    simp only [Formula.eval, Formula.evalG] at *
    rw [e₁]; rfl
  | imp A₁ A₂ ih₁ ih₂ =>
    simp only [girard, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨B₁, h₁, B₂, h₂, rfl⟩ := h
    have e₂ := ih₂ h₂
    simp only [Formula.eval, Formula.evalG] at *
    rw [e₂]; exact himp_top

/-- From `ff`-free hypotheses, the empty succedent is not provable in **LJ**. -/
theorem LJ.not_none_of_girard {Δ : Multiset (IL.Formula α)} {Δ' : Multiset (ILL.Formula α)}
    (hΔ : Multiset.Rel (fun A B => girard A = some B) Δ Δ') : ¬ LJ Δ none := by
  have htop : ∀ {Δ : Multiset (IL.Formula α)} {Δ' : Multiset (ILL.Formula α)},
      Multiset.Rel (fun A B => girard A = some B) Δ Δ' →
        (Δ.map (Formula.eval fun _ => (⊤ : Bool))).inf = ⊤ := by
    intro Δ Δ' hΔ
    induction hΔ with
    | zero => rfl
    | cons hab _ ih => rw [Multiset.map_cons, Multiset.inf_cons, ih, eval_top_of_girard hab]; rfl
  intro h
  have hv := (valid_iff _ _ _).1 (h.sound (fun _ => (⊤ : Bool)))
  rw [htop hΔ] at hv
  simp only [Option.elim] at hv
  exact absurd hv (by decide)

/-- **Girard's translation of LJ into LLJ** (top arrow) —
**Paper Section 3.5, Corollary 3.37** (PDF p. 35):
conditional on the conservativity of ILC(_ι) over LLJ: let `Δ ⊢ C` be provable in **LJ**, where
all formulas are `ff`-free, and let `Δ'`, `C'` be their Girard translations.
Then `!Δ' ⊢ C'` is provable in **LLJ**. -/
theorem LJ.toLLJ_of_conservative (ι : Bool) (hcons : ILL.ILCConservative (α := α) ι)
    {Δ : Multiset (IL.Formula α)} {C : Option (IL.Formula α)} (h : LJ Δ C)
    {Δ' : Multiset (ILL.Formula α)} {C' : Option (ILL.Formula α)}
    (hΔ : Multiset.Rel (fun A B => girard A = some B) Δ Δ')
    (hC : Option.Rel (fun A B => girard A = some B) C C') :
    ILL.LLJ (Δ'.map .bang) C' := by
  rw [hcons.1]
  have e1 : (Δ'.map ILL.Formula.bang).map ILL.embed = (Δ.map girardE).map .bang := by
    rw [map_girardE_of_rel hΔ, Multiset.map_map, Multiset.map_map]; rfl
  cases hC with
  | none => exact absurd h (LJ.not_none_of_girard hΔ)
  | @some a b hab =>
    have h1 := LJ.toILC ι h
    rw [e1]
    simpa [embed_girard_eq_girardE hab] using h1

end IL

end
