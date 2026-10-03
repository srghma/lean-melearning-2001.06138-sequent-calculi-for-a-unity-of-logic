module

public import RequestProject.Logics.Calculi

/-!
# Maps between the six logics (at the level of formulas and sequents)

Each arrow of the diagram (Paper **Section 1.3**, Theorem p. 3; **Section 3.5**, Figure 6, p. 30):

```
ILL      ──Girard's translation──▶  IL
 │ (conservative extension)          │ (conservative extension)
ILLᵉ_ι   ──unlinearisation (_)_!──▶  ILᵉ
 │ classicalisation (_)_?            │ classicalisation (_)_?
CLL⁻     ──unlinearisation (_)_!──▶  CL
```

is realised by a translation of formulas going in the *opposite* direction (from the
"target" logic back into the "source" one), together with the corresponding map on sequents:

* `ILL.embed : ILL → ILLᵉ` (**Section 3.1**, Corollary 3.7, PDF p. 16);
* `IL.embed : IL → ILᵉ` (**Section 3.2**, Corollary 3.14, PDF p. 20);
* `IL.girard : IL → ILL` (Girard's translation, **Section 2.2**, PDF p. 12; **Section 3.2**, PDF p. 17; partial, see below), with
  sequent map `Δ ⊢ C ↦ !Δ° ⊢ C°`;
* `ILe.T : ILᵉ → ILLᵉ` (translation `𝒯_!`, unlinearisation, **Section 3.2**, Lemma 3.16, PDF p. 23), sequent map
  `Δ ⊢ Γ ↦ !𝒯(Δ) ⊢ 𝒯(Γ)`;
* `CL.Tbang : CL → CLL⁻` (translation `𝒯_!`, unlinearisation, **Section 3.3**, Lemma 3.22, PDF p. 26), same sequent map;
* `CLLneg.T : CLL⁻ → ILLᵉ` (translation `𝒯_?`, classicalisation, **Section 3.3**, Lemma 3.23, PDF p. 27), sequent map
  `Δ ⊢ Γ ↦ 𝒯(Δ) ⊢ ?𝒯(Γ)`;
* `CL.Twn : CL → ILᵉ` (translation `𝒯_?`, classicalisation, **Section 3.2**, Lemma 3.15, PDF p. 22), same sequent map.

Girard's translation needs a translation of falsity `ff`; since ILL (as defined in the paper)
has neither `0` nor `⊥`, we define it as a partial map `IL.girard : IL → Option ILL`, which is
defined exactly on the `ff`-free formulas. On those formulas it agrees with `ILe.T ∘ IL.embed`
(`IL.embed_girard`), which is what makes the top square commute; `IL.girardE := ILe.T ∘ IL.embed`
is the total version landing in ILLᵉ (with `ff ↦ !⊥`).
-/

@[expose] public section

universe u

variable {α : Type u}

/-! ## The two conservative extensions (vertical top arrows) -/

/-- Embedding of ILL formulas into ILLᵉ formulas (`A ⊸ B ↦ ¬A ⅋ B`) —
**Paper Section 3.1**, Corollary 3.7 (`ILC(ι) as a conservative extension of LLJ`, PDF p. 16). -/
def ILL.embed : ILL.Formula α → ILLe.Formula α
  | .var x => .var x
  | .top => .top
  | .tensor A B => .tensor (embed A) (embed B)
  | .with A B => .with (embed A) (embed B)
  | .plus A B => .plus (embed A) (embed B)
  | .limp A B => ILLe.Formula.limp (embed A) (embed B)
  | .bang A => .bang (embed A)

/-- Embedding of IL formulas into ILᵉ formulas —
**Paper Section 3.2**, Corollary 3.14 (`INC as a conservative extension of LJ`, PDF p. 20). -/
def IL.embed : IL.Formula α → ILe.Formula α
  | .var x => .var x
  | .top => .top
  | .ff => .ff
  | .with A B => .with (embed A) (embed B)
  | .disj A B => .disj (embed A) (embed B)
  | .imp A B => .imp (embed A) (embed B)

/-! ## Unlinearisation `(_)_!` (horizontal arrows) -/

/-- The translation `𝒯_!` of ILᵉ formulas into ILLᵉ formulas (unlinearisation
`ILLᵉ_ι ⟶ ILᵉ`): `⊤ ↦ ⊤`, `ff ↦ !⊥`, `A & B ↦ 𝒯A & 𝒯B`, `A ∨ B ↦ !𝒯A ⊕ !𝒯B`,
`A ⇒ B ↦ !𝒯A ⊸ 𝒯B`, `?A ↦ ?𝒯A` —
**Paper Section 3.2, Lemma 3.16** (`Translation 𝒯_! of INC into ILC_ι`, PDF p. 23). -/
def ILe.T : ILe.Formula α → ILLe.Formula α
  | .var x => .var x
  | .top => .top
  | .ff => .bang .bot
  | .with A B => .with (T A) (T B)
  | .disj A B => .plus (.bang (T A)) (.bang (T B))
  | .imp A B => ILLe.Formula.limp (.bang (T A)) (T B)
  | .wn A => .wn (T A)

/-- The translation `𝒯_!` of CL formulas into CLL⁻ formulas (unlinearisation
`CLL⁻ ⟶ CL`): `tt ↦ tt`, `ff ↦ !⊥`, `A ∧ B ↦ 𝒯A ∧ 𝒯B`, `A ∨ B ↦ !𝒯A ⊕ !𝒯B`,
`A ⇛ B ↦ !𝒯A ↬ 𝒯B` —
**Paper Section 3.3, Lemma 3.22** (`Translation 𝒯_! of LK into CLC`, PDF p. 26). -/
def CL.Tbang : CL.Formula α → CLLneg.Formula α
  | .var x => .var x
  | .tt => .tt
  | .ff => .bang .bot
  | .conj A B => .conj (Tbang A) (Tbang B)
  | .disj A B => .plus (.bang (Tbang A)) (.bang (Tbang B))
  | .imp A B => .imp (.bang (Tbang A)) (Tbang B)

/-- Girard's translation of IL formulas into ILL formulas (`A ∨ B ↦ !A ⊕ !B`,
`A ⇒ B ↦ !A ⊸ B`) — **Paper Section 2.2**, PDF p. 12; **Section 3.2**, PDF p. 17.
It is undefined (`none`) exactly on formulas containing `ff`, since ILL has no falsity constant. -/
def IL.girard : IL.Formula α → Option (ILL.Formula α)
  | .var x => some (.var x)
  | .top => some .top
  | .ff => none
  | .with A B => do return .with (← girard A) (← girard B)
  | .disj A B => do return .plus (.bang (← girard A)) (.bang (← girard B))
  | .imp A B => do return .limp (.bang (← girard A)) (← girard B)

/-- The total version of Girard's translation, landing in ILLᵉ (with `ff ↦ !⊥`):
`𝒯_! ∘ embed` — **Paper Section 1.3 / Section 3.2** (PDF p. 3, 17). -/
def IL.girardE (A : IL.Formula α) : ILLe.Formula α := ILe.T (IL.embed A)

/-! ## Classicalisation `(_)_?` (vertical bottom arrows) -/

/-- The translation `𝒯_?` of CLL⁻ formulas into ILLᵉ formulas (classicalisation
`ILLᵉ_ι ⟶ CLL⁻`): `tt ↦ ?⊤`, `⊥ ↦ ⊥`, `A ∧ B ↦ ?𝒯A & ?𝒯B`, `A ⊕ B ↦ 𝒯A ⊕ 𝒯B`,
`A ↬ B ↦ 𝒯A ⊸ ?𝒯B`, `!A ↦ !𝒯A` —
**Paper Section 3.3, Lemma 3.23** (`Translation 𝒯_? of CLC into ILC_ι`, PDF p. 27). -/
def CLLneg.T : CLLneg.Formula α → ILLe.Formula α
  | .var x => .var x
  | .tt => .wn .top
  | .bot => .bot
  | .conj A B => .with (.wn (T A)) (.wn (T B))
  | .plus A B => .plus (T A) (T B)
  | .imp A B => ILLe.Formula.limp (T A) (.wn (T B))
  | .bang A => .bang (T A)

/-- The translation `𝒯_?` of CL formulas into ILᵉ formulas (classicalisation
`ILᵉ ⟶ CL`): `tt ↦ ?⊤`, `ff ↦ ff`, `A ∧ B ↦ ?𝒯A & ?𝒯B`, `A ∨ B ↦ 𝒯A ∨ 𝒯B`,
`A ⇛ B ↦ 𝒯A ⇒ ?𝒯B` —
**Paper Section 3.2, Lemma 3.15** (`Translation 𝒯_? of LK into INC`, PDF p. 22). -/
def CL.Twn : CL.Formula α → ILe.Formula α
  | .var x => .var x
  | .tt => .wn .top
  | .ff => .ff
  | .conj A B => .with (.wn (Twn A)) (.wn (Twn B))
  | .disj A B => .disj (Twn A) (Twn B)
  | .imp A B => .imp (Twn A) (.wn (Twn B))

/-! ## The composite translations of CL into ILLᵉ_ι -/

/-- `𝒯_{!?} := 𝒯_! ∘ 𝒯_?` : CL → ILᵉ → ILLᵉ (route through ILᵉ) —
**Paper Section 3.2, Corollary 3.18** (PDF p. 25); **Section 3.4, Theorem 3.26** (PDF p. 29). -/
def CL.Tbangwn (A : CL.Formula α) : ILLe.Formula α := ILe.T (CL.Twn A)

/-- `𝒯_{?!} := 𝒯_? ∘ 𝒯_!` : CL → CLL⁻ → ILLᵉ (route through CLL⁻) —
**Paper Section 3.3, Corollary 3.25** (PDF p. 29); **Section 3.4, Theorem 3.26** (PDF p. 29). -/
def CL.Twnbang (A : CL.Formula α) : ILLe.Formula α := CLLneg.T (CL.Tbang A)

/-! ## Commutativity of the diagram at the level of formulas -/

/-- **Commutativity of the lower square** (formulas) —
**Paper Section 3.4, Theorem 3.26** (`Commutative unity of logic`, PDF p. 29):
the two routes CL → ILᵉ → ILLᵉ and CL → CLL⁻ → ILLᵉ yield the same translation `𝒯_{!?} = 𝒯_{?!}`. -/
theorem CL.Tbangwn_eq_Twnbang (A : CL.Formula α) : CL.Tbangwn A = CL.Twnbang A := by
  induction A with
  | var x => rfl
  | tt => rfl
  | ff => rfl
  | conj A B ihA ihB =>
    simp only [CL.Tbangwn, CL.Twnbang] at *
    simp [CL.Twn, CL.Tbang, ILe.T, CLLneg.T, ihA, ihB]
  | disj A B ihA ihB =>
    simp only [CL.Tbangwn, CL.Twnbang] at *
    simp [CL.Twn, CL.Tbang, ILe.T, CLLneg.T, ihA, ihB]
  | imp A B ihA ihB =>
    simp only [CL.Tbangwn, CL.Twnbang] at *
    simp [CL.Twn, CL.Tbang, ILe.T, CLLneg.T, ihA, ihB]

/-- **Commutativity of the upper square** (formulas): whenever Girard's translation of an IL
formula `A` is defined (i.e. `A` is `ff`-free), embedding it into ILLᵉ gives the same
formula as first embedding `A` into ILᵉ and then applying `𝒯_!`. -/
theorem IL.embed_girard {A : IL.Formula α} {B : ILL.Formula α} (h : IL.girard A = some B) :
    ILL.embed B = ILe.T (IL.embed A) := by
  induction A generalizing B with
  | var x => simp [IL.girard] at h; subst h; rfl
  | top => simp [IL.girard] at h; subst h; rfl
  | ff => simp [IL.girard] at h
  | «with» A₁ A₂ ih₁ ih₂ =>
    simp only [IL.girard, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨B₁, h₁, B₂, h₂, rfl⟩ := h
    simp [ILL.embed, IL.embed, ILe.T, ih₁ h₁, ih₂ h₂]
  | disj A₁ A₂ ih₁ ih₂ =>
    simp only [IL.girard, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨B₁, h₁, B₂, h₂, rfl⟩ := h
    simp [ILL.embed, IL.embed, ILe.T, ih₁ h₁, ih₂ h₂]
  | imp A₁ A₂ ih₁ ih₂ =>
    simp only [IL.girard, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨B₁, h₁, B₂, h₂, rfl⟩ := h
    simp [ILL.embed, IL.embed, ILe.T, ih₁ h₁, ih₂ h₂]

end
