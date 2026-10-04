module

public import RequestProject.Logics.Util
public import RequestProject.Semantics.Polycategory

/-!
# Heyting algebras and Lindenbaum algebras: the algebraic models of intuitionistic logic

## What is the Lindenbaum algebra?

The **Lindenbaum–Tarski algebra** of a logic is the set of formulas *quotiented by provable
equivalence*: `A ~ B` iff both `A ⊢ B` and `B ⊢ A` are provable. It is partially ordered by
provability (`[A] ≤ [B]` iff `A ⊢ B`), and the connectives induce the algebraic operations:
`[A] ⊓ [B] = [A & B]`, `[A] ⊔ [B] = [A ∨ B]`, `[A] ⇨ [B] = [A ⇒ B]`, `⊤ = [⊤]`.

We construct it once and for all (`IL.ImpPreorder.Lindenbaum`) for any *implicative preorder*
on IL formulas, i.e. any provability relation `A ⊢ B` having the rules of the
`⊤, &, ∨, ⇒`-fragment, and prove it is a generalized Heyting algebra (a Heyting algebra
except possibly for a least element), and a Heyting algebra as soon as `ff ⊢ A` for all `A`.

## Intuitionistic vs. minimal logic

The calculus `IL.LJ` of the project is LJ *with* right weakening of an empty succedent
(`Δ ⊢` / `Δ ⊢ B`, hence ex falso `ff ⊢ B`), i.e. full intuitionistic logic. We prove:

* `IL.Lindenbaum.instHeytingAlgebra`: **the Lindenbaum algebra of intuitionistic logic is a
  Heyting algebra**;
* `IL.LJ.sound`, `IL.LJ.complete`, `IL.LJ.iff_valid`: **Heyting algebras are the
  algebraic models of intuitionistic logic** (soundness and completeness).
* `IL.LJ.operad`, `IL.evalOperadFunctor`: provability forms a thin coloured operad, and
  evaluation in a Heyting algebra is a functor of operads.

For comparison we also keep **minimal logic** `IL.LJm` (LJ *without* right weakening; this is
the explicit rule figure of LJ in the source). It has `ffL : ff ⊢` and `ffR : Δ ⊢ / Δ ⊢ ff`
but **no ex falso** (`IL.LJm.not_exfalso`), and its algebraic models are generalized Heyting
algebras with an *arbitrary* element interpreting `ff`:

* `IL.LJm.soundG`, `IL.LJm.completeG`, `IL.LJm.iff_validG`: soundness and completeness;
  `IL.LindenbaumM.instGeneralizedHeytingAlgebra`: its Lindenbaum algebra is a generalized
  Heyting algebra;
* `IL.LJm.sound`: LJm is sound for Heyting algebras (`ff ↦ ⊥`); `IL.LJm.toLJ`: LJm ⊆ LJ.
-/

@[expose] public section

universe u v

variable {α : Type u}

namespace IL

open Formula

/-! ## Semantics in (generalized) Heyting algebras -/

/-- Interpretation of an IL formula in a generalized Heyting algebra `H`, given a valuation
`v` of the variables and an element `f` interpreting `ff`. -/
def Formula.evalG {H : Type v} [GeneralizedHeytingAlgebra H] (f : H) (v : α → H) :
    Formula α → H
  | var x => v x
  | top => ⊤
  | ff => f
  | «with» A₁ A₂ => A₁.evalG f v ⊓ A₂.evalG f v
  | disj A₁ A₂ => A₁.evalG f v ⊔ A₂.evalG f v
  | imp A₁ A₂ => A₁.evalG f v ⇨ A₂.evalG f v

/-- Validity of `Δ ⊢ C` in a generalized Heyting algebra (an empty succedent is read as
`f`, the interpretation of `ff`). -/
def ValidG {H : Type v} [GeneralizedHeytingAlgebra H] (f : H) (v : α → H)
    (Δ : Multiset (Formula α)) (C : Option (Formula α)) : Prop :=
  (Δ.map (Formula.evalG f v)).inf ≤ C.elim f (Formula.evalG f v)

/-- Interpretation of an IL formula in a Heyting algebra: `ff ↦ ⊥`. -/
def Formula.eval {H : Type v} [HeytingAlgebra H] (v : α → H) (A : Formula α) : H :=
  A.evalG ⊥ v

/-- Validity of `Δ ⊢ C` in a Heyting algebra: `⋀ ⟦Δ⟧ ≤ ⟦C⟧`, where an empty succedent is
read as `⊥`. -/
def Valid {H : Type v} [HeytingAlgebra H] (v : α → H) (Δ : Finset (Formula α))
    (C : Option (Formula α)) : Prop :=
  Δ.inf (Formula.eval v) ≤ C.elim ⊥ (Formula.eval v)

lemma valid_iff {H : Type v} [HeytingAlgebra H] (v : α → H) (Δ : Finset (Formula α))
    (C : Option (Formula α)) :
    Valid v Δ C ↔ Δ.inf (Formula.eval v) ≤ C.elim ⊥ (Formula.eval v) := Iff.rfl

/-! ## Minimal logic: LJ without right weakening -/

/-- The sequent calculus **LJᵐ** for *minimal logic*: the rules of **LJ** (`IL.LJ`) *without*
the right weakening `Δ ⊢` / `Δ ⊢ B`. (This is the explicit rule figure of LJ in the source,
which the project used as `IL.LJ` before right weakening was added.) -/
inductive LJm : Multiset (Formula α) → Option (Formula α) → Prop
  | weakL {Δ : Multiset (Formula α)} {C} (A) : LJm Δ C → LJm (A ::ₘ Δ) C
  | contrL {Δ : Multiset (Formula α)} {C A} : LJm (A ::ₘ A ::ₘ Δ) C → LJm (A ::ₘ Δ) C
  | id (A) : LJm {A} (some A)
  | cut {Δ Δ' : Multiset (Formula α)} {C B} : LJm Δ (some B) → LJm (B ::ₘ Δ') C → LJm (Δ + Δ') C
  | topL {Δ : Multiset (Formula α)} {C} : LJm Δ C → LJm (top ::ₘ Δ) C
  | topR : LJm 0 (some top)
  | ffL : LJm {ff} none
  | ffR {Δ : Multiset (Formula α)} : LJm Δ none → LJm Δ (some ff)
  | withL₁ {Δ : Multiset (Formula α)} {C A₁} (A₂) : LJm (A₁ ::ₘ Δ) C → LJm («with» A₁ A₂ ::ₘ Δ) C
  | withL₂ {Δ : Multiset (Formula α)} {C A₂} (A₁) : LJm (A₂ ::ₘ Δ) C → LJm («with» A₁ A₂ ::ₘ Δ) C
  | withR {Δ : Multiset (Formula α)} {B₁ B₂} :
      LJm Δ (some B₁) → LJm Δ (some B₂) → LJm Δ (some («with» B₁ B₂))
  | disjL {Δ : Multiset (Formula α)} {C A₁ A₂} :
      LJm (A₁ ::ₘ Δ) C → LJm (A₂ ::ₘ Δ) C → LJm (disj A₁ A₂ ::ₘ Δ) C
  | disjR₁ {Δ : Multiset (Formula α)} {B₁} (B₂) : LJm Δ (some B₁) → LJm Δ (some (disj B₁ B₂))
  | disjR₂ {Δ : Multiset (Formula α)} {B₂} (B₁) : LJm Δ (some B₂) → LJm Δ (some (disj B₁ B₂))
  | impL {Δ : Multiset (Formula α)} {C A B} :
      LJm Δ (some A) → LJm (B ::ₘ Δ) C → LJm (imp A B ::ₘ Δ) C
  | impR {Δ : Multiset (Formula α)} {A B} : LJm (A ::ₘ Δ) (some B) → LJm Δ (some (imp A B))

/-- **Soundness of LJm for generalized Heyting algebras** with an arbitrary interpretation
`f` of `ff`. -/
theorem LJm.soundG {H : Type v} [GeneralizedHeytingAlgebra H] (f : H) (v : α → H)
    {Δ : Multiset (Formula α)} {C : Option (Formula α)} (h : LJm Δ C) : ValidG f v Δ C := by
  unfold ValidG
  induction h with
  | weakL A _ ih => simpa using inf_le_of_right_le ih
  | contrL _ ih => simpa using ih
  | id A => simp
  | cut _ _ ih₁ ih₂ =>
    simp only [Multiset.map_cons, Multiset.map_add, Multiset.inf_cons, Multiset.inf_add,
      Option.elim] at *
    exact (inf_le_inf_right _ ih₁).trans ih₂
  | topL _ ih => simpa [evalG] using ih
  | topR => simp [evalG]
  | ffL => simp [evalG]
  | ffR _ ih => simpa [evalG] using ih
  | withL₁ A₂ _ ih =>
    simp only [Multiset.map_cons, Multiset.inf_cons, evalG] at *
    exact le_trans (inf_le_inf_right _ inf_le_left) ih
  | withL₂ A₁ _ ih =>
    simp only [Multiset.map_cons, Multiset.inf_cons, evalG] at *
    exact le_trans (inf_le_inf_right _ inf_le_right) ih
  | withR _ _ ih₁ ih₂ =>
    simp only [Option.elim, evalG] at *
    exact le_inf ih₁ ih₂
  | disjL _ _ ih₁ ih₂ =>
    simp only [Multiset.map_cons, Multiset.inf_cons, evalG] at *
    rw [inf_sup_right]
    exact sup_le ih₁ ih₂
  | disjR₁ B₂ _ ih =>
    simp only [Option.elim, evalG] at *
    exact ih.trans le_sup_left
  | disjR₂ B₁ _ ih =>
    simp only [Option.elim, evalG] at *
    exact ih.trans le_sup_right
  | impL _ _ ih₁ ih₂ =>
    simp only [Multiset.map_cons, Multiset.inf_cons, Option.elim, evalG] at *
    refine le_trans ?_ ih₂
    exact le_inf (le_trans (le_inf inf_le_left (inf_le_right.trans ih₁)) himp_inf_le)
      inf_le_right
  | impR _ ih =>
    simp only [Multiset.map_cons, Multiset.inf_cons, Option.elim, evalG] at *
    rw [le_himp_iff, inf_comm]
    exact ih

/-- **Soundness of LJm for Heyting algebras.** -/
theorem LJm.sound {H : Type v} [HeytingAlgebra H] (v : α → H) {Δ : Multiset (Formula α)}
    {C : Option (Formula α)} (h : LJm Δ C) : (Δ.map (Formula.eval v)).inf ≤ C.elim ⊥ (Formula.eval v) :=
  LJm.soundG ⊥ v h

/-- The calculus `IL.LJm` (without right weakening) has **no ex falso**: `ff ⊢ X` is not
provable. (Counter-model: the two-element algebra `Bool` with `ff ↦ ⊤`, `X ↦ ⊥`.) -/
theorem LJm.not_exfalso (x : α) : ¬ LJm {ff} (some (var x)) := by
  intro h
  have := LJm.soundG (H := Bool) true (fun _ => false) h
  simp [ValidG, evalG] at this
  exact absurd this (by decide)

/-! ## Intuitionistic logic proper: LJ (with ex falso) -/

/-- Every **LJm**-provable sequent is **LJ**-provable. -/
theorem LJm.toLJ [DecidableEq α] {Δ : Multiset (Formula α)} {C : Option (Formula α)} (h : LJm Δ C) :
    LJ Δ.toFinset C := by
  induction h with
  | weakL A _ ih =>
    simpa only [Multiset.toFinset_cons] using LJ.weakL A ih
  | contrL _ ih =>
    simpa only [Multiset.toFinset_cons, Finset.insert_idem] using ih
  | id A => simpa using LJ.id A
  | cut _ _ ih₁ ih₂ =>
    have hcut := LJ.cut ih₁ (by simpa using ih₂)
    simpa [Multiset.toFinset_add] using hcut
  | topL _ ih =>
    simpa only [Multiset.toFinset_cons] using LJ.topL ih
  | topR => simpa using LJ.topR
  | ffL => simpa using LJ.ffL
  | ffR _ ih => exact LJ.ffR ih
  | withL₁ A₂ _ ih =>
    simpa only [Multiset.toFinset_cons] using LJ.withL₁ A₂ (by simpa using ih)
  | withL₂ A₁ _ ih =>
    simpa only [Multiset.toFinset_cons] using LJ.withL₂ A₁ (by simpa using ih)
  | withR _ _ ih₁ ih₂ => exact LJ.withR ih₁ ih₂
  | disjL _ _ ih₁ ih₂ =>
    simpa only [Multiset.toFinset_cons] using LJ.disjL (by simpa using ih₁) (by simpa using ih₂)
  | disjR₁ B₂ _ ih => exact LJ.disjR₁ B₂ ih
  | disjR₂ B₁ _ ih => exact LJ.disjR₂ B₁ ih
  | impL _ _ ih₁ ih₂ =>
    simpa only [Multiset.toFinset_cons] using LJ.impL ih₁ (by simpa using ih₂)
  | impR _ ih =>
    exact LJ.impR (by simpa using ih)

/-- **Soundness of LJ for Heyting algebras.** -/
theorem LJ.sound [DecidableEq α] {H : Type v} [HeytingAlgebra H] (v : α → H) {Δ : Finset (Formula α)}
    {C : Option (Formula α)} (h : LJ Δ C) : Valid v Δ C := by
  unfold Valid
  induction h with
  | weakL A _ ih =>
    rw [Finset.inf_insert]
    exact inf_le_of_right_le ih
  | weakR B _ ih => exact ih.trans bot_le
  | id A => simp [eval]
  | @cut Δ Δ' C B _ _ ih₁ ih₂ =>
    rw [Finset.inf_union]
    rw [Finset.inf_insert] at ih₂
    calc Δ.inf (eval v) ⊓ Δ'.inf (eval v)
      _ ≤ eval v B ⊓ Δ'.inf (eval v) := inf_le_inf_right _ ih₁
      _ ≤ C.elim ⊥ (eval v) := ih₂
  | topL _ ih =>
    rw [Finset.inf_insert]
    simpa [eval, evalG] using ih
  | topR => simp [eval, evalG]
  | ffL => simp [eval, evalG]
  | ffR _ ih => simpa [eval, evalG] using ih
  | @withL₁ Δ C A₁ A₂ _ ih =>
    rw [Finset.inf_insert] at *
    simp only [eval, evalG] at *
    calc (evalG ⊥ v A₁ ⊓ evalG ⊥ v A₂) ⊓ Δ.inf (eval v)
      _ ≤ evalG ⊥ v A₁ ⊓ Δ.inf (eval v) := inf_le_inf_right _ inf_le_left
      _ ≤ C.elim ⊥ (eval v) := ih
  | @withL₂ Δ C A₂ A₁ _ ih =>
    rw [Finset.inf_insert] at *
    simp only [eval, evalG] at *
    calc (evalG ⊥ v A₁ ⊓ evalG ⊥ v A₂) ⊓ Δ.inf (eval v)
      _ ≤ evalG ⊥ v A₂ ⊓ Δ.inf (eval v) := inf_le_inf_right _ inf_le_right
      _ ≤ C.elim ⊥ (eval v) := ih
  | withR _ _ ih₁ ih₂ =>
    simp only [Option.elim, eval, evalG] at *
    exact le_inf ih₁ ih₂
  | disjL _ _ ih₁ ih₂ =>
    rw [Finset.inf_insert] at *
    simp only [eval, evalG] at *
    rw [inf_sup_right]
    exact sup_le ih₁ ih₂
  | disjR₁ B₂ _ ih =>
    simp only [Option.elim, eval, evalG] at *
    exact ih.trans le_sup_left
  | disjR₂ B₁ _ ih =>
    simp only [Option.elim, eval, evalG] at *
    exact ih.trans le_sup_right
  | impL _ _ ih₁ ih₂ =>
    rw [Finset.inf_insert] at *
    simp only [Option.elim, eval, evalG] at *
    refine le_trans ?_ ih₂
    exact le_inf (le_trans (le_inf inf_le_left (inf_le_right.trans ih₁)) himp_inf_le)
      inf_le_right
  | impR _ ih =>
    rw [Finset.inf_insert] at ih
    simp only [Option.elim, eval, evalG] at *
    rw [le_himp_iff, inf_comm]
    exact ih

/-! ## The Lindenbaum algebra of an implicative preorder -/

/-- An **implicative preorder** on IL formulas: a provability relation `R A B` ("`A ⊢ B`")
which is reflexive and transitive and has the rules of `⊤`, `&`, `∨` and `⇒`. -/
structure ImpPreorder (α : Type u) where
  /-- `R A B`: `A ⊢ B` is provable -/
  R : Formula α → Formula α → Prop
  refl : ∀ A, R A A
  trans : ∀ {A B C}, R A B → R B C → R A C
  le_top : ∀ A, R A top
  with_le_left : ∀ A B, R («with» A B) A
  with_le_right : ∀ A B, R («with» A B) B
  le_with : ∀ {A B C}, R C A → R C B → R C («with» A B)
  le_disj_left : ∀ A B, R A (disj A B)
  le_disj_right : ∀ A B, R B (disj A B)
  disj_le : ∀ {A B C}, R A C → R B C → R (disj A B) C
  le_imp_iff : ∀ {A B C}, R C (imp A B) ↔ R («with» C A) B

namespace ImpPreorder

variable (P : ImpPreorder α)

/-- Formulas preordered by `P`. -/
def Carrier (_ : ImpPreorder α) : Type u := Formula α

instance : Preorder P.Carrier where
  le := P.R
  le_refl := P.refl
  le_trans _ _ _ := P.trans

/-- The **Lindenbaum algebra** of `P`: formulas modulo `P`-provable equivalence. -/
def Lindenbaum : Type u := Antisymmetrization P.Carrier (· ≤ ·)

namespace Lindenbaum

variable {P}

instance : PartialOrder P.Lindenbaum :=
  inferInstanceAs (PartialOrder (Antisymmetrization P.Carrier (· ≤ ·)))

/-- The equivalence class of a formula. -/
def mk (A : Formula α) : P.Lindenbaum := toAntisymmetrization (· ≤ ·) (A : P.Carrier)

lemma mk_le_mk {A B : Formula α} : (mk A : P.Lindenbaum) ≤ mk B ↔ P.R A B :=
  toAntisymmetrization_le_toAntisymmetrization_iff

@[elab_as_elim]
lemma ind {motive : P.Lindenbaum → Prop} (h : ∀ A, motive (mk A)) (x : P.Lindenbaum) :
    motive x := Quotient.ind h x

lemma with_mono {a a' b b' : Formula α} (ha : P.R a a') (hb : P.R b b') :
    P.R («with» a b) («with» a' b') :=
  P.le_with (P.trans (P.with_le_left _ _) ha) (P.trans (P.with_le_right _ _) hb)

lemma disj_mono {a a' b b' : Formula α} (ha : P.R a a') (hb : P.R b b') :
    P.R (disj a b) (disj a' b') :=
  P.disj_le (P.trans ha (P.le_disj_left _ _)) (P.trans hb (P.le_disj_right _ _))

lemma imp_mono {a a' b b' : Formula α} (ha : P.R a' a) (hb : P.R b b') :
    P.R (imp a b) (imp a' b') := by
  rw [P.le_imp_iff]
  have h1 : P.R («with» (imp a b) a) b := P.le_imp_iff.1 (P.refl _)
  exact P.trans (with_mono (P.refl _) ha) (P.trans h1 hb)

instance : Max P.Lindenbaum :=
  ⟨Quotient.map₂ (disj : P.Carrier → P.Carrier → P.Carrier)
    (fun _ _ ha _ _ hb => ⟨disj_mono ha.1 hb.1, disj_mono ha.2 hb.2⟩)⟩
instance : Min P.Lindenbaum :=
  ⟨Quotient.map₂ («with» : P.Carrier → P.Carrier → P.Carrier)
    (fun _ _ ha _ _ hb => ⟨with_mono ha.1 hb.1, with_mono ha.2 hb.2⟩)⟩
instance : Top P.Lindenbaum := ⟨mk top⟩
instance : HImp P.Lindenbaum :=
  ⟨Quotient.map₂ (imp : P.Carrier → P.Carrier → P.Carrier)
    (fun _ _ ha _ _ hb => ⟨imp_mono ha.2 hb.1, imp_mono ha.1 hb.2⟩)⟩

@[simp] lemma mk_sup (A B : Formula α) : (mk A : P.Lindenbaum) ⊔ mk B = mk (disj A B) := rfl
@[simp] lemma mk_inf (A B : Formula α) : (mk A : P.Lindenbaum) ⊓ mk B = mk («with» A B) := rfl
@[simp] lemma mk_top : (⊤ : P.Lindenbaum) = mk top := rfl
@[simp] lemma mk_himp (A B : Formula α) : (mk A : P.Lindenbaum) ⇨ mk B = mk (imp A B) := rfl

/-- **The Lindenbaum algebra of an implicative preorder is a generalized Heyting algebra.** -/
instance instGeneralizedHeytingAlgebra : GeneralizedHeytingAlgebra P.Lindenbaum where
  sup := (· ⊔ ·)
  inf := (· ⊓ ·)
  top := ⊤
  himp := (· ⇨ ·)
  le_sup_left x y := by
    induction x using ind; induction y using ind; exact mk_le_mk.2 (P.le_disj_left _ _)
  le_sup_right x y := by
    induction x using ind; induction y using ind; exact mk_le_mk.2 (P.le_disj_right _ _)
  sup_le x y z := by
    induction x using ind; induction y using ind; induction z using ind
    intro h₁ h₂; exact mk_le_mk.2 (P.disj_le (mk_le_mk.1 h₁) (mk_le_mk.1 h₂))
  inf_le_left x y := by
    induction x using ind; induction y using ind; exact mk_le_mk.2 (P.with_le_left _ _)
  inf_le_right x y := by
    induction x using ind; induction y using ind; exact mk_le_mk.2 (P.with_le_right _ _)
  le_inf x y z := by
    induction x using ind; induction y using ind; induction z using ind
    intro h₁ h₂; exact mk_le_mk.2 (P.le_with (mk_le_mk.1 h₁) (mk_le_mk.1 h₂))
  le_top x := by induction x using ind; exact mk_le_mk.2 (P.le_top _)
  le_himp_iff x y z := by
    induction x using ind; induction y using ind; induction z using ind
    exact (mk_le_mk.trans P.le_imp_iff).trans mk_le_mk.symm

/-- If moreover `ff ⊢ A` for every `A`, **the Lindenbaum algebra is a Heyting algebra**,
with least element `[ff]`. -/
def heytingAlgebra (hff : ∀ A, P.R ff A) : HeytingAlgebra P.Lindenbaum where
  bot := mk ff
  bot_le x := by induction x using ind; exact mk_le_mk.2 (hff _)
  compl x := x ⇨ mk ff
  himp_bot _ := rfl

end Lindenbaum

end ImpPreorder

/-! ## Derived rules of LJm and LJ -/

namespace LJm

lemma cast' {Δ Δ' : Multiset (Formula α)} {C C' : Option (Formula α)} (h : LJm Δ C)
    (h₁ : Δ = Δ') (h₂ : C = C') : LJm Δ' C' := h₁ ▸ h₂ ▸ h

lemma swap2 (a b : Formula α) : a ::ₘ ({b} : Multiset (Formula α)) = b ::ₘ {a} :=
  Multiset.cons_swap a b 0

/-- modus ponens: `A ⇒ B, A ⊢ B` -/
lemma mp (A B : Formula α) : LJm (imp A B ::ₘ {A}) (some B) :=
  impL (Δ := {A}) (id A) ((weakL A (id B)).cast' (swap2 _ _) rfl)

/-- `C, A ⊢ C & A` -/
lemma pair (C A : Formula α) : LJm (A ::ₘ {C}) (some («with» C A)) :=
  withR ((weakL A (id C))) ((weakL C (id A)).cast' (swap2 _ _) rfl)

/-- `C, A ⊢ B` from `C & A ⊢ B` and conversely. -/
lemma with_left_iff {C A B : Formula α} : LJm {«with» C A} (some B) ↔ LJm (A ::ₘ {C}) (some B) := by
  constructor
  · intro h
    exact (cut (Δ' := 0) (pair C A) h).cast' (by simp) rfl
  · intro h
    have h1 := withL₂ (Δ := {C}) C h
    have h2 := withL₁ (Δ := {«with» C A}) A (h1.cast' (swap2 _ _) rfl)
    exact contrL h2

/-- The provability preorder of **LJm** on single formulas. -/
def impPreorder (α : Type u) : ImpPreorder α where
  R A B := LJm {A} (some B)
  refl := id
  trans h₁ h₂ := (cut (Δ' := 0) h₁ h₂).cast' (by simp) rfl
  le_top A := weakL (Δ := 0) A topR
  with_le_left A B := withL₁ (Δ := 0) B (id A)
  with_le_right A B := withL₂ (Δ := 0) A (id B)
  le_with := withR
  le_disj_left A B := disjR₁ B (id A)
  le_disj_right A B := disjR₂ A (id B)
  disj_le := disjL (Δ := 0)
  le_imp_iff {A B C} := by
    rw [with_left_iff]
    constructor
    · intro h
      exact (cut (Δ' := {A}) h (mp A B)).cast' (by rw [add_comm]; rfl) rfl
    · intro h
      exact impR (Δ := {C}) h

end LJm

namespace LJ

lemma cast' [DecidableEq α] {Δ Δ' : Finset (Formula α)} {C C' : Option (Formula α)} (h : LJ Δ C)
    (h₁ : Δ = Δ') (h₂ : C = C') : LJ Δ' C' := h₁ ▸ h₂ ▸ h

/-- The provability preorder of **LJ** on single formulas. -/
def impPreorder (α : Type u) [DecidableEq α] : ImpPreorder α where
  R A B := LJ {A} (some B)
  refl := id
  trans h₁ h₂ := (cut (Δ' := ∅) h₁ h₂).cast' (by simp) rfl
  le_top A := weakL A topR
  with_le_left A B := withL₁ (Δ := ∅) B (id A)
  with_le_right A B := withL₂ (Δ := ∅) A (id B)
  le_with := withR
  le_disj_left A B := disjR₁ B (id A)
  le_disj_right A B := disjR₂ A (id B)
  disj_le h₁ h₂ := disjL (Δ := ∅) h₁ h₂
  le_imp_iff {A B C} := by
    constructor
    · intro h
      have hmp : LJ (imp A B ::ᵢ {A}) (some B) := by
        have h1 : LJ (B ::ᵢ {A}) (some B) := by
          have e : (B ::ᵢ {A} : Finset (Formula α)) = A ::ᵢ {B} := by ext; simp [or_comm]
          rw [e]; exact weakL A (id B)
        exact impL (id A) h1
      have h1 : LJ (A ::ᵢ {C}) (some B) := by
        have hcut := cut (Δ' := {A}) h hmp
        have e : ({C} ∪ {A} : Finset (Formula α)) = A ::ᵢ {C} := by ext; simp [or_comm]
        rwa [e] at hcut
      have h2 : LJ («with» C A ::ᵢ {C}) (some B) := withL₂ C h1
      have e2 : («with» C A ::ᵢ {C} : Finset (Formula α)) = C ::ᵢ {«with» C A} := by ext; simp [or_comm]
      rw [e2] at h2
      have h3 := withL₁ A h2
      simpa using h3
    · intro h
      have hpair : LJ (A ::ᵢ ({C} : Finset (Formula α))) (some («with» C A)) := by
        have h1 : LJ (A ::ᵢ {C}) (some C) := weakL A (id C)
        have h2 : LJ (A ::ᵢ {C}) (some A) := by
          have e : (A ::ᵢ {C} : Finset (Formula α)) = C ::ᵢ {A} := by ext; simp [or_comm]
          rw [e]; exact weakL C (id A)
        exact withR h1 h2
      have hcut : LJ (A ::ᵢ {C}) (some B) := by
        have := cut (Δ' := ∅) hpair h
        have e : (A ::ᵢ {C} : Finset (Formula α)) ∪ ∅ = A ::ᵢ {C} := by simp
        rwa [e] at this
      exact impR hcut

end LJ

/-! ## Lindenbaum algebras of minimal and intuitionistic logic -/

/-- The **Lindenbaum algebra of LJm**: IL formulas modulo **LJm**-provable equivalence. -/
abbrev LindenbaumM (α : Type u) : Type u := (LJm.impPreorder α).Lindenbaum

/-- The **Lindenbaum algebra of intuitionistic logic** (formulas modulo provable equivalence
in **LJ**: `A ~ B` iff `A ⊢ B` and `B ⊢ A`). -/
abbrev Lindenbaum (α : Type u) [DecidableEq α] : Type u := (LJ.impPreorder α).Lindenbaum

/-- **The Lindenbaum algebra of LJm is a generalized Heyting algebra.** -/
instance LindenbaumM.instGeneralizedHeytingAlgebra : GeneralizedHeytingAlgebra (LindenbaumM α) :=
  ImpPreorder.Lindenbaum.instGeneralizedHeytingAlgebra

/-- **The Lindenbaum algebra of intuitionistic logic is a Heyting algebra.** -/
instance Lindenbaum.instHeytingAlgebra [DecidableEq α] : HeytingAlgebra (Lindenbaum α) :=
  ImpPreorder.Lindenbaum.heytingAlgebra (P := LJ.impPreorder α)
    (fun A => show (LJ.impPreorder α).R ff A from LJ.weakR A LJ.ffL)

open ImpPreorder.Lindenbaum in
lemma LindenbaumM.evalG_mk (A : Formula α) :
    A.evalG (mk ff : LindenbaumM α) (fun x => mk (var x)) = mk A := by
  induction A with
  | var x => rfl
  | top => rfl
  | ff => rfl
  | «with» A B ihA ihB => simp only [evalG, ihA, ihB]; rfl
  | disj A B ihA ihB => simp only [evalG, ihA, ihB]; rfl
  | imp A B ihA ihB => simp only [evalG, ihA, ihB]; rfl

open ImpPreorder.Lindenbaum in
lemma Lindenbaum.eval_mk [DecidableEq α] (A : Formula α) :
    A.eval (fun x => (mk (var x) : Lindenbaum α)) = mk A := by
  induction A with
  | var x => rfl
  | top => rfl
  | ff => rfl
  | «with» A B ihA ihB => simp only [eval, evalG] at *; rw [ihA, ihB]; rfl
  | disj A B ihA ihB => simp only [eval, evalG] at *; rw [ihA, ihB]; rfl
  | imp A B ihA ihB => simp only [eval, evalG] at *; rw [ihA, ihB]; rfl

open ImpPreorder.Lindenbaum in
lemma LJm.of_inf_le (Δ : Multiset (Formula α)) :
    ∀ B, (Δ.map (mk : Formula α → LindenbaumM α)).inf ≤ mk B → LJm Δ (some B) := by
  induction Δ using Multiset.induction_on with
  | empty =>
    intro B h
    have h' : LJm {top} (some B) := mk_le_mk.1 (by simpa using h)
    exact (LJm.cut (Δ := 0) LJm.topR h').cast' (by simp) rfl
  | cons A Δ ih =>
    intro B h
    simp only [Multiset.map_cons, Multiset.inf_cons] at h
    have h2 : (Δ.map (mk : Formula α → LindenbaumM α)).inf ≤ mk (imp A B) := by
      rw [← mk_himp, le_himp_iff, inf_comm]; exact h
    exact (LJm.cut (Δ' := {A}) (ih _ h2) (LJm.mp A B)).cast'
      (by rw [add_comm]; rfl) rfl

open ImpPreorder.Lindenbaum in
lemma LJ.of_inf_le [DecidableEq α] (Δ : Finset (Formula α)) :
    ∀ B, (Δ.inf (mk : Formula α → Lindenbaum α)) ≤ mk B → LJ Δ (some B) := by
  induction Δ using Finset.induction_on with
  | empty =>
    intro B h
    have h' : LJ {top} (some B) := by
      have hle : (mk top : Lindenbaum α) ≤ mk B := by simpa using h
      have hr : (LJ.impPreorder α).R top B := mk_le_mk.1 hle
      exact hr
    exact (LJ.cut (Δ' := ∅) LJ.topR h').cast' (by simp) rfl
  | insert A Δ _ ih =>
    intro B h
    rw [Finset.inf_insert] at h
    have h2 : (Δ.inf (mk : Formula α → Lindenbaum α)) ≤ mk (imp A B) := by
      rw [← mk_himp, le_himp_iff, inf_comm]; exact h
    have hmp : LJ (imp A B ::ᵢ {A}) (some B) := by
      have h1 : LJ (B ::ᵢ {A}) (some B) := by
        have e : (B ::ᵢ {A} : Finset (Formula α)) = A ::ᵢ {B} := by ext; simp [or_comm]
        rw [e]; exact weakL A (id B)
      exact impL (id A) h1
    have hcut := LJ.cut (Δ' := {A}) (ih _ h2) hmp
    have e : Δ ∪ {A} = A ::ᵢ Δ := by ext; simp
    rwa [e] at hcut

open ImpPreorder.Lindenbaum in
/-- **Completeness of LJm for generalized Heyting algebras** (with a designated element
interpreting `ff`). -/
theorem LJm.completeG {Δ : Multiset (Formula α)} {C : Option (Formula α)}
    (h : ∀ (H : Type u) [GeneralizedHeytingAlgebra H] (f : H) (v : α → H), ValidG f v Δ C) :
    LJm Δ C := by
  have := h (LindenbaumM α) (mk ff) (fun x => mk (var x))
  have hmap : Δ.map (Formula.evalG (mk ff : LindenbaumM α) (fun x => mk (var x))) = Δ.map mk :=
    Multiset.map_congr rfl (fun A _ => LindenbaumM.evalG_mk A)
  simp only [ValidG, hmap] at this
  have key : ∀ B, (Δ.map (mk : Formula α → LindenbaumM α)).inf ≤ mk B → LJm Δ (some B) :=
    LJm.of_inf_le Δ
  rcases C with _ | B
  · exact (LJm.cut (Δ' := 0) (key ff this) LJm.ffL).cast' (by simp) rfl
  · exact key B (by simpa [LindenbaumM.evalG_mk] using this)

/-- **LJm is minimal logic**: provability in **LJm** = validity in all generalized Heyting
algebras with an arbitrary interpretation of `ff`. -/
theorem LJm.iff_validG {Δ : Multiset (Formula α)} {C : Option (Formula α)} :
    LJm Δ C ↔ ∀ (H : Type u) [GeneralizedHeytingAlgebra H] (f : H) (v : α → H), ValidG f v Δ C :=
  ⟨fun h _ _ f v => h.soundG f v, LJm.completeG⟩

open ImpPreorder.Lindenbaum in
/-- **Completeness of intuitionistic logic (LJ) for Heyting algebras.** -/
theorem LJ.complete [DecidableEq α] {Δ : Finset (Formula α)} {C : Option (Formula α)}
    (h : ∀ (H : Type u) [HeytingAlgebra H] (v : α → H), Valid v Δ C) : LJ Δ C := by
  have := h (Lindenbaum α) (fun x => mk (var x))
  rw [valid_iff] at this
  have hmap : Δ.inf (Formula.eval (fun x => (mk (var x) : Lindenbaum α))) = Δ.inf mk :=
    Finset.inf_congr rfl (fun A _ => Lindenbaum.eval_mk A)
  rw [hmap] at this
  have key : ∀ B, (Δ.inf (mk : Formula α → Lindenbaum α)) ≤ mk B → LJ Δ (some B) :=
    LJ.of_inf_le Δ
  rcases C with _ | B
  · exact (LJ.cut (Δ' := ∅) (key ff this) LJ.ffL).cast' (by simp) rfl
  · exact key B (by simpa [Lindenbaum.eval_mk] using this)

/-- **Heyting algebras are the algebraic models of intuitionistic logic**: a sequent is
provable in **LJ** iff it is valid in every Heyting algebra under every valuation. -/
theorem LJ.iff_valid [DecidableEq α] {Δ : Finset (Formula α)} {C : Option (Formula α)} :
    LJ Δ C ↔ ∀ (H : Type u) [HeytingAlgebra H] (v : α → H), Valid v Δ C :=
  ⟨fun h _ _ v => h.sound v, LJ.complete⟩

/-! ## The categorical picture: coloured operads -/

/-- Provability in **LJ** (with a non-empty succedent) forms a thin coloured operad. -/
def LJ.operad (α : Type u) [DecidableEq α] : ThinColoredOperad (Formula α) where
  Hom Δ B := LJ Δ (some B)
  id := LJ.id
  comp := LJ.cut

/-- **Soundness, categorically**: evaluation in a Heyting algebra is a functor of operads. -/
def evalOperadFunctor {H : Type v} [DecidableEq α] [DecidableEq H] [HeytingAlgebra H] (v : α → H) :
    ThinColoredOperad.Functor (LJ.operad α) (SemilatticeInf.toThinColoredOperad H) where
  obj := Formula.eval v
  map {Γ B} h := by
    dsimp [SemilatticeInf.toThinColoredOperad]
    have := h.sound v
    unfold Valid at this
    dsimp at this
    rw [Finset.inf_image]
    exact this

end IL

end
