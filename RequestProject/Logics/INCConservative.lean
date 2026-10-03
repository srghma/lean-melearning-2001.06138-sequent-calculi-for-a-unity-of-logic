module

public import RequestProject.Logics.Diagram
public import RequestProject.Semantics.Okada

/-!
# INC is a conservative extension of minimal LJ

The source paper derives "INC is a conservative extension of LJ" from cut-elimination. Since
**INC** has no ex falso (`ILe.INC.not_exfalso`), the statement holds for *minimal* logic
**LJᵐ** (`IL.LJm`, the explicit rule figure of LJ in the source) and fails for full
intuitionistic **LJ** (`IL.not_INCConservative`). Here it is proved for **LJᵐ** without any
cut-elimination theorem:

* **INC ⟹ LJᵐ** (`IL.INC.toLJm`): **INC** is sound for generalized Heyting algebras when
  `ff` denotes an arbitrary element `f` and `?A` is read as `(A ⇨ f) ⇨ f`, with the `?`-formulas
  on the right moved to the left as `A ⇨ f` (`ILe.INC.soundG`); on IL formulas this is the
  semantics for which **LJᵐ** is complete (`IL.LJm.completeG`). The same soundness theorem shows
  that every provable sequent has at most one non-`?` formula on the right
  (`IL.INC.card_le_one_of_embed`).
* **LJᵐ ⟹ INC** (`IL.LJm.toINC`): the sets of contexts closed under **INC** provability form a
  generalized Heyting algebra (`Okada.Closed`); **LJᵐ** is sound for it, and Okada's lemma
  (`IL.okada`) turns validity there back into **INC** provability. This replaces the use of
  cut-elimination for **LJ** in the source (INC only has the restricted cut `Cut^?`).
* `IL.incConservativeMin`: the conservativity statement `IL.INCConservativeMin`.
* `IL.LJm.toILC`, `IL.LJm.toLLJ_of_conservative`: Girard's translation on the minimal-logic
  presentation of the top-right corner.
-/

@[expose] public section

universe u v

variable {α : Type u}

namespace ILe

open Formula

/-! ## A sound interpretation of INC in generalized Heyting algebras -/

variable {H : Type v} [GeneralizedHeytingAlgebra H]

/-- Interpretation of ILᵉ formulas in a generalized Heyting algebra with a designated element
`f` for `ff`; `?A` is read as the `f`-relative double negation `(⟦A⟧ ⇨ f) ⇨ f`. -/
def Formula.evalG (f : H) (v : α → H) : Formula α → H
  | var x => v x
  | top => ⊤
  | ff => f
  | «with» A B => A.evalG f v ⊓ B.evalG f v
  | disj A B => A.evalG f v ⊔ B.evalG f v
  | imp A B => A.evalG f v ⇨ B.evalG f v
  | wn A => (A.evalG f v ⇨ f) ⇨ f

/-- Whether a formula is of the form `?A`. -/
def Formula.isWn : Formula α → Bool
  | wn _ => true
  | _ => false

/-- The non-`?` part of a succedent. -/
def nonWn (Γ : Multiset (Formula α)) : Multiset (Formula α) := Γ.filter (fun A => A.isWn = false)

/-- Contribution of a succedent formula `?C` to the antecedent: `⟦C⟧ ⇨ f`. -/
def wnPart (f : H) (v : α → H) : Formula α → H
  | wn C => C.evalG f v ⇨ f
  | _ => ⊤

/-- The antecedent value of a sequent `Δ ⊢ Γ`: `⋀⟦Δ⟧ ⊓ ⋀_{?C ∈ Γ} (⟦C⟧ ⇨ f)`. -/
def lhs (f : H) (v : α → H) (Δ Γ : Multiset (Formula α)) : H :=
  (Δ.map (Formula.evalG f v)).inf ⊓ (Γ.map (wnPart f v)).inf

/-- Semantic validity of an INC sequent: at most one non-`?` formula on the right, and the
antecedent value lies below it (or below `f` if there is none). -/
def Sem (f : H) (v : α → H) (Δ Γ : Multiset (Formula α)) : Prop :=
  (nonWn Γ).card ≤ 1 ∧ (nonWn Γ = 0 → lhs f v Δ Γ ≤ f) ∧
    ∀ B ∈ nonWn Γ, lhs f v Δ Γ ≤ B.evalG f v

lemma triple_neg (b f : H) : ((b ⇨ f) ⇨ f) ⇨ f = b ⇨ f := by
  have hb : b ≤ (b ⇨ f) ⇨ f := by rw [le_himp_iff]; exact inf_himp_le
  apply le_antisymm
  · rw [le_himp_iff]
    exact (inf_le_inf_left _ hb).trans himp_inf_le
  · rw [le_himp_iff]; exact inf_himp_le

lemma wnPart_wn_evalG (f : H) (v : α → H) (B : Formula α) :
    wnPart f v (wn B) = B.evalG f v ⇨ f := rfl

@[simp] lemma nonWn_zero : nonWn (0 : Multiset (Formula α)) = 0 := rfl

lemma nonWn_cons (A : Formula α) (Γ : Multiset (Formula α)) :
    nonWn (A ::ₘ Γ) = if A.isWn = false then A ::ₘ nonWn Γ else nonWn Γ := by
  unfold nonWn; rw [Multiset.filter_cons]; split_ifs <;> simp

@[simp] lemma nonWn_cons_wn (A : Formula α) (Γ : Multiset (Formula α)) :
    nonWn (wn A ::ₘ Γ) = nonWn Γ := by
  rw [nonWn_cons]; simp [Formula.isWn]

@[simp] lemma nonWn_add (Γ Γ' : Multiset (Formula α)) :
    nonWn (Γ + Γ') = nonWn Γ + nonWn Γ' := Multiset.filter_add _ _ _

@[simp] lemma nonWn_map_wn (Γ : Multiset (Formula α)) : nonWn (Γ.map wn) = 0 := by
  unfold nonWn; rw [Multiset.filter_eq_nil]; intro a ha
  obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 ha; simp [Formula.isWn]

lemma map_wnPart_map_wn (f : H) (v : α → H) (Γ : Multiset (Formula α)) :
    (Γ.map wn).map (wnPart f v) = Γ.map (fun C => C.evalG f v ⇨ f) := by
  rw [Multiset.map_map]; rfl

/-- `Sem` for a succedent `A, ?Γ`. -/
lemma sem_single_iff (f : H) (v : α → H) (Δ Γ : Multiset (Formula α)) (A : Formula α) :
    Sem f v Δ (A ::ₘ Γ.map wn) ↔
      (Δ.map (Formula.evalG f v)).inf ⊓ (Γ.map (fun C => C.evalG f v ⇨ f)).inf ≤
        A.evalG f v := by
  cases A with
  | wn B =>
    simp only [Sem, nonWn_cons_wn, nonWn_map_wn, Multiset.card_zero, zero_le, true_and,
      Multiset.notMem_zero, false_imp_iff, implies_true, and_true, forall_const, lhs,
      Multiset.map_cons, Multiset.inf_cons, wnPart_wn_evalG, map_wnPart_map_wn,
      Formula.evalG]
    rw [le_himp_iff]
    constructor <;> intro h <;> refine le_trans (le_of_eq ?_) h <;> ac_rfl
  | _ =>
    simp only [Sem, lhs, Multiset.map_cons, Multiset.inf_cons, map_wnPart_map_wn]
    simp [nonWn_cons, Formula.isWn, wnPart]

/-- `Sem` for a succedent `?Γ`. -/
lemma sem_none_iff (f : H) (v : α → H) (Δ Γ : Multiset (Formula α)) :
    Sem f v Δ (Γ.map wn) ↔
      (Δ.map (Formula.evalG f v)).inf ⊓ (Γ.map (fun C => C.evalG f v ⇨ f)).inf ≤ f := by
  simp only [Sem, lhs, map_wnPart_map_wn, nonWn_map_wn]
  simp

/-- Transfer of `Sem` along a smaller antecedent value with the same non-`?` part. -/
lemma sem_of_le {f : H} {v : α → H} {Δ Γ Δ' Γ' : Multiset (Formula α)} (h : Sem f v Δ Γ)
    (hle : lhs f v Δ' Γ' ≤ lhs f v Δ Γ) (hN : nonWn Γ' = nonWn Γ) : Sem f v Δ' Γ' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hN ▸ h1, fun h0 => hle.trans (h2 (hN ▸ h0)), fun B hB => hle.trans (h3 B (hN ▸ hB))⟩

/-- **Soundness of INC** for the `f`-relative double-negation reading of `?`. -/
theorem INC.soundG (f : H) (v : α → H) {Δ Γ : Multiset (Formula α)} (h : INC Δ Γ) :
    Sem f v Δ Γ := by
  induction h with
  | weakL A _ ih =>
    refine sem_of_le ih ?_ rfl
    simp only [lhs, Multiset.map_cons, Multiset.inf_cons]
    exact inf_le_inf_right _ inf_le_right
  | wnW B _ ih =>
    refine sem_of_le ih ?_ (nonWn_cons_wn _ _)
    simp only [lhs, Multiset.map_cons, Multiset.inf_cons]
    exact inf_le_inf_left _ inf_le_right
  | contrL _ ih =>
    refine sem_of_le ih ?_ rfl
    simp only [lhs, Multiset.map_cons, Multiset.inf_cons, inf_idem, ← inf_assoc, le_refl]
  | wnC _ ih =>
    refine sem_of_le ih ?_ (by simp)
    simp only [lhs, Multiset.map_cons, Multiset.inf_cons, ← inf_assoc, inf_idem, le_refl]
  | @wnD Δ Γ B _ ih =>
    cases hBw : B.isWn with
    | true =>
      obtain ⟨B', rfl⟩ : ∃ B', B = wn B' := by cases B <;> simp_all [Formula.isWn]
      refine sem_of_le ih ?_ (by simp)
      simp only [lhs, Multiset.map_cons, Multiset.inf_cons, wnPart_wn_evalG, Formula.evalG,
        triple_neg, le_refl]
    | false =>
      obtain ⟨h1, -, h3⟩ := ih
      simp only [nonWn_cons, hBw, ↓reduceIte, Multiset.card_cons] at h1 h3
      replace h1 : nonWn Γ = 0 := Multiset.card_eq_zero.1 (by omega)
      have hB := h3 B (by simp)
      refine ⟨by simp [h1], fun _ => ?_, fun B hB' => by simp [h1] at hB'⟩
      have hw : wnPart f v B = ⊤ := by cases B <;> simp_all [Formula.isWn, wnPart]
      simp only [lhs, Multiset.map_cons, Multiset.inf_cons, wnPart_wn_evalG, hw, top_inf_eq]
        at hB ⊢
      calc _ ≤ ((Δ.map (Formula.evalG f v)).inf ⊓ (Γ.map (wnPart f v)).inf) ⊓
              (B.evalG f v ⇨ f) := le_of_eq (by ac_rfl)
        _ ≤ B.evalG f v ⊓ (B.evalG f v ⇨ f) := inf_le_inf_right _ hB
        _ ≤ f := inf_himp_le
  | @wnL Δ Γ A _ ih =>
    rw [sem_none_iff] at ih ⊢
    simp only [Multiset.map_cons, Multiset.inf_cons, Formula.evalG] at ih ⊢
    have : (Δ.map (Formula.evalG f v)).inf ⊓ (Γ.map (fun C => C.evalG f v ⇨ f)).inf ≤
        A.evalG f v ⇨ f := by
      rw [le_himp_iff]; exact le_trans (le_of_eq (by ac_rfl)) ih
    calc _ ≤ ((A.evalG f v ⇨ f) ⇨ f) ⊓ (A.evalG f v ⇨ f) := by
          rw [inf_assoc]; exact inf_le_inf_left _ this
      _ ≤ f := himp_inf_le
  | id A =>
    have := (sem_single_iff f v {A} 0 A).2 (by simp)
    simpa using this
  | @cut Δ Γ Δ' Γ' B _ _ ih₁ ih₂ =>
    rw [← Multiset.map_add, sem_none_iff]
    rw [← Multiset.map_cons, sem_none_iff] at ih₁
    rw [sem_none_iff] at ih₂
    simp only [Multiset.map_cons, Multiset.inf_cons, Multiset.map_add, Multiset.inf_add]
      at ih₁ ih₂ ⊢
    have h1 : (Δ.map (Formula.evalG f v)).inf ⊓ (Γ.map (fun C => C.evalG f v ⇨ f)).inf ≤
        (B.evalG f v ⇨ f) ⇨ f := by
      rw [le_himp_iff]; exact le_trans (le_of_eq (by ac_rfl)) ih₁
    have h2 : (Δ'.map (Formula.evalG f v)).inf ⊓ (Γ'.map (fun C => C.evalG f v ⇨ f)).inf ≤
        B.evalG f v ⇨ f := by
      rw [le_himp_iff]; exact le_trans (le_of_eq (by ac_rfl)) ih₂
    calc _ ≤ ((Δ.map (Formula.evalG f v)).inf ⊓ (Γ.map (fun C => C.evalG f v ⇨ f)).inf) ⊓
          ((Δ'.map (Formula.evalG f v)).inf ⊓ (Γ'.map (fun C => C.evalG f v ⇨ f)).inf) :=
          le_of_eq (by ac_rfl)
      _ ≤ ((B.evalG f v ⇨ f) ⇨ f) ⊓ (B.evalG f v ⇨ f) := inf_le_inf h1 h2
      _ ≤ f := himp_inf_le
  | topL _ ih =>
    refine sem_of_le ih ?_ rfl
    simp [lhs, Formula.evalG]
  | topR =>
    have := (sem_single_iff f v (0 : Multiset (Formula α)) 0 top).2 (by simp [Formula.evalG])
    simpa using this
  | ffL =>
    have := (sem_none_iff f v ({ff} : Multiset (Formula α)) 0).2 (by simp [Formula.evalG])
    simpa using this
  | ffR _ ih =>
    rw [sem_single_iff]; rw [sem_none_iff] at ih; simpa [Formula.evalG] using ih
  | withL₁ A₂ _ ih =>
    refine sem_of_le ih ?_ rfl
    simp only [lhs, Multiset.map_cons, Multiset.inf_cons, Formula.evalG]
    exact inf_le_inf_right _ (inf_le_inf_right _ inf_le_left)
  | withL₂ A₁ _ ih =>
    refine sem_of_le ih ?_ rfl
    simp only [lhs, Multiset.map_cons, Multiset.inf_cons, Formula.evalG]
    exact inf_le_inf_right _ (inf_le_inf_right _ inf_le_right)
  | withR _ _ ih₁ ih₂ =>
    rw [sem_single_iff] at ih₁ ih₂ ⊢
    exact le_inf ih₁ ih₂
  | @disjL Δ Γ A₁ A₂ _ _ ih₁ ih₂ =>
    obtain ⟨a1, a2, a3⟩ := ih₁
    obtain ⟨b1, b2, b3⟩ := ih₂
    have key : ∀ x : H, lhs f v (A₁ ::ₘ Δ) Γ ≤ x → lhs f v (A₂ ::ₘ Δ) Γ ≤ x →
        lhs f v (disj A₁ A₂ ::ₘ Δ) Γ ≤ x := by
      intro x h1 h2
      simp only [lhs, Multiset.map_cons, Multiset.inf_cons, Formula.evalG] at h1 h2 ⊢
      rw [inf_assoc, inf_sup_right]
      exact sup_le (le_trans (le_of_eq (by ac_rfl)) h1) (le_trans (le_of_eq (by ac_rfl)) h2)
    exact ⟨a1, fun h0 => key _ (a2 h0) (b2 h0), fun B hB => key _ (a3 B hB) (b3 B hB)⟩
  | disjR₁ B₂ _ ih =>
    rw [sem_single_iff] at ih ⊢
    exact ih.trans le_sup_left
  | disjR₂ B₁ _ ih =>
    rw [sem_single_iff] at ih ⊢
    exact ih.trans le_sup_right
  | @impL Δ Γ Θ Ξ A B _ _ ih₁ ih₂ =>
    rw [sem_single_iff] at ih₂
    refine sem_of_le ih₁ ?_ (by simp)
    simp only [lhs, Multiset.map_cons, Multiset.inf_cons, Multiset.map_add, Multiset.inf_add,
      map_wnPart_map_wn, Formula.evalG]
    calc _ ≤ ((A.evalG f v ⇨ B.evalG f v) ⊓ ((Θ.map (Formula.evalG f v)).inf ⊓
            (Ξ.map (fun C => C.evalG f v ⇨ f)).inf)) ⊓
          ((Δ.map (Formula.evalG f v)).inf ⊓ (Γ.map (wnPart f v)).inf) := le_of_eq (by ac_rfl)
      _ ≤ ((A.evalG f v ⇨ B.evalG f v) ⊓ A.evalG f v) ⊓
          ((Δ.map (Formula.evalG f v)).inf ⊓ (Γ.map (wnPart f v)).inf) :=
          inf_le_inf_right _ (inf_le_inf_left _ ih₂)
      _ ≤ B.evalG f v ⊓
          ((Δ.map (Formula.evalG f v)).inf ⊓ (Γ.map (wnPart f v)).inf) :=
          inf_le_inf_right _ himp_inf_le
      _ = _ := by ac_rfl
  | impR _ ih =>
    rw [sem_single_iff] at ih ⊢
    simp only [Multiset.map_cons, Multiset.inf_cons, Formula.evalG] at ih ⊢
    rw [le_himp_iff]; exact le_trans (le_of_eq (by ac_rfl)) ih

end ILe

namespace IL

open ILe

/-! ## INC ⟹ LJm (conservativity) -/

lemma evalG_embed {H : Type v} [GeneralizedHeytingAlgebra H] (f : H) (v : α → H)
    (A : IL.Formula α) : (embed A).evalG f v = A.evalG f v := by
  induction A with
  | var x => rfl
  | top => rfl
  | ff => rfl
  | «with» A B ihA ihB => simp only [embed, ILe.Formula.evalG, IL.Formula.evalG, ihA, ihB]
  | disj A B ihA ihB => simp only [embed, ILe.Formula.evalG, IL.Formula.evalG, ihA, ihB]
  | imp A B ihA ihB => simp only [embed, ILe.Formula.evalG, IL.Formula.evalG, ihA, ihB]

lemma isWn_embed (A : IL.Formula α) : (embed A).isWn = false := by
  cases A <;> rfl

lemma nonWn_map_embed (Γ : Multiset (IL.Formula α)) : nonWn (Γ.map embed) = Γ.map embed := by
  unfold nonWn; rw [Multiset.filter_eq_self]; intro a ha
  obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 ha; exact isWn_embed b

lemma wnPart_embed {H : Type v} [GeneralizedHeytingAlgebra H] (f : H) (v : α → H)
    (A : IL.Formula α) : wnPart f v (embed A) = ⊤ := by
  cases A <;> rfl

lemma lhs_map_embed {H : Type v} [GeneralizedHeytingAlgebra H] (f : H) (v : α → H)
    (Δ Γ : Multiset (IL.Formula α)) :
    lhs f v (Δ.map embed) (Γ.map embed) = (Δ.map (IL.Formula.evalG f v)).inf := by
  have h1 : ((Γ.map embed).map (wnPart f v)).inf = ⊤ := by
    induction Γ using Multiset.induction_on with
    | empty => rfl
    | cons a Γ ih => rw [Multiset.map_cons, Multiset.map_cons, Multiset.inf_cons, ih,
        wnPart_embed, inf_top_eq]
  rw [lhs, h1, inf_top_eq, Multiset.map_map]
  exact congrArg Multiset.inf (Multiset.map_congr rfl fun A _ => evalG_embed f v A)

lemma optMs_map_embed (C : Option (IL.Formula α)) :
    optMs (C.map embed) = (optMs C).map embed := by
  cases C <;> rfl

/-- **Conservativity of INC over minimal logic**: if a sequent of IL formulas is provable in
**INC**, it is provable in **LJᵐ**. -/
theorem INC.toLJm {Δ : Multiset (IL.Formula α)} {C : Option (IL.Formula α)}
    (h : INC (Δ.map embed) (optMs (C.map embed))) : LJm Δ C := by
  apply LJm.completeG
  intro H _ f v
  obtain ⟨-, h2, h3⟩ := INC.soundG f v h
  rw [optMs_map_embed, lhs_map_embed, nonWn_map_embed] at h2 h3
  unfold ValidG
  rcases C with _ | B
  · exact h2 rfl
  · simpa [evalG_embed] using h3 (embed B) (by simp)

/-- In **INC**, a provable sequent of IL formulas has at most one formula on the right. -/
theorem INC.card_le_one_of_embed {Δ Γ : Multiset (IL.Formula α)}
    (h : INC (Δ.map embed) (Γ.map embed)) : Γ.card ≤ 1 := by
  have := (INC.soundG (H := Prop) True (fun _ => True) h).1
  rwa [nonWn_map_embed, Multiset.card_map] at this

/-! ## LJm ⟹ INC, by an Okada-style closed-set model built from INC provability -/

lemma INC.weakL_add (Γ : Multiset (IL.Formula α)) {Δ : Multiset (IL.Formula α)}
    {Γr : Multiset (ILe.Formula α)} (h : INC (Δ.map embed) Γr) :
    INC ((Γ + Δ).map embed) Γr := by
  induction Γ using Multiset.induction_on with
  | empty => simpa using h
  | cons a Γ ih => rw [Multiset.cons_add, Multiset.map_cons]; exact INC.weakL _ ih

lemma INC.contrL_add (Γ : Multiset (IL.Formula α)) :
    ∀ {Δ : Multiset (IL.Formula α)} {Γr : Multiset (ILe.Formula α)},
      INC ((Γ + Γ + Δ).map embed) Γr → INC ((Γ + Δ).map embed) Γr := by
  induction Γ using Multiset.induction_on with
  | empty => intro Δ Γr h; simpa using h
  | cons a Γ ih =>
    intro Δ Γr h
    have e : a ::ₘ Γ + a ::ₘ Γ + Δ = Γ + Γ + (a ::ₘ a ::ₘ Δ) := by
      simp only [Multiset.cons_add, Multiset.add_cons]
    rw [e] at h
    have := ih h
    rw [show Γ + a ::ₘ a ::ₘ Δ = a ::ₘ a ::ₘ (Γ + Δ) by simp [Multiset.add_cons],
      Multiset.map_cons, Multiset.map_cons] at this
    rw [Multiset.cons_add, Multiset.map_cons]
    exact INC.contrL this

/-- The provability relation of **INC** on sequents of IL formulas, as an Okada system. -/
def incSys : Okada.Sys (IL.Formula α) (Option (IL.Formula α)) where
  R Δ C := INC (Δ.map embed) (optMs (C.map embed))
  weak Γ _ _ h := INC.weakL_add Γ h
  contr Γ _ _ h := INC.contrL_add Γ h

open Okada Okada.Closed

/-- The interpretation of `ff`: the basic set `⌊⊢⌋`. -/
def okF : Closed (incSys (α := α)) := ofBasic 0 none

/-- The interpretation of variables: `⌊⊢ x⌋`. -/
def okV (x : α) : Closed (incSys (α := α)) := ofBasic 0 (some (.var x))

lemma mem_basic_zero {Δ : Multiset (IL.Formula α)} {C : Option (IL.Formula α)} :
    Δ ∈ basic (incSys (α := α)) 0 C ↔ INC (Δ.map embed) (optMs (C.map embed)) := by
  simp [basic, incSys]

/-- **Okada's lemma**: `A ∈ ⟦A⟧ ⊆ ⌊⊢ A⌋`. -/
lemma okada (A : IL.Formula α) :
    {A} ∈ (A.evalG okF okV).1 ∧ (A.evalG okF okV).1 ⊆ basic incSys 0 (some A) := by
  induction A with
  | var x =>
    refine ⟨?_, subset_rfl⟩
    rw [IL.Formula.evalG, okV, ofBasic, mem_basic_zero]
    exact INC.id _
  | top =>
    refine ⟨trivial, fun Δ _ => ?_⟩
    rw [mem_basic_zero, ← add_zero Δ]
    exact INC.weakL_add Δ INC.topR
  | ff =>
    refine ⟨?_, fun Δ hΔ => ?_⟩
    · simp only [IL.Formula.evalG, okF, ofBasic]
      rw [mem_basic_zero]; exact INC.ffL
    · simp only [IL.Formula.evalG, okF, ofBasic] at hΔ
      rw [mem_basic_zero] at hΔ ⊢
      exact INC.ffR (Γ := 0) hΔ
  | «with» A B ihA ihB =>
    refine ⟨⟨?_, ?_⟩, fun Δ hΔ => ?_⟩
    · apply (A.evalG okF okV).2
      intro Θ d hX
      have := hX ihA.1
      simp only [basic, incSys, Set.mem_setOf_eq, Multiset.singleton_add,
        Multiset.map_cons] at this ⊢
      exact INC.withL₁ _ this
    · apply (B.evalG okF okV).2
      intro Θ d hX
      have := hX ihB.1
      simp only [basic, incSys, Set.mem_setOf_eq, Multiset.singleton_add,
        Multiset.map_cons] at this ⊢
      exact INC.withL₂ _ this
    · have h1 := ihA.2 hΔ.1
      have h2 := ihB.2 hΔ.2
      rw [mem_basic_zero] at h1 h2 ⊢
      exact INC.withR (Γ := 0) h1 h2
  | disj A B ihA ihB =>
    refine ⟨?_, ?_⟩
    · intro Θ d hX
      have h1 := hX (Or.inl ihA.1)
      have h2 := hX (Or.inr ihB.1)
      simp only [basic, incSys, Set.mem_setOf_eq, Multiset.singleton_add,
        Multiset.map_cons] at h1 h2 ⊢
      exact INC.disjL h1 h2
    · apply cl_subset_basic
      rintro Δ (hΔ | hΔ)
      · have := ihA.2 hΔ
        rw [mem_basic_zero] at this ⊢
        exact INC.disjR₁ (Γ := 0) _ this
      · have := ihB.2 hΔ
        rw [mem_basic_zero] at this ⊢
        exact INC.disjR₂ (Γ := 0) _ this
  | imp A B ihA ihB =>
    refine ⟨?_, fun Δ hΔ => ?_⟩
    · intro Γ hΓ
      apply (B.evalG okF okV).2
      intro Θ d hX
      have h1 := hX ihB.1
      have h2 := ihA.2 hΓ
      rw [mem_basic_zero] at h2
      simp only [basic, incSys, Set.mem_setOf_eq, Multiset.singleton_add,
        Multiset.map_cons] at h1 ⊢
      have := INC.impL (Ξ := 0) h1 h2
      simp only [Multiset.map_zero, add_zero] at this
      rw [Multiset.cons_add, Multiset.map_cons, Multiset.map_add]
      simp only [embed]
      rwa [add_comm (Multiset.map embed Γ)]
    · have := ihB.2 (hΔ {A} ihA.1)
      rw [mem_basic_zero] at this ⊢
      rw [add_comm, Multiset.singleton_add, Multiset.map_cons] at this
      exact INC.impR (Γ := 0) this

/-- Every context belongs to the meet of the interpretations of its formulas. -/
lemma mem_inf_evalG (Δ : Multiset (IL.Formula α)) :
    Δ ∈ ((Δ.map (IL.Formula.evalG okF okV)).inf).1 := by
  rw [mem_inf_map]
  intro A hA
  obtain ⟨Δ', rfl⟩ := Multiset.exists_cons_of_mem hA
  rw [← Multiset.singleton_add, add_comm]
  exact add_mem _ Δ' (okada A).1

/-- **INC extends minimal logic**: every sequent provable in **LJᵐ** is provable in **INC**
(no cut-elimination needed: the proof goes through an Okada-style closed-set model). -/
theorem LJm.toINC {Δ : Multiset (IL.Formula α)} {C : Option (IL.Formula α)} (h : LJm Δ C) :
    INC (Δ.map embed) (optMs (C.map embed)) := by
  have hv := h.soundG okF okV
  unfold ValidG at hv
  have hmem := hv (mem_inf_evalG Δ)
  rw [← mem_basic_zero]
  rcases C with _ | B
  · exact hmem
  · exact (okada B).2 hmem

/-- **INC is a conservative extension of minimal logic LJᵐ** (the right-hand top arrow of
the diagram, with **IL** presented by the explicit rule figure of LJ in the source). -/
theorem incConservativeMin : INCConservativeMin (α := α) :=
  ⟨fun _ _ => ⟨LJm.toINC, INC.toLJm⟩, fun _ _ h => INC.card_le_one_of_embed h⟩

/-- **Girard's translation** of minimal **LJᵐ** into **ILC** / **ILC_ι** (top arrow of the
diagram with **IL** presented by **LJᵐ**). -/
theorem LJm.toILC (ι : Bool) {Δ : Multiset (IL.Formula α)} {C : Option (IL.Formula α)}
    (h : LJm Δ C) : ILLe.ILC ι ((Δ.map girardE).map .bang) {girardS C} :=
  LJ.toILC ι h.toLJ

/-- **Girard's translation of LJᵐ into LLJ**, conditional on the conservativity of ILC(_ι) over
LLJ (as for `IL.LJ.toLLJ_of_conservative`). -/
theorem LJm.toLLJ_of_conservative (ι : Bool) (hcons : ILL.ILCConservative (α := α) ι)
    {Δ : Multiset (IL.Formula α)} {C : Option (IL.Formula α)} (h : LJm Δ C)
    {Δ' : Multiset (ILL.Formula α)} {C' : Option (ILL.Formula α)}
    (hΔ : Multiset.Rel (fun A B => girard A = some B) Δ Δ')
    (hC : Option.Rel (fun A B => girard A = some B) C C') :
    ILL.LLJ (Δ'.map .bang) C' :=
  LJ.toLLJ_of_conservative ι hcons h.toLJ hΔ hC

end IL

end
