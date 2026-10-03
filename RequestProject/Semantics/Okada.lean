module

public import Mathlib

/-!
# Okada-style closed-set algebras

Given a provability relation `R Δ d` between multisets `Δ` of formulas ("contexts") and
succedents `d`, satisfying left weakening and left contraction, the sets of contexts that are
intersections of *basic sets* `⌊Θ ⊢ d⌋ = {Δ | R (Δ + Θ) d}` form a generalized Heyting
algebra (`Okada.Closed`), with `∩` as meet and `X ⇨ Y = {Δ | ∀ Γ ∈ X, Δ + Γ ∈ Y}`.

This is the algebraic core of Okada's semantic proof of cut-elimination; it is used to show
that a sequent calculus *without a general cut rule* still derives everything that a calculus
sound for generalized Heyting algebras derives (`IL.LJm.toINC`).
-/

@[expose] public section

namespace Okada

universe u v

/-- A provability relation with left weakening and left contraction. -/
structure Sys (F : Type u) (D : Type v) where
  /-- provability of `Δ ⊢ d` -/
  R : Multiset F → D → Prop
  /-- left weakening -/
  weak : ∀ (Γ Δ : Multiset F) (d : D), R Δ d → R (Γ + Δ) d
  /-- left contraction -/
  contr : ∀ (Γ Δ : Multiset F) (d : D), R (Γ + Γ + Δ) d → R (Γ + Δ) d

variable {F : Type u} {D : Type v} (S : Sys F D)

/-- The basic set `⌊Θ ⊢ d⌋ = {Δ | Δ, Θ ⊢ d}`. -/
def basic (Θ : Multiset F) (d : D) : Set (Multiset F) := {Δ | S.R (Δ + Θ) d}

/-- The closure of a set of contexts: the intersection of all basic sets containing it. -/
def cl (X : Set (Multiset F)) : Set (Multiset F) :=
  {Δ | ∀ Θ d, X ⊆ basic S Θ d → Δ ∈ basic S Θ d}

variable {S}

lemma subset_cl (X : Set (Multiset F)) : X ⊆ cl S X := fun _ h _ _ hX => hX h

lemma cl_subset_basic {X : Set (Multiset F)} {Θ : Multiset F} {d : D}
    (h : X ⊆ basic S Θ d) : cl S X ⊆ basic S Θ d := fun _ hΔ => hΔ Θ d h

lemma cl_mono {X Y : Set (Multiset F)} (h : X ⊆ Y) : cl S X ⊆ cl S Y :=
  fun _ hΔ Θ d hY => hΔ Θ d (h.trans hY)

variable (S) in
/-- Closed sets of contexts. -/
def Closed : Type u := {X : Set (Multiset F) // cl S X ⊆ X}

namespace Closed

lemma basic_closed (Θ : Multiset F) (d : D) : cl S (basic S Θ d) ⊆ basic S Θ d :=
  cl_subset_basic subset_rfl

lemma cl_closed (X : Set (Multiset F)) : cl S (cl S X) ⊆ cl S X :=
  fun _ hΔ Θ d hX => hΔ Θ d (cl_subset_basic hX)

/-- A basic set as a closed set. -/
def ofBasic (Θ : Multiset F) (d : D) : Closed S := ⟨basic S Θ d, basic_closed Θ d⟩

/-- Closed sets are closed under adding hypotheses (by weakening). -/
lemma add_mem (X : Closed S) (Γ : Multiset F) {Δ : Multiset F} (h : Δ ∈ X.1) :
    Γ + Δ ∈ X.1 := by
  apply X.2
  intro Θ d hX
  have := hX h
  simp only [basic, Set.mem_setOf_eq] at this ⊢
  rw [add_assoc]; exact S.weak Γ _ d this

/-- Closed sets are closed under contraction. -/
lemma mem_of_add_self (X : Closed S) {Γ : Multiset F} (h : Γ + Γ ∈ X.1) : Γ ∈ X.1 := by
  apply X.2
  intro Θ d hX
  have := hX h
  exact S.contr Γ Θ d this

instance : PartialOrder (Closed S) := PartialOrder.lift Subtype.val Subtype.val_injective

lemma le_def {X Y : Closed S} : X ≤ Y ↔ X.1 ⊆ Y.1 := Iff.rfl

instance : Lattice (Closed S) where
  sup X Y := ⟨cl S (X.1 ∪ Y.1), cl_closed _⟩
  le_sup_left _ _ := (Set.subset_union_left).trans (subset_cl _)
  le_sup_right _ _ := (Set.subset_union_right).trans (subset_cl _)
  sup_le _ _ Z hX hY := (cl_mono (Set.union_subset hX hY)).trans Z.2
  inf X Y := ⟨X.1 ∩ Y.1, fun _ hΔ =>
    ⟨X.2 (cl_mono Set.inter_subset_left hΔ), Y.2 (cl_mono Set.inter_subset_right hΔ)⟩⟩
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ hY hZ := Set.subset_inter hY hZ

lemma inf_val (X Y : Closed S) : (X ⊓ Y).1 = X.1 ∩ Y.1 := rfl

lemma sup_val (X Y : Closed S) : (X ⊔ Y).1 = cl S (X.1 ∪ Y.1) := rfl

instance : OrderTop (Closed S) where
  top := ⟨Set.univ, Set.subset_univ _⟩
  le_top _ := Set.subset_univ _

lemma top_val : (⊤ : Closed S).1 = Set.univ := rfl

/-- The implication `X ⇨ Y = {Δ | ∀ Γ ∈ X, Δ + Γ ∈ Y}`. -/
instance : HImp (Closed S) where
  himp X Y := ⟨{Δ | ∀ Γ ∈ X.1, Δ + Γ ∈ Y.1}, by
    intro Δ hΔ Γ hΓ
    apply Y.2
    intro Θ d hY
    have : {Δ | ∀ Γ ∈ X.1, Δ + Γ ∈ Y.1} ⊆ basic S (Γ + Θ) d := by
      intro Δ' hΔ'
      have := hY (hΔ' Γ hΓ)
      simp only [basic, Set.mem_setOf_eq] at this ⊢
      rwa [← add_assoc]
    have := hΔ _ _ this
    simp only [basic, Set.mem_setOf_eq] at this ⊢
    rwa [add_assoc]⟩

lemma himp_val (X Y : Closed S) : (X ⇨ Y).1 = {Δ | ∀ Γ ∈ X.1, Δ + Γ ∈ Y.1} := rfl

instance : GeneralizedHeytingAlgebra (Closed S) where
  le_himp_iff X Y Z := by
    constructor
    · intro h Δ hΔ
      have := h hΔ.1 Δ hΔ.2
      exact mem_of_add_self Z this
    · intro h Δ hΔ Γ hΓ
      apply h
      refine ⟨?_, ?_⟩
      · rw [add_comm]; exact add_mem X Γ hΔ
      · exact add_mem Y Δ hΓ

/-- Membership in a finite meet of closed sets. -/
lemma mem_inf_map {ι : Type*} (g : ι → Closed S) (s : Multiset ι) (Δ : Multiset F) :
    Δ ∈ ((s.map g).inf).1 ↔ ∀ i ∈ s, Δ ∈ (g i).1 := by
  induction s using Multiset.induction_on with
  | empty => simp [top_val]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.inf_cons, inf_val, Set.mem_inter_iff, ih]
    simp

end Closed

end Okada

end
