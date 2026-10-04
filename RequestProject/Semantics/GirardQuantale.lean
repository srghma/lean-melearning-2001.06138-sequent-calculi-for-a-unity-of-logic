module

public import RequestProject.Logics.ILCLemmas
public import RequestProject.Semantics.Polycategory

/-!
# Girard quantales: the algebraic model of linear logic

A **commutative quantale** is a complete lattice with a commutative monoid multiplication
which distributes over arbitrary joins: `x * ⨆ S = ⨆_{y ∈ S} x * y`. It has a residuation
(linear implication) `a ⊸ b = ⨆ {z | z * a ≤ b}`, characterised by `x ≤ a ⊸ b ↔ x * a ≤ b`.

A **Girard quantale** is a commutative quantale with a *dualizing element* `d` such that the
linear negation `a⊥ := a ⊸ d` satisfies the **law of double negation** `a⊥⊥ = a`.

To interpret the exponentials we add an **exponential** (storage) operator `!` satisfying
the usual (Seely-style) conditions: `!` is monotone, `!a ≤ a`, `!a ≤ !!a`,
`!(a ⊓ b) = !a * !b` and `!⊤ = 1`; then `?a := (!(a⊥))⊥`.

The connectives of **ILLᵉ** (paper notation: `⊤` is the unit of `⊗`, `1` the unit of `&`)
are interpreted as
`⟦⊤⟧ = 1`, `⟦⊥⟧ = d`, `⟦1⟧ = ⊤`, `⟦0⟧ = ⊥`, `⟦A ⊗ B⟧ = a * b`, `⟦A ⅋ B⟧ = (a⊥ * b⊥)⊥`,
`⟦A & B⟧ = a ⊓ b`, `⟦A ⊕ B⟧ = a ⊔ b`, `⟦¬A⟧ = a⊥`, `⟦!A⟧ = !a`, `⟦?A⟧ = (!(a⊥))⊥`,
and a sequent `Δ ⊢ Γ` is valid when `∏ ⟦Δ⟧ ≤ ⅋ ⟦Γ⟧`, i.e. `∏ ⟦Δ⟧ * ∏ ⟦Γ⟧⊥ ≤ d`.

Main results:
* `GirardQuantale.lneg_lneg` etc.: the De Morgan laws of a Girard quantale.
* `ILLe.ILC.sound_girardQuantale`: **soundness of ILC** (classical linear logic with
  exponentials, the calculus for ILLᵉ) in every Girard quantale with an exponential.
* `GirardQuantale.toThinPolycategory`, `ILLe.ILC.evalPolyfunctor`: a Girard quantale is a
  (thin) polycategory and evaluation is a polyfunctor.
* `GirardQuantale.instOfCompleteBooleanAlgebra`: every complete Boolean algebra is a Girard
  quantale with exponential (`* = ⊓`, `d = ⊥`, `! = id`), so the notion is not vacuous.

The weakly distributive rules of **ILC_ι** are not sound in arbitrary Girard quantales, so
soundness is stated for **ILC** (`ι = false`).
-/

@[expose] public section

universe u v

/-- A **commutative (unital) quantale**: a complete lattice with a commutative monoid
structure whose multiplication distributes over arbitrary joins. -/
class CommQuantale (Q : Type u) extends CommMonoid Q, CompleteLattice Q where
  mul_sSup_distrib : ∀ (x : Q) (s : Set Q), x * sSup s = ⨆ y ∈ s, x * y

namespace CommQuantale

variable {Q : Type u} [CommQuantale Q]

/-- Linear implication (residuation) `a ⊸ b = ⨆ {z | z * a ≤ b}`. -/
def limp (a b : Q) : Q := sSup {z | z * a ≤ b}

lemma sSup_mul (s : Set Q) (x : Q) : sSup s * x = ⨆ y ∈ s, y * x := by
  rw [mul_comm, mul_sSup_distrib]; simp only [mul_comm]

lemma qmul_sup (a b c : Q) : a * (b ⊔ c) = a * b ⊔ a * c := by
  rw [← sSup_pair, mul_sSup_distrib, iSup_pair]

lemma qsup_mul (a b c : Q) : (a ⊔ b) * c = a * c ⊔ b * c := by
  rw [mul_comm, qmul_sup, mul_comm, mul_comm c]

lemma qmul_le_mul_left {a b : Q} (h : a ≤ b) (c : Q) : c * a ≤ c * b := by
  rw [← sup_eq_right.2 h, qmul_sup]; exact le_sup_left

lemma le_limp_iff {x a b : Q} : x ≤ limp a b ↔ x * a ≤ b := by
  constructor
  · intro h
    calc x * a ≤ limp a b * a := by
          rw [mul_comm x, mul_comm (limp a b)]; exact qmul_le_mul_left h a
      _ = ⨆ y ∈ {z | z * a ≤ b}, y * a := sSup_mul _ _
      _ ≤ b := iSup₂_le fun _ hy => hy
  · intro h; exact le_sSup h

instance (priority := 100) toIsOrderedMonoid : IsOrderedMonoid Q where
  mul_le_mul_left a b h c := by simpa [mul_comm] using qmul_le_mul_left h c
  mul_le_mul_right a b h c := qmul_le_mul_left h c

instance (priority := 100) toIsQuantale : IsQuantale Q where
  mul_sSup_distrib := mul_sSup_distrib
  sSup_mul_distrib s x := sSup_mul s x

@[simp] lemma mul_bot (a : Q) : a * ⊥ = ⊥ := by
  rw [← sSup_empty, mul_sSup_distrib]; simp

@[simp] lemma bot_mul (a : Q) : ⊥ * a = ⊥ := by rw [mul_comm, mul_bot]

end CommQuantale

/-- A **Girard quantale**: a commutative quantale with a dualizing element `d` for which
linear negation `a⊥ = a ⊸ d` satisfies the law of double negation `a⊥⊥ = a`. -/
class GirardQuantale (Q : Type u) extends CommQuantale Q where
  /-- the dualizing element (interpretation of `⊥`, the unit of `⅋`) -/
  dualizing : Q
  /-- the law of double negation -/
  lneg_lneg' : ∀ a : Q, CommQuantale.limp (CommQuantale.limp a dualizing) dualizing = a

namespace GirardQuantale

open CommQuantale

variable {Q : Type u} [GirardQuantale Q]

/-- Linear negation `a⊥ = a ⊸ d`. -/
def lneg (a : Q) : Q := limp a dualizing

@[simp] lemma lneg_lneg (a : Q) : lneg (lneg a) = a := lneg_lneg' a

lemma le_lneg_iff {x a : Q} : x ≤ lneg a ↔ x * a ≤ dualizing := le_limp_iff

lemma le_iff_mul_lneg {x a : Q} : x ≤ a ↔ x * lneg a ≤ dualizing := by
  conv_lhs => rw [← lneg_lneg a]
  exact le_lneg_iff

lemma mul_lneg_le (a : Q) : a * lneg a ≤ dualizing := le_iff_mul_lneg.1 le_rfl

lemma lneg_mul_le (a : Q) : lneg a * a ≤ dualizing := le_lneg_iff.1 le_rfl

lemma lneg_anti {a b : Q} (h : a ≤ b) : lneg b ≤ lneg a :=
  le_lneg_iff.2 ((qmul_le_mul_left h _).trans (lneg_mul_le b))

lemma lneg_inj {a b : Q} (h : lneg a = lneg b) : a = b := by
  rw [← lneg_lneg a, h, lneg_lneg]

lemma lneg_le_iff {a b : Q} : lneg a ≤ b ↔ lneg b ≤ a := by
  constructor
  · intro h; simpa using lneg_anti h
  · intro h; simpa using lneg_anti h

@[simp] lemma lneg_one : lneg (1 : Q) = dualizing :=
  le_antisymm (by simpa using lneg_mul_le (1 : Q)) (le_lneg_iff.2 (by simp))

@[simp] lemma lneg_dualizing : lneg (dualizing : Q) = 1 := by
  rw [← lneg_one, lneg_lneg]

@[simp] lemma lneg_bot : lneg (⊥ : Q) = ⊤ := top_unique (le_lneg_iff.2 (by simp))

@[simp] lemma lneg_top : lneg (⊤ : Q) = ⊥ := by rw [← lneg_bot, lneg_lneg]

lemma lneg_sup (a b : Q) : lneg (a ⊔ b) = lneg a ⊓ lneg b := by
  apply le_antisymm
  · exact le_inf (lneg_anti le_sup_left) (lneg_anti le_sup_right)
  · rw [le_lneg_iff, qmul_sup]
    exact sup_le (le_lneg_iff.1 inf_le_left) (le_lneg_iff.1 inf_le_right)

lemma lneg_inf (a b : Q) : lneg (a ⊓ b) = lneg a ⊔ lneg b := by
  apply lneg_inj
  rw [lneg_lneg, lneg_sup, lneg_lneg, lneg_lneg]

/-- An **exponential** on a Girard quantale: a "storage" operator `!` with the Seely-style
conditions. -/
class Exponential (Q : Type u) [GirardQuantale Q] where
  /-- of-course `!` -/
  bang : Q → Q
  bang_mono : Monotone bang
  bang_le : ∀ a, bang a ≤ a
  bang_le_bang_bang : ∀ a, bang a ≤ bang (bang a)
  bang_inf : ∀ a b, bang (a ⊓ b) = bang a * bang b
  bang_top : bang ⊤ = 1

section Exponential

variable [Exponential Q]

open Exponential

lemma bang_le_one (a : Q) : bang a ≤ 1 := bang_top (Q := Q) ▸ bang_mono le_top

lemma bang_mul_self (a : Q) : bang a * bang a = bang a := by rw [← bang_inf, inf_idem]

/-- `x` is a value of `!` -/
def IsBang (x : Q) : Prop := ∃ k, x = bang k

lemma isBang_one : IsBang (1 : Q) := ⟨⊤, bang_top.symm⟩

lemma IsBang.mul {x y : Q} : IsBang x → IsBang y → IsBang (x * y) := by
  rintro ⟨k, rfl⟩ ⟨l, rfl⟩; exact ⟨k ⊓ l, (bang_inf k l).symm⟩

lemma isBang_prod (s : Multiset Q) (h : ∀ x ∈ s, IsBang x) : IsBang s.prod :=
  Multiset.prod_induction _ s (fun _ _ => IsBang.mul) isBang_one h

/-- **Promotion**: a `!`-value below `b` is below `!b`. -/
lemma IsBang.le_bang {x b : Q} (hx : IsBang x) (h : x ≤ b) : x ≤ bang b := by
  obtain ⟨k, rfl⟩ := hx
  exact (bang_le_bang_bang k).trans (bang_mono h)

end Exponential

/-- A Girard quantale is a (thin) polycategory: `Γ → Δ` iff `∏ Γ ≤ ⅋ Δ`, i.e.
`∏ Γ * ∏ Δ⊥ ≤ d`. -/
def toThinPolycategory (Q : Type u) [GirardQuantale Q] : ThinMultisetPolycategory Q where
  Hom Γ Δ := Γ.prod * (Δ.map lneg).prod ≤ dualizing
  id A := by simpa using mul_lneg_le A
  comp {Γ Δ Γ' Δ' A} f g := by
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.map_add,
      Multiset.prod_add] at *
    have h1 : Γ.prod * (Δ.map lneg).prod ≤ A := le_iff_mul_lneg.2 (by
      calc _ = Γ.prod * (lneg A * (Δ.map lneg).prod) := by ac_rfl
        _ ≤ _ := f)
    calc Γ.prod * Γ'.prod * ((Δ.map lneg).prod * (Δ'.map lneg).prod)
        = (Γ.prod * (Δ.map lneg).prod) * (Γ'.prod * (Δ'.map lneg).prod) := by ac_rfl
      _ ≤ A * (Γ'.prod * (Δ'.map lneg).prod) := mul_le_mul' h1 le_rfl
      _ = A * Γ'.prod * (Δ'.map lneg).prod := by ac_rfl
      _ ≤ dualizing := g

/-! ### Sanity check: complete Boolean algebras are Girard quantales -/

/-- A complete Boolean algebra viewed as a quantale with multiplication `⊓`. -/
def OfCompleteBooleanAlgebra (B : Type u) : Type u := B

instance (B : Type u) [CompleteBooleanAlgebra B] :
    CompleteBooleanAlgebra (OfCompleteBooleanAlgebra B) := ‹CompleteBooleanAlgebra B›

/-- Every complete Boolean algebra is a Girard quantale with `* = ⊓`, `1 = ⊤` and dualizing
element `⊥`; linear negation is Boolean complement. -/
instance instOfCompleteBooleanAlgebra (B : Type u) [CompleteBooleanAlgebra B] :
    GirardQuantale (OfCompleteBooleanAlgebra B) where
  mul := (· ⊓ ·)
  one := ⊤
  mul_assoc := inf_assoc
  one_mul := top_inf_eq
  mul_one := inf_top_eq
  mul_comm := inf_comm
  mul_sSup_distrib _ _ := inf_sSup_eq
  dualizing := ⊥
  lneg_lneg' a := by
    have key : ∀ x : OfCompleteBooleanAlgebra B,
        sSup {z : OfCompleteBooleanAlgebra B | z ⊓ x ≤ ⊥} = xᶜ := fun x =>
      le_antisymm (sSup_le fun z hz => by simpa [le_compl_iff_disjoint_right,
        disjoint_iff_inf_le] using hz)
        (le_sSup (by simp))
    change sSup {z | z ⊓ sSup {z | z ⊓ a ≤ ⊥} ≤ ⊥} = a
    rw [key, key, compl_compl]

/-- With `! = id`, a complete Boolean algebra is a Girard quantale with exponential. -/
instance (B : Type u) [CompleteBooleanAlgebra B] :
    Exponential (OfCompleteBooleanAlgebra B) where
  bang := id
  bang_mono := monotone_id
  bang_le _ := le_rfl
  bang_le_bang_bang _ := le_rfl
  bang_inf _ _ := rfl
  bang_top := rfl

end GirardQuantale

/-! ## Soundness of ILC in Girard quantales -/

namespace ILLe

open Formula GirardQuantale GirardQuantale.Exponential CommQuantale

variable {α : Type u} {Q : Type v} [GirardQuantale Q] [Exponential Q]

/-- Interpretation of an ILLᵉ formula in a Girard quantale with exponential. -/
def Formula.qeval (v : α → Q) : Formula α → Q
  | var x => v x
  | top => 1
  | bot => dualizing
  | one => ⊤
  | zero => ⊥
  | tensor A B => A.qeval v * B.qeval v
  | par A B => lneg (lneg (A.qeval v) * lneg (B.qeval v))
  | «with» A B => A.qeval v ⊓ B.qeval v
  | plus A B => A.qeval v ⊔ B.qeval v
  | neg A => lneg (A.qeval v)
  | bang A => Exponential.bang (A.qeval v)
  | wn A => lneg (Exponential.bang (lneg (A.qeval v)))

/-- Validity of `Δ ⊢ Γ` in a Girard quantale: `∏ ⟦Δ⟧ * ∏ ⟦Γ⟧⊥ ≤ d` (equivalently
`∏ ⟦Δ⟧ ≤ ⅋ ⟦Γ⟧`). -/
def QValid (v : α → Q) (Δ Γ : Multiset (Formula α)) : Prop :=
  (Δ.map (Formula.qeval v)).prod * (Γ.map (fun B => lneg (B.qeval v))).prod ≤ dualizing

lemma isBang_prod_bang (v : α → Q) (Δ : Multiset (Formula α)) :
    IsBang ((Δ.map bang).map (Formula.qeval v)).prod := by
  apply isBang_prod
  intro x hx
  simp only [Multiset.map_map, Multiset.mem_map, Function.comp_apply] at hx
  obtain ⟨A, _, rfl⟩ := hx
  exact ⟨_, rfl⟩

lemma isBang_prod_wn (v : α → Q) (Γ : Multiset (Formula α)) :
    IsBang ((Γ.map wn).map (fun B => lneg (B.qeval v))).prod := by
  apply isBang_prod
  intro x hx
  simp only [Multiset.map_map, Multiset.mem_map, Function.comp_apply] at hx
  obtain ⟨A, _, rfl⟩ := hx
  exact ⟨lneg (A.qeval v), by simp [qeval]⟩

/-- **Soundness of ILC (classical linear logic with exponentials) for Girard quantales.**
If `Δ ⊢ Γ` is provable in **ILC** then `∏ ⟦Δ⟧ ≤ ⅋ ⟦Γ⟧` in every Girard quantale with
exponential, under every valuation. -/
theorem ILC.sound_girardQuantale (v : α → Q) {Δ Γ : Multiset (Formula α)}
    (h : ILC false Δ Γ) : QValid v Δ Γ := by
  unfold QValid
  induction h with
  | bangW A _ ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval] at *
    rw [mul_assoc]
    exact (mul_le_mul' (bang_le_one _) le_rfl).trans (by simpa using ih)
  | wnW B _ ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval, lneg_lneg] at *
    rw [mul_left_comm]
    exact (mul_le_mul' (bang_le_one _) le_rfl).trans (by simpa using ih)
  | bangC _ ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval] at *
    rw [← bang_mul_self]; simpa [mul_assoc] using ih
  | wnC _ ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval, lneg_lneg] at *
    rw [← bang_mul_self]; simpa [mul_assoc] using ih
  | bangD _ ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval] at *
    exact (mul_le_mul' (mul_le_mul' (bang_le _) le_rfl) le_rfl).trans ih
  | wnD _ ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval, lneg_lneg] at *
    exact (mul_le_mul' le_rfl (mul_le_mul' (bang_le _) le_rfl)).trans ih
  | wnL _ ih =>
    rename_i Δ Γ A _
    have hK := (isBang_prod_bang v Δ).mul (isBang_prod_wn v Γ)
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval] at *
    set P := ((Δ.map bang).map (Formula.qeval v)).prod
    set N := ((Γ.map wn).map (fun B => lneg (B.qeval v))).prod
    have h1 : P * N ≤ lneg (A.qeval v) := le_lneg_iff.2 (by
      calc P * N * A.qeval v = A.qeval v * P * N := by ac_rfl
        _ ≤ _ := ih)
    have h2 := hK.le_bang h1
    calc lneg (bang (lneg (A.qeval v))) * P * N
        = lneg (bang (lneg (A.qeval v))) * (P * N) := by ac_rfl
      _ ≤ lneg (bang (lneg (A.qeval v))) * bang (lneg (A.qeval v)) := mul_le_mul' le_rfl h2
      _ ≤ dualizing := lneg_mul_le _
  | bangR _ ih =>
    rename_i Δ Γ B _
    have hK := (isBang_prod_bang v Δ).mul (isBang_prod_wn v Γ)
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval] at *
    set P := ((Δ.map bang).map (Formula.qeval v)).prod
    set N := ((Γ.map wn).map (fun B => lneg (B.qeval v))).prod
    have h1 : P * N ≤ B.qeval v := le_iff_mul_lneg.2 (by
      calc P * N * lneg (B.qeval v) = P * (lneg (B.qeval v) * N) := by ac_rfl
        _ ≤ _ := ih)
    have h2 := hK.le_bang h1
    calc P * (lneg (bang (B.qeval v)) * N) = P * N * lneg (bang (B.qeval v)) := by ac_rfl
      _ ≤ dualizing := le_iff_mul_lneg.1 h2
  | id A => simpa using mul_lneg_le _
  | cut _ _ ih₁ ih₂ =>
    rename_i Δ Γ Δ' Γ' B _ _
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.map_add,
      Multiset.prod_add] at *
    set P := (Δ.map (Formula.qeval v)).prod
    set N := (Γ.map (fun B => lneg (B.qeval v))).prod
    set P' := (Δ'.map (Formula.qeval v)).prod
    set N' := (Γ'.map (fun B => lneg (B.qeval v))).prod
    have h1 : P * N ≤ B.qeval v := le_iff_mul_lneg.2 (by
      calc P * N * lneg (B.qeval v) = P * (lneg (B.qeval v) * N) := by ac_rfl
        _ ≤ _ := ih₁)
    calc P * P' * (N * N') = (P * N) * (P' * N') := by ac_rfl
      _ ≤ B.qeval v * (P' * N') := mul_le_mul' h1 le_rfl
      _ = B.qeval v * P' * N' := by ac_rfl
      _ ≤ dualizing := ih₂
  | oneR Δ Γ => simp [qeval]
  | zeroL Δ Γ => simp [qeval]
  | topL _ ih => simpa [qeval] using ih
  | topR => simp [qeval]
  | botL => simp [qeval]
  | botR _ ih => simpa [qeval] using ih
  | tensorL _ ih => simpa [qeval, mul_assoc] using ih
  | tensorR _ _ ih₁ ih₂ =>
    rename_i Δ₁ Δ₂ Γ₁ Γ₂ B₁ B₂ _ _
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.map_add,
      Multiset.prod_add, qeval] at *
    set P₁ := (Δ₁.map (Formula.qeval v)).prod
    set N₁ := (Γ₁.map (fun B => lneg (B.qeval v))).prod
    set P₂ := (Δ₂.map (Formula.qeval v)).prod
    set N₂ := (Γ₂.map (fun B => lneg (B.qeval v))).prod
    have h1 : P₁ * N₁ ≤ B₁.qeval v := le_iff_mul_lneg.2 (by
      calc P₁ * N₁ * lneg (B₁.qeval v) = P₁ * (lneg (B₁.qeval v) * N₁) := by ac_rfl
        _ ≤ _ := ih₁)
    have h2 : P₂ * N₂ ≤ B₂.qeval v := le_iff_mul_lneg.2 (by
      calc P₂ * N₂ * lneg (B₂.qeval v) = P₂ * (lneg (B₂.qeval v) * N₂) := by ac_rfl
        _ ≤ _ := ih₂)
    have h3 := le_iff_mul_lneg.1 (mul_le_mul' h1 h2)
    calc P₁ * P₂ * (lneg (B₁.qeval v * B₂.qeval v) * (N₁ * N₂))
        = P₁ * N₁ * (P₂ * N₂) * lneg (B₁.qeval v * B₂.qeval v) := by ac_rfl
      _ ≤ dualizing := h3
  | withL₁ A₂ _ ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval] at *
    exact (mul_le_mul' (mul_le_mul' inf_le_left le_rfl) le_rfl).trans ih
  | withL₂ A₁ _ ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval] at *
    exact (mul_le_mul' (mul_le_mul' inf_le_right le_rfl) le_rfl).trans ih
  | withR _ _ ih₁ ih₂ =>
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval, lneg_inf] at *
    rw [qsup_mul, qmul_sup]
    exact sup_le ih₁ ih₂
  | parL _ _ ih₁ ih₂ =>
    rename_i Δ₁ Δ₂ Γ₁ Γ₂ A₁ A₂ _ _
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.map_add,
      Multiset.prod_add, qeval] at *
    set P₁ := (Δ₁.map (Formula.qeval v)).prod
    set N₁ := (Γ₁.map (fun B => lneg (B.qeval v))).prod
    set P₂ := (Δ₂.map (Formula.qeval v)).prod
    set N₂ := (Γ₂.map (fun B => lneg (B.qeval v))).prod
    have h1 : P₁ * N₁ ≤ lneg (A₁.qeval v) := le_lneg_iff.2 (by
      calc P₁ * N₁ * A₁.qeval v = A₁.qeval v * P₁ * N₁ := by ac_rfl
        _ ≤ _ := ih₁)
    have h2 : P₂ * N₂ ≤ lneg (A₂.qeval v) := le_lneg_iff.2 (by
      calc P₂ * N₂ * A₂.qeval v = A₂.qeval v * P₂ * N₂ := by ac_rfl
        _ ≤ _ := ih₂)
    set Y := lneg (A₁.qeval v) * lneg (A₂.qeval v)
    calc lneg Y * (P₁ * P₂) * (N₁ * N₂) = lneg Y * ((P₁ * N₁) * (P₂ * N₂)) := by ac_rfl
      _ ≤ lneg Y * Y := mul_le_mul' le_rfl (mul_le_mul' h1 h2)
      _ ≤ dualizing := lneg_mul_le _
  | parR _ ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval, lneg_lneg] at *
    simpa [mul_assoc] using ih
  | plusL _ _ ih₁ ih₂ =>
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval] at *
    rw [qsup_mul, qsup_mul]
    exact sup_le ih₁ ih₂
  | plusR₁ B₂ _ ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval] at *
    exact (mul_le_mul' le_rfl (mul_le_mul' (lneg_anti le_sup_left) le_rfl)).trans ih
  | plusR₂ B₁ _ ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval] at *
    exact (mul_le_mul' le_rfl (mul_le_mul' (lneg_anti le_sup_right) le_rfl)).trans ih
  | negL _ ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval] at *
    calc _ = _ := by ac_rfl
      _ ≤ _ := ih
  | negR _ ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, qeval, lneg_lneg] at *
    calc _ = _ := by ac_rfl
      _ ≤ _ := ih
  | bangWnL hι => exact absurd hι (by decide)
  | wnBangR hι => exact absurd hι (by decide)

/-- Provability in **ILC** / **ILC_ι** forms a (thin) polycategory. -/
def ILC.polycategory (ι : Bool) (α : Type u) : ThinMultisetPolycategory (Formula α) where
  Hom := ILC ι
  id := ILC.id
  comp := ILC.cut

/-- **Soundness, categorically**: evaluation in a Girard quantale is a polyfunctor from the
polycategory of **ILC**-provability to the polycategory of the quantale. -/
def ILC.evalPolyfunctor (v : α → Q) :
    ThinMultisetPolycategory.Functor (ILC.polycategory false α) (GirardQuantale.toThinPolycategory Q) where
  obj := Formula.qeval v
  map h := by
    have := ILC.sound_girardQuantale v h
    simpa [QValid, GirardQuantale.toThinPolycategory, Multiset.map_map,
      Function.comp_def] using this

end ILLe

end
