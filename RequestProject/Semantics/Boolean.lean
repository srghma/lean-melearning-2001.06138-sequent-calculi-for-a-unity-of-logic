module

public import RequestProject.Logics.Util
public import RequestProject.Semantics.Polycategory

/-!
# Boolean algebras: the algebraic model of classical logic

* `CL.Formula.eval`: interpretation of CL formulas in a Boolean algebra.
* `CL.LK.sound`: **soundness** — if `Δ ⊢ Γ` is provable in **LK** then
  `⋀ ⟦Δ⟧ ≤ ⋁ ⟦Γ⟧` in every Boolean algebra, under every valuation.
* `CL.Lindenbaum`: the **Lindenbaum–Tarski algebra** of CL, the quotient of formulas by
  provable equivalence (`A ~ B` iff `A ⊢ B` and `B ⊢ A`), ordered by provability.
  `CL.Lindenbaum.instBooleanAlgebra` shows that it is a Boolean algebra.
* `CL.LK.complete`: **completeness** — a sequent valid in all Boolean algebras is provable.
* `CL.LK.iff_valid`: provability in **LK** = validity in all Boolean algebras.
* `CL.LK.polycategory`, `CL.evalPolyfunctor`: provability in **LK** forms a (thin)
  polycategory, and evaluation in a Boolean algebra is a polyfunctor into the polycategory
  of that Boolean algebra (soundness, categorically).
-/

@[expose] public section

universe u v

variable {α : Type u} [DecidableEq α]

namespace CL

open Formula

/-- Interpretation of a CL formula in a Boolean algebra `B`, given a valuation `v` of the
propositional variables. -/
def Formula.eval {B : Type v} [BooleanAlgebra B] (v : α → B) : Formula α → B
  | var x => v x
  | tt => ⊤
  | ff => ⊥
  | conj A₁ A₂ => A₁.eval v ⊓ A₂.eval v
  | disj A₁ A₂ => A₁.eval v ⊔ A₂.eval v
  | imp A₁ A₂ => A₁.eval v ⇨ A₂.eval v

/-- A sequent `Δ ⊢ Γ` is **valid** in the Boolean algebra `B` under the valuation `v` if
`⋀ ⟦Δ⟧ ≤ ⋁ ⟦Γ⟧`. -/
def Valid {B : Type v} [BooleanAlgebra B] (v : α → B) (Δ Γ : Finset (Formula α)) : Prop :=
  (Δ.inf (Formula.eval v)) ≤ (Γ.sup (Formula.eval v))

section BooleanLemmas

variable {B : Type v} [BooleanAlgebra B]

private lemma boolean_impL {a b d g : B} (h₁ : d ≤ a ⊔ g) (h₂ : b ⊓ d ≤ g) : (a ⇨ b) ⊓ d ≤ g := by
  rw [himp_eq, inf_sup_right]
  refine sup_le h₂ ?_
  calc aᶜ ⊓ d ≤ aᶜ ⊓ (a ⊔ g) := inf_le_inf_left _ h₁
    _ = aᶜ ⊓ g := by rw [inf_sup_left, compl_inf_eq_bot, bot_sup_eq]
    _ ≤ g := inf_le_right

private lemma boolean_impR {a b d g : B} (h : a ⊓ d ≤ b ⊔ g) : d ≤ (a ⇨ b) ⊔ g := by
  rw [himp_eq]
  calc d = (a ⊓ d) ⊔ (aᶜ ⊓ d) := by rw [← inf_sup_right, sup_compl_eq_top, top_inf_eq]
    _ ≤ (b ⊔ g) ⊔ aᶜ := sup_le_sup h inf_le_left
    _ = b ⊔ aᶜ ⊔ g := by ac_rfl

end BooleanLemmas

/-- **Soundness of LK for Boolean algebras.** -/
theorem LK.sound {B : Type v} [BooleanAlgebra B] (v : α → B) {Δ Γ : Finset (Formula α)}
    (h : LK Δ Γ) : Valid v Δ Γ := by
  unfold Valid
  induction h with
  | weakL A _ ih =>
    exact le_trans (Finset.inf_mono (Finset.subset_insert _ _)) ih
  | weakR B _ ih =>
    exact le_trans ih (Finset.sup_mono (Finset.subset_insert _ _))
  -- contrL/contrR are absorbed by Finset: insert A (insert A Δ) = insert A Δ
  | id A => simp
  | cut _ _ ih₁ ih₂ =>
    rename_i Δ Γ Δ' Γ' C _ _
    simp only [Finset.inf_union, Finset.sup_union, Finset.inf_insert, Finset.sup_insert] at *
    calc Δ.inf (eval v) ⊓ Δ'.inf (eval v)
        ≤ (C.eval v ⊔ Γ.sup (eval v)) ⊓ Δ'.inf (eval v) := inf_le_inf_right _ ih₁
      _ = (C.eval v ⊓ Δ'.inf (eval v)) ⊔ (Γ.sup (eval v) ⊓ Δ'.inf (eval v)) :=
          inf_sup_right _ _ _
      _ ≤ Γ.sup (eval v) ⊔ Γ'.sup (eval v) := by
          apply sup_le
          · exact le_trans ih₂ le_sup_right
          · exact le_trans inf_le_left le_sup_left
  | ttL _ ih =>
    exact le_trans (Finset.inf_mono (Finset.subset_insert _ _)) ih
  | ttR => simp [Formula.eval]
  | ffL => simp [Formula.eval]
  | ffR _ ih =>
    exact le_trans ih (Finset.sup_mono (Finset.subset_insert _ _))
  | conjL₁ A₂ _ ih =>
    simp only [Finset.inf_insert, eval] at *
    exact le_trans (inf_le_inf_right _ inf_le_left) ih
  | conjL₂ A₁ _ ih =>
    simp only [Finset.inf_insert, eval] at *
    exact le_trans (inf_le_inf_right _ inf_le_right) ih
  | conjR _ _ ih₁ ih₂ =>
    simp only [Finset.sup_insert, eval] at *
    rw [sup_inf_right]
    exact le_inf ih₁ ih₂
  | disjL _ _ ih₁ ih₂ =>
    simp only [Finset.inf_insert, eval] at *
    rw [inf_sup_right]
    exact sup_le ih₁ ih₂
  | disjR₁ B₂ _ ih =>
    simp only [Finset.sup_insert, eval] at *
    exact le_trans ih (sup_le_sup_right le_sup_left _)
  | disjR₂ B₁ _ ih =>
    simp only [Finset.sup_insert, eval] at *
    exact le_trans ih (sup_le_sup_right le_sup_right _)
  | impL _ _ ih₁ ih₂ =>
    simp only [Finset.inf_insert, Finset.sup_insert, eval] at *
    exact boolean_impL ih₁ ih₂
  | impR _ ih =>
    simp only [Finset.inf_insert, Finset.sup_insert, eval] at *
    exact boolean_impR ih

/-! ## Derived rules of LK used for the Lindenbaum algebra -/

namespace LK

lemma cast' {Δ Γ Δ' Γ' : Finset (Formula α)} (h : LK Δ Γ) (h₁ : Δ = Δ') (h₂ : Γ = Γ') :
    LK Δ' Γ' := h₁ ▸ h₂ ▸ h

lemma trans' {A B C : Formula α} (h₁ : LK {A} {B}) (h₂ : LK {B} {C}) : LK {A} {C} :=
  (cut (Γ := ∅) (Δ' := ∅) h₁ h₂).cast' (by simp) (by simp)

lemma conj_le_left (A B : Formula α) : LK {conj A B} {A} := conjL₁ (Δ := ∅) B (id A)
lemma conj_le_right (A B : Formula α) : LK {conj A B} {B} := conjL₂ (Δ := ∅) A (id B)
lemma le_conj {A B C : Formula α} (h₁ : LK {C} {A}) (h₂ : LK {C} {B}) : LK {C} {conj A B} :=
  conjR (Γ := ∅) h₁ h₂
lemma le_disj_left (A B : Formula α) : LK {A} {disj A B} := disjR₁ (Γ := ∅) B (id A)
lemma le_disj_right (A B : Formula α) : LK {B} {disj A B} := disjR₂ (Γ := ∅) A (id B)
lemma disj_le {A B C : Formula α} (h₁ : LK {A} {C}) (h₂ : LK {B} {C}) : LK {disj A B} {C} :=
  disjL (Δ := ∅) h₁ h₂
lemma le_tt (A : Formula α) : LK {A} {tt} := weakL (Δ := ∅) A ttR
lemma ff_le (A : Formula α) : LK {ff} {A} := weakR (Γ := ∅) A ffL

/-- `A, ∼A ⊢` -/
lemma neg_left (A : Formula α) : LK {A, Formula.neg A} ∅ :=
  (impL (Δ := {A}) (Γ := ∅) (A := A) (B := ff) (id A) ((weakL A ffL).cast' (Finset.pair_comm _ _) rfl)).cast'
    (Finset.pair_comm _ _) rfl

/-- `⊢ A, ∼A` -/
lemma neg_right (A : Formula α) : LK ∅ {A, Formula.neg A} :=
  (impR (Δ := ∅) (Γ := {A}) (A := A) (B := ff) (ffR (id A))).cast' rfl
    (Finset.pair_comm _ _)

lemma conj_neg_le (A : Formula α) : LK {conj A (Formula.neg A)} {ff} := by
  have h1 := conjL₁ (Δ := {Formula.neg A}) (Formula.neg A) (weakR ff (neg_left A))
  have h2 := conjL₂ (Δ := {conj A (Formula.neg A)}) A
    (h1.cast' (Finset.pair_comm _ _) rfl)
  exact h2.cast' (Finset.insert_eq_of_mem (Finset.mem_singleton_self _)) rfl

lemma tt_le_disj_neg (A : Formula α) : LK {tt} {disj A (Formula.neg A)} := by
  have h1 := disjR₁ (Γ := {Formula.neg A}) (Formula.neg A) (neg_right A)
  have h2 := disjR₂ (Γ := {disj A (Formula.neg A)}) A
    (h1.cast' rfl (Finset.pair_comm _ _))
  have h3 : LK ∅ {disj A (Formula.neg A)} :=
    h2.cast' rfl (Finset.insert_eq_of_mem (Finset.mem_singleton_self _))
  exact ttL h3

lemma distrib (x y z : Formula α) :
    LK {conj (disj x y) (disj x z)} {disj x (conj y z)} := by
  set P := conj (disj x y) (disj x z)
  set R := disj x (conj y z)
  have hx : LK {x} {R} := le_disj_left _ _
  have s1 : LK (x ::ᵢ {P}) {R} := (weakL P hx).cast' (Finset.pair_comm _ _) rfl
  have s2 : LK (y ::ᵢ {z}) {R} := by
    have a : LK (y ::ᵢ {z}) {y} := (weakL z (id y)).cast' (Finset.pair_comm _ _) rfl
    have b : LK (y ::ᵢ {z}) {z} := weakL y (id z)
    exact disjR₂ (Γ := ∅) x (conjR (Γ := ∅) a b)
  have s3 : LK (y ::ᵢ {x}) {R} := weakL y hx
  have s4 : LK (disj x z ::ᵢ {y}) {R} :=
    disjL (s3.cast' (Finset.pair_comm _ _) rfl) (s2.cast' (Finset.pair_comm _ _) rfl)
  have s5 : LK (y ::ᵢ {P}) {R} :=
    (conjL₂ (disj x y) s4).cast' (Finset.pair_comm _ _) rfl
  have s6 : LK (disj x y ::ᵢ {P}) {R} := disjL s1 s5
  have s7 := conjL₁ (disj x z) s6
  exact s7.cast' (Finset.insert_eq_of_mem (Finset.mem_singleton_self _)) rfl

lemma imp_le (a b : Formula α) : LK {imp a b} {disj b (Formula.neg a)} := by
  have h1 : LK ∅ (a ::ᵢ {disj b (Formula.neg a)}) :=
    (disjR₂ (Γ := {a}) b ((neg_right a).cast' rfl (Finset.pair_comm _ _))).cast' rfl
      (Finset.pair_comm _ _)
  exact impL (Δ := ∅) h1 (le_disj_left _ _)

lemma le_imp (a b : Formula α) : LK {disj b (Formula.neg a)} {imp a b} :=
  disj_le (impR (Δ := {b}) (Γ := ∅) (weakL a (id b)))
    (impR (Δ := {Formula.neg a}) (Γ := ∅) (weakR b (neg_left a)))

lemma neg_anti {a a' : Formula α} (h : LK {a'} {a}) :
    LK {Formula.neg a} {Formula.neg a'} :=
  impR (Δ := {Formula.neg a}) (Γ := ∅)
    ((cut (Δ := {a'}) (Γ := ∅) h (weakR ff (neg_left a))).cast' (by simp) (by simp))

lemma imp_mono {a a' b b' : Formula α} (ha : LK {a'} {a}) (hb : LK {b} {b'}) :
    LK {imp a b} {imp a' b'} := by
  have h1 : LK {a'} (a ::ᵢ {b'}) := (weakR b' ha).cast' rfl (Finset.pair_comm _ _)
  have h2 : LK (b ::ᵢ {a'}) {b'} := (weakL a' hb).cast' (Finset.pair_comm _ _) rfl
  exact impR (Δ := {imp a b}) (Γ := ∅)
    ((impL (Δ := {a'}) (Γ := {b'}) h1 h2).cast' (Finset.pair_comm _ _) rfl)

lemma conj_mono {a a' b b' : Formula α} (ha : LK {a} {a'}) (hb : LK {b} {b'}) :
    LK {conj a b} {conj a' b'} :=
  le_conj (trans' (conj_le_left _ _) ha) (trans' (conj_le_right _ _) hb)

lemma disj_mono {a a' b b' : Formula α} (ha : LK {a} {a'}) (hb : LK {b} {b'}) :
    LK {disj a b} {disj a' b'} :=
  disj_le (trans' ha (le_disj_left _ _)) (trans' hb (le_disj_right _ _))

end LK

/-! ## The Lindenbaum–Tarski algebra of CL -/

/-- Formulas of CL preordered by provability: `A ≤ B` iff `A ⊢ B` is provable in **LK**. -/
def LPre (α : Type u) [DecidableEq α] : Type u := Formula α

instance : Preorder (LPre α) where
  le A B := LK {A} {B}
  le_refl A := LK.id A
  le_trans _ _ _ := LK.trans'

/-- The **Lindenbaum–Tarski algebra** of classical logic: formulas modulo provable
equivalence (`A ~ B` iff `A ⊢ B` and `B ⊢ A` are provable in **LK**), ordered by
provability. -/
def Lindenbaum (α : Type u) [DecidableEq α] : Type u := Antisymmetrization (LPre α) (· ≤ ·)

namespace Lindenbaum

instance : PartialOrder (Lindenbaum α) :=
  inferInstanceAs (PartialOrder (Antisymmetrization (LPre α) (· ≤ ·)))

/-- The equivalence class of a formula. -/
def mk (A : Formula α) : Lindenbaum α := toAntisymmetrization (· ≤ ·) (A : LPre α)

lemma mk_le_mk {A B : Formula α} : mk A ≤ mk B ↔ LK {A} {B} :=
  toAntisymmetrization_le_toAntisymmetrization_iff

lemma mk_eq_mk {A B : Formula α} : mk A = mk B ↔ LK {A} {B} ∧ LK {B} {A} := by
  rw [le_antisymm_iff, mk_le_mk, mk_le_mk]

@[elab_as_elim]
lemma ind {motive : Lindenbaum α → Prop} (h : ∀ A, motive (mk A)) (x : Lindenbaum α) :
    motive x := Quotient.ind h x

def lift₂ (f : Formula α → Formula α → Formula α)
    (hf : ∀ {a a' b b'}, LK {a} {a'} → LK {b} {b'} → LK {f a b} {f a' b'}) :
    Lindenbaum α → Lindenbaum α → Lindenbaum α :=
  Quotient.map₂ (f : LPre α → LPre α → LPre α)
    (fun _ _ ha _ _ hb => ⟨hf ha.1 hb.1, hf ha.2 hb.2⟩)

instance : Max (Lindenbaum α) := ⟨lift₂ disj LK.disj_mono⟩
instance : Min (Lindenbaum α) := ⟨lift₂ conj LK.conj_mono⟩
instance : Top (Lindenbaum α) := ⟨mk tt⟩
instance : Bot (Lindenbaum α) := ⟨mk ff⟩
instance : Compl (Lindenbaum α) :=
  ⟨Quotient.map (Formula.neg : LPre α → LPre α)
    (fun _ _ ha => ⟨LK.neg_anti ha.2, LK.neg_anti ha.1⟩)⟩
instance : HImp (Lindenbaum α) :=
  ⟨Quotient.map₂ (imp : LPre α → LPre α → LPre α)
    (fun _ _ ha _ _ hb => ⟨LK.imp_mono ha.2 hb.1, LK.imp_mono ha.1 hb.2⟩)⟩

@[simp] lemma mk_sup (A B : Formula α) : mk A ⊔ mk B = mk (disj A B) := rfl
@[simp] lemma mk_inf (A B : Formula α) : mk A ⊓ mk B = mk (conj A B) := rfl
@[simp] lemma mk_top : (⊤ : Lindenbaum α) = mk tt := rfl
@[simp] lemma mk_bot : (⊥ : Lindenbaum α) = mk ff := rfl
@[simp] lemma mk_compl (A : Formula α) : (mk A)ᶜ = mk (Formula.neg A) := rfl
@[simp] lemma mk_himp (A B : Formula α) : mk A ⇨ mk B = mk (imp A B) := rfl

/-- **The Lindenbaum–Tarski algebra of CL is a Boolean algebra.** -/
instance instBooleanAlgebra : BooleanAlgebra (Lindenbaum α) where
  sup := (· ⊔ ·)
  inf := (· ⊓ ·)
  top := ⊤
  bot := ⊥
  compl := (·ᶜ)
  himp := (· ⇨ ·)
  le_sup_left x y := by
    induction x using ind; induction y using ind; exact mk_le_mk.2 (LK.le_disj_left _ _)
  le_sup_right x y := by
    induction x using ind; induction y using ind; exact mk_le_mk.2 (LK.le_disj_right _ _)
  sup_le x y z := by
    induction x using ind; induction y using ind; induction z using ind
    intro h₁ h₂; exact mk_le_mk.2 (LK.disj_le (mk_le_mk.1 h₁) (mk_le_mk.1 h₂))
  inf_le_left x y := by
    induction x using ind; induction y using ind; exact mk_le_mk.2 (LK.conj_le_left _ _)
  inf_le_right x y := by
    induction x using ind; induction y using ind; exact mk_le_mk.2 (LK.conj_le_right _ _)
  le_inf x y z := by
    induction x using ind; induction y using ind; induction z using ind
    intro h₁ h₂; exact mk_le_mk.2 (LK.le_conj (mk_le_mk.1 h₁) (mk_le_mk.1 h₂))
  le_sup_inf x y z := by
    induction x using ind; induction y using ind; induction z using ind
    exact mk_le_mk.2 (LK.distrib _ _ _)
  inf_compl_le_bot x := by
    induction x using ind; exact mk_le_mk.2 (LK.conj_neg_le _)
  top_le_sup_compl x := by
    induction x using ind; exact mk_le_mk.2 (LK.tt_le_disj_neg _)
  le_top x := by induction x using ind; exact mk_le_mk.2 (LK.le_tt _)
  bot_le x := by induction x using ind; exact mk_le_mk.2 (LK.ff_le _)
  sdiff x y := x ⊓ yᶜ
  sdiff_eq _ _ := rfl
  himp_eq x y := by
    induction x using ind; induction y using ind
    exact mk_eq_mk.2 ⟨LK.imp_le _ _, LK.le_imp _ _⟩

/-- In the Lindenbaum–Tarski algebra, under the canonical valuation `X ↦ [X]`, every
formula evaluates to its own equivalence class. -/
lemma eval_mk (A : Formula α) : A.eval (fun x => mk (var x)) = mk A := by
  induction A with
  | var x => rfl
  | tt => rfl
  | ff => rfl
  | conj A B ihA ihB => simp only [eval, ihA, ihB]; rfl
  | disj A B ihA ihB => simp only [eval, ihA, ihB]; rfl
  | imp A B ihA ihB => simp only [eval, ihA, ihB]; rfl

lemma le_sup_imp_LK (Γ : Finset (Formula α)) :
    ∀ C : Formula α, mk C ≤ Γ.sup mk → LK {C} Γ := by
  induction Γ using Finset.induction_on with
  | empty =>
    intro C h
    have h' : LK {C} {ff} := mk_le_mk.1 (by simpa using h)
    exact (LK.cut (Δ := {C}) (Γ := ∅) (Δ' := ∅) (Γ' := ∅) h' LK.ffL).cast' (by simp) (by simp)
  | @insert B Γ hB ih =>
    intro C h
    simp only [Finset.sup_insert] at h
    have h2 : mk (conj C (Formula.neg B)) ≤ Γ.sup mk := by
      rw [← mk_inf, ← mk_compl, ← sdiff_eq]; exact sdiff_le_iff.2 h
    have h3 := ih _ h2
    have h1 : LK {C} (conj C (Formula.neg B) ::ᵢ {B}) := by
      refine LK.conjR (Γ := {B}) ((LK.weakR B (LK.id C)).cast' rfl (Finset.pair_comm _ _)) ?_
      exact LK.impR (Δ := {C}) (Γ := {B}) (LK.ffR ((LK.weakL C (LK.id B)).cast' (Finset.pair_comm _ _) rfl))
    have hcut := LK.cut (Δ' := ∅) h1 h3
    exact hcut.cast' (by simp) (by ext x; simp)

lemma inf_le_sup_imp_LK (Δ : Finset (Formula α)) :
    ∀ Γ : Finset (Formula α), Δ.inf mk ≤ Γ.sup mk → LK Δ Γ := by
  induction Δ using Finset.induction_on with
  | empty =>
    intro Γ h
    have h' := le_sup_imp_LK Γ tt (by simpa using h)
    exact (LK.cut (Δ' := ∅) (Γ := ∅) LK.ttR h').cast' (by simp) (by simp)
  | @insert A Δ hA ih =>
    intro Γ h
    simp only [Finset.inf_insert] at h
    have h2 : Δ.inf mk ≤ (insert (Formula.neg A) Γ).sup mk := by
      simp only [Finset.sup_insert, ← mk_compl]
      calc Δ.inf mk ≤ (mk A)ᶜ ⊔ (mk A ⊓ Δ.inf mk) := by
            rw [sup_inf_left, compl_sup_eq_top, top_inf_eq]; exact le_sup_right
        _ ≤ (mk A)ᶜ ⊔ Γ.sup mk := sup_le_sup_left h _
    have h3 := ih _ h2
    have hneg : LK (Formula.neg A ::ᵢ {A}) ∅ := (LK.neg_left A).cast' (Finset.pair_comm _ _) rfl
    have hcut := LK.cut (Δ' := {A}) (Γ' := ∅) h3 hneg
    exact hcut.cast' (by ext x; simp) (by simp)

end Lindenbaum

/-- **Completeness of LK for Boolean algebras**: a sequent that is valid in every Boolean
algebra under every valuation is provable. (It suffices to quantify over Boolean algebras in
the same universe as the variables: the Lindenbaum–Tarski algebra is one of them.) -/
theorem LK.complete {Δ Γ : Finset (Formula α)}
    (h : ∀ (B : Type u) [BooleanAlgebra B] (v : α → B), Valid v Δ Γ) : LK Δ Γ := by
  have := h (Lindenbaum α) (fun (x : α) => Lindenbaum.mk (var x))
  have h_eval : Formula.eval (fun (x : α) => Lindenbaum.mk (var x)) = Lindenbaum.mk := funext Lindenbaum.eval_mk
  unfold Valid at this
  rw [h_eval] at this
  exact Lindenbaum.inf_le_sup_imp_LK Δ Γ this

/-- **Boolean algebras are the algebraic models of classical logic**: a sequent is provable
in **LK** iff it is valid in every Boolean algebra under every valuation. -/
theorem LK.iff_valid {Δ Γ : Finset (Formula α)} :
    LK Δ Γ ↔ ∀ (B : Type u) [BooleanAlgebra B] (v : α → B), Valid v Δ Γ :=
  ⟨fun h _ _ v => h.sound v, LK.complete⟩

/-! ## The categorical picture: polycategories -/

/-- Provability in **LK** forms a (thin) polycategory, whose colours are the formulas of CL:
identities are the identity axioms and composition is the cut rule. -/
def LK.polycategory (α : Type u) [DecidableEq α] : ThinPolycategory (Formula α) where
  Hom := LK
  id := LK.id
  comp := LK.cut

/-- **Soundness, categorically**: evaluation in a Boolean algebra `B` is a polyfunctor from
the polycategory of **LK**-provability to the polycategory of `B`. -/
def evalPolyfunctor {B : Type v} [DecidableEq B] [BooleanAlgebra B] (v : α → B) :
    ThinPolycategory.Functor (LK.polycategory α) (DistribLattice.toThinPolycategory B) where
  obj := Formula.eval v
  map {Γ Δ} h := by
    have hs := h.sound v
    unfold Valid at hs
    simpa [DistribLattice.toThinPolycategory, Finset.inf_image, Finset.sup_image] using hs

end CL

end
