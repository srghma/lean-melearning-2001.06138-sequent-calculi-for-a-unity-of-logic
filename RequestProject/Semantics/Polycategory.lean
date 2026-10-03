module

public import Mathlib

/-!
# Thin polycategories and thin coloured operads

A *polycategory* has morphisms `f : A₁, …, Aₙ → B₁, …, Bₘ` with many inputs and many
outputs, identities `A → A`, and composition along one colour
(`Γ → A, Δ` and `A, Γ' → Δ'` give `Γ, Γ' → Δ, Δ'`): exactly the shape of the
identity and cut rules of a two-sided (classical) sequent calculus.
A *coloured operad* (symmetric multicategory) is the special case of morphisms
with exactly one output, the shape of an intuitionistic sequent calculus.

All calculi in this project are formalised at the level of *provability*, so here we use
the **thin** (proof-irrelevant) versions: the hom-sets are propositions. In a thin
structure all coherence laws (associativity, unit laws, equivariance) hold automatically,
so the structures consist only of identities and composition. Symmetry (the action of
permutations on inputs and outputs) is built in by using multisets of colours.
-/

@[expose] public section

universe u v

/-- A **thin symmetric polycategory** with colours (objects) `C`: `Hom Γ Δ` says that
there is a polymorphism from the multiset of inputs `Γ` to the multiset of outputs `Δ`. -/
structure ThinPolycategory (C : Type u) where
  /-- there is a morphism `Γ → Δ` -/
  Hom : Multiset C → Multiset C → Prop
  /-- identities `A → A` -/
  id : ∀ A, Hom {A} {A}
  /-- composition along a single colour `A` (the shape of the cut rule) -/
  comp : ∀ {Γ Δ Γ' Δ' : Multiset C} {A : C},
    Hom Γ (A ::ₘ Δ) → Hom (A ::ₘ Γ') Δ' → Hom (Γ + Γ') (Δ + Δ')

/-- A **thin coloured operad** (thin symmetric multicategory) with colours `C`:
`Hom Γ B` says that there is a multimorphism from the inputs `Γ` to the single output `B`. -/
structure ThinColoredOperad (C : Type u) where
  /-- there is a multimorphism `Γ → B` -/
  Hom : Multiset C → C → Prop
  /-- identities `A → A` -/
  id : ∀ A, Hom {A} A
  /-- (partial) composition `∘ᵢ` along the colour `A` -/
  comp : ∀ {Γ Γ' : Multiset C} {A B : C}, Hom Γ A → Hom (A ::ₘ Γ') B → Hom (Γ + Γ') B

/-- A **polyfunctor** between thin polycategories: a map of colours preserving morphisms. -/
structure ThinPolycategory.Functor {C : Type u} {D : Type v}
    (P : ThinPolycategory C) (Q : ThinPolycategory D) where
  /-- action on colours -/
  obj : C → D
  /-- action on morphisms -/
  map : ∀ {Γ Δ}, P.Hom Γ Δ → Q.Hom (Γ.map obj) (Δ.map obj)

/-- A **functor of operads** between thin coloured operads. -/
structure ThinColoredOperad.Functor {C : Type u} {D : Type v}
    (P : ThinColoredOperad C) (Q : ThinColoredOperad D) where
  /-- action on colours -/
  obj : C → D
  /-- action on morphisms -/
  map : ∀ {Γ B}, P.Hom Γ B → Q.Hom (Γ.map obj) (obj B)

/-- Every polycategory has an underlying coloured operad: the morphisms with exactly one
output. -/
def ThinPolycategory.toOperad {C : Type u} (P : ThinPolycategory C) : ThinColoredOperad C where
  Hom Γ B := P.Hom Γ {B}
  id := P.id
  comp {Γ Γ' A B} f g := by
    simpa using P.comp (Δ := 0) (by simpa using f) g

/-- A **distributive lattice** (in particular a Boolean algebra) is a thin polycategory:
there is a morphism `Γ → Δ` iff `⋀ Γ ≤ ⋁ Δ`. Composition is the algebraic cut rule, which
needs distributivity. -/
def DistribLattice.toThinPolycategory (L : Type u) [DistribLattice L] [BoundedOrder L] :
    ThinPolycategory L where
  Hom Γ Δ := Γ.inf ≤ Δ.sup
  id A := by simp
  comp {Γ Δ Γ' Δ' A} f g := by
    simp only [Multiset.inf_cons, Multiset.sup_cons, Multiset.inf_add, Multiset.sup_add] at *
    calc Γ.inf ⊓ Γ'.inf ≤ (A ⊔ Δ.sup) ⊓ Γ'.inf := inf_le_inf_right _ f
      _ = (A ⊓ Γ'.inf) ⊔ (Δ.sup ⊓ Γ'.inf) := inf_sup_right _ _ _
      _ ≤ Δ.sup ⊔ Δ'.sup := sup_le (g.trans le_sup_right) (inf_le_left.trans le_sup_left)

/-- A **meet-semilattice with top** (in particular a Heyting algebra) is a thin coloured
operad: there is a multimorphism `Γ → B` iff `⋀ Γ ≤ B`. -/
def SemilatticeInf.toThinColoredOperad (L : Type u) [SemilatticeInf L] [OrderTop L] :
    ThinColoredOperad L where
  Hom Γ B := Γ.inf ≤ B
  id A := by simp
  comp {Γ Γ' A B} f g := by
    simp only [Multiset.inf_cons, Multiset.inf_add] at *
    exact (inf_le_inf_right _ f).trans g

end
