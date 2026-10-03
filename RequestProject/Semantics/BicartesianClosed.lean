module

public import RequestProject.Semantics.Heyting

/-!
# Bicartesian closed categories: the categorical model of intuitionistic logic

A **bicartesian closed category** is a cartesian closed category (finite products — here a
`CartesianMonoidalCategory` — and exponentials, `MonoidalClosed`) which also has finite
coproducts (binary coproducts and an initial object). Intuitionistic formulas are
interpreted as objects:

`⟦⊤⟧ = 𝟙` (terminal), `⟦ff⟧ = ⊥` (initial), `⟦A & B⟧ = ⟦A⟧ ⊗ ⟦B⟧` (product),
`⟦A ∨ B⟧ = ⟦A⟧ ⨿ ⟦B⟧` (coproduct), `⟦A ⇒ B⟧ = ⟦A⟧ ⟹ ⟦B⟧` (exponential),

and a sequent `A₁, …, Aₙ ⊢ B` as a morphism `⟦A₁⟧ ⊗ ⋯ ⊗ ⟦Aₙ⟧ ⟶ ⟦B⟧`.

* `CategoryTheory.PosetReflection C`: the posetal reflection of a category `C` (objects up to
  the equivalence `X ~ Y` iff there are morphisms `X ⟶ Y` and `Y ⟶ X`, ordered by existence
  of morphisms).
* `CategoryTheory.PosetReflection.instHeytingAlgebra`: **the posetal reflection of a
  bicartesian closed category is a Heyting algebra**. This is the bridge between the
  categorical and the algebraic models: Heyting algebras are exactly the thin bicartesian
  closed categories.
* `IL.LJ.sound_bicartesianClosed`: **soundness of intuitionistic logic in every bicartesian
  closed category**: if `A₁, …, Aₙ ⊢ B` is provable then there is a morphism
  `⟦A₁⟧ ⊗ ⋯ ⊗ ⟦Aₙ⟧ ⟶ ⟦B⟧` (and a morphism to the initial object for an empty succedent).
-/

@[expose] public noncomputable section

universe w u v

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- Objects of `C` preordered by existence of morphisms. -/
def PosetReflection.Pre : Type u := C

variable {C} in
/-- An object of `C`, seen in `PosetReflection.Pre C`. -/
def PosetReflection.Pre.of (X : C) : PosetReflection.Pre C := X

variable {C} in
/-- The underlying object. -/
def PosetReflection.Pre.val (X : PosetReflection.Pre C) : C := X

instance : Preorder (PosetReflection.Pre C) where
  le X Y := Nonempty (X.val ⟶ Y.val)
  le_refl X := ⟨𝟙 X.val⟩
  le_trans _ _ _ := fun ⟨f⟩ ⟨g⟩ => ⟨f ≫ g⟩

variable {C} in
lemma PosetReflection.Pre.le_def {X Y : PosetReflection.Pre C} :
    X ≤ Y ↔ Nonempty (X.val ⟶ Y.val) := Iff.rfl

/-- The **posetal reflection** of a category: objects modulo `X ~ Y` iff `X ⟶ Y` and
`Y ⟶ X` exist, ordered by existence of a morphism. -/
def PosetReflection : Type u := Antisymmetrization (PosetReflection.Pre C) (· ≤ ·)

namespace PosetReflection

variable {C}

instance : PartialOrder (PosetReflection C) :=
  inferInstanceAs (PartialOrder (Antisymmetrization (PosetReflection.Pre C) (· ≤ ·)))

/-- The class of an object. -/
def mk (X : C) : PosetReflection C := toAntisymmetrization (· ≤ ·) (Pre.of X)

lemma mk_le_mk {X Y : C} : mk X ≤ mk Y ↔ Nonempty (X ⟶ Y) :=
  toAntisymmetrization_le_toAntisymmetrization_iff

@[elab_as_elim]
lemma ind {motive : PosetReflection C → Prop} (h : ∀ X, motive (mk X)) (x : PosetReflection C) :
    motive x := Quotient.ind (fun X => h X.val) x

/-- Lift a binary operation on objects, functorial in the given variances, to the posetal
reflection. -/
def lift₂ (F : C → C → C)
    (hF : ∀ {X X' Y Y' : C}, (X ⟶ X') → (X' ⟶ X) → (Y ⟶ Y') → (Y' ⟶ Y) → (F X Y ⟶ F X' Y')) :
    PosetReflection C → PosetReflection C → PosetReflection C :=
  Quotient.map₂ (fun X Y : Pre C => Pre.of (F X.val Y.val)) (fun _ _ hX _ _ hY => by
    obtain ⟨f⟩ := Pre.le_def.1 hX.1; obtain ⟨f'⟩ := Pre.le_def.1 hX.2
    obtain ⟨g⟩ := Pre.le_def.1 hY.1; obtain ⟨g'⟩ := Pre.le_def.1 hY.2
    exact ⟨Pre.le_def.2 ⟨hF f f' g g'⟩, Pre.le_def.2 ⟨hF f' f g' g⟩⟩)

lemma lift₂_mk (F : C → C → C) (hF) (X Y : C) :
    lift₂ F hF (mk X) (mk Y) = mk (F X Y) := rfl

section BCCC

variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasBinaryCoproducts C] [HasInitial C]

/-- the swap map `X ⊗ Y ⟶ Y ⊗ X` of a cartesian monoidal category -/
def swap (X Y : C) : X ⊗ Y ⟶ Y ⊗ X := lift (snd X Y) (fst X Y)

/-- functoriality of the exponential: contravariant in the base, covariant in the target -/
def expMap {X X' Y Y' : C} (f : X' ⟶ X) (g : Y ⟶ Y') :
    (ihom X).obj Y ⟶ (ihom X').obj Y' :=
  MonoidalClosed.curry ((f ▷ (ihom X).obj Y) ≫ MonoidalClosed.uncurry (𝟙 _) ≫ g)

/-- product morphism `X ⊗ Y ⟶ X' ⊗ Y'` -/
def prodMap {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') : X ⊗ Y ⟶ X' ⊗ Y' :=
  lift (fst X Y ≫ f) (snd X Y ≫ g)

instance : Min (PosetReflection C) :=
  ⟨lift₂ (fun X Y => X ⊗ Y) (fun f _ g _ => prodMap f g)⟩
instance : Max (PosetReflection C) :=
  ⟨lift₂ (fun X Y => X ⨿ Y) (fun f _ g _ => coprod.map f g)⟩
instance : HImp (PosetReflection C) :=
  ⟨lift₂ (fun X Y => (ihom X).obj Y) (fun _ f' g _ => expMap f' g)⟩
instance : Top (PosetReflection C) := ⟨mk (𝟙_ C)⟩
instance : Bot (PosetReflection C) := ⟨mk (⊥_ C)⟩


/-- **The posetal reflection of a bicartesian closed category is a Heyting algebra**
(meet = product, join = coproduct, implication = exponential, `⊤` = terminal object,
`⊥` = initial object). -/
instance instHeytingAlgebra : HeytingAlgebra (PosetReflection C) where
  sup := (· ⊔ ·)
  inf := (· ⊓ ·)
  top := ⊤
  bot := ⊥
  himp := (· ⇨ ·)
  compl x := x ⇨ ⊥
  le_sup_left x y := by
    induction x using ind; induction y using ind; exact mk_le_mk.2 ⟨coprod.inl⟩
  le_sup_right x y := by
    induction x using ind; induction y using ind; exact mk_le_mk.2 ⟨coprod.inr⟩
  sup_le x y z := by
    induction x using ind; induction y using ind; induction z using ind
    intro h₁ h₂
    obtain ⟨f⟩ := mk_le_mk.1 h₁
    obtain ⟨g⟩ := mk_le_mk.1 h₂
    exact mk_le_mk.2 ⟨coprod.desc f g⟩
  inf_le_left x y := by
    induction x using ind; induction y using ind; exact mk_le_mk.2 ⟨fst _ _⟩
  inf_le_right x y := by
    induction x using ind; induction y using ind; exact mk_le_mk.2 ⟨snd _ _⟩
  le_inf x y z := by
    induction x using ind; induction y using ind; induction z using ind
    intro h₁ h₂
    obtain ⟨f⟩ := mk_le_mk.1 h₁
    obtain ⟨g⟩ := mk_le_mk.1 h₂
    exact mk_le_mk.2 ⟨lift f g⟩
  le_top x := by induction x using ind; exact mk_le_mk.2 ⟨toUnit _⟩
  bot_le x := by induction x using ind; exact mk_le_mk.2 ⟨initial.to _⟩
  le_himp_iff x y z := by
    induction x using ind; induction y using ind; induction z using ind
    rename_i X Y Z
    change mk X ≤ mk ((ihom Y).obj Z) ↔ mk (X ⊗ Y) ≤ mk Z
    rw [mk_le_mk, mk_le_mk]
    constructor
    · rintro ⟨f⟩; exact ⟨swap X Y ≫ MonoidalClosed.uncurry f⟩
    · rintro ⟨g⟩; exact ⟨MonoidalClosed.curry (swap Y X ≫ g)⟩
  himp_bot _ := rfl

end BCCC

end PosetReflection

end CategoryTheory

namespace IL

open Formula CategoryTheory.PosetReflection

variable {α : Type w} {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [MonoidalClosed C] [HasBinaryCoproducts C] [HasInitial C]

/-- Interpretation of an IL formula as an object of a bicartesian closed category, given an
object `V x` for each propositional variable `x`. -/
def Formula.interp (V : α → C) : Formula α → C
  | var x => V x
  | top => 𝟙_ C
  | ff => ⊥_ C
  | «with» A₁ A₂ => A₁.interp V ⊗ A₂.interp V
  | disj A₁ A₂ => A₁.interp V ⨿ A₂.interp V
  | imp A₁ A₂ => (ihom (A₁.interp V)).obj (A₂.interp V)

/-- Interpretation of a context (a list of objects) as their product `X₁ ⊗ (X₂ ⊗ ⋯ ⊗ 𝟙)`. -/
def ctxObj : List C → C
  | [] => 𝟙_ C
  | X :: l => X ⊗ ctxObj l

lemma mk_interp (V : α → C) (A : Formula α) :
    mk (A.interp V) = A.eval (fun x => mk (V x)) := by
  induction A with
  | var x => rfl
  | top => rfl
  | ff => rfl
  | «with» A B ihA ihB =>
    change mk (A.interp V) ⊓ mk (B.interp V) = _
    rw [ihA, ihB]; rfl
  | disj A B ihA ihB =>
    change mk (A.interp V) ⊔ mk (B.interp V) = _
    rw [ihA, ihB]; rfl
  | imp A B ihA ihB =>
    change mk (A.interp V) ⇨ mk (B.interp V) = _
    rw [ihA, ihB]; rfl

lemma mk_ctxObj (l : List C) : mk (ctxObj l) = ((l : Multiset C).map PosetReflection.mk).inf := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    simp only [ctxObj, ← Multiset.cons_coe, Multiset.map_cons, Multiset.inf_cons, ← ih]
    rfl

/-- **Soundness of intuitionistic logic in bicartesian closed categories.** If
`A₁, …, Aₙ ⊢ B` is provable in **LJ**, then in every bicartesian closed category there is
a morphism `⟦A₁⟧ ⊗ ⋯ ⊗ ⟦Aₙ⟧ ⟶ ⟦B⟧`. -/
theorem LJ.sound_bicartesianClosed (V : α → C) {l : List (Formula α)} {B : Formula α}
    (h : LJ (l : Multiset (Formula α)) (some B)) :
    Nonempty (ctxObj (l.map (Formula.interp V)) ⟶ B.interp V) := by
  have := h.sound (fun x => mk (V x))
  rw [valid_iff] at this
  rw [← mk_le_mk, mk_ctxObj, mk_interp]
  simpa [Multiset.map_coe, List.map_map, Function.comp_def, mk_interp] using this

/-- **Soundness for empty succedents**: if `A₁, …, Aₙ ⊢` is provable in **LJ**, there is a
morphism `⟦A₁⟧ ⊗ ⋯ ⊗ ⟦Aₙ⟧ ⟶ ⊥` into the initial object. -/
theorem LJ.sound_bicartesianClosed_none (V : α → C) {l : List (Formula α)}
    (h : LJ (l : Multiset (Formula α)) none) :
    Nonempty (ctxObj (l.map (Formula.interp V)) ⟶ ⊥_ C) :=
  LJ.sound_bicartesianClosed V (B := ff) (LJ.ffR h)

end IL

end
