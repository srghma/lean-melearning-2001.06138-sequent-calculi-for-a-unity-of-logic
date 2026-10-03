# Other ways to write the rules of `Calculi.lean`

This note answers: *are there other ways to write the rules in
`RequestProject/Logics/Calculi.lean`, possibly more strongly typed?* It lists several
designs, each with a Lean sketch and its trade-offs. **The current implementation is not
changed.**

The Lean snippets below are sketches on cut-down formula types so they stay short. Each
one was type-checked on its own with the project's Lean/Mathlib versions. None of them is
imported by the project.

---

## 0. What the current encoding does

Each calculus is an inductive *predicate*:

```lean
inductive LK : Multiset (Formula α) → Multiset (Formula α) → Prop
  | impR {Δ Γ} {A B} : LK (A ::ₘ Δ) (B ::ₘ Γ) → LK Δ (imp A B ::ₘ Γ)
  ...
```

Characteristics:

* **Proof-irrelevant** (`Prop`): you can state *that* a sequent is provable, but you cannot
  talk about *a particular proof* (its size, cut-freeness, rule permutations, …).
* **Untyped sequents**: a sequent is just two curried arguments, and `Δ ⊢ Γ` appears only
  in comments.
* **Side conditions as patterns**: "the context is `!Δ`" is written `Δ.map bang`, and
  "the succedent is `?Γ`" is written `Γ.map wn`, directly in the indices.
* **Variants by Boolean flag**: ILC vs ILC_ι is `ILC (ι : Bool)`, and the two extra rules
  take a proof `hι : ι = true`.
* **Rule set baked in**: the rules of a calculus are its constructors, so you cannot
  manipulate a calculus as an object (union, inclusion, mapping a translation over the
  rules, …).
* **Intuitionistic shape by type**: LJ/LLJ use `Option` on the right. This is already a
  "typed" choice.

Each proposal below changes one or more of these points. They can mostly be combined.

---

## 1. A `Sequent` structure with notation

Make the judgement a first-class type and give it notation, so the rules look like the
paper.

```lean
structure Sequent (F : Type u) where
  ant : Multiset F     -- antecedent Δ
  suc : Multiset F     -- succedent  Γ

infix:45 " ⊢ₛ " => Sequent.mk

inductive LK : Sequent (Formula α) → Prop
  | id (A)          : LK ({A} ⊢ₛ {A})
  | weakL {Δ Γ} (A) : LK (Δ ⊢ₛ Γ) → LK (A ::ₘ Δ ⊢ₛ Γ)
  | cut {Δ Γ Δ' Γ'} {B} :
      LK (Δ ⊢ₛ B ::ₘ Γ) → LK (B ::ₘ Δ' ⊢ₛ Γ') → LK (Δ + Δ' ⊢ₛ Γ + Γ')
  | impR {Δ Γ} {A B} : LK (A ::ₘ Δ ⊢ₛ B ::ₘ Γ) → LK (Δ ⊢ₛ imp A B ::ₘ Γ)
```

You can go further with a notation that names the calculus, e.g.
`notation:45 Δ " ⊢[LK] " Γ => LK (Sequent.mk Δ Γ)`.

* **Pros:** easier to read. Translations become functions `Sequent F → Sequent G`, so
  unlinearisation and classicalisation are one-liners (`fun s => ⟨s.ant.map bang, s.suc⟩`),
  and lemmas such as "the translation commutes with `⊢`" are stated on one object.
* **Cons:** purely cosmetic for the logic itself. `induction` produces goals of the form
  `⟨Δ, Γ⟩ = …`, which sometimes need a `cases` on the structure first.

---

## 2. Proof-relevant derivations (`Type` instead of `Prop`)

Make derivations data. Provability then becomes `Nonempty`.

```lean
inductive LK : Sequent (Formula α) → Type u
  | id (A) : LK ({A} ⊢ₛ {A})
  | weakL {Δ Γ} (A) : LK (Δ ⊢ₛ Γ) → LK (A ::ₘ Δ ⊢ₛ Γ)
  | cut {Δ Γ Δ' Γ'} {B} :
      LK (Δ ⊢ₛ B ::ₘ Γ) → LK (B ::ₘ Δ' ⊢ₛ Γ') → LK (Δ + Δ' ⊢ₛ Γ + Γ')
  | impR {Δ Γ} {A B} : LK (A ::ₘ Δ ⊢ₛ B ::ₘ Γ) → LK (Δ ⊢ₛ imp A B ::ₘ Γ)

def LK.Provable (s : Sequent (Formula α)) : Prop := Nonempty (LK s)

def LK.size : {s : Sequent (Formula α)} → LK s → ℕ
  | _, .id _      => 1
  | _, .weakL _ d => d.size + 1
  | _, .cut d e   => d.size + e.size + 1
  | _, .impR d    => d.size + 1

def LK.cutFree : {s : Sequent (Formula α)} → LK s → Bool
  | _, .id _ => true | _, .weakL _ d => d.cutFree
  | _, .cut _ _ => false | _, .impR d => d.cutFree
```

* **Pros:** this is the design that can express the paper's statement that the two routes
  around the lower square give *the same proof trees modulo permuting axioms and rules*,
  which is currently only formalised at the level of provability. The translations become
  functions `LK s → ILC ι (T s)` on proof trees, so you can compare the two composites. It
  also opens the way to cut-elimination (needed for the unproved conservativity results
  `ILL.ILCConservative` and `IL.INCConservative`), which needs induction on size or height.
* **Cons:** heavier. Equality of derivations runs into multiset index equalities
  (`HEq`/casts), because indices like `Δ + Δ'` are not constructor patterns. The existing
  `Prop` results can be recovered with `Nonempty.map`.

A useful halfway point is to keep the `Prop` calculi and add a separate `Type`-valued
copy, with `Provable ↔ Nonempty Deriv`.

---

## 3. Rules as data: calculi as sets of rule instances

Separate *what a rule is* from *what a calculus is*:

```lean
structure Rule (F : Type u) where
  prems : List (Sequent F)
  concl : Sequent F

abbrev RuleSet (F : Type u) := Set (Rule F)

inductive Derivable (R : RuleSet F) : Sequent F → Prop
  | rule (r : Rule F) : r ∈ R → (∀ p ∈ r.prems, Derivable R p) → Derivable R r.concl

theorem Derivable.mono {R S : RuleSet F} (h : R ⊆ S) {s} :
    Derivable R s → Derivable S s := by
  intro d; induction d with
  | rule r hr _ ih => exact .rule r (h hr) ih
```

Rule *families* are then small inductive predicates on `Rule F`, and calculi are unions of
families:

```lean
inductive Structural : Rule (F α) → Prop
  | bangW (A : F α) (Δ Γ) : Structural ⟨[⟨Δ, Γ⟩], ⟨.bang A ::ₘ Δ, Γ⟩⟩
  | id (A : F α)          : Structural ⟨[], ⟨{A}, {A}⟩⟩

inductive WeaklyDistributive : Rule (F α) → Prop
  | bangWnL (A : F α) (Δ Γ : Multiset (F α)) :
      WeaklyDistributive ⟨[⟨.bang A ::ₘ Δ.map .bang, Γ.map .wn⟩],
                          ⟨.bang (.wn A) ::ₘ Δ.map .bang, Γ.map .wn⟩⟩

def ILC  : RuleSet (F α) := setOf Structural            -- ∪ setOf Multiplicatives ∪ …
def ILCι : RuleSet (F α) := setOf Structural ∪ setOf WeaklyDistributive

example (s) : Derivable ILC s → Derivable ILCι s := Derivable.mono Set.subset_union_left
```

* **Pros:**
  * ILC ⊆ ILC_ι becomes literally a set inclusion, so the `hι : ι = true` hack goes away.
  * Shared rule groups (identity/cut, additives `&`/`⊕`, exponentials `!W !C !D`, …) are
    written once and reused across ILC, CLC, INC, … whenever the formula types agree.
  * **Unlinearisation and classicalisation act on rules**: the paper describes `C_!` and
    `C_?` as transformations of the *rules* (`Δ ⊢ Γ ↦ !Δ ⊢ Γ`). With a map
    `Rule.map f g` you could define CL's rules as the image of CLL⁻'s rules and so on, and
    prove soundness of a translation once, generically, by checking that every image rule
    is derivable ("admissible-rule" style).
  * Meta-theory such as structural induction, admissibility of a rule, or conservativity of
    adding rules is proved once for every calculus.
* **Cons:** an extra layer. Concrete derivations are more verbose (you build a `Rule`
  record and prove membership), so you would want smart constructors such as
  `LK.impR : … → Derivable LK _` that wrap `Derivable.rule`, and probably a small
  `simp`/`aesop` set for membership.

A variant is to make the rule *names* an inductive type (`inductive LKRuleName | id | cut
| impR …`) with a function giving the premises and conclusion of each instance. This gives
finite, decidable rule names, which is handy for counting rules or for automation.

---

## 4. Typed side conditions for `!Δ` / `?Γ`

The current rules write the promotion-style side conditions as patterns (`Δ.map bang`).
There are three more-typed alternatives.

**(a) Predicate-guarded rules.**

```lean
def F.IsBang : F α → Prop | .bang _ => True | _ => False
def AllBang (Δ : Multiset (F α)) : Prop := ∀ A ∈ Δ, A.IsBang

-- rule:  | bangR {Δ Γ B} (hΔ : AllBang Δ) (hΓ : AllWn Γ) : ILC ι Δ (B ::ₘ Γ) → ILC ι Δ (bang B ::ₘ Γ)

theorem allBang_iff (Δ : Multiset (F α)) :
    AllBang Δ ↔ ∃ Δ' : Multiset (F α), Δ = Δ'.map .bang   -- proved in the sketch
```

The rules are easier to *apply*: you don't have to rewrite a goal context into the form
`_.map bang`. They are slightly harder to *invert*, which is what `allBang_iff` is for.

**(b) Subtypes / structured contexts.** Make the boxed part of a context a separate
component of the sequent:

```lean
structure Ctx (α : Type u) where
  boxed  : Multiset (F α)   -- the formulas under `!` (stored without the `!`)
  linear : Multiset (F α)
def Ctx.flatten (c : Ctx α) : Multiset (F α) := c.boxed.map .bang + c.linear
```

This is the *dual-context* (Andreoli / Barber DILL) presentation: `Θ ; Δ ⊢ Γ`, where `Θ`
is the unrestricted zone. Promotion becomes "linear zone empty", dereliction moves a
formula from `Θ` to `Δ`, and weakening and contraction on `Θ` become implicit. Then:

* unlinearisation `(_)_!` is just "put everything in the unrestricted zone";
* the rules `!W`, `!C` disappear, which shortens the soundness proofs considerably.

This is the most invasive option, and you need a lemma relating it to the one-zone
calculus to stay faithful to the paper's rules.

**(c) Modal-head index on formulas.** Index formulas by their outermost connective class,
e.g. `Formula : Head → Type` with `Head := plain | bang | wn`, so that `Multiset (Formula
.bang)` *is* a `!`-context. This is the most strongly typed option but awkward in
Lean (heterogeneous multisets need `Σ h, Formula h`), and it is rarely worth it.

---

## 5. Variants by an extension index instead of `ι : Bool`

If you keep constructors (no proposal 3), replace `ι : Bool` + `hι : ι = true` with a typed
index for which extensions are present:

```lean
inductive Variant | base | iota
-- | bangWnL {…} : ILC .iota (…) → ILC .iota (…)          -- only typable at `.iota`
```

or parametrise by a set of extensions `(E : Set Ext)` with `(h : .weaklyDistributive ∈ E)`.
This scales if more variants appear (e.g. both ι and an additional classical rule), and
`ILC E → ILC E'` for `E ⊆ E'` is a single lemma. It has the same expressive power as now,
with better documentation value.

---

## 6. A single formula type with fragments

At present the six grammars are six separate inductive types, and the conservative
extensions `ILL.embed`, `IL.embed` are explicit coercions. An alternative is **one**
formula type, indexed by the set of available connectives:

```lean
structure Features where
  bang : Bool
  wn   : Bool
  -- …

inductive Formula (L : Features) (α : Type u) : Type u
  | var    : α → Formula L α
  | tensor : Formula L α → Formula L α → Formula L α
  | bang   : L.bang = true → Formula L α → Formula L α
  | wn     : L.wn   = true → Formula L α → Formula L α

def Formula.lift {L M : Features} (hb : L.bang → M.bang) (hw : L.wn → M.wn) :
    Formula L α → Formula M α     -- the embeddings, defined once
```

(A lighter version: a single big `Formula` type plus a predicate `InFragment L A`, with
each logic's formulas being the subtype `{A // InFragment L A}`.)

* **Pros:** conservative extensions become `lift`, or literally the identity on the
  subtype. Rules shared by several calculi (`&`, `⊕`, `!`, `?`) can be stated once,
  generic in `L`, guarded by features. Combined with proposal 3, a calculus is a pair
  (feature set, rule set).
* **Cons:** the paper's six logics use *different* connectives that look alike (CL's `∧`
  vs ILL's `&`, CL's `⇛` vs CLL⁻'s `↬` vs ILLᵉ's defined `⊸`). Merging them in one type
  risks blurring distinctions the paper makes on purpose. Pattern matching with
  feature-proof arguments is also noisier.

---

## 7. Abstracting the succedent shape

LJ/LLJ use `Option F` and the others use `Multiset F`. You could make the shape a
parameter, so that the structural/logical rules shared by single- and multi-succedent
calculi are written once:

```lean
inductive Shape | single | multi
def Succ (F : Type u) : Shape → Type u
  | .single => Option F
  | .multi  => Multiset F

-- or a type class with an embedding into multisets
class Succedent (S : Type u → Type u) where
  toMs {F : Type u} : S F → Multiset F
instance : Succedent Option   := ⟨fun | none => 0 | some a => {a}⟩
instance : Succedent Multiset := ⟨id⟩

-- or a subtype of multisets of size at most one
def AtMostOne (F : Type u) := { Γ : Multiset F // Multiset.card Γ ≤ 1 }
```

The `AtMostOne` subtype makes "LJ sequents are LK sequents" definitional (no `optMs`
conversion), at the price of carrying cardinality proofs through the rules.

---

## 8. (Less typed, for completeness) Lists plus explicit exchange

The opposite direction: contexts as `List`s with the exchange rules XL/XR as actual
constructors (or closure under `List.Perm`). It is closer to the paper's rule figure and
needed if you ever want to count exchange steps or study the "modulo permutations"
statement precisely. Otherwise multisets, as now, are simpler.

---

## Summary / recommendation

| # | Change | Main gain | Cost |
|---|--------|-----------|------|
| 1 | `Sequent` structure + `⊢` notation | readability, translations as sequent maps | low |
| 2 | `Type`-valued derivations | proof trees: "same proofs modulo permutation", cut-elimination | medium–high |
| 3 | rules as data, calculi as rule sets | ILC ⊆ ILC_ι by inclusion; `(_)_!`, `(_)_?` act on rules; shared rule groups | medium |
| 4a | predicate side conditions `AllBang Δ` | easier rule application | low |
| 4b | dual-context `Θ ; Δ ⊢ Γ` | no `!W`/`!C`, simpler soundness proofs | high |
| 5 | extension index instead of `ι : Bool` | typed variants, scales | low |
| 6 | one formula type with fragments | embeddings become trivial, shared rules | high |
| 7 | abstract succedent shape | share rules between LJ-style and LK-style calculi | medium |

A good incremental path is **1 → 5 → 3**, adding **2** if you want to formalise the
proof-tree-level commutativity from the paper or the cut-elimination theorems behind the
conservativity results.
