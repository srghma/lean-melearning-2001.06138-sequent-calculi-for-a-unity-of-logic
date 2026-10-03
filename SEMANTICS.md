# Algebraic and categorical models (`RequestProject/Semantics/`)

All files build without `sorry` and use only the standard axioms.

| Logic | Algebraic model | Categorical model |
|---|---|---|
| Classical (CL, calculus **LK**) | Boolean algebras — `Boolean.lean` | polycategories — `Polycategory.lean`, `Boolean.lean` |
| Intuitionistic (IL) | Heyting algebras, Lindenbaum algebra — `Heyting.lean` | coloured operads (`Heyting.lean`); bicartesian closed categories — `BicartesianClosed.lean` |
| Linear (ILLᵉ, calculus **ILC**) | Girard quantales — `GirardQuantale.lean` | \*-autonomous categories, linear distributions, representable polycategories — `StarAutonomous.lean` |

## 1. Classical logic — `Boolean.lean`
* `CL.Formula.eval`, `CL.Valid`: formulas are evaluated in any Boolean algebra. A sequent `Δ ⊢ Γ` is valid when `⋀⟦Δ⟧ ≤ ⋁⟦Γ⟧`.
* `CL.LK.sound` proves soundness and `CL.LK.complete` proves completeness. Together they give `CL.LK.iff_valid`: **LK ⊢ Δ ⇒ Γ iff the sequent is valid in every Boolean algebra**.
* `CL.Lindenbaum` is the Lindenbaum–Tarski algebra of CL. `CL.Lindenbaum.instBooleanAlgebra` shows it is a Boolean algebra.
* Polycategories: `ThinPolycategory` (identities plus composition along one colour, which has the shape of the cut rule). The other pieces are:
  * `CL.LK.polycategory`: LK-provability as a polycategory;
  * `DistribLattice.toThinPolycategory`: the polycategory of a Boolean algebra;
  * `CL.evalPolyfunctor`: soundness stated as a polyfunctor.

## 2. Intuitionistic logic — `Heyting.lean`, `BicartesianClosed.lean`
**The Lindenbaum algebra (the TODO in the request).** Take the formulas modulo provable equivalence: \(A \sim B\) iff \(A \vdash B\) and \(B \vdash A\). Order the classes by provability, so \([A] \le [B]\) iff \(A \vdash B\). The operations are \([A]\sqcap[B]=[A\mathbin{\&}B]\), \([A]\sqcup[B]=[A\vee B]\), \([A]\Rightarrow[B]=[A\Rightarrow B]\), \(\top=[\top]\) and \(\bot=[\mathrm{ff}]\). In Lean this is `IL.ImpPreorder.Lindenbaum`, which is a quotient by `Antisymmetrization`.

* **LJ is full intuitionistic logic.** `IL.LJ` contains the right weakening `Δ ⊢` / `Δ ⊢ B` (the intuitionistic instance of LK's `WR`), so it proves ex falso `ff ⊢ B` (`IL.LJ.exfalso`). For it:
  * `IL.Lindenbaum.instHeytingAlgebra`: **the Lindenbaum algebra is a Heyting algebra**;
  * `IL.LJ.iff_valid`: **LJ-provability = validity in all Heyting algebras**.
* **Minimal logic, kept for comparison.** `IL.LJm` is LJ without right weakening (the paper's explicit rule figure). It has **no ex falso** (`IL.LJm.not_exfalso`). As a result:
  * `IL.LJm.iff_validG`: LJᵐ is sound and complete for *generalized* Heyting algebras in which `ff` can be any element;
  * `IL.LindenbaumM.instGeneralizedHeytingAlgebra`: its Lindenbaum algebra is a generalized Heyting algebra;
  * `IL.LJm.sound`: LJᵐ is still sound for Heyting algebras; `IL.LJm.toLJ`: every LJᵐ proof is an LJ proof.
* Coloured operads: `ThinColoredOperad`, `IL.LJ.operad` and `IL.evalOperadFunctor`.
* Bicartesian closed categories (`BicartesianClosed.lean`), built from Mathlib's `CartesianMonoidalCategory`, `MonoidalClosed`, binary coproducts and an initial object:
  * `CategoryTheory.PosetReflection.instHeytingAlgebra`: the posetal reflection of a bicartesian closed category is a Heyting algebra;
  * `IL.LJ.sound_bicartesianClosed`: if `A₁,…,Aₙ ⊢ B` is provable, there is a morphism `⟦A₁⟧ ⊗ ⋯ ⊗ ⟦Aₙ⟧ ⟶ ⟦B⟧`. Formulas are interpreted as follows: `&` as the product, `∨` as the coproduct, `⇒` as the exponential, `⊤` as the terminal object and `ff` as the initial object.

## 3. Linear logic — `GirardQuantale.lean`, `StarAutonomous.lean`
* Definitions:
  * `CommQuantale`: a complete lattice with a commutative monoid whose multiplication distributes over arbitrary joins;
  * `GirardQuantale`: a commutative quantale with a dualizing element `d` such that negation `a⊥ = a ⊸ d` satisfies **`a⊥⊥ = a`**;
  * `GirardQuantale.Exponential`: the `!` operator.
* De Morgan laws: `lneg_lneg`, `lneg_sup`, `lneg_inf`, `lneg_one`, `lneg_top`, …
* `ILLe.ILC.sound_girardQuantale`: **soundness of ILC** (classical linear logic with exponentials, the calculus of ILLᵉ) in every Girard quantale with an exponential.
* `GirardQuantale.instOfCompleteBooleanAlgebra`: every complete Boolean algebra is a Girard quantale, which shows the definition is not vacuous.
* \*-autonomous categories:
  * `CategoryTheory.StarAutonomous`: Barr's definition — a symmetric monoidal closed category with a dualizing object, for which `A ⟶ A**` is an isomorphism;
  * `StarAutonomous.linearDistrib` and `linearDistrib'`: the two linear distributions linking `⊗` and `⅋ := (A* ⊗ B*)*`;
  * `GirardQuantale.instStarAutonomous`: **every Girard quantale is a (thin) \*-autonomous category**, which also has all products and coproducts.
* Representability:
  * `GirardQuantale.polycategory_representable`: in a Girard quantale, polymorphisms `Γ → Δ` correspond to morphisms `⊗Γ → ⅋Δ`;
  * `ILLe.ILC.representable`: `Γ ⊢ Δ` is provable in ILC iff `⊗Γ ⊢ ⅋Δ` is.

## Limitations
* The polycategories and operads are **thin**: their hom-sets are propositions. This matches the provability-level calculi of the project, and all coherence laws hold automatically. Proof-relevant polycategories and operads are not formalised.
* For linear logic, soundness only is proved. Completeness, e.g. via phase semantics, is not. The weakly distributive rules of ILC_ι are not covered.
* The two linear distributions are constructed, but the coherence equations of linearly distributive categories are not stated. Soundness of linear logic directly in arbitrary \*-autonomous categories is not formalised; it is done in Girard quantales, which are thin \*-autonomous categories.
* For bicartesian closed categories, soundness is proved; completeness is not. The \(\{\top,\&,\Rightarrow\}\) fragment in plain cartesian closed categories is not treated separately.
