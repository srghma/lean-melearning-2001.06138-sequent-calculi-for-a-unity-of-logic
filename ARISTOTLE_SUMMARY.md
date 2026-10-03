# Summary of changes for run b3de4eb7-9ebd-4bcb-9cc0-1853b27c95ac
I fixed the broken arrow from IL to ILᵉ. Last run showed that INC is not a conservative extension of full intuitionistic LJ, because INC has no ex falso. I have now proved that INC **is** a conservative extension of minimal LJ (`IL.LJm`), which is the LJ given by the paper's rule figure. The paper's own definitions support this: its INC derives `ff ⊢ ?Γ` but never `ff ⊢ B`. So the right-hand column of the diagram is consistent with IL presented by `IL.LJm`. Before this run, this result was only stated, never proved. The whole project builds with no `sorry`, and the main theorem uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**New results** (`RequestProject/Logics/INCConservative.lean`)
- `IL.incConservativeMin` proves `IL.INCConservativeMin` in full:
  - a sequent of IL formulas is provable in `IL.LJm` iff its embedding is provable in INC;
  - every INC-provable sequent of IL formulas has at most one formula on the right.
- **INC ⟹ LJᵐ** (`IL.INC.toLJm`): INC is sound for generalized Heyting algebras (`ILe.INC.soundG`). Here `ff` is read as an arbitrary element \(f\), `?A` as \((A \Rightarrow f) \Rightarrow f\), and each `?C` on the right as the extra hypothesis \(C \Rightarrow f\) on the left. On IL formulas this is exactly the semantics for which `IL.LJm` is already known to be complete. The same soundness theorem gives "at most one formula on the right" (`IL.INC.card_le_one_of_embed`).
- **LJᵐ ⟹ INC** (`IL.LJm.toINC`): the paper gets this from cut-elimination for LJ, which is not formalised here. INC's own cut rule only applies when the formulas are under `?`. Instead I used Okada's construction:
  - sets of contexts closed under INC provability form a generalized Heyting algebra (new generic file `RequestProject/Semantics/Okada.lean`);
  - `IL.LJm` is sound for this algebra;
  - `IL.okada` turns validity in it back into INC provability.
- Girard's translation for the minimal-logic top-right corner: `IL.LJm.toILC` (into ILC / ILC_ι) and `IL.LJm.toLLJ_of_conservative`.

**Unchanged:** `IL.LJ` is still full intuitionistic logic, and `IL.not_INCConservative` still shows INC is not conservative over it. I updated the docstrings in `Diagram.lean` and the note in `CALCULI_EXPLAINED.md` to say the minimal-logic statement is now proved. `Main.lean` imports the new file. Two rows were added to the Properties table as proved: `IL.incConservativeMin` and `IL.LJm.toILC`.

**Still open:** the left-hand top arrow, that ILC is conservative over LLJ (`ILL.ILCConservative`), is still unproved. Only its "extension" half (`ILL.LLJ.toILC`) is proved. The argument used for the right-hand arrow does not carry over directly, because ILC has `⅋`, `?`, `¬` and allows several formulas on the right.

# Summary of changes for run 3bbafd23-58c5-455d-9ea8-2c5e91d88fb3
I took "fix it" to mean the change offered at the end of the last run: `IL.LJ` is now full intuitionistic logic instead of minimal logic. The whole project builds with no `sorry`, and the new theorems use only the standard axioms. One consequence you should know about: the paper's INC is now provably **not** a conservative extension of LJ.

**What changed**
- **LJ** (`Logics/Calculi.lean`): I added the right-weakening rule `weakR : Δ ⊢ / Δ ⊢ B`. This is the intuitionistic case of LK's WR, and it is what the paper's prose definition of LJ includes. LJ now proves ex falso `ff ⊢ B` (`IL.LJ.exfalso`).
- **Girard's translation** (`Translations.lean`, `SoundTop.lean`): it used to send `ff ↦ !⊥`, which cannot handle ex falso. `IL.girardE` now sends `ff ↦ 0`, as in Girard's original translation, and an empty succedent is read as `0`.
  - `IL.LJ.toILC`: if `Δ ⊢ C` is provable in the new LJ, its translation `!Δ° ⊢ C°` is provable in ILC / ILC_ι.
  - The top square still commutes: on formulas without `ff`, `girardE` agrees with the partial translation `IL.girard` and with `𝒯_! ∘ embed` (`IL.embed_girard_eq_girardE`, `IL.girardE_eq_T_embed`).
  - `IL.LJ.toLLJ_of_conservative` is re-proved. It still assumes ILC is conservative over LLJ, as before. The empty-succedent case can't happen, because LJ can't prove `Δ ⊢` when `Δ` contains no `ff` (`IL.LJ.not_none_of_girard`).
- **The INC arrow no longer works** (`Diagram.lean`):
  - `ILe.INC.not_exfalso`: INC cannot prove `ff ⊢ X`. The proof uses a sound reading of INC in which `ff` and every `?A` count as true.
  - `IL.not_INCConservative`: so the conservativity statement `IL.INCConservative` is false for the new LJ.
  - This is a gap in the paper itself. INC has no ex falso, so the IL → ILᵉ arrow can only be conservative over minimal logic.
  - I recorded the minimal-logic version as `IL.INCConservativeMin`. Like the old statement, it is stated but not proved, because it needs cut-elimination.
- **Minimal logic kept for comparison** (`Semantics/Heyting.lean`): the old calculus is now `IL.LJm`, with all its results under that name (`LJm.not_exfalso`, `LJm.iff_validG`, `LindenbaumM.instGeneralizedHeytingAlgebra`, `LJm.toLJ`). The separate `IL.LJi` was identical to the new LJ, so it is gone and its results have moved:
  - `IL.LJ.iff_valid`: LJ is sound and complete for Heyting algebras.
  - `IL.Lindenbaum.instHeytingAlgebra`: its Lindenbaum algebra is a Heyting algebra.
  - `IL.LJ.operad` and `IL.LJ.sound_bicartesianClosed`: the operad and bicartesian-closed results.

I updated `SEMANTICS.md`, `CALCULI_EXPLAINED.md` and `FORMULAS_EXPLAINED.md` to match. I added the two new main results to the Properties table as proved. Older table rows that mention `IL.LJi` or `IL.LindenbaumI` now refer to `IL.LJ` and `IL.Lindenbaum`; I could not update those rows' names in this run.

## Suggested follow-up

The source paper is inconsistent on this point. Its prose definition of LJ includes right weakening, which gives ex falso, but its INC has no ex falso. So INC can only be a conservative extension of minimal logic, not of full intuitionistic logic, and this is now proved (`IL.not_INCConservative`). If you would rather go back to the paper's rule figure for LJ, which is minimal logic, so the INC arrow is conservative again, I can switch `IL.LJ` back. Or I can keep both and present the diagram with `IL.LJm` on the right-hand column.

# Summary of changes for run d31617b2-d730-4cf9-9da7-3d538ba3e004
I added the three algebraic models and their categorical counterparts in a new directory, `RequestProject/Semantics/`. The whole project builds, the new files contain no `sorry`, and the main theorems use only the standard axioms. `SEMANTICS.md` maps every result to its Lean name.

**1. Classical logic → Boolean algebras; polycategories** (`Boolean.lean`, `Polycategory.lean`)
- `CL.LK.iff_valid`: a sequent `Δ ⊢ Γ` is provable in LK iff \(\bigwedge⟦Δ⟧ \le \bigvee⟦Γ⟧\) in every Boolean algebra. Both soundness and completeness are proved.
- `CL.Lindenbaum.instBooleanAlgebra`: the Lindenbaum algebra of CL is a Boolean algebra.
- I defined polycategories and coloured operads (`ThinPolycategory`, `ThinColoredOperad`). LK provability forms a polycategory, and evaluating formulas in a Boolean algebra preserves it (`CL.evalPolyfunctor`). This is soundness in categorical form.

**2. Intuitionistic logic → Lindenbaum/Heyting algebras; bicartesian closed categories** (`Heyting.lean`, `BicartesianClosed.lean`)
- **Your TODO:** the Lindenbaum algebra is the set of formulas modulo provable equivalence (\(A\sim B\) iff \(A\vdash B\) and \(B\vdash A\)), ordered by provability. Conjunction, disjunction and implication become meet, join and the Heyting implication.
- **Something to be aware of:** the project's `IL.LJ` (which follows the paper's rule figure, without right weakening) has no ex falso. `IL.LJ.not_exfalso` proves that `ff ⊢ X` is not provable, so LJ as it stands is minimal logic.
  - `IL.LJ.iff_validG`: LJ is sound and complete for generalized Heyting algebras in which `ff` can denote any element.
  - `IL.LJ.sound`: LJ is still sound for ordinary Heyting algebras.
- For full intuitionistic logic I added `IL.LJi`, which is LJ plus the rule `Δ ⊢` / `Δ ⊢ B`:
  - `IL.LindenbaumI.instHeytingAlgebra`: its Lindenbaum algebra is a Heyting algebra;
  - `IL.LJi.iff_valid`: soundness and completeness for Heyting algebras.
- Categorical side:
  - `IL.LJi.sound_bicartesianClosed`: in any bicartesian closed category, a provable `A₁,…,Aₙ ⊢ B` gives a morphism `⟦A₁⟧⊗⋯⊗⟦Aₙ⟧ ⟶ ⟦B⟧`;
  - `CategoryTheory.PosetReflection.instHeytingAlgebra`: collapsing such a category to a poset gives a Heyting algebra;
  - LJⁱ provability also forms a coloured operad.

**3. Linear logic → Girard quantales; \*-autonomous categories** (`GirardQuantale.lean`, `StarAutonomous.lean`)
- `GirardQuantale`: a commutative quantale with a dualizing element whose negation satisfies the double-negation law \(a^{\perp\perp}=a\). The De Morgan laws are proved.
- `GirardQuantale.Exponential` adds a `!` operator.
- Every complete Boolean algebra is an example (`instOfCompleteBooleanAlgebra`), so the definition is not vacuous.
- `ILLe.ILC.sound_girardQuantale`: ILC (the calculus for ILLᵉ, with exponentials) is sound in every Girard quantale with `!`.
- `CategoryTheory.StarAutonomous` is Barr's definition: a symmetric monoidal closed category with a dualizing object for which the canonical map `A ⟶ A**` is an isomorphism (the duality involution).
- With `⅋ := (A*⊗B*)*`, I constructed both linear distributions linking `⊗` and `⅋`: `δ : A⊗(B⅋C) ⟶ (A⊗B)⅋C` and `δ'`.
- `GirardQuantale.instStarAutonomous`: every Girard quantale is a \*-autonomous category (with one arrow `a ⟶ b` exactly when `a ≤ b`). It also has all products and coproducts.
- Representability:
  - `ILLe.ILC.representable`: `Γ ⊢ Δ` is provable iff `⊗Γ ⊢ ⅋Δ` is;
  - `polycategory_representable` proves the same correspondence inside a Girard quantale.

**Limits**
- The polycategories and operads only record whether a morphism exists, not which one. This matches the project's calculi, which only record provability.
- For linear logic and for bicartesian closed categories only soundness is proved, not completeness.
- The extra weakly distributive rules of ILC_ι are not covered.
- The coherence equations of linearly distributive categories are not stated.
- Soundness of linear logic directly in arbitrary \*-autonomous categories is not proved; it is proved for Girard quantales.

All new results are recorded in the Properties table, and `RequestProject/Main.lean` imports the new files.

## Suggested follow-up

One thing worth checking: `IL.LJ` as formalised from the paper's rule figure has no right weakening, so it cannot prove ex falso (`ff ⊢ X`). That makes it minimal logic rather than intuitionistic logic, which is proved in `IL.LJ.not_exfalso`. If you meant full intuitionistic logic, I can add a rule such as `Δ ⊢` / `Δ ⊢ B` to `IL.LJ` itself, as `IL.LJi` does, and then re-check the existing diagram results, including the conservativity statement for INC.

# Summary of changes for run cee2cb78-562a-406b-a491-9792d633fd8d
I added relevance logic to the project, based on the paper that introduced the rule you quoted. It is in `RequestProject/Relevance/`, the whole project builds, and the new files contain no `sorry` and use only the standard axioms.

**Which paper.** I picked these references from my knowledge of the literature and did not look them up online, so please check the citations before relying on them:
- **I. E. Orlov (1928)** gave the earliest known axiomatisation of a relevance logic, the implication–negation fragment of what is now called **R**.
- **Ackermann (1956)** and **Anderson & Belnap (*Entailment*, 1975)** developed the field and gave it its name.
- **Alonzo Church, *The weak theory of implication* (1951)** (and, around the same time, Moh Shaw-Kwei, 1950) is the system I formalised. Church's principle is exactly your criterion: his deduction theorem only covers deductions in which every hypothesis is actually used. That means no weakening, but contraction is still allowed.

`RELEVANCE_LOGIC.md` sets out this background and maps each part to its file.

**What is formalised**
- **`Church.lean`:** the formulas (variables and \(A \to B\)) and Church's Hilbert system `Relevance.Thm`. Its axioms are I, B, C and W with modus ponens; the weakening axiom K is absent. It also defines `Relevance.Deriv Γ A`, Church's deductions from a multiset of hypotheses \(Γ\) in which each hypothesis is used.
- **`Sequent.lean`:** the sequent calculus `Relevance.LR`, which is implicational LJ without weakening. Proved:
  - `LR.iff_thm`: \(A_1,\dots,A_n \vdash C\) is provable iff \(A_1 \to (\dots \to (A_n \to C))\) is a theorem.
  - `Deriv.iff_LR`: Church's deductions are exactly the provable LR sequents.
  - `Deriv.deduction`, Church's relevant deduction theorem: `Deriv (A ::ₘ Γ) B ↔ Deriv Γ (A → B)`.
- **`Sugihara.lean`:** soundness for the three-valued Sugihara truth table, used to show weakening fails. For distinct variables \(p, q\):
  - `Deriv.weakening_fails`: \(p \to p\) is deducible from no hypotheses, but not from the unused hypothesis \(q\).
  - `LR.weakening_not_admissible`: the weakening rule is not admissible in LR.
  - `not_thm_K`, `LR.not_K`: \(p \to (q \to p)\) is not a theorem.
- **`Embeddings.lean`:** maps into the existing diagram.
  - `LR.toLJ` and `LR.toLK`: reading relevant implication as intuitionistic or classical implication preserves provability.
  - `toIL_not_conservative`, `toCL_not_conservative`: neither map is conservative, because K becomes provable in IL and CL.

`RequestProject/Main.lean` now imports the new files. All of this is committed and recorded in the Properties table.

**Limits:** only the implicational fragment (Church's system) is formalised. The full Anderson–Belnap logic **R**, with negation, conjunction and disjunction, is not included. Neither is a map between linear logic (ILL) and relevance logic.

# Summary of changes for run 22f73195-d2b3-4f8c-abe8-db6c415fbe27
I wrote two Markdown files at the project root explaining every constructor in `Formulas.lean` and `Calculi.lean` with metaphors. No Lean file was changed. Both files are committed.

**`FORMULAS_EXPLAINED.md`**
- **Framing:** it starts from the paper's own reading of the two dimensions. Linearity is about counting resources; classicality is about "reasoning do-overs". From that, `!A` is a **tap** (as many copies as you want) and `?A` is a **save point** (you may retry, and one attempt has to succeed).
- **The six grammars:** each one gets an overall metaphor:
  - CL: a courtroom where evidence can be photocopied and arguments rewound
  - IL: a workshop where evidence can be photocopied but answers are final
  - ILL: a market with one customer
  - ILLᵉ: a market with many products on the counter, plus taps and save points
  - ILᵉ: the IL workshop with save points installed
  - CLL⁻: a market with a rewind button
- **Constructors:** there is a table for every constructor of each grammar. Examples: `⊗` is a bag holding both items, `&` is a menu where you pick, `⊕` is a mystery box where the seller picks, `⊸` is a vending machine, `¬` is an IOU that moves an item across `⊢`, `1` is a rubbish chute that accepts anything, and `0` is a counterfeit ticket.
- **Other parts:** it covers the derived negations and implication, the `optMs` helper, and a closing picture of the whole diagram. It also flags the paper's swapped notation, where `⊤` is the unit of `⊗` and `1` the unit of `&`.

**`CALCULI_EXPLAINED.md`**
- **Framing:** a sequent `Δ ⊢ Γ` is read as a work order: supplies on the bench, deliverables on the counter, and a proof as the recipe.
- **Lean conventions:** it explains multisets as unordered bags (so exchange comes for free), `::ₘ` and `+`, `Δ.map bang` / `Γ.map wn` as workshop-wide rules that some inference rules require, explicitly named arguments, and the single-slot `Option` used in LJ and LLJ.
- **Rule dictionary:** one metaphor per rule family, for example cut as plumbing two workshops together, contraction as a photocopier, and dereliction as drawing one cup from a tap.
- **Per-calculus tables:** LK, LJ, LLJ, ILC/ILC_ι, INC and CLC each get a table covering every constructor, including its side conditions.
  - In ILC, the `ι` flag is a switch on the wall and `hι` is the key showing it is on.
  - It points out the INC/CLC duality: where INC requires all other deliverables to be save points, CLC requires all other supplies to be taps.
  - It notes why LJ has no right weakening.
- **The two operations:** it ends with `Unlinearisation` (put a tap on every supply) and `Classicalisation` (put a save point behind every deliverable), and why the square commutes.

Where the files refer to project theorems (for example `CL.Tbangwn_eq_Twnbang`, `CL.LK.routes_agree` and `ILLe.ILC.bang_wn_le_wn_bang`), they use the existing declarations. The metaphors are informal aids only; the precise meaning is given by the Lean rules.

# Summary of changes for run 568cc008-f3ad-4fab-a237-f4cdba03a339
Yes, there are several other ways to write the rules, some of them more strongly typed. I wrote them up in `CALCULI_RULE_STYLES.md` at the project root. I did not change `Calculi.lean` or any other Lean file.

The note first describes how the rules are written now: as `Prop`-valued predicates on pairs of multisets. The `!Δ` / `?Γ` side conditions are written as `Δ.map bang` / `Γ.map wn`, and ILC vs ILC_ι is a Boolean flag, with the two extra rules taking a proof `hι : ι = true`. Each proposal below comes with a Lean sketch and its pros and cons:

1. **A `Sequent` structure with `⊢` notation.** Rules read like the paper, and translations become functions on sequents.
2. **Derivations as data (`Type` instead of `Prop`).** You can then talk about individual proof trees (size, whether they use cut), with provability recovered as `Nonempty`. This is what you would need to state the paper's "same proof trees modulo permutation" claim, or to formalise cut-elimination.
3. **Rules as data, with a calculus as a set of rule instances.** ILC ⊆ ILC_ι becomes a plain set inclusion, so the `hι` argument goes away. Groups of rules shared by several calculi are written once, and unlinearisation / classicalisation become maps on rules.
4. **Typed versions of the `!Δ` / `?Γ` conditions:**
   - (a) a predicate such as `AllBang Δ` attached to the rule;
   - (b) a two-zone sequent `Θ ; Δ ⊢ Γ`, where `Θ` holds the `!`-formulas, which removes the `!W` / `!C` rules;
   - (c) formulas indexed by their outermost connective.
5. **A typed variant index instead of `ι : Bool`.**
6. **A single formula type indexed by which connectives are available.** The two conservative-extension embeddings then become trivial. The cost is that connectives the paper keeps apart (for example CL's `∧` vs ILL's `&`) might get blurred.
7. **One rule format for both one-formula-on-the-right calculi (LJ, LLJ) and multi-formula ones**, via `Option`, a type class, or multisets with at most one element.
8. **For completeness, the less typed direction:** lists with explicit exchange rules.

The note ends with a comparison table. It suggests going in the order 1 → 5 → 3, and adding 2 if you want the proof-tree-level results.

The Lean snippets in the note are cut-down sketches. Each was type-checked on its own with the project's Lean and Mathlib versions, but none is part of the project build. The note is committed.

# Summary of changes for run cb4d9b97-4241-4776-a4a3-0010257d7c2b
I formalised the six logics from the diagram in `ArXivSequentCalculi.tex`, their sequent calculi, and the maps between them. I also proved that each translation preserves provability and that the diagram commutes on formulas and at the level of provability. Everything is in `RequestProject/Logics/` and builds with no `sorry`, using only the standard axioms.

**The six logics** (`Formulas.lean`, `Calculi.lean`)
- Grammars: `CL.Formula`, `IL.Formula`, `ILL.Formula`, `ILLe.Formula` (shared by ILLᵉ and ILLᵉ_ι), `ILe.Formula` and `CLLneg.Formula`.
- Calculi, defined as provability predicates: `CL.LK`, `IL.LJ`, `ILL.LLJ`, `ILLe.ILC ι` (ILC when `ι = false`, ILC_ι with the two weakly distributive rules when `ι = true`), `ILe.INC` and `CLLneg.CLC`.
- Unlinearisation (`Δ ⊢ Γ ↦ !Δ ⊢ Γ`) and classicalisation (`Δ ⊢ Γ ↦ Δ ⊢ ?Γ`) are defined as generic operations on sequent calculi.

Formalisation choices you should know about:
- Contexts are multisets, so the exchange rules are built in rather than listed.
- LJ and LLJ have at most one formula on the right, represented as an `Option`.
- The paper's two descriptions of LJ disagree. The prose ("the rules of LK restricted to intuitionistic sequents") includes right weakening and a weak form of `⇒L`. The explicit rule figure (inside an `\if0` block) has the usual `⇒L` and no right weakening. I followed the figure. With right weakening, LJ proves `ff ⊢ B`, which INC cannot, so INC would not be a conservative extension.

**The maps** (`Translations.lean`)
Each arrow is a formula translation going from the arrow's target back into its source:
- `ILL.embed` and `IL.embed`: the two conservative extensions.
- `IL.girard`: Girard's translation. It is partial (returns `none` exactly on formulas containing `ff`), because ILL as defined in the paper has no falsity constant. `IL.girardE` is the total version into ILLᵉ, sending `ff` to `!⊥`.
- `ILe.T` and `CL.Tbang`: unlinearisation 𝒯_!.
- `CLLneg.T` and `CL.Twn`: classicalisation 𝒯_?.

**Proved results**
- **Each translation preserves provability:**
  - `CL.LK.toINC`: LK to INC
  - `ILe.INC.toILC`: INC to ILC_ι
  - `CL.LK.toCLC`: LK to CLC
  - `CLLneg.CLC.toILC`: CLC to ILC_ι
  - `ILL.LLJ.toILC`: LLJ to ILC and ILC_ι
  - `IL.LJ.toILC`: Girard's translation of LJ into ILC
- **The diagram commutes on formulas:** `CL.Tbangwn_eq_Twnbang` shows 𝒯_!∘𝒯_? = 𝒯_?∘𝒯_! for the lower square, and `IL.embed_girard` covers the upper square.
- **Commutativity on sequents:** `CL.LK.toILC_viaILe`, `CL.LK.toILC_viaCLLneg` and `CL.LK.routes_agree` show that both routes send a provable CL sequent to the same provable ILLᵉ_ι sequent `!𝒯Δ ⊢ ?𝒯Γ`.
- **Sanity checks** (`Examples.lean`): the law of excluded middle is provable in LK and its translation is provable in ILC_ι; `!?A ⊢ ?!A` is provable in ILC_ι.

**Not proved**
- The conservativity halves of the vertical top arrows are stated as propositions (`ILL.ILCConservative`, `IL.INCConservative`) but not proved. The paper derives them from cut-elimination theorems, which I did not formalise.
- `IL.LJ.toLLJ_of_conservative` shows Girard's translation sends LJ into LLJ, but only assuming `ILL.ILCConservative` as a hypothesis.
- The paper's claim that the two routes give the same proof trees "modulo permuting axioms and rules" is about individual proofs. I formalised commutativity only at the level of provability.