# Relevance logic

> "You may only list a premise if you actually use it in your proof."

In proof-theoretic terms this rule forbids **weakening** (adding unused premises) but still
allows **contraction** (using a premise more than once). Relevance logic therefore sits
between intuitionistic linear logic (ILL: no weakening, no contraction) and intuitionistic
logic (IL: both rules).

## Where relevance logic comes from

The references below are standard in the literature on relevance logic. They are cited from
that literature; I did not look them up online for this note.

* **I. E. Orlov (1928)**, "The calculus of compatibility of propositions" (in Russian),
  *Matematicheskii Sbornik* 35. This is the earliest known axiomatisation of what is now
  called a relevance logic (the implication–negation fragment of **R**). It went largely
  unnoticed until much later.
* **Moh Shaw-Kwei (1950)** and **Alonzo Church (1951)**, *The weak theory of implication*.
  These give the implicational fragment **R→**. Church's motivation is exactly the criterion
  quoted above: his deduction theorem only applies to deductions in which **every hypothesis
  is actually used**.
* **W. Ackermann (1956)**, "Begründung einer strengen Implikation", *Journal of Symbolic
  Logic* 21. This paper introduced "strict implication" (strenge Implikation), which became
  the starting point for Anderson and Belnap.
* **A. R. Anderson & N. D. Belnap (1975)**, *Entailment: The Logic of Relevance and
  Necessity*, vol. 1. This book develops the systems **R** and **E** under the name
  relevance logic.

**What is formalised:** Church's 1951 system, because its defining principle is exactly the
rule you described.

## The formalisation (`RequestProject/Relevance/`)

| File | Contents |
| --- | --- |
| `Church.lean` | Formulas `Relevance.Formula` (`X`, `A → B`). Church's Hilbert system `Relevance.Thm`: axioms **I** `A→A`, **B** `(A→B)→((C→A)→(C→B))`, **C** `(A→(B→C))→(B→(A→C))`, **W** `(A→(A→B))→(A→B)`, plus modus ponens. `Relevance.Deriv Γ A`: deductions from a multiset of hypotheses `Γ` in which every hypothesis is used. |
| `Sequent.lean` | The sequent calculus `Relevance.LR` (**LR→**): implicational **LJ** without weakening. Equivalence with Church's system (`LR.iff_thm`, `LR.nil_iff_thm`), equivalence with Church's deductions (`Deriv.iff_LR`), and **Church's relevant deduction theorem** `Deriv.deduction`: `Deriv (A ::ₘ Γ) B ↔ Deriv Γ (A → B)`. |
| `Sugihara.lean` | Soundness for the three-element Sugihara matrix. As consequences: weakening `p → (q → p)` is **not** a theorem (`not_thm_K`, `LR.not_K`), and unused hypotheses are forbidden (`Deriv.weakening_fails`: `p → p` is deducible from no hypotheses but not from the unused hypothesis `q`; `LR.weakening_not_admissible`). |
| `Embeddings.lean` | Maps into the existing diagram: `LR.toLJ` (into **LJ**, i.e. IL) and `LR.toLK` (into **LK**, i.e. CL) preserve provability. They are not conservative (`toIL_not_conservative`, `toCL_not_conservative`): `K` becomes provable. |

In the diagram, relevance logic fits as follows:

```
R→ (no weakening, contraction) ──toIL──▶ IL (LJ)
   │
   └───────────────────────────toCL──▶ CL (LK)
```

Scope: only the implicational fragment **R→** (Church's system) is formalised. The full
logic **R**, with negation, conjunction and disjunction, is not included. Neither is a map
between ILL and **R→**.
