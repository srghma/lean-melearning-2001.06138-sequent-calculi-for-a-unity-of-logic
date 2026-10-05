module

public import RequestProject.Logics.Formulas

/-!
# The six sequent calculi

Sequent calculi embodying the six logics:

* `CL.LK`        — the sequent calculus **LK** for CL (**Section 2.1, Definition 2.4, Figure 1**, PDF pages 8–9);
* `IL.LJ`        — the sequent calculus **LJ** for IL (**Section 2.1, Definition 2.7**, PDF page 8);
* `ILL.LLJ`      — the sequent calculus **LLJ** for ILL (**Section 2.2, Definition 2.13**, PDF page 12);
* `CLL.LLK`      — the sequent calculus **LLK** for CLL (**Section 2.2, Definition 2.3, Figure 2**, PDF pages 10–11);
* `ILLe.ILC ι`   — the sequent calculus **ILC** for ILLᵉ (`ι = false`, **Section 3.1, Definition 3.3, Figure 3**, PDF pages 13–14)
                   and **ILC_ι** for ILLᵉ_ι (`ι = true`, **Section 3.1, Definition 3.4**, PDF page 13, adding the *weakly distributive rules*);
* `ILe.INC`      — the sequent calculus **INC** for ILᵉ (**Section 3.2, Definition 3.12, Figure 4**, PDF pages 20–21);
* `CLLneg.CLC`   — the sequent calculus **CLC** for CLL⁻ (**Section 3.3, Definition 3.20, Figure 5**, PDF pages 25–26).

We formalise *provability*: each calculus is an inductive predicate `Δ ⊢ Γ` on sequents.

## Formalisation conventions

* Contexts are **multisets** of formulas. This absorbs the exchange rules XL and XR of the
  paper (which only permute formulas), so they are not listed as separate rules.
* For the intuitionistic calculi **LJ** and **LLJ**, whose sequents have at most one formula
  on the right, the right-hand side is an `Option`.
* `!Δ` is written `Δ.map .bang` and `?Γ` is written `Γ.map .wn`.
* **LJ** is the sequent calculus for full intuitionistic logic: the rules of LK restricted to
  intuitionistic sequents (as in the prose definition of the source), with `⇒L` in its usual
  form `Δ ⊢ A`, `Δ, B ⊢ C` / `Δ, A ⇒ B ⊢ C`. In particular it contains the right weakening
  `Δ ⊢` / `Δ ⊢ B` (the intuitionistic instance of LK's `WR`), which yields ex falso
  `ff ⊢ B`. (The explicit rule figure of LJ in the source omits this rule; that calculus is
  minimal logic, kept as `IL.LJm` in `RequestProject/Semantics/Heyting.lean`.)

Finally we define the two generic operations on sequent calculi, *unlinearisation* `(_)_!`
and *classicalisation* `(_)_?` (**Section 1.3, Definition 1.1**, PDF page 4).
-/

@[expose] public section

universe u

variable {α : Type u} [DecidableEq α]

/-- Notation for `Finset.insert` mirroring `::ₘ` for multisets. -/
infixr:67 " ::ᵢ " => Insert.insert

/-! ## LK for CL -/

namespace CL

open Formula

/-- The sequent calculus **LK** for classical logic —
**Paper Section 2.1, Definition 2.4, Figure 1** (PDF pages 8–9).
`LK Δ Γ` means the sequent `Δ ⊢ Γ` is provable in LK. -/
inductive LK : Finset (Formula α) → Finset (Formula α) → Prop
  | weakL {Δ Γ : Finset (Formula α)} (A) : LK Δ Γ → LK (A ::ᵢ Δ) Γ
  | weakR {Δ Γ : Finset (Formula α)} (B) : LK Δ Γ → LK Δ (B ::ᵢ Γ)
  -- Contraction rules are absorbed by Finset idempotence (A ::ᵢ A ::ᵢ Δ = A ::ᵢ Δ):
  -- | contrL {Δ Γ : Finset (Formula α)} {A} : LK (A ::ᵢ A ::ᵢ Δ) Γ → LK (A ::ᵢ Δ) Γ
  -- | contrR {Δ Γ : Finset (Formula α)} {B} : LK Δ (B ::ᵢ B ::ᵢ Γ) → LK Δ (B ::ᵢ Γ)
  | id (A) : LK {A} {A}
  | cut {Δ Γ Δ' Γ' : Finset (Formula α)} {B} :
      LK Δ (B ::ᵢ Γ) → LK (B ::ᵢ Δ') Γ' → LK (Δ ∪ Δ') (Γ ∪ Γ')
  | ttL {Δ Γ : Finset (Formula α)} : LK Δ Γ → LK (tt ::ᵢ Δ) Γ
  | ttR : LK ∅ {tt}
  | ffL : LK {ff} ∅
  | ffR {Δ Γ : Finset (Formula α)} : LK Δ Γ → LK Δ (ff ::ᵢ Γ)
  | conjL₁ {Δ Γ : Finset (Formula α)} {A₁} (A₂) : LK (A₁ ::ᵢ Δ) Γ → LK (conj A₁ A₂ ::ᵢ Δ) Γ
  | conjL₂ {Δ Γ : Finset (Formula α)} {A₂} (A₁) : LK (A₂ ::ᵢ Δ) Γ → LK (conj A₁ A₂ ::ᵢ Δ) Γ
  | conjR {Δ Γ : Finset (Formula α)} {B₁ B₂} :
      LK Δ (B₁ ::ᵢ Γ) → LK Δ (B₂ ::ᵢ Γ) → LK Δ (conj B₁ B₂ ::ᵢ Γ)
  | disjL {Δ Γ : Finset (Formula α)} {A₁ A₂} :
      LK (A₁ ::ᵢ Δ) Γ → LK (A₂ ::ᵢ Δ) Γ → LK (disj A₁ A₂ ::ᵢ Δ) Γ
  | disjR₁ {Δ Γ : Finset (Formula α)} {B₁} (B₂) : LK Δ (B₁ ::ᵢ Γ) → LK Δ (disj B₁ B₂ ::ᵢ Γ)
  | disjR₂ {Δ Γ : Finset (Formula α)} {B₂} (B₁) : LK Δ (B₂ ::ᵢ Γ) → LK Δ (disj B₁ B₂ ::ᵢ Γ)
  | impL {Δ Γ : Finset (Formula α)} {A B} : LK Δ (A ::ᵢ Γ) → LK (B ::ᵢ Δ) Γ → LK (imp A B ::ᵢ Δ) Γ
  | impR {Δ Γ : Finset (Formula α)} {A B} : LK (A ::ᵢ Δ) (B ::ᵢ Γ) → LK Δ (imp A B ::ᵢ Γ)

end CL

/-! ## LJ for IL -/

namespace IL

open Formula

/-- The sequent calculus **LJ** for intuitionistic logic —
**Paper Section 2.1, Definition 2.7** (PDF page 8).
`LJ Δ C` means `Δ ⊢ C` is provable, where the right-hand side `C` has at most one formula. -/
inductive LJ : Finset (Formula α) → Option (Formula α) → Prop
  | weakL {Δ : Finset (Formula α)} {C} (A) : LJ Δ C → LJ (A ::ᵢ Δ) C
  -- Contraction rule is absorbed by Finset idempotence (A ::ᵢ A ::ᵢ Δ = A ::ᵢ Δ):
  -- | contrL {Δ : Finset (Formula α)} {C A} : LJ (A ::ᵢ A ::ᵢ Δ) C → LJ (A ::ᵢ Δ) C
  /-- right weakening `Δ ⊢` / `Δ ⊢ B` (the intuitionistic instance of LK's `WR`) -/
  | weakR {Δ : Finset (Formula α)} (B) : LJ Δ none → LJ Δ (some B)
  | id (A) : LJ {A} (some A)
  | cut {Δ Δ' : Finset (Formula α)} {C B} : LJ Δ (some B) → LJ (B ::ᵢ Δ') C → LJ (Δ ∪ Δ') C
  | topL {Δ : Finset (Formula α)} {C} : LJ Δ C → LJ (top ::ᵢ Δ) C
  | topR : LJ ∅ (some top)
  | ffL : LJ {ff} none
  | ffR {Δ : Finset (Formula α)} : LJ Δ none → LJ Δ (some ff)
  | withL₁ {Δ : Finset (Formula α)} {C A₁} (A₂) : LJ (A₁ ::ᵢ Δ) C → LJ («with» A₁ A₂ ::ᵢ Δ) C
  | withL₂ {Δ : Finset (Formula α)} {C A₂} (A₁) : LJ (A₂ ::ᵢ Δ) C → LJ («with» A₁ A₂ ::ᵢ Δ) C
  | withR {Δ : Finset (Formula α)} {B₁ B₂} :
      LJ Δ (some B₁) → LJ Δ (some B₂) → LJ Δ (some («with» B₁ B₂))
  | disjL {Δ : Finset (Formula α)} {C A₁ A₂} :
      LJ (A₁ ::ᵢ Δ) C → LJ (A₂ ::ᵢ Δ) C → LJ (disj A₁ A₂ ::ᵢ Δ) C
  | disjR₁ {Δ : Finset (Formula α)} {B₁} (B₂) : LJ Δ (some B₁) → LJ Δ (some (disj B₁ B₂))
  | disjR₂ {Δ : Finset (Formula α)} {B₂} (B₁) : LJ Δ (some B₂) → LJ Δ (some (disj B₁ B₂))
  | impL {Δ : Finset (Formula α)} {C A B} : LJ Δ (some A) → LJ (B ::ᵢ Δ) C → LJ (imp A B ::ᵢ Δ) C
  | impR {Δ : Finset (Formula α)} {A B} : LJ (A ::ᵢ Δ) (some B) → LJ Δ (some (imp A B))

/-- General Modus Ponens rule: If `Δ ⊢ A ⇒ B`, then `Δ ∪ {A} ⊢ B`. -/
theorem modus_ponens {Δ : Finset (Formula α)} {A B : Formula α} (h : LJ Δ (some (imp A B))) :
    LJ (Δ ∪ {A}) (some B) :=
  LJ.cut h (LJ.impL (LJ.id A) (Finset.pair_comm A B ▸ LJ.weakL A (LJ.id B)))

end IL

/-! ## LLJ for ILL -/

namespace ILL

open Formula

/-- The sequent calculus **LLJ** for intuitionistic linear logic —
**Paper Section 2.2, Definition 2.13** (PDF page 12).
`LLJ Δ C` means `Δ ⊢ C` is provable, where the right-hand side `C` has at most one formula. -/
inductive LLJ : Multiset (Formula α) → Option (Formula α) → Prop
  | id (A) : LLJ {A} (some A)
  | cut {Δ Δ' : Multiset (Formula α)} {C B} : LLJ Δ (some B) → LLJ (B ::ₘ Δ') C → LLJ (Δ + Δ') C
  | topL {Δ : Multiset (Formula α)} {C} : LLJ Δ C → LLJ (top ::ₘ Δ) C
  | topR : LLJ 0 (some top)
  | tensorL {Δ : Multiset (Formula α)} {C A₁ A₂} :
      LLJ (A₁ ::ₘ A₂ ::ₘ Δ) C → LLJ (tensor A₁ A₂ ::ₘ Δ) C
  | tensorR {Δ₁ Δ₂ : Multiset (Formula α)} {B₁ B₂} :
      LLJ Δ₁ (some B₁) → LLJ Δ₂ (some B₂) → LLJ (Δ₁ + Δ₂) (some (tensor B₁ B₂))
  | withL₁ {Δ : Multiset (Formula α)} {C A₁} (A₂) : LLJ (A₁ ::ₘ Δ) C → LLJ («with» A₁ A₂ ::ₘ Δ) C
  | withL₂ {Δ : Multiset (Formula α)} {C A₂} (A₁) : LLJ (A₂ ::ₘ Δ) C → LLJ («with» A₁ A₂ ::ₘ Δ) C
  | withR {Δ : Multiset (Formula α)} {B₁ B₂} :
      LLJ Δ (some B₁) → LLJ Δ (some B₂) → LLJ Δ (some («with» B₁ B₂))
  | plusL {Δ : Multiset (Formula α)} {C A₁ A₂} :
      LLJ (A₁ ::ₘ Δ) C → LLJ (A₂ ::ₘ Δ) C → LLJ (plus A₁ A₂ ::ₘ Δ) C
  | plusR₁ {Δ : Multiset (Formula α)} {B₁} (B₂) : LLJ Δ (some B₁) → LLJ Δ (some (plus B₁ B₂))
  | plusR₂ {Δ : Multiset (Formula α)} {B₂} (B₁) : LLJ Δ (some B₂) → LLJ Δ (some (plus B₁ B₂))
  | bangW {Δ : Multiset (Formula α)} {C} (A) : LLJ Δ C → LLJ (bang A ::ₘ Δ) C
  | bangC {Δ : Multiset (Formula α)} {C A} : LLJ (bang A ::ₘ bang A ::ₘ Δ) C → LLJ (bang A ::ₘ Δ) C
  | bangD {Δ : Multiset (Formula α)} {C A} : LLJ (A ::ₘ Δ) C → LLJ (bang A ::ₘ Δ) C
  | bangR {Δ : Multiset (Formula α)} {B} :
      LLJ (Δ.map bang) (some B) → LLJ (Δ.map bang) (some (bang B))
  | limpL {Δ Γ : Multiset (Formula α)} {C A B} :
      LLJ Δ (some A) → LLJ (B ::ₘ Γ) C → LLJ (limp A B ::ₘ (Δ + Γ)) C
  | limpR {Δ : Multiset (Formula α)} {A B} : LLJ (A ::ₘ Δ) (some B) → LLJ Δ (some (limp A B))

end ILL

/-! ## ILC and ILC_ι for ILLᵉ and ILLᵉ_ι -/

namespace ILLe

open Formula

/-- The sequent calculi **ILC** (`ι = false`, **Paper Section 3.1, Definition 3.3, Figure 3**, PDF pages 13–14) for ILLᵉ
and **ILC_ι** (`ι = true`, **Paper Section 3.1, Definition 3.4**, PDF page 13) for ILLᵉ_ι.
**ILC_ι** additionally has the two *weakly distributive rules* `!?L^{!?}` and `?!R^{!?}`. -/
inductive ILC (ι : Bool) : Multiset (Formula α) → Multiset (Formula α) → Prop
  | bangW {Δ Γ : Multiset (Formula α)} (A) : ILC ι Δ Γ → ILC ι (bang A ::ₘ Δ) Γ
  | wnW {Δ Γ : Multiset (Formula α)} (B) : ILC ι Δ Γ → ILC ι Δ (wn B ::ₘ Γ)
  | bangC {Δ Γ : Multiset (Formula α)} {A} :
      ILC ι (bang A ::ₘ bang A ::ₘ Δ) Γ → ILC ι (bang A ::ₘ Δ) Γ
  | wnC {Δ Γ : Multiset (Formula α)} {B} : ILC ι Δ (wn B ::ₘ wn B ::ₘ Γ) → ILC ι Δ (wn B ::ₘ Γ)
  | bangD {Δ Γ : Multiset (Formula α)} {A} : ILC ι (A ::ₘ Δ) Γ → ILC ι (bang A ::ₘ Δ) Γ
  | wnD {Δ Γ : Multiset (Formula α)} {B} : ILC ι Δ (B ::ₘ Γ) → ILC ι Δ (wn B ::ₘ Γ)
  /-- `?L^{!?}`: `!Δ, A ⊢ ?Γ` / `!Δ, ?A ⊢ ?Γ` -/
  | wnL {Δ Γ : Multiset (Formula α)} {A} :
      ILC ι (A ::ₘ Δ.map bang) (Γ.map wn) → ILC ι (wn A ::ₘ Δ.map bang) (Γ.map wn)
  /-- `!R^{!?}`: `!Δ ⊢ B, ?Γ` / `!Δ ⊢ !B, ?Γ` -/
  | bangR {Δ Γ : Multiset (Formula α)} {B} :
      ILC ι (Δ.map bang) (B ::ₘ Γ.map wn) → ILC ι (Δ.map bang) (bang B ::ₘ Γ.map wn)
  | id (A) : ILC ι {A} {A}
  | cut {Δ Γ Δ' Γ' : Multiset (Formula α)} {B} :
      ILC ι Δ (B ::ₘ Γ) → ILC ι (B ::ₘ Δ') Γ' → ILC ι (Δ + Δ') (Γ + Γ')
  | oneR (Δ Γ) : ILC ι Δ (one ::ₘ Γ)
  | zeroL (Δ Γ) : ILC ι (zero ::ₘ Δ) Γ
  | topL {Δ Γ : Multiset (Formula α)} : ILC ι Δ Γ → ILC ι (top ::ₘ Δ) Γ
  | topR : ILC ι 0 {top}
  | botL : ILC ι {bot} 0
  | botR {Δ Γ : Multiset (Formula α)} : ILC ι Δ Γ → ILC ι Δ (bot ::ₘ Γ)
  | tensorL {Δ Γ : Multiset (Formula α)} {A₁ A₂} :
      ILC ι (A₁ ::ₘ A₂ ::ₘ Δ) Γ → ILC ι (tensor A₁ A₂ ::ₘ Δ) Γ
  | tensorR {Δ₁ Δ₂ Γ₁ Γ₂ : Multiset (Formula α)} {B₁ B₂} :
      ILC ι Δ₁ (B₁ ::ₘ Γ₁) → ILC ι Δ₂ (B₂ ::ₘ Γ₂) →
      ILC ι (Δ₁ + Δ₂) (tensor B₁ B₂ ::ₘ (Γ₁ + Γ₂))
  | withL₁ {Δ Γ : Multiset (Formula α)} {A₁} (A₂) :
      ILC ι (A₁ ::ₘ Δ) Γ → ILC ι («with» A₁ A₂ ::ₘ Δ) Γ
  | withL₂ {Δ Γ : Multiset (Formula α)} {A₂} (A₁) :
      ILC ι (A₂ ::ₘ Δ) Γ → ILC ι («with» A₁ A₂ ::ₘ Δ) Γ
  | withR {Δ Γ : Multiset (Formula α)} {B₁ B₂} :
      ILC ι Δ (B₁ ::ₘ Γ) → ILC ι Δ (B₂ ::ₘ Γ) → ILC ι Δ («with» B₁ B₂ ::ₘ Γ)
  | parL {Δ₁ Δ₂ Γ₁ Γ₂ : Multiset (Formula α)} {A₁ A₂} :
      ILC ι (A₁ ::ₘ Δ₁) Γ₁ → ILC ι (A₂ ::ₘ Δ₂) Γ₂ →
      ILC ι (par A₁ A₂ ::ₘ (Δ₁ + Δ₂)) (Γ₁ + Γ₂)
  | parR {Δ Γ : Multiset (Formula α)} {B₁ B₂} :
      ILC ι Δ (B₁ ::ₘ B₂ ::ₘ Γ) → ILC ι Δ (par B₁ B₂ ::ₘ Γ)
  | plusL {Δ Γ : Multiset (Formula α)} {A₁ A₂} :
      ILC ι (A₁ ::ₘ Δ) Γ → ILC ι (A₂ ::ₘ Δ) Γ → ILC ι (plus A₁ A₂ ::ₘ Δ) Γ
  | plusR₁ {Δ Γ : Multiset (Formula α)} {B₁} (B₂) : ILC ι Δ (B₁ ::ₘ Γ) → ILC ι Δ (plus B₁ B₂ ::ₘ Γ)
  | plusR₂ {Δ Γ : Multiset (Formula α)} {B₂} (B₁) : ILC ι Δ (B₂ ::ₘ Γ) → ILC ι Δ (plus B₁ B₂ ::ₘ Γ)
  | negL {Δ Γ : Multiset (Formula α)} {B} : ILC ι Δ (B ::ₘ Γ) → ILC ι (neg B ::ₘ Δ) Γ
  | negR {Δ Γ : Multiset (Formula α)} {A} : ILC ι (A ::ₘ Δ) Γ → ILC ι Δ (neg A ::ₘ Γ)
  /-- weakly distributive rule `!?L^{!?}` (only in **ILC_ι**):
  `!Δ, !A ⊢ ?Γ` / `!Δ, !?A ⊢ ?Γ` -/
  | bangWnL {Δ Γ : Multiset (Formula α)} {A} (hι : ι = true) :
      ILC ι (bang A ::ₘ Δ.map bang) (Γ.map wn) → ILC ι (bang (wn A) ::ₘ Δ.map bang) (Γ.map wn)
  /-- weakly distributive rule `?!R^{!?}` (only in **ILC_ι**):
  `!Δ ⊢ ?B, ?Γ` / `!Δ ⊢ ?!B, ?Γ` -/
  | wnBangR {Δ Γ : Multiset (Formula α)} {B} (hι : ι = true) :
      ILC ι (Δ.map bang) (wn B ::ₘ Γ.map wn) → ILC ι (Δ.map bang) (wn (bang B) ::ₘ Γ.map wn)

end ILLe

/-! ## LLK for CLL -/

namespace CLL

open ILLe.Formula

/-- The sequent calculus **LLK** for classical linear logic (CLL) —
**Paper Section 2.2, Definition 2.3, Figure 2** (PDF pages 10–11).
`LLK Δ Γ` means the sequent `Δ ⊢ Γ` is provable in LLK.

CLL formulas are `ILLe.Formula α` (= `CLL.Formula α`). -/
inductive LLK : Multiset (Formula α) → Multiset (Formula α) → Prop
  -- Structural rules for ! and ?
  /-- `!W`: weakening on the left with `!A`. -/
  | bangW {Δ Γ : Multiset (Formula α)} (A) : LLK Δ Γ → LLK (bang A ::ₘ Δ) Γ
  /-- `?W`: weakening on the right with `?B`. -/
  | wnW {Δ Γ : Multiset (Formula α)} (B) : LLK Δ Γ → LLK Δ (wn B ::ₘ Γ)
  /-- `!C`: contraction of `!A` on the left. -/
  | bangC {Δ Γ : Multiset (Formula α)} {A} :
      LLK (bang A ::ₘ bang A ::ₘ Δ) Γ → LLK (bang A ::ₘ Δ) Γ
  /-- `?C`: contraction of `?B` on the right. -/
  | wnC {Δ Γ : Multiset (Formula α)} {B} :
      LLK Δ (wn B ::ₘ wn B ::ₘ Γ) → LLK Δ (wn B ::ₘ Γ)
  /-- `!D`: dereliction on the left (`!A` to `A`). -/
  | bangD {Δ Γ : Multiset (Formula α)} {A} : LLK (A ::ₘ Δ) Γ → LLK (bang A ::ₘ Δ) Γ
  /-- `?D`: dereliction on the right (`?B` to `B`). -/
  | wnD {Δ Γ : Multiset (Formula α)} {B} : LLK Δ (B ::ₘ Γ) → LLK Δ (wn B ::ₘ Γ)
  /-- `?L^{!?}` (storage/promotion for `?` on the left):
  `!Δ, A ⊢ ?Γ  ⟹  !Δ, ?A ⊢ ?Γ`. -/
  | wnL {Δ Γ : Multiset (Formula α)} {A} :
      LLK (A ::ₘ Δ.map bang) (Γ.map wn) → LLK (wn A ::ₘ Δ.map bang) (Γ.map wn)
  /-- `!R^{!?}` (storage/promotion for `!` on the right):
  `!Δ ⊢ B, ?Γ  ⟹  !Δ ⊢ !B, ?Γ`. -/
  | bangR {Δ Γ : Multiset (Formula α)} {B} :
      LLK (Δ.map bang) (B ::ₘ Γ.map wn) → LLK (Δ.map bang) (bang B ::ₘ Γ.map wn)
  -- Identity and Cut
  /-- Identity axiom: `A ⊢ A`. -/
  | id (A) : LLK {A} {A}
  /-- Cut rule: `Δ ⊢ B, Γ` and `Δ', B ⊢ Γ'` give `Δ, Δ' ⊢ Γ, Γ'`. -/
  | cut {Δ Γ Δ' Γ' : Multiset (Formula α)} {B} :
      LLK Δ (B ::ₘ Γ) → LLK (B ::ₘ Δ') Γ' → LLK (Δ + Δ') (Γ + Γ')
  -- Units: 1R, 0L, ⊤L, ⊤R, ⊥L, ⊥R
  /-- `1R`: `Δ ⊢ 1, Γ` (axiom). -/
  | oneR (Δ Γ : Multiset (Formula α)) : LLK Δ (one ::ₘ Γ)
  /-- `0L`: `Δ, 0 ⊢ Γ` (axiom). -/
  | zeroL (Δ Γ : Multiset (Formula α)) : LLK (zero ::ₘ Δ) Γ
  /-- `⊤L`: `Δ ⊢ Γ` gives `Δ, ⊤ ⊢ Γ`. -/
  | topL {Δ Γ : Multiset (Formula α)} : LLK Δ Γ → LLK (top ::ₘ Δ) Γ
  /-- `⊤R`: `⊢ ⊤` (axiom). -/
  | topR : LLK 0 {top}
  /-- `⊥L`: `⊥ ⊢` (axiom). -/
  | botL : LLK {bot} 0
  /-- `⊥R`: `Δ ⊢ Γ` gives `Δ ⊢ ⊥, Γ`. -/
  | botR {Δ Γ : Multiset (Formula α)} : LLK Δ Γ → LLK Δ (bot ::ₘ Γ)
  -- Multiplicative conjunction ⊗ (Tensor)
  /-- `⊗L`: `Δ, A₁, A₂ ⊢ Γ` gives `Δ, A₁ ⊗ A₂ ⊢ Γ`. -/
  | tensorL {Δ Γ : Multiset (Formula α)} {A₁ A₂} :
      LLK (A₁ ::ₘ A₂ ::ₘ Δ) Γ → LLK (tensor A₁ A₂ ::ₘ Δ) Γ
  /-- `⊗R` (multiplicative split):
  `Δ₁ ⊢ B₁, Γ₁` and `Δ₂ ⊢ B₂, Γ₂` give `Δ₁, Δ₂ ⊢ B₁ ⊗ B₂, Γ₁, Γ₂`. -/
  | tensorR {Δ₁ Δ₂ Γ₁ Γ₂ : Multiset (Formula α)} {B₁ B₂} :
      LLK Δ₁ (B₁ ::ₘ Γ₁) → LLK Δ₂ (B₂ ::ₘ Γ₂) →
      LLK (Δ₁ + Δ₂) (tensor B₁ B₂ ::ₘ (Γ₁ + Γ₂))
  -- Multiplicative disjunction ⅋ (Par)
  /-- `⅋L` (multiplicative split):
  `Δ₁, A₁ ⊢ Γ₁` and `Δ₂, A₂ ⊢ Γ₂` give `Δ₁, Δ₂, A₁ ⅋ A₂ ⊢ Γ₁, Γ₂`. -/
  | parL {Δ₁ Δ₂ Γ₁ Γ₂ : Multiset (Formula α)} {A₁ A₂} :
      LLK (A₁ ::ₘ Δ₁) Γ₁ → LLK (A₂ ::ₘ Δ₂) Γ₂ →
      LLK (par A₁ A₂ ::ₘ (Δ₁ + Δ₂)) (Γ₁ + Γ₂)
  /-- `⅋R`: `Δ ⊢ B₁, B₂, Γ` gives `Δ ⊢ B₁ ⅋ B₂, Γ`. -/
  | parR {Δ Γ : Multiset (Formula α)} {B₁ B₂} :
      LLK Δ (B₁ ::ₘ B₂ ::ₘ Γ) → LLK Δ (par B₁ B₂ ::ₘ Γ)
  -- Additive conjunction & (With)
  /-- `&L₁` (`i = 1`): `Δ, A₁ ⊢ Γ` gives `Δ, A₁ & A₂ ⊢ Γ`. -/
  | withL₁ {Δ Γ : Multiset (Formula α)} {A₁} (A₂) :
      LLK (A₁ ::ₘ Δ) Γ → LLK («with» A₁ A₂ ::ₘ Δ) Γ
  /-- `&L₂` (`i = 2`): `Δ, A₂ ⊢ Γ` gives `Δ, A₁ & A₂ ⊢ Γ`. -/
  | withL₂ {Δ Γ : Multiset (Formula α)} {A₂} (A₁) :
      LLK (A₂ ::ₘ Δ) Γ → LLK («with» A₁ A₂ ::ₘ Δ) Γ
  /-- `&R` (shared context): `Δ ⊢ B₁, Γ` and `Δ ⊢ B₂, Γ` give `Δ ⊢ B₁ & B₂, Γ`. -/
  | withR {Δ Γ : Multiset (Formula α)} {B₁ B₂} :
      LLK Δ (B₁ ::ₘ Γ) → LLK Δ (B₂ ::ₘ Γ) → LLK Δ («with» B₁ B₂ ::ₘ Γ)
  -- Additive disjunction ⊕ (Plus)
  /-- `⊕L` (shared context): `Δ, A₁ ⊢ Γ` and `Δ, A₂ ⊢ Γ` give `Δ, A₁ ⊕ A₂ ⊢ Γ`. -/
  | plusL {Δ Γ : Multiset (Formula α)} {A₁ A₂} :
      LLK (A₁ ::ₘ Δ) Γ → LLK (A₂ ::ₘ Δ) Γ → LLK (plus A₁ A₂ ::ₘ Δ) Γ
  /-- `⊕R₁` (`i = 1`): `Δ ⊢ B₁, Γ` gives `Δ ⊢ B₁ ⊕ B₂, Γ`. -/
  | plusR₁ {Δ Γ : Multiset (Formula α)} {B₁} (B₂) :
      LLK Δ (B₁ ::ₘ Γ) → LLK Δ (plus B₁ B₂ ::ₘ Γ)
  /-- `⊕R₂` (`i = 2`): `Δ ⊢ B₂, Γ` gives `Δ ⊢ B₁ ⊕ B₂, Γ`. -/
  | plusR₂ {Δ Γ : Multiset (Formula α)} {B₂} (B₁) :
      LLK Δ (B₂ ::ₘ Γ) → LLK Δ (plus B₁ B₂ ::ₘ Γ)
  -- Linear negation ¬ / (_)⊥
  /-- `(_)⊥L` / `¬L`: `Δ ⊢ B, Γ` gives `Δ, ¬B ⊢ Γ`. -/
  | negL {Δ Γ : Multiset (Formula α)} {B} :
      LLK Δ (B ::ₘ Γ) → LLK (neg B ::ₘ Δ) Γ
  /-- `(_)⊥R` / `¬R`: `Δ, A ⊢ Γ` gives `Δ ⊢ ¬A, Γ`. -/
  | negR {Δ Γ : Multiset (Formula α)} {A} :
      LLK (A ::ₘ Δ) Γ → LLK Δ (neg A ::ₘ Γ)

end CLL

/-! ## INC for ILᵉ -/

namespace ILe

open Formula

/-- The sequent calculus **INC** for intuitionistic logic extended ILᵉ —
**Paper Section 3.2, Definition 3.12, Figure 4** (PDF pages 20–21). -/
inductive INC : Multiset (Formula α) → Multiset (Formula α) → Prop
  | weakL {Δ Γ : Multiset (Formula α)} (A) : INC Δ Γ → INC (A ::ₘ Δ) Γ
  | wnW {Δ Γ : Multiset (Formula α)} (B) : INC Δ Γ → INC Δ (wn B ::ₘ Γ)
  | contrL {Δ Γ : Multiset (Formula α)} {A} : INC (A ::ₘ A ::ₘ Δ) Γ → INC (A ::ₘ Δ) Γ
  | wnC {Δ Γ : Multiset (Formula α)} {B} : INC Δ (wn B ::ₘ wn B ::ₘ Γ) → INC Δ (wn B ::ₘ Γ)
  | wnD {Δ Γ : Multiset (Formula α)} {B} : INC Δ (B ::ₘ Γ) → INC Δ (wn B ::ₘ Γ)
  /-- `?L^?`: `Δ, A ⊢ ?Γ` / `Δ, ?A ⊢ ?Γ` -/
  | wnL {Δ Γ : Multiset (Formula α)} {A} : INC (A ::ₘ Δ) (Γ.map wn) → INC (wn A ::ₘ Δ) (Γ.map wn)
  | id (A) : INC {A} {A}
  /-- `Cut^?`: `Δ ⊢ ?B, ?Γ`, `Δ', B ⊢ ?Γ'` / `Δ, Δ' ⊢ ?Γ, ?Γ'` -/
  | cut {Δ Γ Δ' Γ' : Multiset (Formula α)} {B} :
      INC Δ (wn B ::ₘ Γ.map wn) → INC (B ::ₘ Δ') (Γ'.map wn) →
      INC (Δ + Δ') (Γ.map wn + Γ'.map wn)
  | topL {Δ Γ : Multiset (Formula α)} : INC Δ Γ → INC (top ::ₘ Δ) Γ
  | topR : INC 0 {top}
  | ffL : INC {ff} 0
  /-- `ffR^?`: `Δ ⊢ ?Γ` / `Δ ⊢ ff, ?Γ` -/
  | ffR {Δ Γ : Multiset (Formula α)} : INC Δ (Γ.map wn) → INC Δ (ff ::ₘ Γ.map wn)
  | withL₁ {Δ Γ : Multiset (Formula α)} {A₁} (A₂) : INC (A₁ ::ₘ Δ) Γ → INC («with» A₁ A₂ ::ₘ Δ) Γ
  | withL₂ {Δ Γ : Multiset (Formula α)} {A₂} (A₁) : INC (A₂ ::ₘ Δ) Γ → INC («with» A₁ A₂ ::ₘ Δ) Γ
  /-- `&R^?` -/
  | withR {Δ Γ : Multiset (Formula α)} {B₁ B₂} : INC Δ (B₁ ::ₘ Γ.map wn) → INC Δ (B₂ ::ₘ Γ.map wn) →
      INC Δ («with» B₁ B₂ ::ₘ Γ.map wn)
  | disjL {Δ Γ : Multiset (Formula α)} {A₁ A₂} :
      INC (A₁ ::ₘ Δ) Γ → INC (A₂ ::ₘ Δ) Γ → INC (disj A₁ A₂ ::ₘ Δ) Γ
  /-- `∨R^?` -/
  | disjR₁ {Δ Γ : Multiset (Formula α)} {B₁} (B₂) :
      INC Δ (B₁ ::ₘ Γ.map wn) → INC Δ (disj B₁ B₂ ::ₘ Γ.map wn)
  /-- `∨R^?` -/
  | disjR₂ {Δ Γ : Multiset (Formula α)} {B₂} (B₁) :
      INC Δ (B₂ ::ₘ Γ.map wn) → INC Δ (disj B₁ B₂ ::ₘ Γ.map wn)
  /-- `⇒L^?`: `Δ, B ⊢ Γ`, `Θ ⊢ A, ?Ξ` / `Δ, Θ, A ⇒ B ⊢ Γ, ?Ξ` -/
  | impL {Δ Γ Θ Ξ : Multiset (Formula α)} {A B} : INC (B ::ₘ Δ) Γ → INC Θ (A ::ₘ Ξ.map wn) →
      INC (imp A B ::ₘ (Δ + Θ)) (Γ + Ξ.map wn)
  /-- `⇒R^?`: `Δ, A ⊢ B, ?Γ` / `Δ ⊢ A ⇒ B, ?Γ` -/
  | impR {Δ Γ : Multiset (Formula α)} {A B} :
      INC (A ::ₘ Δ) (B ::ₘ Γ.map wn) → INC Δ (imp A B ::ₘ Γ.map wn)

end ILe

/-! ## CLC for CLL⁻ -/

namespace CLLneg

open Formula

/-- The sequent calculus **CLC** for classical linear logic negative CLL⁻ —
**Paper Section 3.3, Definition 3.20, Figure 5** (PDF pages 25–26). -/
inductive CLC : Multiset (Formula α) → Multiset (Formula α) → Prop
  | bangW {Δ Γ : Multiset (Formula α)} (A) : CLC Δ Γ → CLC (bang A ::ₘ Δ) Γ
  | weakR {Δ Γ : Multiset (Formula α)} (B) : CLC Δ Γ → CLC Δ (B ::ₘ Γ)
  | bangC {Δ Γ : Multiset (Formula α)} {A} : CLC (bang A ::ₘ bang A ::ₘ Δ) Γ → CLC (bang A ::ₘ Δ) Γ
  | contrR {Δ Γ : Multiset (Formula α)} {B} : CLC Δ (B ::ₘ B ::ₘ Γ) → CLC Δ (B ::ₘ Γ)
  /-- `!D`: `!Δ, A ⊢ Γ` / `!Δ, !A ⊢ Γ` -/
  | bangD {Δ Γ : Multiset (Formula α)} {A} :
      CLC (A ::ₘ Δ.map bang) Γ → CLC (bang A ::ₘ Δ.map bang) Γ
  /-- `!R^!`: `!Δ ⊢ B, Γ` / `!Δ ⊢ !B, Γ` -/
  | bangR {Δ Γ : Multiset (Formula α)} {B} :
      CLC (Δ.map bang) (B ::ₘ Γ) → CLC (Δ.map bang) (bang B ::ₘ Γ)
  | id (A) : CLC {A} {A}
  /-- `Cut^!`: `!Δ ⊢ B, Γ`, `!Δ', !B ⊢ Γ'` / `!Δ, !Δ' ⊢ Γ, Γ'` -/
  | cut {Δ Γ Δ' Γ' : Multiset (Formula α)} {B} :
      CLC (Δ.map bang) (B ::ₘ Γ) → CLC (bang B ::ₘ Δ'.map bang) Γ' →
      CLC (Δ.map bang + Δ'.map bang) (Γ + Γ')
  /-- `ttL^!` -/
  | ttL {Δ Γ : Multiset (Formula α)} : CLC (Δ.map bang) Γ → CLC (tt ::ₘ Δ.map bang) Γ
  | ttR : CLC 0 {tt}
  | botL : CLC {bot} 0
  | botR {Δ Γ : Multiset (Formula α)} : CLC Δ Γ → CLC Δ (bot ::ₘ Γ)
  /-- `∧L^!` -/
  | conjL₁ {Δ Γ : Multiset (Formula α)} {A₁} (A₂) :
      CLC (A₁ ::ₘ Δ.map bang) Γ → CLC (conj A₁ A₂ ::ₘ Δ.map bang) Γ
  /-- `∧L^!` -/
  | conjL₂ {Δ Γ : Multiset (Formula α)} {A₂} (A₁) :
      CLC (A₂ ::ₘ Δ.map bang) Γ → CLC (conj A₁ A₂ ::ₘ Δ.map bang) Γ
  | conjR {Δ Γ : Multiset (Formula α)} {B₁ B₂} :
      CLC Δ (B₁ ::ₘ Γ) → CLC Δ (B₂ ::ₘ Γ) → CLC Δ (conj B₁ B₂ ::ₘ Γ)
  /-- `⊕L^!` -/
  | plusL {Δ Γ : Multiset (Formula α)} {A₁ A₂} :
      CLC (A₁ ::ₘ Δ.map bang) Γ → CLC (A₂ ::ₘ Δ.map bang) Γ →
      CLC (plus A₁ A₂ ::ₘ Δ.map bang) Γ
  | plusR₁ {Δ Γ : Multiset (Formula α)} {B₁} (B₂) : CLC Δ (B₁ ::ₘ Γ) → CLC Δ (plus B₁ B₂ ::ₘ Γ)
  | plusR₂ {Δ Γ : Multiset (Formula α)} {B₂} (B₁) : CLC Δ (B₂ ::ₘ Γ) → CLC Δ (plus B₁ B₂ ::ₘ Γ)
  /-- `↬L^!`: `!Δ, B ⊢ Γ`, `Θ ⊢ A, Ξ` / `!Δ, Θ, !(A ↬ B) ⊢ Γ, Ξ` -/
  | impL {Δ Γ Θ Ξ : Multiset (Formula α)} {A B} : CLC (B ::ₘ Δ.map bang) Γ → CLC Θ (A ::ₘ Ξ) →
      CLC (bang (imp A B) ::ₘ (Δ.map bang + Θ)) (Γ + Ξ)
  /-- `↬R^!`: `!Δ, A ⊢ B, Γ` / `!Δ ⊢ A ↬ B, Γ` -/
  | impR {Δ Γ : Multiset (Formula α)} {A B} :
      CLC (A ::ₘ Δ.map bang) (B ::ₘ Γ) → CLC (Δ.map bang) (imp A B ::ₘ Γ)

end CLLneg

/-! ## Unlinearisation and classicalisation of a sequent calculus -/

/-- **Unlinearisation** `C_!` of a sequent calculus `C` having of-course `!` —
**Paper Section 1.3, Definition 1.1** (PDF page 4):
its provable sequents `Δ ⊢ Γ` are those for which `!Δ ⊢ Γ` is provable in `C`. -/
def Unlinearisation {F : Type u} (bang : F → F) (C : Multiset F → Multiset F → Prop) :
    Multiset F → Multiset F → Prop :=
  fun Δ Γ => C (Δ.map bang) Γ

/-- **Classicalisation** `C_?` of a sequent calculus `C` having why-not `?` —
**Paper Section 1.3, Definition 1.1** (PDF page 4):
its provable sequents `Δ ⊢ Γ` are those for which `Δ ⊢ ?Γ` is provable in `C`. -/
def Classicalisation {F : Type u} (wn : F → F) (C : Multiset F → Multiset F → Prop) :
    Multiset F → Multiset F → Prop :=
  fun Δ Γ => C Δ (Γ.map wn)

end
