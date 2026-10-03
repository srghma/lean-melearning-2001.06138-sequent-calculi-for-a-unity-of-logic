# A guided tour of `Formulas.lean`, with metaphors

`RequestProject/Logics/Formulas.lean` defines six **grammars**, one per logic in the diagram:

```
ILL      ──Girard's translation──▶  IL
 │ (conservative extension)          │ (conservative extension)
ILLᵉ_ι   ──unlinearisation (_)_!──▶  ILᵉ
 │ classicalisation (_)_?            │ classicalisation (_)_?
CLL⁻     ──unlinearisation (_)_!──▶  CL
```

Each grammar is a Lean `inductive` type. Each **constructor** is one way of building a
formula. This note goes through every constructor and gives it a metaphor. The metaphors
are only aids to intuition. The precise meaning of each connective is fixed by the rules in
`Calculi.lean` (explained in `CALCULI_EXPLAINED.md`).

---

## 0. The two big metaphors

The paper (`ArXivSequentCalculi.tex`) describes its two dimensions this way:

* **Linearity is about resources.** In a linear logic a formula is like a **coin** or an
  **ingredient**: a proof must use each premise **exactly once**. You cannot spend a coin
  twice, and you cannot throw a coin away without saying so.
  *Non-linear* logics (IL, CL, ILᵉ) treat formulas like **facts written on a whiteboard**:
  you can read a fact as often as you like, or not at all.
* **Classicality is about do-overs.** A *classical* logic lets a proof **backtrack**: try
  one answer, and if that fails, go back and try another. Think of a **video game with save
  points**. *Intuitionistic* logics allow this only where it is marked explicitly.

The two **exponentials** make these dimensions visible inside a single formula:

| symbol | name     | metaphor |
|--------|----------|----------|
| `!A`   | of-course | a **photocopier / tap** for `A`: as many copies of `A` as you want, including none |
| `?A`   | why-not   | a **save point** for `A`: you may attempt `A` several times, and only one attempt has to succeed |

*Unlinearisation* `(_)_!` puts an invisible photocopier in front of every assumption.
*Classicalisation* `(_)_?` puts an invisible save point behind every conclusion.

Throughout, `α` is the type of **propositional variables**: the alphabet of atomic
sentence names.

> **Notation warning.** Following the paper, in the linear grammars `⊤` (`top`) is the
> unit of tensor `⊗`, and `1` (`one`) is the unit of with `&`. This is the **reverse** of
> the usual linear-logic notation. The metaphors below follow the convention used in the
> code.

---

## 1. `CL.Formula`: classical logic

`A, B ::= X | tt | ff | A ∧ B | A ∨ B | A ⇛ B`

Picture CL as a **courtroom of eternal facts**. Every statement is either established or
not. Evidence can be photocopied freely (non-linear), and the lawyers may change their
argument as often as they like (classical).

| constructor | reads as | metaphor |
|---|---|---|
| `var x` | `X` | a **named sealed envelope**: an atomic claim whose content we do not look into |
| `tt` | `tt` | the **empty checklist**: always satisfied, nothing to verify |
| `ff` | `ff` | the **fire alarm**: if it is ever genuinely triggered (assumed), the trial is over and anything follows |
| `conj A B` | `A ∧ B` | a **double-sided document** with `A` on one side and `B` on the other. Holding it, you may read either side. Producing it, you must write both sides |
| `disj A B` | `A ∨ B` | a **sealed ballot** with `A` or `B` on it. Whoever uses it must be ready for both outcomes |
| `imp A B` | `A ⇛ B` | a **conditional contract**: "give me `A` and I give you `B`". Because the courtroom is classical, the contract may be honoured by "backtracking" lawyering |

Derived:

* `CL.Formula.neg A := A ⇛ ff`, written `∼A`: "**`A` would set off the fire alarm.**"

---

## 2. `IL.Formula`: intuitionistic logic

`A, B ::= X | ⊤ | ff | A & B | A ∨ B | A ⇒ B`

Picture IL as a **workshop of constructive evidence**. Evidence can still be photocopied
(non-linear), but you must **commit**: no taking back an answer once it is given (no
do-overs). A proof of `A ∨ B` must actually say *which* side holds.

| constructor | reads as | metaphor |
|---|---|---|
| `var x` | `X` | a named sealed envelope |
| `top` | `⊤` | the **empty toolbox**: trivially available, gives you nothing |
| `ff` | `ff` | the **fire alarm**, as in CL |
| `with A B` | `A & B` | a **two-item menu**: whoever holds it chooses `A` or `B`. Whoever offers it must be able to cook both |
| `disj A B` | `A ∨ B` | a **labelled parcel**: it contains either `A` or `B`, and the label honestly tells you which |
| `imp A B` | `A ⇒ B` | a **machine** that turns evidence for `A` into evidence for `B`. It may use its input any number of times |

Derived:

* `IL.Formula.neg A := A ⇒ ff`, written `A⋆`: "**a machine turning `A` into a fire alarm.**"

IL's conjunction is spelled `&` ("with") because Girard's translation sends it to linear
`&`.

---

## 3. `ILL.Formula`: intuitionistic linear logic

`A, B ::= X | ⊤ | A ⊗ B | A & B | A ⊕ B | A ⊸ B | !A`

Now we are in a **market**. Formulas are **goods and money**. Every good you bring to a
transaction must be used **exactly once**. There is still a single customer asking for a
single product (intuitionistic: one conclusion).

| constructor | reads as | metaphor |
|---|---|---|
| `var x` | `X` | a **named commodity** (one apple, one euro, …) |
| `top` | `⊤` | the **empty wallet**: the unit of `⊗`. Paying with it costs nothing and buys nothing |
| `tensor A B` | `A ⊗ B` | **a bag holding both `A` and `B` at the same time**. You get to use both, and you must use both |
| `with A B` | `A & B` | a **restaurant menu**: the kitchen can make `A` or `B`, but **you pick one**, and you get only that one |
| `plus A B` | `A ⊕ B` | a **mystery box**: it contains `A` or `B`, and **the seller decides**. You must be prepared for either |
| `limp A B` | `A ⊸ B` | a **vending machine**: insert exactly one `A`, receive one `B`. The paper calls `⊸` *up-linear implication* to keep it apart from the standard `⊸` of CLL |
| `bang A` | `!A` | a **tap** of `A`: draw zero, one, or many units of `A` whenever you want |

There is no falsity constant in ILL. This is why Girard's translation in `Translations.lean`
is *partial*: it has nothing to send `ff` to. The total version `IL.girardE` lands in ILLᵉ
and sends `ff` to the additive zero `0` (the counterfeit ticket).

---

## 4. `ILLe.Formula`: intuitionistic linear logic extended (ILLᵉ and ILLᵉ_ι)

`A, B ::= X | ⊤ | ⊥ | 1 | 0 | A ⊗ B | A ⅋ B | A & B | A ⊕ B | ¬A | !A | ?A`

This is the **central hub** of the diagram. The market from §3 now allows **several
products on the counter at once** (many formulas on the right of a sequent). It also gets
**save points** `?`, which the classical side needs. ILLᵉ and ILLᵉ_ι share this grammar
and differ only in their rules.

| constructor | reads as | metaphor |
|---|---|---|
| `var x` | `X` | a named commodity |
| `top` | `⊤` | the **empty wallet** (unit of `⊗`), as in ILL |
| `bot` | `⊥` | the **empty output tray** (unit of `⅋`). Producing it delivers nothing |
| `one` | `1` | the **menu with no dishes** (unit of `&`). Offering it costs nothing, so it can be offered in **any** situation and swallows any surrounding context. Think of a **bottomless rubbish chute** on the output side |
| `zero` | `0` | the **counterfeit golden ticket** (unit of `⊕`). It never legitimately exists, so whoever holds one can claim anything |
| `tensor A B` | `A ⊗ B` | a **bag holding both** `A` and `B` |
| `par A B` | `A ⅋ B` | **two parallel production lines**, one for `A` and one for `B`, sharing the work. The paper calls `⅋` "the binary version of `?`": two attempts juggled together, and one of them completes |
| `with A B` | `A & B` | a **menu** (the consumer picks) |
| `plus A B` | `A ⊕ B` | a **mystery box** (the producer picks) |
| `neg A` | `¬A` | an **IOU for `A`**: holding `¬A` on the left is like *owing* an `A` on the right, and vice versa. It is a **mirror across the turnstile**. The paper calls it *up-linear negation* to separate it from the involutive `(_)^⊥` of CLL |
| `bang A` | `!A` | a **tap** of `A` (unlimited copies on the input side) |
| `wn A` | `?A` | a **save point** for producing `A`: you may make many attempts at `A`, or none, and the game only needs one to count |

Derived:

* `ILLe.Formula.limp A B := ¬A ⅋ B`, written `A ⊸ B`: "**either pay off your debt of `A`
  or produce `B`, in parallel**". This is how a vending machine looks once it is
  disassembled into an IOU and an output line.

---

## 5. `ILe.Formula`: intuitionistic logic extended (ILᵉ)

`A, B ::= X | ⊤ | ff | A & B | A ∨ B | A ⇒ B | ?A`

This is the **IL workshop with a few save points installed**. Evidence is still freely
photocopied (non-linear), and do-overs are allowed, but **only where a `?` explicitly marks
them**. Classicalisation of IL-like reasoning takes place here.

| constructor | reads as | metaphor |
|---|---|---|
| `var x` | `X` | a named sealed envelope |
| `top` | `⊤` | the empty toolbox |
| `ff` | `ff` | the fire alarm |
| `with A B` | `A & B` | the two-item menu (consumer's choice) |
| `disj A B` | `A ∨ B` | the labelled parcel |
| `imp A B` | `A ⇒ B` | the reusable machine. In the paper, `A ⇒ B` corresponds to `!A ⊸ B` in the linear world: a vending machine with a tap of `A` plugged in |
| `wn A` | `?A` | a **save point** for `A`: "I will establish `A`, but I keep the right to go back and change my mind". For instance, excluded middle `A ∨ ∼A` is translated roughly to `?(A ∨ ∼A)`, which is provable in ILᵉ: first claim `∼A`, and if someone later produces an `A`, rewind and claim `A` instead |

Derived:

* `ILe.Formula.neg A := A ⇒ ff`, written `A⋆`, as in IL.

---

## 6. `CLLneg.Formula`: classical linear logic negative (CLL⁻)

`A, B ::= X | tt | ⊥ | A ∧ B | A ⊕ B | A ↬ B | !A`

This is the **market with an unlimited rewind button**: resources are still counted
(linear), but every conclusion silently has a save point (classical). The paper designs
CLL⁻ as the **mirror image (dual)** of ILᵉ. ILᵉ is "non-linear but explicitly
do-over-aware". CLL⁻ is "classical but explicitly resource-aware", the awareness coming
from `!`.

| constructor | reads as | metaphor |
|---|---|---|
| `var x` | `X` | a named commodity |
| `tt` | `tt` | the **empty checklist** (classical truth) |
| `bot` | `⊥` | the **empty output tray** |
| `conj A B` | `A ∧ B` | a **menu** (the consumer picks one side). It plays the role of `&`, but is named after CL's `∧`, which it becomes under unlinearisation |
| `plus A B` | `A ⊕ B` | a **mystery box** (the producer picks) |
| `imp A B` | `A ↬ B` | a **classical vending machine**: one `A` in, one `B` out, with classical freedom on the output side |
| `bang A` | `!A` | a **tap** of `A` |

Derived:

* `CLLneg.Formula.neg A := A ↬ ⊥`, written `A⋆`: "**a vending machine that eats an `A`
  and returns an empty tray.**"

---

## 7. The small helper at the end: `optMs`

```lean
def optMs : Option β → Multiset β
```

Intuitionistic sequents (LJ, LLJ) have **at most one** conclusion, so their right-hand side
is an `Option`. `optMs` **pours a cup that holds at most one item into a bag**: `none`
becomes the empty bag and `some b` becomes the one-item bag `{b}`. This lets the
single-conclusion calculi be compared with the multi-conclusion ones. The lemmas
`optMs_none`, `optMs_some` and `optMs_map` say that pouring behaves as expected, including
after relabelling the item with a function `f`.

---

## 8. One picture for the whole diagram

```
          resource-aware (linear)                 resource-blind (non-linear)
          ───────────────────────                 ───────────────────────────
commit    ILL      market, 1 customer   ──────▶   IL    workshop, photocopier
            │                            Girard     │
            ▼                                       ▼
explicit  ILLᵉ_ι   market, many products ─(_)_!─▶ ILᵉ  workshop + explicit save points
save pts    │      + taps ! + save points ?         │
            ▼ (_)_?                                 ▼ (_)_?
rewind    CLL⁻     market with rewind    ─(_)_!─▶  CL   courtroom: photocopy + rewind
always             button everywhere
```

* Going **right** (`(_)_!`): install a photocopier on every input, so resources stop
  mattering.
* Going **down** (`(_)_?`): install a save point on every output, so commitments stop
  mattering.
* The lower square **commutes**: installing photocopiers and then save points gives the same
  result as doing it in the other order. In the project this is the theorem
  `CL.Tbangwn_eq_Twnbang`.
