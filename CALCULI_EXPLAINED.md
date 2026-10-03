# A guided tour of `Calculi.lean`, with metaphors

`RequestProject/Logics/Calculi.lean` defines **six sequent calculi**, one per logic, plus
two generic operations on calculi:

| Lean name | calculus | logic | sequent shape |
|---|---|---|---|
| `CL.LK` | LK | CL | many ⊢ many |
| `IL.LJ` | LJ | IL | many ⊢ at most one |
| `ILL.LLJ` | LLJ | ILL | many ⊢ at most one |
| `ILLe.ILC ι` | ILC (`ι = false`) / ILC_ι (`ι = true`) | ILLᵉ / ILLᵉ_ι | many ⊢ many |
| `ILe.INC` | INC | ILᵉ | many ⊢ many |
| `CLLneg.CLC` | CLC | CLL⁻ | many ⊢ many |
| `Unlinearisation`, `Classicalisation` | operations `(_)_!`, `(_)_?` | – | – |

Each calculus is an `inductive` **predicate**: `LK Δ Γ` is the proposition "the sequent
`Δ ⊢ Γ` is provable". Each **constructor is one inference rule**: its arguments are the
premises and its result type is the conclusion. The metaphors for the individual formulas
(coins, menus, taps, save points, …) are explained in `FORMULAS_EXPLAINED.md`. This note
explains the rules that act on them.

---

## 0. The workshop metaphor for a sequent

Read a sequent `Δ ⊢ Γ` as a **work order in a workshop**:

* `Δ` (left) is the **bag of supplies on the workbench**,
* `Γ` (right) is the **list of deliverables on the dispatch counter**,
* a **proof** is a **recipe** showing how to turn the supplies into the deliverables
  (in the classical calculi: into *at least one* of the deliverables).

A rule says: "*if you already have recipes for the premises, here is a recipe for the
conclusion*". Reading a rule **from the conclusion up**, it is a step of **planning**:
"to make this, it suffices to make those".

Rules come in four families:

| family | metaphor |
|---|---|
| **identity / cut** | **pipes**: route a supply straight to the counter, or connect two workshops |
| **structural** (weakening, contraction) | **bag management**: throwing away or duplicating items |
| **left rules** (`…L`) | **unpacking** a compound supply on the bench |
| **right rules** (`…R`) | **packaging** a compound deliverable for the counter |

### Lean conventions used everywhere

* Contexts are `Multiset`s: **bags, not queues**. Order does not matter, so the paper's
  exchange rules (XL, XR: "reorder items") are free and not listed.
* `A ::ₘ Δ` is "**drop `A` into the bag `Δ`**", and `Δ + Δ'` is "**pour two bags together**".
* `Δ.map bang` is `!Δ`: "**every supply is a tap**". `Γ.map wn` is `?Γ`: "**every
  deliverable has a save point**". These are the **workshop-wide safety regulations** that
  some rules require.
* An argument written explicitly, like `(A)` in `weakL (A)`, is a formula that appears in the
  conclusion but in no premise, so Lean cannot guess it. You **name the newcomer**.
* In LJ and LLJ the right-hand side is an `Option`: `some C` is a **single delivery slot
  holding `C`**, and `none` is an **empty slot**.

---

## 1. Rule dictionary: metaphors shared by all calculi

The same rule names recur in several calculi. Here is the metaphor once for each name. The
sections after this one list exactly which calculus has which rules, with which
restrictions.

### Pipes

* **`id A`**: `A ⊢ A`. A **straight pipe**: one `A` in, the same `A` out.
* **`cut`**: from `Δ ⊢ B, Γ` and `B, Δ' ⊢ Γ'` infer `Δ, Δ' ⊢ Γ, Γ'`. **Plumbing two
  workshops together**: the first produces an intermediate part `B`, the second consumes
  it, and the part `B` disappears inside the joined factory. Mathematically, this is
  "proving and then using a lemma".

### Bag management (structural rules)

* **Weakening** (`weakL`, `weakR`, `bangW`, `wnW`): **bring an unused item**. A supply you
  never touch, or a deliverable you never promise to make. In non-linear calculi it applies
  to any formula. In linear calculi only **taps** `!A` (left) and **save points** `?B`
  (right) may be weakened: "an unopened tap costs nothing", "an unused save point costs
  nothing".
* **Contraction** (`contrL`, `contrR`, `bangC`, `wnC`): the **photocopier**. Two copies of
  an item may be merged into one, so read bottom-up, an item may be used twice. In linear
  calculi only taps `!A` and save points `?B` may be copied.
* **Dereliction** (`bangD`, `wnD`): **draw a single cup from the tap** (`!A` becomes `A` on
  the left), or **play just one attempt at the save point** (`B` becomes `?B` on the right).

### Exponential "promotion" rules (`bangR`, `wnL`)

* **`!R`** (`bangR`): **build a tap of `B`**. Allowed only if the whole workbench consists of
  taps (`!Δ`, and in ILC also only save points on the counter). A tap must be refillable
  forever, so it can only be built from refillable supplies.
* **`?L`** (`wnL`): **open a save point on the input side**. A supply `?A` may be treated
  as a plain `A`, but only if every deliverable has its own save point, so that the
  do-overs carried by `?A` can be passed on to them.

### Units

* **`ttL` / `topL`**: **throw away an empty wrapper** (`tt` / `⊤` on the bench gives you
  nothing).
* **`ttR` / `topR`**: **deliver an empty box** from an empty bench.
* **`ffL` / `botL`**: **the fire alarm / empty tray as a supply**: having `ff` (or `⊥`) alone
  proves the empty conclusion.
* **`ffR` / `botR`**: **add an empty tray to the counter**: delivering `ff` / `⊥` alongside
  what you already deliver costs nothing.
* **`oneR`** (ILC only): **the bottomless rubbish chute**. `Δ ⊢ 1, Γ` is provable for
  *any* `Δ`, `Γ`: all supplies may be thrown down it.
* **`zeroL`** (ILC only): **the counterfeit golden ticket**. `0, Δ ⊢ Γ` is provable for
  *any* `Δ`, `Γ`.

### Connectives

* **Menu / additive conjunction** (`conj`, `with`):
  * left (`…L₁`, `…L₂`): **order one dish from the menu**, the first or the second.
  * right (`…R`): **open a restaurant offering both dishes**. You must show that the *same*
    supplies `Δ` can cook either one (the two premises share `Δ`).
* **Bag / tensor** (`tensor`):
  * left: **unzip the bag**: `A₁ ⊗ A₂` becomes the two items `A₁`, `A₂`.
  * right: **pack two products made in separate workshops**: the supplies are **split**,
    with `Δ₁` going to `B₁` and `Δ₂` going to `B₂`.
* **Parallel lines / par** (`par`): the mirror image of tensor.
  * right: two deliverables `B₁, B₂` on the counter are **wired into one double line**
    `B₁ ⅋ B₂`.
  * left: a supply `A₁ ⅋ A₂` **splits the workshop in two**, one half handling `A₁` and the
    other `A₂`, each with its own share of supplies and deliverables.
* **Mystery box / ballot / parcel** (`disj`, `plus`):
  * left: **prepare for both outcomes**: one recipe if the box contains `A₁` and one if it
    contains `A₂`, with the same surroundings.
  * right (`…R₁`, `…R₂`): **choose what to put in the box**: deliver `B₁` (or `B₂`) and
    label it as a box.
* **Contract / machine / vending machine** (`imp`, `limp`):
  * right: **build the machine**: if with an extra `A` on the bench you can produce `B`,
    then you can deliver the machine `A → B`.
  * left: **use the machine**: produce an `A` to feed it, then continue with the `B` it
    returns.
* **IOU / up-linear negation** (`neg`, ILC only): **move an item across the turnstile**.
  * `negL`: if you could *deliver* `B`, then *holding* the IOU `¬B` is harmless.
  * `negR`: if you could *use* `A` as a supply, then you can *deliver* the IOU `¬A`.

---

## 2. `CL.LK`: classical logic

**Metaphor: a courtroom with unlimited photocopying and unlimited rewinding.** There are many
supplies and many deliverables, and every structural rule applies to every formula.

| constructor | rule | metaphor / remark |
|---|---|---|
| `weakL (A)` | WL | bring an unused piece of evidence `A` |
| `weakR (B)` | WR | add a claim `B` you never need to defend |
| `contrL` | CL | photocopy evidence `A` |
| `contrR` | CR | defend the claim `B` twice (a classical do-over) |
| `id A` | Id | straight pipe |
| `cut` | Cut | plumbing: prove and use a lemma `B` |
| `ttL` | ttL | discard an empty checklist |
| `ttR` | ttR | `⊢ tt` from nothing |
| `ffL` | ffL | `ff ⊢` : the alarm alone ends the case |
| `ffR` | ffR | add `ff` to the claims for free |
| `conjL₁ (A₂)`, `conjL₂ (A₁)` | ∧L | read one side of the double-sided document |
| `conjR` | ∧R | write both sides, from the same evidence |
| `disjL` | ∨L | prepare for both ballot outcomes |
| `disjR₁ (B₂)`, `disjR₂ (B₁)` | ∨R | fill in the ballot with one side |
| `impL` | ⇛L | use the contract: from `Δ ⊢ A, Γ` and `B, Δ ⊢ Γ` get `A ⇛ B, Δ ⊢ Γ`. Both premises share the same surroundings, which the free photocopier makes harmless |
| `impR` | ⇛R | build the contract: `A, Δ ⊢ B, Γ` gives `Δ ⊢ A ⇛ B, Γ` |

---

## 3. `IL.LJ`: intuitionistic logic

**Metaphor: a workshop with a photocopier for supplies, but a single delivery slot.** You
deliver **one** thing (or nothing), so there is no room for do-overs.

| constructor | rule | metaphor / remark |
|---|---|---|
| `weakL (A)` | WL | bring an unused supply |
| `contrL` | CL | photocopy a supply |
| `weakR (B)` | WR | if the slot is empty (`Δ ⊢`), you may put anything `B` in it (gives ex falso `ff ⊢ B`) |
| `id A` | Id | straight pipe |
| `cut` | Cut | plumbing through the single slot |
| `topL` | ⊤L | discard an empty toolbox |
| `topR` | ⊤R | deliver an empty toolbox from nothing |
| `ffL` | ffL | `ff ⊢` (empty slot) |
| `ffR` | ffR | if the slot is empty (`Δ ⊢`), you may put `ff` in it |
| `withL₁ (A₂)`, `withL₂ (A₁)` | &L | order one dish from the menu |
| `withR` | &R | offer both dishes from the same supplies |
| `disjL` | ∨L | prepare for both labels of the parcel |
| `disjR₁ (B₂)`, `disjR₂ (B₁)` | ∨R | send a parcel honestly labelled `B₁` (or `B₂`) |
| `impL` | ⇒L | use the machine: make an `A` from `Δ`, feed it in, carry on with `B` (and `Δ`) |
| `impR` | ⇒R | build the machine `A ⇒ B` |

> **Right weakening.** With a single slot, right weakening lets you "fill an empty slot with
> anything", proving `ff ⊢ B`. The paper's two descriptions of LJ disagree on this point:
> the prose ("the rules of LK restricted to intuitionistic sequents") includes it, the
> explicit rule figure does not. The project follows the prose, so `IL.LJ` is full
> intuitionistic logic. The figure's version (minimal logic) is kept as `IL.LJm`. Because INC
> has no ex falso, INC is **not** a conservative extension of this LJ
> (`IL.not_INCConservative`). It *is* a conservative extension of the minimal-logic version
> `IL.LJm` (`IL.incConservativeMin`, in `RequestProject/Logics/INCConservative.lean`), so the
> diagram's right-hand top arrow holds with IL presented by `IL.LJm`.

---

## 4. `ILL.LLJ`: intuitionistic linear logic

**Metaphor: a market with one customer.** Every supply must be spent **exactly once**, and
there is a single delivery slot. There is no general weakening or contraction: only
**taps** `!A` may be discarded or copied.

| constructor | rule | metaphor / remark |
|---|---|---|
| `id A` | Id | straight pipe |
| `cut` | Cut | plumbing |
| `topL` | ⊤L | an empty wallet on the bench can be ignored |
| `topR` | ⊤R | deliver an empty wallet from no supplies at all |
| `tensorL` | ⊗L | unzip the bag into its two items |
| `tensorR` | ⊗R | split the supplies `Δ₁ + Δ₂` and make each half of the pair separately |
| `withL₁ (A₂)`, `withL₂ (A₁)` | &L | pick one dish from the menu |
| `withR` | &R | the same supplies `Δ` must cook either dish (only one will be eaten) |
| `plusL` | ⊕L | be ready for both contents of the mystery box |
| `plusR₁ (B₂)`, `plusR₂ (B₁)` | ⊕R | as seller, decide what goes in the box |
| `bangW (A)` | !W | an unopened tap may be ignored |
| `bangC` | !C | a tap can be split into two taps |
| `bangD` | !D | draw one cup from the tap |
| `bangR` | !R | build a tap of `B`, allowed only if the whole bench is taps (`Δ.map bang`) |
| `limpL` | ⊸L | use the vending machine: supplies `Δ` make the coin `A`, and the *other* supplies `Γ`, together with the returned `B`, make `C`. The supplies are **split** |
| `limpR` | ⊸R | build the vending machine `A ⊸ B` |

---

## 5. `ILLe.ILC ι`: ILC and ILC_ι, the hub

**Metaphor: a market with many products on the counter, taps `!` on the input side and save
points `?` on the output side.** The flag `ι : Bool` is a **switch on the wall**: when
`ι = true` two extra machines (the *weakly distributive rules*) are switched on. Their
argument `hι : ι = true` is the **key** that proves the switch is on.

| constructor | rule | metaphor / remark |
|---|---|---|
| `bangW (A)` | !W | ignore an unopened tap |
| `wnW (B)` | ?W | add a save point you never use |
| `bangC` | !C | split one tap into two |
| `wnC` | ?C | merge two save points for `B` into one |
| `bangD` | !D | draw one cup from the tap |
| `wnD` | ?D | make a single attempt at `B` and store it under a save point |
| `wnL` | ?L^{!?} | open a save point on the bench, allowed only if the bench is all taps and the counter is all save points (`!Δ, A ⊢ ?Γ` / `!Δ, ?A ⊢ ?Γ`) |
| `bangR` | !R^{!?} | build a tap, under the same regulations (`!Δ ⊢ B, ?Γ` / `!Δ ⊢ !B, ?Γ`) |
| `id A` | Id | straight pipe |
| `cut` | Cut | plumbing |
| `oneR (Δ Γ)` | 1R | the rubbish chute: `Δ ⊢ 1, Γ`, always |
| `zeroL (Δ Γ)` | 0L | the counterfeit ticket: `0, Δ ⊢ Γ`, always |
| `topL` | ⊤L | ignore an empty wallet |
| `topR` | ⊤R | `⊢ ⊤` |
| `botL` | ⊥L | `⊥ ⊢` |
| `botR` | ⊥R | add an empty tray to the counter |
| `tensorL` | ⊗L | unzip the bag |
| `tensorR` | ⊗R | two separate workshops, each with its own supplies **and** its own other deliverables, pack `B₁ ⊗ B₂` together |
| `withL₁ (A₂)`, `withL₂ (A₁)` | &L | order one dish |
| `withR` | &R | both dishes from the same supplies and the same other deliverables |
| `parL` | ⅋L | the supply `A₁ ⅋ A₂` splits the workshop in two |
| `parR` | ⅋R | wire two deliverables into one double line |
| `plusL` | ⊕L | ready for both contents of the box |
| `plusR₁ (B₂)`, `plusR₂ (B₁)` | ⊕R | choose the content of the box |
| `negL` | ¬L | being able to deliver `B` makes holding an IOU `¬B` harmless |
| `negR` | ¬R | being able to use `A` lets you deliver an IOU `¬A` |
| `bangWnL hι` | !?L^{!?} | **ILC_ι only.** A **tap of save points** `!?A` on the bench may be used as a **tap** `!A`, under the regulations (`!Δ, !A ⊢ ?Γ` / `!Δ, !?A ⊢ ?Γ`) |
| `wnBangR hι` | ?!R^{!?} | **ILC_ι only.** Delivering a **save point** `?B` is enough to deliver a **save point for a tap** `?!B`, under the regulations (`!Δ ⊢ ?B, ?Γ` / `!Δ ⊢ ?!B, ?Γ`) |

The two weakly distributive rules let a tap and a save point "**swap places**" when the
workshop is fully regulated. The project's sanity check `ILLe.ILC.bang_wn_le_wn_bang`
proves `!?A ⊢ ?!A` in ILC_ι. Per the paper, at least one of these rules is needed for the
translations in the diagram to land in the hub.

---

## 6. `ILe.INC`: intuitionistic logic extended

**Metaphor: the IL workshop where you may put several items on the counter, but only
deliverables with a save point `?` are "safe" to leave alongside.** Supplies are freely
photocopied (non-linear). Do-overs are allowed only through explicit save points. Many rules
carry the superscript `?`, meaning that the **other deliverables must all be save points**
(`Γ.map wn`).

| constructor | rule | metaphor / remark |
|---|---|---|
| `weakL (A)` | WL | bring any unused supply (photocopier world) |
| `wnW (B)` | ?W | add an unused save point (only save points, not arbitrary claims) |
| `contrL` | CL | photocopy any supply |
| `wnC` | ?C | merge two save points |
| `wnD` | ?D | store one attempt under a save point |
| `wnL` | ?L^? | open a save point `?A` on the bench, if all deliverables are save points |
| `id A` | Id | straight pipe |
| `cut` | Cut^? | plumbing, but the intermediate part must be delivered under a save point (`Δ ⊢ ?B, ?Γ`), and all other deliverables must be save points |
| `topL` | ⊤L | ignore an empty toolbox |
| `topR` | ⊤R | `⊢ ⊤` |
| `ffL` | ffL | `ff ⊢` |
| `ffR` | ffR^? | add `ff` to a counter holding only save points |
| `withL₁ (A₂)`, `withL₂ (A₁)` | &L | order one dish |
| `withR` | &R^? | offer both dishes, the other deliverables being save points |
| `disjL` | ∨L | prepare for both labels |
| `disjR₁ (B₂)`, `disjR₂ (B₁)` | ∨R^? | send a labelled parcel, the other deliverables being save points |
| `impL` | ⇒L^? | use the machine: one part of the workshop (`Θ`) makes the input `A`, with only save points as side deliverables (`?Ξ`). The other part (`Δ`) continues with the output `B` |
| `impR` | ⇒R^? | build the machine `A ⇒ B`, the other deliverables being save points |

Intuition: in IL you must **commit to one answer**. In INC you may keep **several
candidate answers in play**, provided all but the one you are working on are under save
points: they are **bookmarks** you may return to.

---

## 7. `CLLneg.CLC`: classical linear logic negative

**Metaphor: the mirror image of INC.** Deliverables are freely duplicated and discarded (do-overs
everywhere, i.e. classical), but supplies are **counted** unless they are **taps**. Many
rules carry the superscript `!`, meaning that the **other supplies must all be taps**
(`Δ.map bang`).

| constructor | rule | metaphor / remark |
|---|---|---|
| `bangW (A)` | !W | ignore an unopened tap (only taps, not arbitrary supplies) |
| `weakR (B)` | WR | add any claim you will not defend (rewinding world) |
| `bangC` | !C | split a tap |
| `contrR` | CR | defend a claim twice |
| `bangD` | !D | draw one cup from a tap, if the rest of the bench is taps |
| `bangR` | !R^! | build a tap of `B` from an all-tap bench |
| `id A` | Id | straight pipe |
| `cut` | Cut^! | plumbing, where the intermediate part `B` is consumed as a **tap** `!B`, and both workshops' benches are taps |
| `ttL` | ttL^! | discard an empty checklist from an all-tap bench |
| `ttR` | ttR | `⊢ tt` |
| `botL` | ⊥L | `⊥ ⊢` |
| `botR` | ⊥R | add an empty tray |
| `conjL₁ (A₂)`, `conjL₂ (A₁)` | ∧L^! | order one dish, the rest of the bench being taps |
| `conjR` | ∧R | offer both dishes |
| `plusL` | ⊕L^! | prepare for both contents of the box, the rest of the bench being taps |
| `plusR₁ (B₂)`, `plusR₂ (B₁)` | ⊕R | choose the content of the box |
| `impL` | ↬L^! | use the vending machine, but it must itself come from a **tap** `!(A ↬ B)`: one part `Θ` makes the coin `A` (with side deliverables `Ξ`), and the rest (taps `!Δ` plus `B`) makes `Γ` |
| `impR` | ↬R^! | build the vending machine from an all-tap bench |

Compare with §6: wherever INC asks "**are all the other deliverables save points?**", CLC
asks "**are all the other supplies taps?**". This is the duality between ILᵉ and CLL⁻
described in the paper.

---

## 8. The two generic operations

```lean
def Unlinearisation  (bang : F → F) (C : Multiset F → Multiset F → Prop) := fun Δ Γ => C (Δ.map bang) Γ
def Classicalisation (wn   : F → F) (C : Multiset F → Multiset F → Prop) := fun Δ Γ => C Δ (Γ.map wn)
```

These take a whole calculus `C` and produce a new one:

* **Unlinearisation `C_!`**: "**fit a tap on every supply**". `Δ ⊢ Γ` holds in `C_!`
  exactly when `!Δ ⊢ Γ` holds in `C`. Supplies become freely reusable, so resource
  accounting disappears.
* **Classicalisation `C_?`**: "**put a save point behind every deliverable**". `Δ ⊢ Γ` holds
  in `C_?` exactly when `Δ ⊢ ?Γ` holds in `C`. Every claim may be retried, so commitment
  disappears.

In the diagram:

```
ILC_ι ──(_)_!──▶  INC          (taps on supplies)
  │                │
(_)_?            (_)_?         (save points on deliverables)
  ▼                ▼
 CLC  ──(_)_!──▶   LK
```

Going **right** fits taps, and going **down** fits save points. Because taps live on the
left and save points live on the right, the two operations **do not interfere**, which is
the intuition behind the commuting square. In the project, `CL.LK.routes_agree` shows that
both routes send a provable LK sequent `Δ ⊢ Γ` to the same provable ILC_ι sequent
`!𝒯Δ ⊢ ?𝒯Γ`.
