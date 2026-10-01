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