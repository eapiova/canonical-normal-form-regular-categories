# Plan: Eliminate `TERMINATING` from `CompTheorem.agda` — v28 (Stage 2 revision)

## Summary — what needs to change vs v27

v27 recommended Option (c): rewrite combinators (`compFSigmaClosed`, `compCSigmaClosed`, …) to take `Derivable` + `Acc _<_ (substTaskMeasure dm)` instead of `HypComputable`. Stage 1 landed clean. **Stage 2 reverted** because wrapping `dm` via `substTmRule dm outerFits` increases `derivSize`, so the sub-Acc lemma `substMeasure-cSigma-m<` no longer bounds the resulting derivation.

**v28 refinement** — Stage 2 uses the "pre-computed Computable body" alternative (already noted as the fallback in v27's Stage 2 post-mortem): the combinator accepts a `Computable n (hasTy (B ∷ A ∷ []) m (subTy (liftSubst (liftSubst idSubst)) M))`-shaped body rather than raw `dm` + Acc. The substitution-composition plumbing moves to the CALLER (SCC 2 case body), where an `Acc` on the outer derivation IS available and sub-Acc threading can produce the body Computable by a direct `substDerivTmCompCF` call. **This does not grow scope at the combinator level**, but requires ~1 additional day for path-arithmetic at the ~6 SCC 2 call sites (cSigma / cQtr across `substDerivTmEqCompCF` and `eqSubDerivTmEqCompCF`).

Lexicographic `(tyDepth outputType, derivSize d)` measures were considered (Plan-agent Option C/B) and **rejected** for Stage 2's specific need: `substTmRule dm` preserves output-type depth (by `tyDepth-subTy`) but increases derivSize, so lex first coord is `=` and second is `↑` — lex increases, not decreases.

Other stages of v27 (3, 4, 5, 6) stand unchanged. Plan-B fallback (narrow TERMINATING on a post-SCC-2 layer of ~800 LoC) remains the safety net if Stage 5 reveals a hidden cycle.

## Current status — what landed this session

- **Stage 0 (audit + baseline)**: complete.
- **Stage 1 (`compFSigmaClosed` trivial rewrite)**: complete, typechecks, `agda src/TReg/Everything.agda` passes. `compFSigmaClosed` now takes `Derivable (isType (A ∷ []) B)` directly instead of `HypComputable (suc n)`; 10 call sites updated to pass `hypCompToDerivable …`.
- **New Measure.agda lemmas**: added `substMeasure-cSigma-m<`, `substMeasure-cSigma-M<`, `substMeasure-cQtr-l<`, `substMeasure-cQtr-L<` (four decrease lemmas useful for future stages).
- **Stage 2 (`compCSigmaClosed` / `compCQtrClosed`) attempted and reverted**: the interface change to take `(dm : Derivable …) + Acc` fails because the caller cannot pass the raw outer `dm_orig` (at context `(B_orig ∷ A_orig ∷ gamma)`) into a signature requiring a substituted `dm` (at context `(B_sub ∷ A_sub ∷ [])`). Wrapping via `substTmRule dm_orig <2-binder lift of sigma>` produces the right TYPE but `derivSize (substTmRule dm fits) > derivSize dm`, so the `substMeasure-cSigma-m<` sub-Acc no longer bounds the new derivation. The alternative — passing the pre-computed body `Computable` directly — works for compCSigmaClosed's body but pushes the substitution-composition plumbing onto the caller (SCC 2 case body), which then needs a non-trivial `compSub (sigmaCompSub …) (liftSubst (liftSubst sigma))` construction and associated path arithmetic. **This is much larger than the 1-day estimate.**
- `agda src/TReg/Everything.agda` currently passes with `{-# TERMINATING #-}` still in place (post-revert state).

## Context

Phase A+B+C is complete: `substTaskMeasure d = derivSize d` (in [Measure.agda](src/TReg/Measure.agda)), ~30 per-constructor decrease lemmas, and every **direct-recursive** `<-wellfounded _` call site in the eight SCC 2 workers (`substDerivT*CompCF` / `eqSubDerivT*CompCF`) now uses `(acc rs)` + `rs _ (substMeasure-*<)` sub-Acc threading. `agda src/TReg/Everything.agda` builds clean with `{-# TERMINATING #-}` still in place on the main mutual block.

With `TERMINATING` removed, Agda reports termination failures in exactly **4 functions** in one SCC:
```
substDerivTyCompCF, substDerivTmCompCF, mkHypComputableTy, sigmaTyFamHypClosed
```
Two architectural blockers survive:

1. **Closure-capture** ([CompTheorem.agda:6530-6535](src/TReg/CompTheorem.agda#L6530-L6535)) — `mkHypComputableTy d` builds `hypTyOpen` whose closure body captures `d` and calls `substDerivTyCompCF d fits cFits (<-wellfounded _)`. SCT sees no strict decrease.
2. **Closure-extraction** ([CompTheorem.agda:7266-7271](src/TReg/CompTheorem.agda#L7266-L7271)) — `sigmaTyFamHypClosed (compTyClosedSigma _ _ _ _ dB) = mkHypComputableTy nonemptyNeNil dB`. The extracted `dB` has no SCT relationship to any caller's Acc.

Options (a) (Phase D — Acc field on `hyp*Open`) and (b1) (store Acc alongside raw `Derivable` in `Computable`) are both **structurally dead**: SCT requires strict decrease in the recursive call, but the closure body uses the SAME `d` unchanged, and no amount of Acc threading can manufacture a decrease where none exists.

The user wants a decision between (b2) and (c).

---

## The b2 vs c comparison

### Option (b2) — Make `HypComputable` an inductive data type mirroring type/term structure

Define `HypTy`/`HypTm`/`HypTyEq`/`HypTmEq` inductively, e.g.
```agda
data HypTy (n : ℕ) : Ctx → RawType → Type where
  hypTop   : HypTy n Γ tyTop
  hypSigma : HypTy n Γ A → HypTy n (A ∷ Γ) B → HypTy n Γ (tySigma A B)
  hypEq    : HypTy n Γ A → HypTm n Γ a A → HypTm n Γ b A → HypTy n Γ (tyEq A a b)
  hypQtr   : HypTy n Γ A → HypTy n Γ (tyQtr A)
```
Building a `HypTy` is structural recursion on the derivation; applying a substitution is structural recursion on the `HypTy`. No cycle.

**Fundamental obstacle:** derivations in T*reg are **not in canonical type form**. They can be wrapped in `reflTy`, `symTy`, `transTy`, `weakenTyEq`, `substTyRule`, `substTyEqRule`, `eqSubTyRule`, `conv`, etc. — rules that have no counterpart in a type-indexed inductive `HypTy`. To define a structural translation `Derivable → HypTy`, every such derivation constructor must be handled, which means either:
- adding an "uninterpreted" constructor to `HypTy` that stores a raw `Derivable` (re-introducing the closure-escape problem), or
- first canonicalizing the derivation into a `HypTy`-compatible shape, which itself needs its own termination argument.

**Scope:** new data types (`HypTy`, `HypTm`, `HypTyEq`, `HypTmEq`), a translation `Derivable → Hyp*`, a substitution-application `Hyp* → Computable`, rewrites of every HypComputable consumer. Estimated **2000–3000 LoC**, multi-week effort. Breaks the current level-split invariant and requires re-establishing semantic equivalence with the old `HypComputable`.

**Verdict:** theoretically viable but unreasonably large, and the non-canonical-derivation problem is not cleanly solved — it is relocated.

### Option (c) — Rewrite combinator interfaces to take raw `Derivable` + `Acc`

The current SCC 2 case bodies use `HypComputable` as an indirection to re-enter SCC 2 at a fresh `<-wellfounded _`. The insight: at every such site we already have (or can obtain) the raw derivation, and an `Acc` witness can be threaded from the outer case's `(acc rs)` via a standard sub-Acc lemma.

Rewrite the combinators (`compFSigmaClosed`, `compCSigmaClosed`, `compESigmaClosed`, `compCQtrClosed`, `compEQtrClosed`) to take **`Derivable` + `Acc` instead of `HypComputable`**, and have them call the SCC 2 worker directly (`substDerivT*CompCF` / `eqSubDerivT*CompCF`) with the sub-Acc. This extends the Phase C Acc-threading technique across the combinator boundary.

After the rewrite, the `mkHypComputable*` / `sigmaTyFamHypClosed` / `openHypTm*` / `sigmaBranchTyHypFromMotive` / `hyp*Right` / `compTransTm` / `compSymTm` / `weakenOneOpen*` family is **no longer called from inside the SCC 2 mutual block**. It moves to a post-SCC-2 layer at the bottom of [CompTheorem.agda](src/TReg/CompTheorem.agda) and is called only by external consumers (Structural.agda). In that post-SCC-2 layer SCT accepts the closures as data, so no `TERMINATING` is needed there either.

**Scope:** 5–8 days, ~1500 LoC touched, **no new data types**, no new invariants.

**Key empirical findings that narrow the scope** (from Explore agents + targeted reads):
- `compFSigmaClosed` at [CompTheorem.agda:582-592](src/TReg/CompTheorem.agda#L582-L592) pattern-binds `subB subEqB` but **never uses them** — it only stores `dB`. Trivial rewrite.
- `compF/I/C/E EqClosed` live in [EqComp.agda](src/TReg/EqComp.agda) (not CompTheorem) and don't take HypComputable at all — the tyEq branches have no binder motive.
- Only `sigmaTyFamHypClosed` exists — no `qtrTyFamHypClosed` / `eqTyFamHypClosed`. The qtr path hand-builds `hypTyOpen` closures directly in case bodies ([CompTheorem.agda:3154-3226](src/TReg/CompTheorem.agda#L3154-L3226)), which means Stage 4 replaces those call sites directly without an intermediate extractor.
- The `compM` motive in `compESigmaClosed` is consumed by `compSingleEqSubstTyClosed compM compLeftCorrSym` ([CompTheorem.agda:848](src/TReg/CompTheorem.agda#L848)), a Structural.agda helper taking HypComputable. Stage 4b introduces `...Raw` variants that take raw `Derivable` + `Acc`.

### Recommendation: **Option (c)**.

Less risky than (b2) (no new data types, no new invariants), 3–4× smaller scope, builds on the proven Phase C technique, and has a **narrow-TERMINATING fallback** at Stage 5 that is itself a major improvement over the status quo.

---

## Staged plan for Option (c)

Each stage ends with an `agda` gate. If a stage fails, rollback is trivial (revert the stage's files) and the project remains at the prior stage's state. Stages 1–2 are independent enough to land as separate PRs.

### Stage 0 — Audit & Baseline *(0.5 day)*
- Document every HypComputable producer/consumer in [CompTheorem.agda](src/TReg/CompTheorem.agda) with file:line references (see `Key sites` section below).
- Verify the full list of decrease lemmas in [Measure.agda](src/TReg/Measure.agda) and note which per-constructor lemmas are missing (at least `substMeasure-cSigma-m<`, `substMeasure-cQtr-l<`, `substMeasure-eSigmaEq-dmm<`, `substMeasure-eQtrEq-dll<`, `substMeasure-eQtrEq-dcoh<`, `substMeasure-eQtrEq-dcoh'<` are candidates).
- **Gate:** `agda src/TReg/Everything.agda` baseline still passes. **Rollback:** trivial.

### Stage 1 — Trivial combinator rewrite: `compFSigmaClosed` *(0.5 day)*
- Change `compFSigmaClosed`'s signature to take `Derivable (isType (A ∷ []) B)` instead of `HypComputable`. Body shrinks from 7 lines to 4.
- Update the handful of callers in SCC 2 case bodies and in `sigmaBranchTyHypFromMotive` at [CompTheorem.agda:7119,7209](src/TReg/CompTheorem.agda#L7119) to pass raw `dB` directly.
- **Gate:** `agda src/TReg/CompTheorem.agda` clean, TERMINATING still present. **Rollback:** revert.

### Stage 2 — Computation-rule rewrites: `compCSigmaClosed`, `compCQtrClosed` *(1.5-2 days — revised from v27)*

**v27 approach failed**: taking `Derivable + Acc _<_ (substTaskMeasure dm)` hits a dead end because the caller must wrap `dm_orig` (context `B_orig ∷ A_orig ∷ gamma`) into the substituted context via `substTmRule dm_orig <2-binder lift of sigma>`, and `derivSize (substTmRule dm fits) > derivSize dm`, so `substMeasure-cSigma-m<` no longer bounds the new derivation.

**v28 approach: pre-computed Computable body.** Rewrite `compCSigmaClosed` ([CompTheorem.agda:609-737](src/TReg/CompTheorem.agda#L609-L737)) to take a body Computable directly:
```agda
compCSigmaClosed : ...
  -> Computable n (hasTy (subTy sigma A ∷ []) (subTm (liftSubst sigma) b)
        (subTy (liftSubst sigma) B))   -- THE NEW ARG: pre-computed body
  -> Computable n (termEq [] ... (singleSubst sigma ...))
```
The combinator body's single `sub (sigmaCompSub …) …` invocation at [638](src/TReg/CompTheorem.agda#L638) becomes a `compSubst` call (or direct projection) on the pre-computed body Computable. Rest of the 130-line body is unchanged.

Identical treatment for `compCQtrClosed` ([CompTheorem.agda:1282-1412](src/TReg/CompTheorem.agda#L1282-L1412)).

**The substitution-composition plumbing moves to the CALLER** (SCC 2 case body). At the cSigma case around [CompTheorem.agda:4141](src/TReg/CompTheorem.agda#L4141) and cQtr case around [CompTheorem.agda:3943](src/TReg/CompTheorem.agda#L3943), the caller has `(acc rs) : Acc _<_ (substTaskMeasure (cSigma …))` and a sub-Acc via `rs _ (substMeasure-cSigma-m< …) : Acc _<_ (substTaskMeasure dm)`. The caller builds the body Computable via `substDerivTmCompCF dm (composedFits) (composedCFits) subAcc`, where `composedFits` is a 2-binder lift of the outer `sigma` and `composedCFits` is the corresponding `ComputableFits` (use existing `liftCompFits` / 2-binder analogue if available, else add).

Add missing decrease lemmas `substMeasure-cSigma-m<` and `substMeasure-cQtr-l<` to [Measure.agda](src/TReg/Measure.agda) if not present.

**Scope risk**: the 2-binder lift of a ComputableFits is new plumbing (~30-60 LoC per SCC 2 caller, x6 sites = ~200-360 LoC). If an existing lift helper exists in the current codebase (check for `lift2CompFits` or similar), this is cheaper.

- **Gate:** `agda src/TReg/CompTheorem.agda` clean, TERMINATING still present. **Rollback:** revert both files.

### Stage 3 — Elimination-rule rewrites: `compESigmaClosed`, `compEQtrClosed` *(2 days)*
- Rewrite `compESigmaClosed` ([CompTheorem.agda:739-1243](src/TReg/CompTheorem.agda#L739-L1243)) to take `(dmm' : Derivable ...) → Acc _<_ (substTaskMeasure dmm')` instead of `compmm' : HypComputable`. The single `subEq (sigmaCompSub …) (sigmaCompSub …) …` invocation at [834](src/TReg/CompTheorem.agda#L834) becomes `eqSubDerivTmEqCompCF dmm' branchFitsEq.fitsEq branchFitsEq.compFitsEq accDmm'`. The ~400 LoC of `mkLeftCanon` / `mkRightCanon` / `mkRightCanonSym` machinery is untouched — it operates on raw derivations and closed `Computable` values only.
- **Risk flag:** a small subst/cong bridge (~10 LoC) may be needed because `eqSubDerivTmEqCompCF`'s return type uses `subTy sigma A` while the original `subEq` call used `closedEqSubJ sigma tau J`. These should be definitionally equal but may require a rewrite.
- Same treatment for `compEQtrClosed` ([CompTheorem.agda:1414+](src/TReg/CompTheorem.agda#L1414)). **Scope risk:** `compEQtrClosed` takes two coherence HypComputables (`coh`, `coh'`). Before editing, verify that each of the four closures (`sub`/`subEq` on each of `coh`/`coh'`/`compll'`) is invoked at only one substitution shape per closure; if any is invoked at multiple shapes, the refactor needs multiple Acc parameters and may bloat.
- Keep `compM`/`compL` (the motive HypComputable) unchanged at this stage — they are consumed via `compSingleEqSubstTyClosed` which is defined in Structural.agda and takes HypComputable. Stage 4b changes that.
- Add missing decrease lemmas (`substMeasure-eSigmaEq-dmm<`, `substMeasure-eQtrEq-dll<`, `substMeasure-eQtrEq-dcoh<`, `substMeasure-eQtrEq-dcoh'<`) as needed.
- **Gate:** `agda src/TReg/CompTheorem.agda` clean, TERMINATING still present. **Rollback:** revert CompTheorem.agda and Measure.agda.

### Stage 4 — Binder-helper rewrites + Raw variants *(1.5 days)*

**Stage 4a — delete intermediate HypComputable constructions at SCC 2 case sites.** After Stages 2–3, the combinators no longer need HypComputable for their branch-term arguments. At every SCC 2 case body that currently constructs `compdm`/`compdp`/`compcoh`/`compcoh'`/`compll'` via `openHypTm1`/`openHypTm2`/`openHypTmEq1`/`openHypTmEq2`/`weakenOneOpenTmEq`, delete the construction and pass the raw `dm`/`dp`/`dcoh`/`dcoh'`/`dll'` + sub-Acc directly. Affected case bodies: eSigma / eSigmaEq / cSigma / iSigmaEq / eQtr / eQtrEq / cQtr in `substDerivTm(Eq)CompCF` and `eqSubDerivTm(Eq)CompCF`. Estimated **−150 to −300 LoC of dead closure-building code**.

**Stage 4b — `compSingleEqSubstTyClosedRaw` / `compSingleSubstTyEqClosedRaw`.** Introduce raw variants in [Structural.agda](src/TReg/Structural.agda) that take `(dB : Derivable …) → Acc _<_ (substTaskMeasure dB)` and call `eqSubDerivTyCompCF dB …` / `substDerivTyEqCompCF dB …` directly. Update `compESigmaClosed`/`compEQtrClosed` to use the Raw variant for the motive path. This lets us also drop the `compM`/`compL` HypComputable argument from those combinators, making them take only raw `Derivable` + Acc. The motive HypComputable construction in SCC 2 case bodies ([CompTheorem.agda:3042-3073](src/TReg/CompTheorem.agda#L3042-L3073) and analogs) disappears.

**Stage 4 also orphans** `openHypTm1`/`openHypTm2`/`openHypTmEq1`/`openHypTmEq2`/`sigmaBranchTyHypFromMotive`/`weakenOneOpenTm*` from SCC 2 — they are no longer called from inside the mutual block, only from `hyp*`-building code in the post-SCC-2 layer.

- **Gate:** `agda src/TReg/CompTheorem.agda` clean, TERMINATING still present. **Rollback:** revert CompTheorem.agda, Structural.agda, Measure.agda.

### Stage 5 — Move `mkHypComputable*` layer out of the SCC 2 mutual block *(0.5 day)*
- Grep-verify that after Stage 4 no function inside the SCC 2 mutual block calls `mkHypComputable*`, `sigmaTyFamHypClosed`, `sigmaBranchTyHypFromMotive`, `openHypTm*`, `openHypTmEq*`, `weakenOneOpen*`, `hypTyEqRight`, `hypTmEqRight`, `hypReflTm`, `compTransTm`, `compSymTm`, or `compTransTyOpenHelper`. Expect: every hit is either inside one of these helpers themselves (they may still call each other), or in a post-SCC-2 section (`compTransportFamilyTy*`, `compTransTyClosedAcc`, etc.), or in Structural.agda.
- Physically move the helpers out of the `mutual` block and below SCC 2 (still inside [CompTheorem.agda](src/TReg/CompTheorem.agda)). They can still reference `substDerivT*CompCF` / `eqSubDerivT*CompCF` because the SCC 2 mutual block is now fully defined above them.
- Agda's SCT on the post-SCC-2 layer sees `mkHypComputableTy d = hypTyOpen neq d (λ … → substDerivTyCompCF d … (<-wellfounded _))` as: helper builds a data value containing a closure that calls a lower layer. This is **not** mutual recursion from the post-SCC-2 layer's perspective, and SCT accepts it without TERMINATING.
- **Gate:** `agda src/TReg/CompTheorem.agda` clean with **TERMINATING removed from the SCC 2 mutual block**. (Post-SCC-2 layer should also not need TERMINATING.) **Rollback:** restore TERMINATING; see Plan B below.

### Stage 6 — Restore `--safe` and verify end-to-end *(0.25 day)*
- Delete `{-# TERMINATING #-}` at [CompTheorem.agda:186](src/TReg/CompTheorem.agda#L186).
- Change [CompTheorem.agda:1](src/TReg/CompTheorem.agda#L1) from `{-# OPTIONS #-}` back to `{-# OPTIONS --safe --cubical #-}`. Remove the stale "Cannot use --safe" comment at the top of [SigmaComp.agda:1](src/TReg/SigmaComp.agda#L1), [QtrComp.agda](src/TReg/QtrComp.agda), [EqComp.agda](src/TReg/EqComp.agda), [TopComp.agda](src/TReg/TopComp.agda) if present and restore `--safe`.
- Run `agda src/TReg/Everything.agda`. Expected: clean build, no TERMINATING in TReg.
- Verify with `rg -n '^\{-# TERMINATING #-\}' src/TReg/` — zero hits.

---

## Plan B — Narrow-TERMINATING fallback *(triggered if Stage 5 fails)*

If Stage 5 reveals a hidden cycle — e.g. `compTransTyClosedAcc` calls `hypComputableTyEq` which calls `mkHypComputableTyEq` whose closure body recurses into `substDerivTyEqCompCF` — then removing TERMINATING from the SCC 2 mutual block may fail. The fallback:

- Keep the post-SCC-2 layer (`mkHypComputable*`, `hypComputable*`, `hypTyEqRight`, `hypTmEqRight`, `hypReflTm`, `compTransTyOpenHelper`, `compTransportFamilyTy*`, `compSymTransportFamilyTyEq`, `compTransTm`, `compSymTm`, `weakenOneOpenTy/Tm/TmEq`, `sigmaBranchTyHypFromMotive`, `sigmaTyFamHypClosed`, `sigmaTyFamEqSubClosed`) in a **dedicated narrow `{-# TERMINATING #-}` block of ~800 LoC at the bottom of CompTheorem.agda**.
- The main SCC 2 mutual block (~6000 LoC — the subject reduction machinery) becomes **fully `--safe` and TERMINATING-free**.
- This is a **7× reduction in the audit surface** from the status quo (the current single TERMINATING block is the entire ~8000-LoC mutual). Even without the full removal, this is a qualitatively better outcome.

---

## Key sites for implementation

### Producers (build HypComputable)
- [`mkHypComputableTy`](src/TReg/CompTheorem.agda#L6526), [`mkHypComputableTyEq`](src/TReg/CompTheorem.agda#L6581), [`mkHypComputableTm`](src/TReg/CompTheorem.agda#L6593), [`mkHypComputableTmEq`](src/TReg/CompTheorem.agda#L6606)
- [`hypComputableTy/TyEq/Tm/TmEq`](src/TReg/CompTheorem.agda#L6619) — trivial wrappers
- [`openHypTm1`](src/TReg/CompTheorem.agda#L262), [`openHypTmEq1`](src/TReg/CompTheorem.agda#L326), [`openHypTm2`](src/TReg/CompTheorem.agda#L388), [`openHypTmEq2`](src/TReg/CompTheorem.agda#L465)
- [`sigmaBranchTyHypFromMotive`](src/TReg/CompTheorem.agda#L6965) — ~300 LoC, called at 6 SCC 2 sites
- [`compTransportFamilyTy`](src/TReg/CompTheorem.agda#L6693), [`compTransportFamilyTyEq`](src/TReg/CompTheorem.agda#L6736), [`compSymTransportFamilyTyEq`](src/TReg/CompTheorem.agda#L6792)
- [`hypTyEqRight`](src/TReg/CompTheorem.agda#L6646), [`hypTmEqRight`](src/TReg/CompTheorem.agda#L6666), [`hypReflTm`](src/TReg/CompTheorem.agda#L6682)
- [`compTransTyOpenHelper`](src/TReg/CompTheorem.agda#L6784), [`compTransTm`](src/TReg/CompTheorem.agda#L6811), [`compSymTm`](src/TReg/CompTheorem.agda#L6829)
- [`weakenOneOpenTy`](src/TReg/CompTheorem.agda#L6852), [`weakenOneOpenTm`](src/TReg/CompTheorem.agda#L6881), [`weakenOneOpenTmEq`](src/TReg/CompTheorem.agda#L6915)

### Combinators to rewrite (SCC 2 mutual block)
- **Stage 1**: [`compFSigmaClosed`](src/TReg/CompTheorem.agda#L582) — trivial
- **Stage 2**: [`compCSigmaClosed`](src/TReg/CompTheorem.agda#L609), [`compCQtrClosed`](src/TReg/CompTheorem.agda#L1282)
- **Stage 3**: [`compESigmaClosed`](src/TReg/CompTheorem.agda#L739), [`compEQtrClosed`](src/TReg/CompTheorem.agda#L1414)

### Extractor
- [`sigmaTyFamHypClosed`](src/TReg/CompTheorem.agda#L7266) — called at lines [3038, 3381, 4032, 5326, 5400, 6019, 6160](src/TReg/CompTheorem.agda#L3038); all disappear after Stage 4a

### External consumers (Structural.agda)
- [`compSingleSubstTyEqClosed`](src/TReg/Structural.agda#L295), [`compSingleEqSubstTyClosed`](src/TReg/Structural.agda#L304) — continue to accept HypComputable from downstream callers; Stage 4b adds `...Raw` variants for use from inside the new combinators

### Data type definitions
- [`Computable`](src/TReg/Computability.agda#L36-L180) — unchanged
- [`HypComputable`](src/TReg/Computability.agda#L213-L259) — unchanged (only the producer/consumer layer around it changes)

---

## Risk assessment

| Stage | Most likely failure mode | Mitigation |
|---|---|---|
| 1 | None | N/A |
| 2 | Missing decrease lemma | Add `substMeasure-cSigma-m<` / `substMeasure-cQtr-l<` in Stage 0 |
| 3 | `compEQtrClosed` closures invoked at multiple substitution shapes, requiring multiple Acc parameters | Read the full ~200 LoC body during Stage 0 audit; if multi-shape, plan extra Acc plumbing |
| 3 | Subst/cong bridge needed between `eqSubDerivTmEqCompCF`'s return type and `closedEqSubJ` | ~10 LoC per call site; solvable |
| 4b | `compSingleEqSubstTyClosedRaw` needs additional path-arithmetic helpers for the `(singleSubst t)` / `(singleSubst u)` shape | ~1 day bridging work; not a showstopper |
| 5 | Hidden cycle preventing the layer move | Fall back to Plan B (narrow TERMINATING) — still a major improvement |

**Most critical stage:** Stage 3 (`compEQtrClosed`). **Smallest stages (quick wins):** Stages 1 and 2.

---

## Effort estimate

| Stage | Time | LoC delta | Status |
|---|---|---|---|
| 0 — Audit | 0.5 day | 0 | ✅ done |
| 1 — `compFSigmaClosed` | 0.5 day | −10 | ✅ done (landed this session) |
| 2 — `compCSigmaClosed`, `compCQtrClosed` (**v28 approach**) | 1.5–2 days | +100 (2-binder lift plumbing) / −30 (combinator shrink) | 🔄 to-do (after v27 revert) |
| 3 — `compESigmaClosed`, `compEQtrClosed` | 2 days | +30 bridging / net flat | ⏸ blocked on Stage 2 |
| 4 — Binder helpers + Raw variants | 1.5 days | −400 to −600 (dead code removal) | ⏸ blocked on Stage 3 |
| 5 — Layer move | 0.5 day | 0 (physical move) | ⏸ blocked on Stage 4 |
| 6 — Verify + restore `--safe` | 0.25 day | −2 | ⏸ blocked on Stage 5 |
| **Total** | **7–9 days** (revised from v27's 6–8) | **−300 to −400 net** | |

**Next actionable step**: before starting v28 Stage 2, check whether a 2-binder `ComputableFits` lift helper already exists (look for `lift2CompFits` / `liftCompFitsEq2` / similar in [CompTheorem.agda:1-586](src/TReg/CompTheorem.agda#L1-L586) or [Computability.agda](src/TReg/Computability.agda)). If not, that helper must be added first (~50 LoC, pre-mutual) to avoid Stage 2 ballooning.

---

## Files modified

- [src/TReg/CompTheorem.agda](src/TReg/CompTheorem.agda) — main refactor (all stages)
- [src/TReg/Measure.agda](src/TReg/Measure.agda) — add missing decrease lemmas in Stages 0, 2, 3
- [src/TReg/Structural.agda](src/TReg/Structural.agda) — add `...Raw` variants in Stage 4b
- [src/TReg/SigmaComp.agda](src/TReg/SigmaComp.agda), [src/TReg/QtrComp.agda](src/TReg/QtrComp.agda), [src/TReg/EqComp.agda](src/TReg/EqComp.agda), [src/TReg/TopComp.agda](src/TReg/TopComp.agda) — restore `--safe` pragma in Stage 6

---

## Verification

At each stage:
```bash
agda src/TReg/CompTheorem.agda        # stage-local check
agda src/TReg/Everything.agda          # full project check (end of each stage)
```

Final verification (end of Stage 6):
```bash
agda src/TReg/Everything.agda          # clean build
rg -n '^\{-# TERMINATING #-\}' src/TReg/   # zero hits (or narrow block only, if Plan B)
rg -n '--no-positivity-check|--sized-types|^postulate' src/TReg/   # zero new hits
```

Confirm [Structural.agda:295-313](src/TReg/Structural.agda#L295-L313)'s `compSingleSubstTyEqClosed` / `compSingleEqSubstTyClosed` still typecheck (external HypComputable consumers continue to work because `mkHypComputable*` is still exported from CompTheorem.agda, just at a physically lower position).

---

## Why Option (c) and not Option (b2)

1. **No new data types.** Option (c) rearranges existing code; Option (b2) introduces `HypTy`/`HypTm`/`HypTyEq`/`HypTmEq` plus translation functions plus semantic-equivalence proofs.
2. **Builds on proven technique.** Option (c) extends the Phase C Acc-threading pattern that already works for the direct-recursive cases. Option (b2) introduces a new termination justification via structural recursion on a new type.
3. **3–4× smaller scope.** (c): 6–8 days, ~1500 LoC touched. (b2): 2–3 weeks, ~2500 LoC new + ~2000 LoC rewrites.
4. **Unresolved obstacle in (b2).** Non-canonical derivation rules (`conv`, `reflTy`, `symTy`, `transTy`, `weakenTyEq`, `substTyEqRule`, `eqSubTyRule`, etc.) have no natural type-indexed inductive counterpart. (b2) either admits a raw-`Derivable` constructor in `HypTy` (re-introducing the closure-escape problem) or needs a separate canonicalization layer with its own termination proof.
5. **Level-split preserved.** (c) leaves `HypComputable` at level `(suc n)` and does not disturb the existing level invariants. (b2) would need to re-establish level discipline from scratch.
6. **Incremental deliverables.** Stages 1+2 alone are demonstrable wins (remove ~30 LoC of indirection, improve the Phase C story). If Stage 3 stalls, the project is still strictly better off than the status quo.
7. **Narrow-TERMINATING fallback.** Even if Stage 5 fails, Plan B reduces the TERMINATING audit surface by 7×. (b2) has no such fallback — if the inductive translation doesn't typecheck, the whole option is dead.
