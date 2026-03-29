# Plan: Eliminate TERMINATING from CompTheorem.agda — v13

## Context

CompTheorem.agda has `{-# TERMINATING #-}` on a mutual block. The goal is to remove it and make all modules `--safe`. **v11** rolled back to wrapper records for open Computable constructors and separated Acc workers from the main mutual block.

The current SCC with `computableTheorem dt` at [line 678](src/TReg/CompTheorem.agda#L678) is just `{fitsToCompFits, computableTheorem}`. But applying the naive v12 fix (replace with `substDerivTmComp ... idSubst`) exposes a larger SCC: `{fitsToCompFits, substDerivTyComp, substDerivTmComp, openCompTy, computeWeakenTy, computableTheorem}`, with edges at [line 1961](src/TReg/CompTheorem.agda#L1961), [line 4008](src/TReg/CompTheorem.agda#L4008), and [line 4890](src/TReg/CompTheorem.agda#L4890). The `fitsToCompFits` rewrite only works AFTER two prerequisite decouplings.

---

## Three blockers and their resolutions

### Blocker 1: Closure cycle (openCompTy calls computableTheorem)

**Problem**: `openCompTy d` builds `compTyOpen ... (λ sigma fits → computableTheorem (substTyRule d fits))`. The closure calls `computableTheorem` on `substTyRule d fits` which is NOT a sub-derivation of `d`.

**Resolution**: SCC 2 — a separate family of functions (`substDerivTyComp` etc.) that do structural recursion on the derivation and never call `computableTheorem`. Closures call SCC 2 instead.

### Blocker 2: Partial substitution gap (open premises for closed builders)

**Problem**: Closed builders like `compFSigmaClosed` take `Computable (isType (A ∷ []) B)` (OPEN). SCC 2 can only produce `Computable (isType [] ...)` (CLOSED).

**Resolution**: **openWrap** — directly construct open Computable values by wrapping derivations in `compTyOpen`/`compTmOpen` with closures delegating to SCC 2:

```agda
openWrapTy : Derivable (isType (B ∷ gamma) A) → Computable (isType (B ∷ gamma) A)
openWrapTy d = compTyOpen nonemptyNeNil d
  (λ sigma fits → substDerivTyComp d fits (fitsToCompFits fits))
  (λ sigma tau fitsEq → eqSubDerivTyComp d fitsEq (fitsEqToCompFitsEq fitsEq))
```

Example fix: `computableTheorem (fSigma {gamma = []} dA dB)` currently calls `compFSigmaClosed (computableTheorem dA) (computableTheorem dB)`. In v6: `compFSigmaClosed (computableTheorem dA) (openWrapTy dB)`.

### Blocker 3: compSymTyClosed/compTransTyClosed non-structural recursion on Computable children

**Problem**: `compSymTyClosed` (Sigma case, [CompTheorem.agda:625-634](src/TReg/CompTheorem.agda#L625)) recurses on `compCE` (structurally smaller ✓) but also calls `compSymTy (compTransportFamilyTyEq compCE compDF)` — a freshly constructed value, NOT structurally smaller. Similarly `compTransTyClosed` (Sigma case, [CompTheorem.agda:686-702](src/TReg/CompTheorem.agda#L686)) calls `compTransTyClosed compCE sigmaTyEqCompHead` and `compTransTy compDF compFH` where `compFH` is freshly constructed.

**Resolution**: `Acc`-based internal workers indexed by `tyDepth` of the evaluated left type.

**DONE** — already implemented at [CompTheorem.agda#L715-L890](src/TReg/CompTheorem.agda#L715). Uses `closedTaskMeasure` from [Structural.agda](src/TReg/Structural.agda) (same measure used by `compConvTmClosedAcc`). Acc witnesses use `tyDepth-fst<Sigma`, `tyDepth-snd<Sigma`, `tyDepth-base<Eq`, `tyDepth-base<Qtr` from [Measure.agda](src/TReg/Measure.agda). Wrappers `compSymTyClosed`/`compTransTyClosed` at lines 879-890 live inside the mutual block (fine — they just call `<-wellfounded` from the library).

---

## Detailed architecture

### SCC 2: substDerivXxxComp functions

#### Exact constructor coverage per judgment form

**`substDerivTyComp`** handles `Derivable (isType gamma A)`:
- `fTop wf` — Top-specific
- `fSigma dA dB` — Sigma-specific
- `fEq dA da db` — Eq-specific
- `fQtr dA` — Qtr-specific
- `weakenTy d wf` — structural
- `substTyRule d fits'` — structural

**`substDerivTyEqComp`** handles `Derivable (typeEq gamma A B)`:
- `reflTy d` — structural
- `symTy d` — structural
- `transTy d₁ d₂` — structural
- `fSigmaEq dAC dBD` — Sigma-specific
- `fEqEq dAC dac dbd` — Eq-specific
- `fQtrEq dAB` — Qtr-specific
- `weakenTyEq d wf` — structural
- `substTyEqRule d fits'` — structural
- `eqSubTyRule d fitsEq'` — structural (produces typeEq)
- `eqSubTyEqRule d fitsEq'` — structural (produces typeEq)

**`substDerivTmComp`** handles `Derivable (hasTy gamma t A)`:
- `varStar wf dA` — variable lookup
- `iTop wf` — Top-specific
- `iSigma da db dSigma` — Sigma-specific
- `iEq da` — Eq-specific
- `iQtr da` — Qtr-specific
- `eSigma dM dd dm` — Sigma elimination
- `eQtr dL dp dl dcoh` — Qtr elimination
- `conv d dAB` — structural
- `weakenTm d wf` — structural
- `substTmRule d fits'` — structural

**`substDerivTmEqComp`** handles `Derivable (termEq gamma t u A)`:
- `reflTm d` — structural
- `symTm d` — structural
- `transTm d₁ d₂` — structural
- `convEq d dAB` — structural
- `cTop d` — Top-specific
- `iSigmaEq dac dbd dA dB` — Sigma-specific
- `eSigmaEq dM dd dm` — Sigma-specific
- `cSigma dM db dc dm` — Sigma-specific
- `iEqEq d` — Eq-specific
- `eEqStar dp dA da db` — Eq-specific
- `cEq dp dA da db` — Eq-specific
- `iQtrEq da db` — Qtr-specific
- `eQtrEq dL dp dl dcoh dcoh'` — Qtr-specific
- `cQtr dL da dl dcoh` — Qtr-specific
- `weakenTmEq d wf` — structural
- `substTmEqRule d fits'` — structural
- `eqSubTmRule d fitsEq'` — structural
- `eqSubTmEqRule d fitsEq'` — structural

**eq-substitution variants** (`eqSubDerivTyComp` etc.) handle the same constructors but produce `typeEq`/`termEq` results (the "equal substitution" judgment).

#### FROZEN RULE: Open sub-derivations within SCC 2

When SCC 2 encounters a constructor with an open sub-derivation (e.g., `fSigma dA dB` where `dB : Derivable (isType (A ∷ gamma) B)`), the closure body must recurse on the **original sub-derivation** (`dB`) with composed fits. **No freshly constructed `substTyRule`, `eqSubTyRule`, or similar wrapper may appear inside a closure body.** This is the only termination-safe construction.

**Rejected approach**: `openWrapTy (substTyRule dB extFits)` — closure would call `substDerivTyComp (substTyRule dB extFits) ...` which is NOT structurally smaller than `fSigma dA dB` at the creation site. Agda's termination checker rejects this.

**Correct pattern** (applies uniformly to `fSigma`, `eSigma`, `cSigma`, `eQtr`, `cQtr`, `fSigmaEq`, and all other constructors with extended-context sub-derivations):

```agda
substDerivTyComp (fSigma dA dB) fits cFits =
  let compA = substDerivTyComp dA fits cFits  -- sub-term ✓
  in compFSigmaClosed compA
    (compTyOpen nonemptyNeNil
      (substTyRule dB (liftFitsOne fits (compToDerivable compA)))
      (λ tau fits2 →
        -- fits2 : FitsSubst [] (subTy sigma A ∷ []) tau
        -- Compose fits2 with fits to get FitsSubst [] (A ∷ gamma) composedSub
        let (cFits2 , cCFits2) = composeOneBinder fits fits2 cFits
        in subst (...) (substDerivTyComp dB cFits2 cCFits2))  -- dB: sub-term of fSigma ✓
      (λ tau1 tau2 fitsEq2 →
        let (cFitsEq2 , cCFitsEq2) = composeOneBinderEq fits fitsEq2 cFits
        in subst (...) (eqSubDerivTyComp dB cFitsEq2 cCFitsEq2)))  -- dB: sub-term ✓
```

The closures capture `dB` from the enclosing scope. At the creation site, Agda sees `substDerivTyComp dB ...` where `dB` IS a sub-term of `fSigma dA dB`. ✓

**Two-binder cases** (`eSigma`/`cSigma` branch `dm : Derivable (hasTy (B ∷ A ∷ gamma) m ...)`, `eQtr`/`cQtr` coherence `dcoh : Derivable (termEq (wkTyBy 1 A ∷ A ∷ gamma) ...)`): same pattern but closures use `composeTwoBinders` to compose the outer fits through two binders. For qtr, `composeTwoBinders` is called with `B = wkTyBy 1 A` and `dWkAσ` is built via `weakenTy dAσ wf` + transport along `sym (wkTyLiftSubst sigma A)`. Closures recurse on `dm`/`dcoh` (original sub-derivations). ✓

#### FitsSubst extension helpers (named, exact)

For constructors with extended contexts, we need to build `FitsSubst [] (A ∷ gamma) composedSigma` from components. The exact helpers needed:

**`extendFitsSingle`**: Given `FitsSubst [] gamma sigma`, a term `t`, and `Derivable (hasTy [] t (subTy sigma A))`, build `FitsSubst [] (A ∷ gamma) (consSubst t sigma)`.
- Implementation: `fitsCons fits dt` — this is just the `fitsCons` constructor! ✓

**`extendCompFitsSingle`**: Given `CompFitsSubst [] gamma sigma`, `Computable (hasTy [] t (subTy sigma A))`, build `CompFitsSubst (A ∷ gamma) (consSubst t sigma)`.
- Implementation: `compFitsCons cFits compT` — just the constructor ✓

**`composeFitsSingle`**: Given outer `FitsSubst [] (subTy sigma A ∷ []) tau` and inner `FitsSubst [] gamma sigma`, build `FitsSubst [] (A ∷ gamma) (compSub tau (liftSubst sigma))`. This is for the one-binder case (Sigma family, Qtr family, Eq family).
- The outer fits gives `tau 0 : hasTy [] (tau 0) (subTy tau (subTy sigma A))`. Need path: `subTy tau (subTy sigma A) ≡ subTy (compSub tau (liftSubst sigma)) A`.
- Build: `fitsCons (composeFitsInner tau fits) transportedEntry`.
- `composeFitsInner tau fits`: For each entry `dt_i : Derivable (hasTy [] (sigma i) (subTy sigma A_i))` in `fits`, produce `Derivable (hasTy [] (sigma i) (subTy (compSub tau (liftSubst sigma)) A_i))` — but this needs `tau` applied to closed terms, which is trivial (closed terms are substitution-invariant modulo path).

Actually this is getting complex. The simpler approach:

**For one-binder cases in SCC 2**, the closure receives `FitsSubst [] (subTy sigma A ∷ []) tau`. This `tau` is `consSubst t₀ idSubst` for some `t₀`. We need `FitsSubst [] (A ∷ gamma) composedSub` where `composedSub = consSubst t₀ sigma`. Build it as:
```agda
fitsCons fits (subst-transport dt₀)
```
where `dt₀` comes from the outer FitsSubst entry, transported along the path `subTy tau (subTy sigma A) ≡ subTy (consSubst t₀ sigma) A`.

This is exactly the `singleFitsSubstHelper` / `sigmaCompFitsHelper` pattern from [Presupposition.agda:192-257](src/TReg/Presupposition.agda#L192), adapted for the composed substitution case.

**For two-binder cases** (`eSigma`/`cSigma` with `B ∷ A ∷ gamma`, `eQtr` coherence with `wkTyBy 1 A ∷ A ∷ gamma`):

The closure receives `FitsSubst [] (subTy sigma (tySigma A B) ∷ []) tau` (for Sigma motive) or `FitsSubst [] (subTy sigma A ∷ []) tau` (for Sigma branch — but the branch lives in `B ∷ A ∷ gamma`, so after substituting sigma for gamma, the branch context is `subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []`, and the closure receives `FitsSubst [] (subTy (liftSubst sigma) B ∷ subTy sigma A ∷ []) tau`).

For the branch, `tau = consSubst t₁ (consSubst t₀ idSubst)`. We build `FitsSubst [] (B ∷ A ∷ gamma) (consSubst t₁ (consSubst t₀ sigma))` as:
```agda
fitsCons (fitsCons fits dt₀_transported) dt₁_transported
```

**Binder-composition helpers** (pre-mutual in CompTheorem.agda, ~5-15 lines each using `subTyComp`, `subTmComp`, `liftSubstCompKeep`):

For each variant (FitsSubst, CompFitsSubst, FitsEqSubst, CompFitsEqSubst) × (one-binder, two-binder):

| Helper | Inputs | Output |
|--------|--------|--------|
| `composeOneBinder` | `FitsSubst [] gamma sigma` + `FitsSubst [] (subTy sigma A ∷ []) tau` | `FitsSubst [] (A ∷ gamma) composedSub` |
| `composeOneBinderComp` | `CompFitsSubst gamma sigma` + `FitsSubst [] (subTy sigma A ∷ []) tau` | `CompFitsSubst (A ∷ gamma) composedSub` |
| `composeOneBinderEq` | `FitsSubst [] gamma sigma` + `FitsEqSubst [] (subTy sigma A ∷ []) tau1 tau2` | `FitsEqSubst [] (A ∷ gamma) ...` |
| `composeOneBinderCompEq` | `CompFitsEqSubst gamma sigma tau` + `FitsEqSubst [] ...` | `CompFitsEqSubst (A ∷ gamma) ...` |
| `composeTwoBinders` | analogous, for `B ∷ A ∷ gamma` | `FitsSubst [] (B ∷ A ∷ gamma) composedSub` |
| `composeTwoBindersComp`/`Eq`/`CompEq` | analogous | ... |

**Qtr coherence** (`wkTyBy 1 A ∷ A ∷ gamma`): use two-binder helpers with `B = wkTyBy 1 A`. Build `dWkAσ : Derivable (isType (subTy sigma A ∷ []) (subTy (liftSubst sigma) (wkTyBy 1 A)))` from `weakenTy dAσ (wfCons wfθ dAσ)` transported along `sym (wkTyLiftSubst sigma A)`. The path `wkTyLiftSubst` is added to [Substitution.agda](src/TReg/Substitution.agda) in Phase 3.0.

#### Handling weakenTy/Tm in SCC 2

`substDerivTyComp (weakenTy {delta = delta} d wf) fits cFits`:
- `d : Derivable (isType gamma A)`, `wf : CtxWF (delta ++ gamma)`
- `fits : FitsSubst [] (delta ++ gamma) sigma`
- Split fits: `dropFits delta fits` gives `FitsSubst [] gamma (dropSubstBy (length delta) sigma)`
- Recurse: `substDerivTyComp d (dropFits delta fits) (dropCompFits delta cFits)`
- Transport result along `subTy sigma (wkTyBy (length delta) A) ≡ subTy (dropSubstBy (length delta) sigma) A` (from `subTyWkBy`)

Need: **`dropCompFits`** — analogous to `dropFits` but for `CompFitsSubst`. ~10 lines, pattern match on the `drop` list, stripping `compFitsCons` entries.

Similarly **`dropCompFitsEq`** for `CompFitsEqSubst`.

#### Handling substTyRule/substTmRule in SCC 2

`substDerivTyComp (substTyRule {delta = delta'} d' fits') fits cFits`:
- `d' : Derivable (isType delta' A)`, `fits' : FitsSubst gamma delta' sigma'`
- `fits : FitsSubst [] gamma sigma`
- Need: `FitsSubst [] delta' (compSub sigma sigma')` and `CompFitsSubst [] delta' (compSub sigma sigma')`
- Build by composing: for each entry in `fits'`, apply `substTmRule` using `fits` entries.

**Naming convention**: The existing `composeFits` / `composeFitsEq` / `composeEqFits` / `composeEqFitsEq` in [Structural.agda#L868-L950](src/TReg/Structural.agda#L868) produce `FitsSubst`/`FitsEqSubst` (derivation-level). They are already used by `liftFits`/`liftFitsEq`. We **reuse** them as-is. The NEW helpers that produce `CompFitsSubst`/`CompFitsEqSubst` are named `composeCompFits` / `composeCompFitsEq`:

**`composeCompFits`**: Given `FitsSubst gamma delta' sigma'` + `FitsSubst [] gamma sigma` + `CompFitsSubst gamma sigma`, produce `FitsSubst [] delta' (compSub sigma sigma')` × `CompFitsSubst delta' (compSub sigma sigma')`.

```agda
composeCompFits (fitsNil wf) fits cFits = (fitsNil wfNil , compFitsNil)
composeCompFits (fitsCons fits' dt) fits cFits =
  let (composedTail, composedCTail) = composeCompFits fits' fits cFits
      compEntry = substDerivTmComp dt fits cFits  -- dt is sub-term of fitsCons ✓
      transported = subst (...) (subTyComp ...) compEntry
  in (fitsCons composedTail (compToDerivable transported),
      compFitsCons composedCTail transported)
```

`composeCompFits` is structural on `FitsSubst`. Each entry calls `substDerivTmComp` on `dt` (sub-term of `fitsCons`) with the SAME `fits`/`cFits`. Agda sees: `fits'` is structural on `FitsSubst`, `dt` is structural on the entry. ✓ Must live inside the mutual block since it calls `substDerivTmComp`.

**`composeCompFitsEq`**: Analogous, producing `FitsEqSubst` × `CompFitsEqSubst`.

#### Variable case

`substDerivTmComp (varStar {delta = delta} wf dA) fits cFits`:
- Need: `Computable (hasTy [] (subTm sigma (var (length delta))) (subTy sigma (wkTyBy (suc (length delta)) A)))`
- `lookupVarFits fits` gives `Derivable (hasTy [] ...)` — but we need `Computable`.
- Use **`lookupCompFits`**: Extract from `CompFitsSubst` at variable position.

**`lookupCompFits`**: Analogous to `lookupVarFits` ([CompTheorem.agda:166-182](src/TReg/CompTheorem.agda#L166)) but extracts `Computable` from `CompFitsSubst`.
```agda
lookupCompFits : {delta gamma : Ctx} {A : RawType} {sigma : Subst}
  → CompFitsSubst (delta ++ (A ∷ gamma)) sigma
  → Computable (hasTy [] (subTm sigma (var (length delta)))
       (subTy sigma (wkTyBy (suc (length delta)) A)))
```
Pattern match on `CompFitsSubst`, strip entries for `delta`, return the `A` entry with path transport. ~15 lines.

**`lookupCompFitsEq`**: Analogous for `CompFitsEqSubst`.

#### fitsToCompFits / fitsEqToCompFitsEq

```agda
fitsToCompFits : FitsSubst [] gamma sigma → CompFitsSubst gamma sigma
fitsToCompFits (fitsNil wf) = compFitsNil
fitsToCompFits (fitsCons fits dt) =
  compFitsCons (fitsToCompFits fits)
    (subst-transport (substDerivTmComp dt (fitsNil wfNil) compFitsNil))
```

**Safety**: `dt : Derivable (hasTy [] t (subTy sigma A))` has context `[]`. `substDerivTmComp dt emptyFits emptyCompFits` recurses structurally on `dt`. Since context is `[]`, `varStar` is impossible. The identity substitution on empty context is trivial. Need path: `subTm idSubst t ≡ t` and `subTy idSubst A ≡ A` (from `subTmId`, `subTyId` in [Substitution.agda:132-139](src/TReg/Substitution.agda)).

`fitsToCompFits` is structural on `FitsSubst`. Each entry calls `substDerivTmComp` on `dt` (sub-term of `fitsCons`). ✓

```agda
fitsEqToCompFitsEq : FitsEqSubst [] gamma sigma tau → CompFitsEqSubst gamma sigma tau
fitsEqToCompFitsEq (fitsEqNil wf) = compFitsEqNil
fitsEqToCompFitsEq (fitsEqCons fitsEq dtu) =
  compFitsEqCons (fitsEqToCompFitsEq fitsEq)
    (subst-transport (substDerivTmEqComp dtu (fitsNil wfNil) compFitsNil))
```

---

### Revised mutual block membership

#### Inside the mutual block

**SCC 1 (structural on Derivable):**
- `computableTheorem` — explicit cases per constructor, gamma=[] uses closed helpers, gamma≠[] dispatches to `openCompTy`/etc.

**SCC 2 (structural on Derivable × FitsSubst, no cycle to SCC 1):**
- `substDerivTyComp`, `substDerivTmComp`, `substDerivTyEqComp`, `substDerivTmEqComp`
- `eqSubDerivTyComp`, `eqSubDerivTmComp`, `eqSubDerivTyEqComp`, `eqSubDerivTmEqComp`
- `fitsToCompFits`, `fitsEqToCompFitsEq`
- Four computable-fit composition helpers (all NEW, inside the mutual block). Each mirrors a derivable helper from [Structural.agda#L868-L950](src/TReg/Structural.agda#L868):

  | Helper | Outer | Inner | Inner entries | SCC 2 call on each entry | Mirrors |
  |--------|-------|-------|---------------|--------------------------|---------|
  | `composeCompFits` | `FitsSubst [] gamma sigma` × `CompFitsSubst` | `FitsSubst gamma delta sigma'` | `Derivable (hasTy gamma t ...)` | `substDerivTmComp` | `composeFits` |
  | `composeCompEqFits` | `FitsEqSubst [] gamma sigma tau` × `CompFitsEqSubst` | `FitsSubst gamma delta sigma'` | `Derivable (hasTy gamma t ...)` | `eqSubDerivTmComp` | `composeEqFits` |
  | `composeCompFitsEq` | `FitsSubst [] gamma sigma` × `CompFitsSubst` | `FitsEqSubst gamma delta sigma' tau'` | `Derivable (termEq gamma t u ...)` | `substDerivTmEqComp` | `composeFitsEq` |
  | `composeCompEqFitsEq` | `FitsEqSubst [] gamma sigma tau` × `CompFitsEqSubst` | `FitsEqSubst gamma delta sigma' tau'` | `Derivable (termEq gamma t u ...)` | `eqSubDerivTmEqComp` | `composeEqFitsEq` |

  Each is structural on the inner `FitsSubst`/`FitsEqSubst`, calling the listed SCC 2 function on entries (sub-terms of the inner fits). The outer fits/cFits are passed unchanged.

**In-place rewrites of existing functions (no new wrapper family — rewrite bodies only):**
- `openCompTy` (line 438) rewritten in-place: `openCompTy d = compTyOpen nonemptyNeNil d (λ sigma fits → substDerivTyComp d fits (fitsToCompFits fits)) (λ sigma tau fitsEq → eqSubDerivTyComp d fitsEq (fitsEqToCompFitsEq fitsEq))`
- `openCompTyEq` (line 448), `openCompTm` (line 459), `openCompTmEq` (line 470) — same pattern, rewritten in-place
- `substTyClosed d fits = substDerivTyComp d fits (fitsToCompFits fits)` — ALWAYS, no `with` dispatch
- `substTyEqClosed`, `substTmClosed`, `substTmEqClosed` — same
- `eqSubTyClosed d fitsEq = eqSubDerivTyComp d fitsEq (fitsEqToCompFitsEq fitsEq)` — fixes the infinite loop
- `eqSubTyEqClosed`, `eqSubTmClosed`, `eqSubTmEqClosed` — same

**Acc-based workers (already implemented, lines 715-890):**
- `compSymTyClosedAcc`, `compTransTyClosedAcc` — Acc on `closedTaskMeasure`
- `compSymTyClosed`, `compTransTyClosed` — wrappers with `<-wellfounded`

**Non-Acc helpers using openComp (which now uses SCC 2):**
- `compTransportFamilyTy compAC compD = openCompTy (transportFamilyTy ...)` — no `computableTheorem`
- `compTransportFamilyTyEq compAC compDF = openCompTyEq (transportFamilyTyEq ...)`
- `compTyEqRight` — closed: `compTyEqRightClosed`; open: existing code at lines 899-911 (already SCC-safe — closures use the comp's own stored closures + `compTransTyClosed`/`compSymTyClosed`)

**General dispatchers (keep general-gamma signatures, dispatch closed/open):**
- `compSymTy comp` — closed cases → `compSymTyClosed comp`; open → `openCompTyEq (symTy d)`
- `compTransTy comp₁ comp₂` — closed → `compTransTyClosed`; open → `openCompTyEq (transTy d₁ d₂)`
- `compConvTm comp compAB` — closed → `compConvTmClosed`; open → `openCompTm (conv d dAB)`
- `compConvTmEq comp compAB` — closed → `compConvTmEqClosed`; open → `openCompTmEq (convEq d dAB)`
- `compSymTm comp` — closed → `compSymTmClosed`; open → `openCompTmEq (symTm d)`

**Variable/weakening handlers (unchanged — once openComp uses SCC 2, these are fine):**
- `computeVar wf dA` (lines 979-987) — `openCompTm (varStar wf dA)`, unchanged
- `computeWeakenTy` (lines 913-927) — existing four-way split: gamma=[],delta=[] → `computableTheorem d` + transport; otherwise → `openCompTy (weakenTy d wf)`. Unchanged.
- `computeWeakenTyEq` (lines 929-943), `computeWeakenTm` (lines 945-959), `computeWeakenTmEq` (lines 961-977) — same pattern, unchanged

**`compWeaken` (lines 670-681):** thin wrapper over `computeWeaken*` helpers — no decision needed, just calls `computeWeakenTy`/etc. which are already correct. Rewrite body to delegate directly:
```agda
compWeaken {J = isType gamma A} compJ deltaWF = computeWeakenTy (compToDerivable compJ) deltaWF
compWeaken {J = typeEq gamma A B} compJ deltaWF = computeWeakenTyEq (compToDerivable compJ) deltaWF
compWeaken {J = hasTy gamma t A} compJ deltaWF = computeWeakenTm (compToDerivable compJ) deltaWF
compWeaken {J = termEq gamma t u A} compJ deltaWF = computeWeakenTmEq (compToDerivable compJ) deltaWF
```

**`compSubst` (lines 683-694) — general-gamma dispatch:**
```agda
compSubst {gamma = []} {J = isType delta A} comp fits = substTyClosed (compToDerivable comp) fits
compSubst {gamma = B ∷ gamma'} {J = isType delta A} comp fits = openCompTy (substTyRule (compToDerivable comp) fits)
-- same pattern for typeEq, hasTy, termEq
```
`gamma = []` uses thin SCC 2 wrappers. `gamma = B ∷ _` uses `openCompXxx` (which now uses SCC 2 closures).

**`compEqSubst` (lines 696-707) — general-gamma dispatch:**
```agda
compEqSubst {gamma = []} {J = isType delta A} comp fitsEq = eqSubTyClosed (compToDerivable comp) fitsEq
compEqSubst {gamma = B ∷ gamma'} {J = isType delta A} comp fitsEq = openCompTyEq (eqSubTyRule (compToDerivable comp) fitsEq)
-- same for typeEq → openCompTyEq, hasTy → openCompTmEq, termEq → openCompTmEq
```

---

### computableTheorem gamma=[] cases — MOSTLY UNCHANGED

**Key insight**: Most `computableTheorem` gamma=[] cases call `computableTheorem` on SUB-TERMS (structurally smaller), which dispatch to `openCompTy`/`openCompTm` etc. Once those lower-level functions use SCC 2 closures instead of `computableTheorem`, termination is automatic. No changes needed for:

- `fSigma dA dB` — `computableTheorem dB` dispatches to `openCompTy dB` (SCC 2 closures) ✓
- `fEq dA da db` — all sub-derivations closed (gamma=[]) ✓
- `fQtr dA`, `iTop`, `iSigma`, `iEq`, `iQtr` — same ✓
- `eSigma dM dd dm` — `computableTheorem dM` and `computableTheorem dm` dispatch to openComp ✓
- `eQtr`, `cSigma`, `cQtr`, `fSigmaEq`, `fEqEq`, `fQtrEq`, `iSigmaEq`, `eSigmaEq`, `eQtrEq` — same ✓
- `reflTy`, `reflTm`, `symTm`, `transTm`, `convEq`, `conv` — all call closed helpers or `computableTheorem` on sub-terms ✓
- `symTy` already calls `compSymTyClosed` (Acc-based) ✓
- `transTy` already calls `compTransTyClosed` (Acc-based) ✓

**Cases that DO change**:
- `substTyRule`, `substTyEqRule`, `substTmRule`, `substTmEqRule`, `eqSubTyRule`, `eqSubTyEqRule`, `eqSubTmRule`, `eqSubTmEqRule` — rewritten in Phase 3c/3d (thin SCC 2 wrappers)
- Three `compConvTm` calls inside `computableTheorem` gamma=[] cases must become `compConvTmClosed`:
  - Line 1050: `compConvTm compcA compAC` → `compConvTmClosed compcA compAC` (in `fEqEq`)
  - Line 1051: `compConvTm compdA compAC` → `compConvTmClosed compdA compAC` (in `fEqEq`)
  - Line 1131: `compConvTm compdA (compSingleEqSubstTyClosed compB compac)` → `compConvTmClosed ...` (in `iSigmaEq`)

---

## Pre-mutual infrastructure (all in CompTheorem.agda, before the mutual block)

### Already existing (baseline)
- `subSubJIntoPath` family (lines 29-111) — substitution composition paths
- `lookupVarFits`, `lookupVarFitsEq` (lines 176-212) — variable lookup in FitsSubst
- `lookupCompFits`, `lookupCompFitsEq` (lines 214-250) — ✓ DONE
- `dropFits`, `dropFitsEq` (lines 252-282) — drop prefix from FitsSubst
- `dropCompFits`, `dropCompFitsEq` (lines 284-314) — ✓ DONE
- `closedEqSubTy/TyEq/Tm/TmEq` (lines 316-346) — ✓ DONE (NOTE: eqSubTyClosed will stop using these once rewritten as SCC 2 wrapper)
- `liftFits`, `liftFitsOne`, `liftFitsEq`, `liftFitsEqOne`, `liftSubstCompKeep` (lines 348-428) — ✓ DONE
- `subTyWkBy`, `subTyWkStep`, `wkTyBy0`, `wkTmBy0`, `compSubKeepBy` (lines 134-166) — path helpers
- `composeFits`, `composeFitsEq`, `composeEqFits`, `composeEqFitsEq` in [Structural.agda#L868-L950](src/TReg/Structural.agda#L868) — derivation-level composition (REUSED, not redefined)

### Still needed (to add before the mutual block)
- `composeOneBinder` / `composeOneBinderComp` / `composeOneBinderEq` / `composeOneBinderCompEq` (~15 lines each)
- `composeTwoBinders` / `composeTwoBindersComp` / `composeTwoBindersEq` / `composeTwoBindersCompEq` (~20 lines each)
- All use `subTyComp`, `subTmComp`, `liftSubstCompKeep`, and the existing path lemmas

---

## Modules affected

| Module | Change | Scope |
|--------|--------|-------|
| **Substitution.agda** | Add `wkTyLiftSubst` + `wkTmLiftSubst` (~6 lines) | Small |
| **Derivability.agda** | Change 3 constructors: `A ∷ A ∷ gamma` → `wkTyBy 1 A ∷ A ∷ gamma` (3 lines) | Small |
| **Presupposition.agda** | Update pattern matches on `eQtr`/`eQtrEq`/`cQtr` — mostly automatic (13 occurrences) | Small–Medium |
| **QtrComp.agda** | Retype `compEQtrClosed`/`compCQtrClosed` signatures + all internal `dcoh`/`dcoh'`/`cohFitsRight`/derivation-assembly sites against new `wkTyBy 1 A ∷ A ∷ []` context. Logic unchanged, annotations change throughout. | Medium |
| **CompTheorem.agda** | SCC 2 qtr cases + 4 thin wrappers + `computableTheorem` gamma=[] cases; remove TERMINATING, add --safe | Large |
| **Everything.agda** | Add `{-# OPTIONS --safe #-}` | 1 line |
| **Inversion.agda** | UNCHANGED | None |
| **Evaluation.agda** | UNCHANGED | None |

---

## Implementation phases

### Phase 1: Representation change — DONE ✓

### Phase 2: Pre-mutual infrastructure — DONE ✓
Implemented by user:
- `lookupCompFits`, `lookupCompFitsEq` (lines 214-250)
- `dropCompFits`, `dropCompFitsEq` (lines 284-314)
- `closedEqSubTy/TyEq/Tm/TmEq` helpers (lines 316-346)
- `liftFits`, `liftFitsOne`, `liftFitsEq`, `liftFitsEqOne`, `liftSubstCompKeep` (lines 348-428)
- `compSymTyClosedAcc`, `compTransTyClosedAcc` (lines 715-877) — Acc workers (Blocker 3)
- `compSymTyClosed`, `compTransTyClosed` wrappers (lines 879-890) — currently inside mutual block (fine)

### Phase 3: Add SCC 2 functions + rewire openComp/substClosed

**Bug note**: The current `eqSubTyClosed` closed cases have an infinite loop: `eqSubTyClosed d fitsEq` → closed → `computableTheorem (closedEqSubTy d wfNil)` → `computableTheorem (eqSubTyRule d (fitsEqNil wfNil))` → `eqSubTyClosed d (fitsEqNil wfNil)` → loop. Same for `eqSubTyEqClosed`, `eqSubTmClosed`, `eqSubTmEqClosed`. The fix: SCC 2 replaces all these paths.

**3a. Add SCC 2 functions to the mutual block** — MOSTLY DONE, ONE BLOCKER REMAINS

All 8 SCC 2 functions + `fitsToCompFits` + `fitsEqToCompFitsEq` + 4 computable-fit composition helpers implemented and typechecking (with TERMINATING). Equal-substitution open helper layer added and sigma-side paths fully rewired.

**Blocker A: computableTheorem calls within SCC 2 bodies — RESOLVED ✓**

The implemented SCC 2 cases for constructors with binder-extended sub-derivations (fSigma, fSigmaEq, eSigma, cSigma, fEqEq, eqSubTy-fSigma, etc.) use the pattern `compSubst (computableTheorem dX) liftedFits` to build open Computable premises. This calls SCC 1 (`computableTheorem`) from within SCC 2 — it works under `{-# TERMINATING #-}` because `dX` is a structural sub-derivation, but Agda's termination checker cannot verify the cross-SCC call when TERMINATING is removed.

Affected lines (all `compSubst/compEqSubst (computableTheorem dX) liftedFits` within SCC 2):
- substDerivTyComp: 711 (fSigmaEq.dBD)
- substDerivTyEqComp: 1017 (eqSubTy-fSigma.dB)
- substDerivTmComp: 819 (eSigma.dM), 848 (eSigma.dm)
- substDerivTmEqComp: 941 (cSigma-helper.dM), 970 (cSigma-helper.dm), 1057 (eSigmaEq-helper.dM), 1085 (eSigmaEq-helper.dm)
- eqSubDerivTyComp: 1198 (fSigma.dB)
- eqSubDerivTyEqComp: 1302 (fSigmaEq.dBD)
- eqSubDerivTmComp: 1458 (eSigma.dM), 1507 (eSigma.dm)
- eqSubDerivTmEqComp: 1604 (eqSubTy-fSigma.dB), 1644 (eSigmaEq-helper.dM), 1693 (eSigmaEq-helper.dm)

**Fix**: Replace each `compSubst (computableTheorem dX) liftedFits` with a direct `compTyOpen`/`compTmOpen`/`compTmEqOpen` construction whose closures call SCC 2 on the original sub-derivation `dX` with composed fits (the frozen rule). Example for `substDerivTyComp (fSigma dA dB)`:

```agda
-- BEFORE (SCC 1 call):
compSubst (computableTheorem dB) (liftFitsOne fits dAσ)

-- AFTER (frozen-rule, pure SCC 2):
compTyOpen nonemptyNeNil
  (substTyRule dB (liftFitsOne fits dAσ))
  (λ tau fits2 →
    let composedFits = composeOneBinder fits dAσ fits2
    in subst (...) (substDerivTyComp dB composedFits (fitsToCompFits composedFits)))
  (λ tau1 tau2 fitsEq2 →
    let composedFitsEq = composeOneBinderEq fits dAσ fitsEq2
    in subst (...) (eqSubDerivTyComp dB composedFitsEq (fitsEqToCompFitsEq composedFitsEq)))
```

All 15 sites follow this pattern. The `subst` paths use `subTyComp`/`subTmComp` + `liftSubstCompKeep` + type-specific lift lemmas (e.g. `sigmaBranchTyLiftComp`, `qtrBranchTyLiftComp`, `qtrCohTyLiftComp`).

For two-binder cases (eSigma.dm, cSigma.dm, eSigmaEq.dm, eQtr.dcoh, etc.), use `composeTwoBinders`/`composeTwoBindersEq` instead. For qtr coherence (`wkTyBy 1 A ∷ A ∷ gamma`), call `composeTwoBinders` with `B = wkTyBy 1 A`; see Blocker B resolution for the `dWkAσ` construction.

**Blocker B: qtr coherence two-binder context mismatch — RESOLVED**

**Problem**: `eQtr`, `eQtrEq`, `cQtr` require coherence premises in context `A ∷ A ∷ gamma`. After double-lifting sigma for gamma, the theta context is `subTy (liftSubst sigma) A ∷ subTy sigma A ∷ []`. But `compEQtrClosed` expects `subTy sigma A ∷ subTy sigma A ∷ []`. The path `subTy (liftSubst sigma) A ≡ subTy sigma A` is **FALSE** in general (counterexample: `gamma = [tyTop]`, `sigma = consSubst tmStar idSubst`, `A = tySigma tyTop (tyEq tyTop (var 0) (var 1))`).

**Root cause**: The context `A ∷ A ∷ gamma` reuses the raw type `A` for BOTH binder entries without weakening the outer one. This is NOT context-well-formed in the standard sense — the outer `A` should be `wkTyBy 1 A` to be well-typed in `A ∷ gamma`.

**Resolution**: Change the qtr derivation rules to use `wkTyBy 1 A` for the outer context entry. This makes the context properly well-formed and eliminates the mismatch.

In [Derivability.agda](src/TReg/Derivability.agda), change:
```agda
-- BEFORE (lines 250-272):
eQtr : ... → Derivable (termEq (A ∷ A ∷ gamma) ...) → ...
eQtrEq : ... → Derivable (termEq (A ∷ A ∷ gamma) ...) → Derivable (termEq (A ∷ A ∷ gamma) ...) → ...
cQtr : ... → Derivable (termEq (A ∷ A ∷ gamma) ...) → ...

-- AFTER:
eQtr : ... → Derivable (termEq (wkTyBy 1 A ∷ A ∷ gamma) ...) → ...
eQtrEq : ... → Derivable (termEq (wkTyBy 1 A ∷ A ∷ gamma) ...) → Derivable (termEq (wkTyBy 1 A ∷ A ∷ gamma) ...) → ...
cQtr : ... → Derivable (termEq (wkTyBy 1 A ∷ A ∷ gamma) ...) → ...
```

**Key lemma** (add to [Substitution.agda](src/TReg/Substitution.agda), ~3 lines each):
```agda
wkTyLiftSubst : (sigma : Subst) (A : RawType)
  → subTy (liftSubst sigma) (wkTyBy 1 A) ≡ wkTyBy 1 (subTy sigma A)
wkTyLiftSubst sigma A =
  subTyRen (liftSubst sigma) suc A
  ∙ cong (λ theta → subTy theta A) (dropLiftRenSub sigma)
  ∙ sym (renTySub suc sigma A)

wkTmLiftSubst : (sigma : Subst) (t : RawTerm)
  → subTm (liftSubst sigma) (wkTmBy 1 t) ≡ wkTmBy 1 (subTm sigma t)
wkTmLiftSubst sigma t =
  subTmRen (liftSubst sigma) suc t
  ∙ cong (λ theta → subTm theta t) (dropLiftRenSub sigma)
  ∙ sym (renTmSub suc sigma t)
```

Proof chain: `subTyRen` gives `subTy (liftSubst sigma) (renTy suc A) ≡ subTy (liftSubst sigma ∘ suc) A`. Then `dropLiftRenSub` gives `(liftSubst sigma ∘ suc) ≡ renSub suc sigma`. Then `sym (renTySub suc sigma A)` gives `subTy (renSub suc sigma) A ≡ renTy suc (subTy sigma A)`. All three lemmas already exist in [Substitution.agda](src/TReg/Substitution.agda) (lines 152, 213, 268).

**Why this works for SCC 2**: After double-lifting sigma for context `wkTyBy 1 A ∷ A ∷ gamma`:
- `liftFits fits dAσ` gives theta = `subTy sigma A ∷ []`
- `liftFits (liftFits ...) dWkAσ` gives theta = `subTy (liftSubst sigma) (wkTyBy 1 A) ∷ subTy sigma A ∷ []`
- By `wkTyLiftSubst`: this equals `wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ []`
- The modified `compEQtrClosed {A = subTy sigma A}` expects exactly `wkTyBy 1 (subTy sigma A) ∷ subTy sigma A ∷ []` ✓

**Blast radius** (34 occurrences across 5 files, but most changes are mechanical):
- [Derivability.agda](src/TReg/Derivability.agda): 3 constructors — change context annotation (3 lines)
- [QtrComp.agda](src/TReg/QtrComp.agda): 5 occurrences — mechanical but nontrivial retyping. Update type signatures of `compEQtrClosed` (line 198) / `compCQtrClosed` (line 57) to use `wkTyBy 1 A ∷ A ∷ []`. Internally, `dcoh`/`dcoh'` extraction (lines 78, 263, 267), `cohFitsRight` (line 315), and all `eQtrEq`/`cQtr` derivation assembly sites (lines 389, 406, 426, 433) must be retyped against the new coherence context. The proof LOGIC is unchanged — the same derivation constructors are called with the same arguments — but the TYPE ANNOTATIONS on `where`-bound names change throughout
- [Presupposition.agda](src/TReg/Presupposition.agda): 13 occurrences — mostly automatic: `coh`/`coh'` from pattern matching get new type, flow into reconstructed `eQtr`/`cQtr` calls unchanged
- [CompTheorem.agda](src/TReg/CompTheorem.agda): 4 occurrences — `computableTheorem` gamma=[] cases + SCC 2 qtr cases
- [Inversion.agda](src/TReg/Inversion.agda): only `tyQtr` type inequalities — **UNAFFECTED**
- [Evaluation.agda](src/TReg/Evaluation.agda): **UNAFFECTED** (no eQtr/cQtr/eQtrEq usage)

**Blocker C: `fitsToCompFits` → `openCompTy` transport cycle — RESOLVED**

**Cycle** (recorded at [CompTheorem.agda:638](src/TReg/CompTheorem.agda#L638)):
`fitsToCompFits` → SCC 2 → `compTransportFamilyTy` → `openCompTy` → closures call `fitsToCompFits`

**Root cause**: [compTransportFamilyTy](src/TReg/CompTheorem.agda#L3863) calls `openCompTy` on a freshly constructed `transportFamilyTy` derivation. `openCompTy`'s closures call `fitsToCompFits`, completing the cycle.

**Resolution**: Rewrite `compTransportFamilyTy` / `compTransportFamilyTyEq` to pattern-match on the input open Computable (`compTyOpen` / `compTyEqOpen`) and compose its stored closures with `headTypeTransportFits`, instead of calling `openCompTy`.

```agda
compTransportFamilyTy compAC (compTyOpen neq dD closureS closureEqS) =
  compTyOpen nonemptyNeNil
    (transportFamilyTy dAC dC dD)
    (λ sigma fits →
      subst ... (closureS _ (composeFits fits (headTypeTransportFits dAC dC))))
    (λ sigma tau fitsEq →
      subst ... (closureEqS _ _ (composeEqFits fitsEq (headTypeTransportFits dAC dC))))
  where
  dAC = compToDerivable compAC
  dC  = compToDerivable (compTyEqRight compAC)
```

**Why it terminates**: `closureS` / `closureEqS` are constructor arguments of the INPUT Computable — not recursive calls. `composeFits` / `composeEqFits` are in [Structural.agda:868](src/TReg/Structural.agda#L868) (pre-mutual). `headTypeTransportFits` is in [Presupposition.agda:311](src/TReg/Presupposition.agda#L311) (pre-mutual). No `fitsToCompFits`, no SCC 2, no `openCompTy` called.

**Transport paths**: Use the same normalization already in [transportFamilyTy](src/TReg/Presupposition.agda#L341): `subTyComp ... idSubst ...` composed with `subTyId`. No new `compSub sigma idSubst ≡ sigma` lemma needed.

**`compTransportFamilyTyEq` nuance**: The third field of `compTyEqOpen` (the left-side type witness) must be rebuilt as `compTransportFamilyTy compAC compD` where `compD` is the left-side witness stored in the input. This is NOT a cycle — `compTransportFamilyTy` calls into the already-fixed version on a constructor argument, not a recursive call through the mutual block.

**Downstream**: The Acc workers (`compSymTyClosedAcc`, `compTransTyClosedAcc`) call `compTransportFamilyTy` / `compTransportFamilyTyEq` but are fixed automatically since the wrappers no longer call `openCompTy`.

**Missing constructor cases (catch-all fallbacks) — all qtr-driven:**

| Function | Missing constructors | Fallback line |
|----------|---------------------|---------------|
| `substDerivTmComp` | `eQtr` | 1420 |
| `substDerivTmEqComp` | `eQtrEq`, `cQtr` | 1671 |
| `eqSubDerivTmComp` | `eQtr` | 2036 |
| `eqSubDerivTmEqComp` | `eQtrEq`, `cQtr` | 2383 |

Note: `iSigmaEq`, `cSigma`, `eSigmaEq` now have explicit cases (done by user). Only the qtr family remains.

**3b. Rewire `openCompTy`/`openCompTyEq`/`openCompTm`/`openCompTmEq`** — DONE ✓

**3c. Rewire closed substitution helpers as thin SCC 2 wrappers** — PARTIALLY DONE:
- `substTyClosed` — DONE ✓ (thin wrapper)
- `substTyEqClosed` — DONE ✓ (thin wrapper)
- `substTmClosed` — DONE ✓ (thin wrapper)
- `substTmEqClosed` — DONE ✓ (thin wrapper)

**3d. Rewire `eqSubTyClosed` etc.** — DONE ✓
**3e–3i.** — All DONE ✓

**Phase 3.0–3.2: All DONE ✓** (qtr rule change, qtr SCC 2 cases, term-side thin wrappers all landed and typecheck)

**Phase 3.3: Break the transport cycle (Blocker C) — DONE ✓**
- Rewrote `compTransportFamilyTy` / `compTransportFamilyTyEq` to compose stored closures instead of calling `openCompTy` / `openCompTyEq`.
- Added `compSymTransportFamilyTyEq` at [CompTheorem.agda:3995](src/TReg/CompTheorem.agda#L3995).
- Removed `with computableTheorem` — confirmed gone.
- Typechecks with TERMINATING.

**Blocker D: Acc/closure cycle in `compSymTyClosedAcc` / `compTransTyClosedAcc`**

**Cycle**: Agda looks inside lambdas passed to data constructors. The closures stored in `compTyEqOpen` (built by `compSymTyOpenHelper` at lines 3942-3966 and `compTransTyOpenHelper` at lines 3982-3993) call `compSymTyClosed` / `compTransTyClosed`, which call `compSymTyClosedAcc <-wellfounded` / `compTransTyClosedAcc <-wellfounded`. The `<-wellfounded` witness is NOT a sub-term of the original `(acc rs)`.

Call chain:
```
compSymTyClosedAcc (compTyEqClosedSigma ...) (acc rs)    [line 4290]
  → compSymTransportFamilyTyEq compCE compDF              [line 4304]
    → compSymTyOpenHelper ...                              [line 4000]
      → compTyEqOpen ... (λ sigma fits → compSymTyClosed (sub sigma fits)) ...   [line 3957]
        → compSymTyClosedAcc ... <-wellfounded             [via compSymTyClosed wrapper]
```

Same pattern for `compTransTyClosedAcc` → `compTransTyOpenHelper` → closures → `compTransTyClosed`.

**Resolution**: Parameterize the open helpers by their closure operations. The helpers currently hardcode calls to `compSymTyClosed`/`compTransTyClosed`. Instead, they should receive these operations as function arguments:

```agda
compSymTyOpenHelper :
  (symCl : ∀ {A B} → Computable (typeEq [] A B) → Computable (typeEq [] B A)) →
  (transCl : ∀ {A B C} → Computable (typeEq [] A B) → Computable (typeEq [] B C) → Computable (typeEq [] A C)) →
  ... → Computable (typeEq gamma B A)
```

**Callers**:
- `compSymTy` (general dispatcher, open case at line 4039): pass `compSymTyClosed` / `compTransTyClosed` — standard wrappers with `<-wellfounded`. Fine because `compSymTy` is not itself Acc-guarded.
- `compSymTyClosedAcc` (sigma case at line 4304): pass Acc-threaded versions `(λ comp → compSymTyClosedAcc comp acHead)` / `(λ comp₁ comp₂ → compTransTyClosedAcc comp₁ comp₂ acHead)`, where `acHead = rs _ proof` is the Acc sub-witness for the sigma head component. The sub-witness is valid because the closures operate on the HEAD type equality, whose measure < the sigma type's measure.

**Why the Acc sub-witness works**: `acHead : Acc _<_ (closedTaskMeasure C)` where `C` is the sigma head. The closures receive `sub sigma fits : Computable (typeEq [] A' B')` whose `closedTaskMeasure` equals `closedTaskMeasure C` (because substitution preserves evaluation of closed head types). So `acHead` is a valid Acc witness for the closure's argument. Specifically, the proof that `closedTaskMeasure C < closedTaskMeasure (tySigma C D)` already exists as `tyDepth-fst<Sigma C D`.

**Same treatment** for `compTransTyOpenHelper`, `compSymTransportFamilyTyEq`, and any other helpers that store `compSymTyClosed`/`compTransTyClosed` in closures.

**Affected functions** (all in [CompTheorem.agda](src/TReg/CompTheorem.agda)):
- `compSymTyOpenHelper` (line 3932): add `symCl`/`transCl` params, replace hardcoded calls
- `compTransTyOpenHelper` (line 3968): add `transCl` param
- `compSymTransportFamilyTyEq` (line 3995): add `symCl`/`transCl` params, pass to `compSymTyOpenHelper`
- `compSymTyClosedAcc` sigma case (line 4290): pass Acc-threaded versions
- `compTransTyClosedAcc` sigma case (line 4377): pass Acc-threaded versions
- `compSymTy` open case (line 4039): pass `compSymTyClosed`/`compTransTyClosed`
- `compTransTy` open case: same

**Implementation order for remaining work:**

The `fitsToCompFits` rewrite only works after two prerequisite decouplings. Applying it early exposes a 6-function SCC through `openCompTy` (line 4008) and `computeWeakenTy` (line 4890).

**Phase 3.5: Decouple SCC 2 from `openComp*`**

~60 `openComp*` calls inside `substDeriv*Comp` / `eqSubDeriv*Comp` (lines 1951-3829) create edges SCC 2 → `openCompTy` → `fitsToCompFits`. Replace each with direct `comp*Open` construction on the original sub-derivation, using the frozen-rule pattern:

- Binder-local closures call SCC 2 on the ORIGINAL sub-derivation with composed fits.
- One-binder closures use `composeOneBinder` / `composeOneBinderEq`.
- Two-binder closures use `composeTwoBinders` / `composeTwoBindersEq`.
- Closure `CompFitsSubst` payloads use the fixed-arity `singleClosedCompFits`, `singleClosedCompFitsEq`, `doubleClosedCompFits`, `doubleClosedCompFitsEq` — NOT the generic `fitsToCompFits`.
- Do NOT call `packClosedSubst`, `packClosedEqSubst`, or the generic `openComp*` from binder closures.

After this phase, SCC 2 has no call edge to `openCompTy` / `fitsToCompFits`.

**Gate 1**: temp stripped build after removing the remaining `openComp*` SCC 2 calls.

**Phase 3.6: Decouple weakening from `computableTheorem`**

`computeWeakenTy {gamma = []} {delta = []}` at [line 4890](src/TReg/CompTheorem.agda#L4890) calls `computableTheorem d`, creating a back-edge from the weakening layer to SCC 1. Replace with Computable-based weakening helpers:

- Base case `delta = []`: just transport along `wkTyBy0` / `wkTmBy0`.
- Non-empty cases: reuse the existing `weakenOneOpen*` helpers and iterate binder-by-binder.

Same treatment for `computeWeakenTyEq`, `computeWeakenTm`, `computeWeakenTmEq`.

After this phase, `computeWeaken*` no longer calls `computableTheorem`.

**Gate 2**: temp stripped build after removing the derivation-based `computeWeaken*` → `computableTheorem` edge.

**Phase 3.7: Rewrite `fitsToCompFits` / `fitsEqToCompFitsEq`**

Now safe to apply:
```agda
fitsToCompFits (fitsCons {sigma = sigmaTail} {A = A} {t = t} fits dt) =
  compFitsCons (fitsToCompFits fits)
    (subst (λ J → Computable J)
      (cong₂ (hasTy []) (subTmId t) (subTyId (subTy sigmaTail A)))
      (substDerivTmComp dt (fitsNil wfNil) compFitsNil))
```
Same pattern for `fitsEqToCompFitsEq` using `substDerivTmEqComp`.

**Gate 3**: real build of `src/TReg/CompTheorem.agda` without `{-# TERMINATING #-}`.

**Phase 4: Remove TERMINATING, add --safe**
- Remove `{-# TERMINATING #-}` at [line 669](src/TReg/CompTheorem.agda#L669).
- Add `{-# OPTIONS --safe #-}` at top.
- **Gate 4**: `agda src/TReg/CompTheorem.agda` typechecks --safe.

**Phase 5: Everything.agda + verification**
- Add `open import TReg.CompTheorem public` + `{-# OPTIONS --safe #-}` to [Everything.agda](src/TReg/Everything.agda).
- `agda src/TReg/Everything.agda` → success.
- `rg -n 'TERMINATING' src/TReg/*.agda` → no matches.

**Gate**: CompTheorem.agda typechecks with TERMINATING ✓

---

## Success criteria

1. `rg -n '^\{-# TERMINATING #-\}$' src/TReg/*.agda` returns no matches
2. `agda src/TReg/Everything.agda` succeeds with `--safe` on every module
3. `MainTheorem.agda` unchanged — `canonicalType`, `canonicalTerm`, etc. still work
