# Locator proposals (Track L)

Four prototypes that shorten the locator code in `theories/Analysis/Locator.v` and its callers in `contrib/`. Each is its own commit on `abooij/claude-locators-track-l2`. They are stacked on `9f18335` (the base of this track), followed by a merge of `abooij/claude-locators` at `6ccaf08` (with Track N3) and a small clean-up. Nothing here is meant to be merged before the user has looked at it.

| Option | Effect | Statements changed | Recommendation |
|---|---|---|---|
| 1. Bounds by search over ℕ | Locator.v −54 sentences, −97 lines. The enumerations `Q_eq`, `QQpos_eq` are gone from the whole Locator.v API and from all of `contrib/` except one search in IntermediateValue.v. `Funext`/`Univalence` remain only on `locates_left` and the equivalence `locator ≃ locator'`. Locator.v about 0.1 s slower. | Every result built on `lower_bound`/`upper_bound` loses its `nat <~> Q` argument (and `Funext`): `lower_bound`, `upper_bound`, `tight_bound`, `archimedean_structure`, `locator_cotransitive(_rational)`, `locator_plus`, `locator_times`, and the contrib results that used them. Same names and index entries. | Adopt |
| 2. A positive rational bound | `qpos_upper_bound` in Locator.v replaces 4 copies: −23 sentences, −26 lines in total | `qpos_upper_bound` is new (it was `Local` in IntermediateValue.v with a `0 ≤ x` hypothesis and a non-strict conclusion); `qpos_of_upper_bound` is no longer used in PicardLindelof.v | Adopt |
| 3. Located from close approximations, any O | `located_from_approximations` (generic in O) and `locator_close`: Locator.v −38, DedekindReals.v −4 sentences. `locator_limit` goes from 45 to 2 sentences, `locator_from_approx` from 23 to 5. | Additions only, statements unchanged; DedekindReals.v now imports `Analysis/Locator.v` | Adopt |
| 4. A locator for a binary operation with a modulus | `BinaryModulus`, `locator_binary`: `locator_plus` and `locator_times` with helpers go from 103 to 51 sentences (−52) | `locator_plus`, `locator_times` keep their statements but become transparent terms; `locator_from_approx` is removed (no uses left) | Adopt, if a modulus-as-data interface is welcome in `theories/` |

All four together: Locator.v goes from 649 to 506 sentences and from 930 to 795 lines, at the same build time (2.1 s). Across the seven affected files the stack removes 171 sentences.

## How it was measured

- Sentences: counted per proof from `rocq compile -time-file` (the sentences between the statement and `Qed`/`Defined`, without `Proof.`; bullets and braces count).
- Times: Rocq 9.1, each file compiled 3 times against the built library of its own state. Per sentence I keep the minimum over the runs. "Sentence time" is the sum over all sentences of the file, "wall" the fastest of the 3 compilations. Between identical runs, times vary by ±0.1 s per proof and ±0.3 s per file, so only larger differences mean anything.
- States: `base` = `9f18335`, `o1` … `o4` = the stack commits below. The merge with `abooij/claude-locators` came after these measurements.

## Option 1. Bounds by search over ℕ

**Before.** `lower_bound` and `upper_bound` searched with `minimal_n_alt_type` through an enumeration `Q_eq : nat <~> Q` for a rational `q` with `locates_right l (q - 1 < q)`, each with its own predicate, its proof that the predicate is a proposition, and an inhabitation proof (45 sentences). `archimedean_structure` searched through `QQpos_eq : nat <~> Q * Qpos Q` for a pair `(q, ε)` (60 sentences with `P`, `P_isHProp`, `P_dec`, `P_inhab`). Both enumerations were section variables of Locator.v. So every locator operation built on them, and much of `contrib/`, took `Q_eq`, e.g. `locator_plus Q F Q_eq l m`.

**After.**
- `lower_bound` (12 sentences): `minimal_n` over `n : nat` with the decidable predicate "the locator puts `x` above `-n-1` when comparing it with `-n-1 < -n`". A rational below `x` (from `archimedean_property`) and `round_up_strict` show that such an `n` merely exists.
- `upper_bound` (4): `lower_bound` of `-x`, through `locator_minus`. `locator_minus` moved up for this; its statement is unchanged.
- `archimedean_structure` (29, plus `precision_lt`, 6): with the precision `e_n = 1/(n+1)`, take `u` with `u < x < u + e_n/2` from `tight_bound`, and search for the least `n` for which the locator of `y` puts `y` above `u + e_n/2` (comparing with `u + e_n/2 < u + e_n`). It merely exists because some rational `d` satisfies `0 < d < y − x`.
- Total: 105 → 51 sentences.

**Funext.** As Track H found, `Funext` entered every result only through `upper_bound`, whose search predicate `locates_left` is a negation made into an `HProp`. The new searches use the decidable `locates_right`, so `Funext` and `Univalence` are now needed only by:
- `locates_left`, which takes `{Funext}` as its own binder;
- the equivalence `locator x ≃ locator' x`, whose section `logic2` now has the `Context`.

`nltqx_locates_left` and `ltxq_locates_left` now conclude `~ locates_right l' ltqr`, which is convertible to `locates_left l' ltqr` but needs no `Funext`. Checking the types of all definitions of Locator.v, no other one mentions `Funext` or `Univalence`. In `contrib/`, `qpos_upper_bound` and others lose `Funext`; `approximate_ivt_locator` keeps it for other reasons (`approximate_candidate`).

**Callers.**
- The calls `locator_plus Q F Q_eq …`, `upper_bound Q F Q_eq …` and so on in Integral.v, IntermediateValue.v, LocatorCuts.v, LocatorDigits.v and PicardLindelof.v drop `Q_eq`. Unused `(Q_eq : nat <~> Q)` and `(QQpos_eq …)` section variables are removed.
- As a result, `approximate_candidate_locator`, `approximate_ivt_locator`, `signed_digits_locator`, `merely_locator_iff_limit`, `merely_locator_iff_signed_digits`, `iscauchyreal_iscut_merely_locator`, `iscauchyreal_merely_locator` and the other results of those sections lose the argument.
- The index `contrib/Booij2020Thesis.v` uses `@name` aliases and needed no change; the same results stay registered.
- The public but unused `P_lower_prop` and `P_upper_prop` are gone.
- One enumeration is left: `locally_nonconstant_rational` (IntermediateValue.v) still searches over `QQpos_eq` for a pair (r, η). It could be converted the same way (a grid of precision 1/n around r), but that is a contrib-side change of its own.

**Measurements.**

| file | sentences | lines | sentence time (s) | wall (s) |
|---|---|---|---|---|
| Locator.v | 649 → 595 (−54) | 930 → 833 (−97) | 2.11 → 2.23 | 2.41 → 2.63 |
| LocatorCuts.v | 261 → 261 | 599 → 597 | 2.19 → 2.12 | 2.46 → 2.21 |
| LocatorDigits.v | 218 → 218 | 516 → 515 | 1.36 → 1.75 | 1.58 → 1.77 |

Per proof: `archimedean_structure` with its helpers 0.10 → 0.38 s, `lower_bound` 0.01 → 0.08 s. The new inhabitation proof does its arithmetic in F, with casts, `pos_split2` and `preserves_plus`, and each such rewrite costs 0.02–0.06 s. The old one worked in Q. The other contrib files did not change by more than the noise.

**Risks.**
- About 0.1–0.3 s more for Locator.v (in `archimedean_structure`), recovered by option 4.
- `archimedean_structure` now depends on `tight_bound`, which is still the 143-sentence trisection proof. The located walk of P2 would shorten it, but that is not part of this option.
- `BLUEPRINT.md` still describes the enumerations as part of the context (line 26, the rows of 6.7.3 and 6.10.3). I did not edit it; the coordinator should.

**Commit.** `621fb32`.

## Option 2. A positive rational bound from a locator

**Lemma.**
```coq
Definition qpos_upper_bound {x : F} (l : locator x) : {B : Qpos Q & x < ' (' B)}.
```
Proof (7 sentences): `upper_bound` of `join x 0`. It needs no hypothesis `0 ≤ x` and gives a strict bound, so it serves all the copies:
- `qpos_upper_bound` (Local, IntermediateValue.v, which assumed `0 ≤ u` and gave `u ≤ B`): removed. Its two uses take `lt_le` of the new bound.
- `qpos_of_upper_bound` in PicardLindelof.v: its three uses (`picard_bound`, the radius and the bound `C` in `picard_lindelof`) now get a `Qpos` directly. In `picard_bound` the bound `K := r + N` is a sum in `Qpos`.
- The inline positivity arguments in `locator_integral_le` (Integral.v, 8 → 2 sentences) and in `locator_times` (`Zpos`, 44 → 38).

I did not add the variant for `|x|` via `join x (- x)`. `picard_bound` applies `qpos_upper_bound` to `locator_join l (locator_minus l)` directly. `locator_times` needs a common bound for `x` and `y`, which it gets by `qpos_upper_bound` of a fourfold join, as before. A separate lemma would have one use.

**Measurements** (o1 → o2):

| file | sentences | lines | sentence time (s) | wall (s) |
|---|---|---|---|---|
| Locator.v | 595 → 596 (+1) | 833 → 839 | 2.23 → 2.27 | 2.63 → 2.65 |
| Integral.v | 181 → 175 (−6) | 508 → 504 | 2.36 → 2.32 | 2.57 → 2.54 |
| IntermediateValue.v | 428 → 420 (−8) | 988 → 973 | 5.72 → 6.36 | 6.14 → 6.12 |
| PicardLindelof.v | 209 → 199 (−10) | 411 → 398 | 3.56 → 3.32 | 3.64 → 3.54 |

The sentence time of IntermediateValue.v rises across many untouched proofs; this is noise, since its wall time did not move.

**Relation to Track N3.** N3, now merged into `abooij/claude-locators`, deduplicated the same helpers one level lower. It made `qpos_of_upper_bound` ("a rational strict upper bound of a nonnegative element is positive") a shared lemma of IntermediateValue.v, used by IntermediateValue's `qpos_upper_bound`, by `merely_bound` and by the three uses in PicardLindelof.v. PicardLindelof.v imported IntermediateValue.v for that. In the merge (`895d19d`), option 2 takes over all the locator uses:
- IntermediateValue's `qpos_upper_bound` is gone;
- PicardLindelof.v no longer uses `qpos_of_upper_bound` and no longer imports IntermediateValue.v (`4e62c9e`);
- `qpos_of_upper_bound` stays in IntermediateValue.v for `merely_bound`, whose bound comes from `archimedean_property`, not from a locator.

N3 also made `locator_0` shared, so Integral.v's copy was already gone. It removed `ltQnegQ`/`ltQposQ` from Locator.v; their uses in the new code of options 1 and 3 are inlined the same way. And it added `plus_swap_middle` to `Classes/theory/rings.v`, which now replaces my local `plus_minus_plus` of option 4.

**Commits.** `be19172` on top of option 1. Independent variant on the base: `3665510`. There `qpos_upper_bound` still takes `Q_eq` through `upper_bound`, and callers pass it. It builds and passes `bin/build test`.

## Option 3. Located pairs of predicates from close approximations

**Lemma** (Locator.v, next to the locator lemmas):
```coq
Definition located_from_approximations (O : ReflectiveSubuniverse) {L U : Q -> Type}
  (La Ua : Qpos Q -> Q -> Type) (loc : forall e q r, q < r -> O (La e q + Ua e r))
  (lower : forall e q, La e (q + ' e) -> L q) (upper : forall e r, Ua e (r - ' e) -> U r)
  (q r : Q) (ltqr : q < r)
  : O (L q + U r)
  := O_functor O (functor_sum (lower _ q) (upper _ r)) (loc _ _ _ (lt_trisect q r ltqr)).
```
A pair of predicates is O-located if it has O-located approximations of every precision. For `q < r`, use precision `(r − q)/3`: `lt_trisect` (10 sentences) proves `q + e < r − e`. This contains the trisection once.

**Instances.**
- `locator_close` (13 sentences), with `O = purely`: a real that is within every `e` of a real with a locator has a locator. `purely` reduces, so the result is a `locator` by conversion.
- `locator_limit`: 45 → 2 sentences. It is `locator_close` with the approximation `xs (M (e/2))` given by `modulus_close_limit`.
- `locator_from_approx`: 23 → 5 sentences. A rational approximation `p` is a real `' p` with `locator_left p`.
- The locatedness of the limit cut (last component of `isdedekindcut_limit`, DedekindReals.v), with `O = Tr (-1)` and the cuts of `x (M (e/2))` as approximations: 12 → 11 sentences, and `limit_located_aux` (3) is no longer needed.

It does not need the located walk of P2.

**Not covered.**
- `box_located` exists only in track-w's P3 rewrite of DedekindReals.v, not on this base.
- The analogous locatedness proofs here, for `+` (`isdedekindcut_plus`) and `·` (`mult_located`), use `cut_approximate`. They have approximations only merely, inside the truncation, not as a family `La e`. Fitting them would need `located_from_approximations` with approximations under O (a Σ over predicate pairs inside O), which costs more than these 8-line proofs.

**Measurements** (o2 → o3):

| file | sentences | lines | sentence time (s) | wall (s) |
|---|---|---|---|---|
| Locator.v | 596 → 558 (−38) | 839 → 827 | 2.27 → 2.22 | 2.65 → 2.50 |
| DedekindReals.v | 1321 → 1317 (−4) | 1795 → 1785 | 10.33 → 9.74 | 10.61 → 10.55 |

That is 42 sentences, against the estimate of 15–20; the extra comes from `locator_from_approx`. `locator_limit` drops from 0.16 to 0.01 s, `lt_trisect` costs 0.06–0.09 s.

**Readability.** The goals are the two implications `La e (q + e) → L q` and `Ua e (r − e) → U r`, each a 3-line inequality step. In DedekindReals.v the implications are a transport along `pos_split2`.

**Risks.**
- DedekindReals.v now depends on `Analysis/Locator.v`.
- `located_from_approximations` is a transparent term.
- On Rocq 9.2 the use in the Dedekind section adds no universe constraints: the build passes (see Validation).

**Commits.** `cf58d95` on top of option 2. Independent variant on the base: `98aed67`. It does not depend on options 1 and 2, builds and passes `bin/build test`.

## Option 4. A locator for a binary operation with a modulus

**Definitions.**
```coq
Definition BinaryModulus (f : F -> F -> F)
  := forall B e : Qpos Q, {d : Qpos Q & forall u v u' v' : F,
       - ' (' B) < u < ' (' B) -> - ' (' B) < v < ' (' B) ->
       - ' (' d) < u - u' < ' (' d) -> - ' (' d) < v - v' < ' (' d) ->
       - ' (' e) < f u v - f u' v' < ' (' e)}.

Definition locator_binary (f : F -> F -> F) (fmod : BinaryModulus f)
  (frat : forall a c : Q, locator (f (' a) (' c)))
  {x y : F} (l : locator x) (m : locator y)
  : locator (f x y).
```
The modulus is data: a Σ-type. `locator_binary` (16 sentences):
- bounds `x` and `y` by `qpos_upper_bound` (option 2);
- takes `d` for that bound and the precision `e`;
- approximates `x` and `y` by rationals `a` and `c` with `tight_bound`;
- concludes with `locator_close` (option 3), using the approximation `f a c`.

**Instances.**
- `locator_plus := locator_binary (+) binarymodulus_plus …`. The modulus `binarymodulus_plus` takes `d = e/2` (4 sentences).
- `locator_times := locator_binary (.*.) binarymodulus_mult …`. The modulus `binarymodulus_mult` (19 sentences) takes `d` from the existing `mult_precision` (the precision depends on the bound) and `mult_minus_mult_lt_bound`. A new `lt_close_succ` (10) bounds the approximation `v'` by `B + 1`; it replaces `lt_bound_tight_succ` (9).
- In both, the values at rationals get their locators from `locator_left` transported along `preserves_plus`/`preserves_mult`.

Before: `locator_plus` 51 + `locator_times` 38 + `lt_bound_tight_succ` 9 + `locator_from_approx` 5 = 103 sentences. After: 16 + 4 + 19 + 10 + 2 (`plus_minus_plus`, replaced by `plus_swap_middle` after the merge) = 51. `locator_from_approx` had no uses left and is removed.

**Measurements** (o3 → o4): Locator.v 558 → 506 sentences (−52), 827 → 795 lines, sentence time 2.22 → 2.05 s, wall 2.50 → 2.42 s.

**Dependencies.** Option 4 depends on options 2 (`qpos_upper_bound`) and 3 (`locator_close`), so it has no independent variant.

**Risks.**
- `locator_plus` was `Qed` before and is now a transparent term. Nothing computes with it, since `tight_bound` is opaque.
- `BinaryModulus` is a new notion of local uniform continuity next to those of `premetric.v` and `contrib/` (see "Three notions of closeness" in `BLUEPRINT.md`). It is stated for binary operations on F only, and it would make sense to align it with whatever replaces those.
- `locator_meet` and `locator_join` could be instances too (modulus `d = e`), but their direct proofs are 10 sentences each.

**Commit.** `fbdb170`. Clean-up after the merge: `4e62c9e`.

## Commits on `abooij/claude-locators-track-l2`

| commit | content |
|---|---|
| `621fb32` | option 1 |
| `be19172` | option 2 |
| `cf58d95` | option 3 |
| `fbdb170` | option 4 |
| `895d19d` | merge of `abooij/claude-locators` (`6ccaf08`, with Track N3) |
| `4e62c9e` | `plus_swap_middle` in the modulus of addition; PicardLindelof.v drops its import of IntermediateValue.v |
| `9fa6c81` | `-s ours` merge that makes the independent variants `3665510` (option 2 on base) and `98aed67` (option 3 on base) reachable; tree unchanged |

The branch `abooij/claude-locators-track-l` holds an earlier, unrelated track (literature review), so this work went to `-track-l2` at the coordinator's request.

## Validation

- Every stack commit and both independent variants: `bin/build` and `bin/build test` pass (Rocq 9.1).
- After the merge (`895d19d`) and the clean-up (`4e62c9e`): `bin/build` and `bin/build test` pass.
- `bin/build check`, Rocq 9.2 and Rocq dev: see the final section below.
- `git diff --check` is clean on every commit.
