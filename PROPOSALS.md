# Proposals for the weak spots of the development

This report investigates the weak spots listed in `BLUEPRINT.md` ("Known weak spots", "Known problems") and the rest of the new code. Each proposal has a prototype commit; nothing has been merged into `abooij/claude-locators`. Times are Rocq 9.1 on 4 cores. File times are from `rocq compile -time-file`, summed over the file's sentences on a single core, unless marked "dune" (the wall-clock duration of the file's job in `dune build --trace-file`, with 4 jobs in parallel). Per-proof figures give the summed time and the number of sentences.

The branch `abooij/claude-locators-track-w` stacks all prototypes on top of `9ee5894` (the base of this track):

| commit | proposal | builds on its own on the base? |
|---|---|---|
| `5eb5ce6` | P1 faster `strip_truncations` | yes (independent copy `48703c7`) |
| `7310aa0` | P2 located walks for locators and cuts | yes (`406066d`) |
| `7de09fb`, `e8d5842` | P3 Dedekind arithmetic by extension | needs P2 (both edit `cut_approximate`) |
| `bc38353` | P4 Picard–Lindelöf radius | yes (`f4687a4`) |

The independent copies were built and tested in separate worktrees. The stack passes `bin/build`, `bin/build test` and `bin/build check`; see "Validation" at the end for Rocq 9.2 and dev.

## Summary

| rank | proposal | effect | effort to adopt | recommendation |
|---|---|---|---|---|
| 1 | **P1** `strip_truncations` checks the head of a hypothesis first | DedekindReals 11.8 s → 5.2 s (dune); files using the tactic −14 %, about −17 % net of run-to-run noise; the tactic itself is 20× faster on a sample goal | one tactic in `theories/Truncations/Core.v`; whole library builds unchanged | adopt (and offer upstream) |
| 2 | **P2** one *located walk* lemma for any reflective subuniverse | `tight_bound` 146 → 8 sentences, `locator_plus` 54 → 12, `locator_limit` 48 → 5, `cut_approximate` 47 → 9; Locator.v 2.0 s → 1.5 s, −134 lines | small; statements unchanged | adopt |
| 3 | **P3** Dedekind operations as extensions of locally uniformly continuous maps, with laws by continuity; limit cut by rounding | the 12 longest proofs of DedekindReals.v (41–89 sentences each) disappear; ring laws are 1–5 lines; new results: closeness of cuts, continuity of all operations, uniqueness of continuous extensions; same length (1797 vs 1768 lines) and time (9.2 s vs 9.4 s); with P1, 4.1 s | larger review: the operations section of one file is rewritten; public names and statements kept | adopt, possibly after review of the new framework's names |
| 4 | **P4** Picard–Lindelöf: radius as its own lemma | `picard_lindelof` 52 → 9 sentences; 3.7 s → 3.4 s | small | adopt |
| 5 | **N1** concrete models: diagnosis of the universe pinning | four distinct causes identified (below); no prototype | upstream changes in `natpair_integers.v`, `theory/integers.v`, `interfaces/archimedean.v` | open question for the user |
| 6 | **N2** one notion of closeness and limit | plan below, no prototype | medium–large | follow-up |
| – | **N3** small duplicated helpers | list below | small, mechanical | adopt opportunistically |
| – | investigated and left alone | `char_times_*`/`hexists4`, the two bisections, IntervalObject/DomainTheory annotations, IntermediateValue.v time | – | not worth changing (reasons below) |

New mathematics:
- **The located walk** (P2): for any reflective subuniverse O, an O-located pair of predicates on an Archimedean ordered field contains a pair of points closer than any given ε. One proof gives both the search with a locator (O = identity) and the approximation of a Dedekind cut (O = propositional truncation).
- **Rounded closure** (P3): an inhabited, ordered and located pair of predicates becomes a Dedekind cut by rounding.
- **Extension by continuity** (P3): every locally uniformly continuous binary operation on ℚ extends uniquely, as a continuous operation, to the Dedekind reals.

---

## P1. A faster `strip_truncations`

**Problem.** `contrib/Analysis/DedekindReals.v` was the slowest file of the library: 11.8 s (dune), against 6.7 s for the next file, `Homotopy/Syllepsis.v`. `BLUEPRINT.md` attributes this to long proofs, but measuring per sentence shows otherwise: **6.4 s of the 9.9 s** of the file is spent in the 131 sentences that call `strip_truncations`. On one sample goal in the context of the Dedekind reals, `strip_truncations` takes 0.14–0.18 s, while `revert p; apply Trunc_rec; intros p` takes 0.003 s.

**Diagnosis** (`Set Ltac Profiling`). The tactic matches *every* hypothesis `T : _`, reverts it and tries `refine (@Trunc_ind _ _ _ _ _)`; it relies on that failing for hypotheses that are not truncations. In a section over an abstract model of ℚ the context holds about 17 instance hypotheses, and each failed `refine` costs about 13 ms of unification and typeclass search. Even for a real truncation, `Trunc_ind` costs about 15 ms, because of its typeclass search for `forall aa, IsTrunc n (P aa)`; `Trunc_rec` costs about 2 ms.

**Proposal** (`theories/Truncations/Core.v`):

```coq
Ltac strip_truncations :=
  progress repeat
    match goal with
    | [ T : ?A |- _ ]
      => lazymatch eval hnf in A with Trunc _ _ => idtac end;
        revert_opaque T;
        first [ refine (@Trunc_rec _ _ _ _ _) | refine (@Trunc_ind _ _ _ _ _) ];
        [];
        intro T
    end.
```

`hnf` unfolds `hexists`, `hor`, `merely` and `Build_HProp`-wrapped predicates to `Trunc`, exactly as the old unification did, so the tactic strips the same hypotheses. `Trunc_rec` is tried first, and is used whenever the goal does not depend on the hypothesis.

**Effect.** The sample goal takes 0.007 s instead of 0.139 s. The whole library builds unchanged with the new tactic, and all tests pass. Dune per-file times, base against P1:

| | base | P1 |
|---|---|---|
| DedekindReals.v | 11.8 s | 5.2 s |
| IntermediateValue.v | 6.8 s | 5.2 s |
| EuclideanReals.v | 3.1 s | 2.1 s |
| FunctionSpace.v | 3.3 s | 2.5 s |
| `Algebra/Rings/Ideal.v` (upstream) | 2.1 s | 1.4 s |
| the 74 files using the tactic | 100.9 s | 87.1 s |
| all other files (noise control) | 281.9 s | 294.2 s |

Wall-clock time of a full build is unchanged at 1m45s, because the critical path lies elsewhere.

**Risks.** This changes a core tactic of the library. One case would behave differently: a hypothesis whose type becomes `Trunc` only after more than head reduction, such as a let-bound type or an evar. Nothing in the library or contrib is affected. `strip_reflections` and `strip_modalities` have the same structure and probably the same cost; they were not changed.

**Recommendation.** Adopt, and propose it upstream (Coq-HoTT), since the gain is not specific to this development.

---

## P2. One located walk for tight bounds, cut approximations and locator operations

**Problem.** Three proofs walk a grid with a locator:
- `tight_bound` (`Analysis/Locator.v`, 146 sentences, 0.49 s): a trisection on `Fin` through Sperner's lemma, with long arithmetic and a `TODO`;
- `cut_approximate` (DedekindReals.v, 47 sentences): the same argument for the truncated locatedness of a cut;
- `locator_scan` (LocatorDigits.v, 25 lines): a third variant on an integer-indexed grid.

`locator_plus` (54) and `locator_limit` (48) redo trisection arithmetic inline.

**Mathematics.** Let `A` be an ordered field in which every element lies below a natural number, `O` a reflective subuniverse, and `L, U : A → Type` with `loc : q < r → O (L q + U r)`.

*Located walk.* If `L q₀` and `d > 0`, then for every `n`, `O ({q & L q × U (q + 2d)} + L (q₀ + n d))`. By induction: from `L q`, apply `loc` to `q + d < q + 2d`. Either `L (q + d)` and we continue, or `U (q + 2d)` and we stop.

*Located closeness.* If moreover `L q → U r → q < r`, and `L q₀` and `U r₀`, then `O {q & L q × U (q + 2d)}`: take `n` with `r₀ − q₀ < n d`; then `L (q₀ + n d)` is impossible.

For `O = purely` (identity modality) the hypothesis is a locator and the result is computed. For `O = Tr (-1)` the hypothesis is the locatedness of a Dedekind cut. No finite choice is needed, because the walk runs inside `O`.

*Locators from close reals* (`locator_close`): a real that is within ε of a real with a locator, for every ε, has a locator. Proof: for `q < r`, use the locator of a real within `(r − q)/3`. This contains the trisection once. `locator_limit` is an instance, with the limit within ε of `xs (M (ε/2))`.

**Prototype** (`7310aa0`; `theories/Analysis/Locator.v`, `contrib/Analysis/DedekindReals.v`):
- `located_walk`, `located_close`: generic in `O`;
- `tight_bound := located_close purely …` (8 sentences);
- `locator_approx` (a locator gives centred rational approximations, 7 sentences);
- `locator_plus` from two approximations (12);
- `locator_close` (15) and `locator_limit` (5); `locator_limit` still needs no enumeration of ℚ, nor `Funext`/`Univalence`;
- `cut_approximate := located_close (Tr (-1)) …` (9).

**Effect.** Locator.v: 2.04 s → 1.49 s, 930 → 822 lines (+160/−294 over both files). The import of `Spaces.Finite.Fin` and the local instances `inc_N_Q` and `inc_fin_N` disappear.

**Risks.** `tight_bound` and `locator_plus` are now transparent (`Defined`), as befits data. DedekindReals.v now imports `Analysis/Locator.v`. `locator_scan` (LocatorDigits.v) could also use the walk if `located_walk` returned the index of the grid point; I left it, since the digit bookkeeping (conversions between ℕ, ℤ and ℚ) would make it no shorter.

Two side findings:
- `Qpos_diff_pr` and `Q_dense` in `Classes/theory/rationals.v` require `Funext` and `Univalence` although their proofs do not need them, because they live in a section with that context. Using them silently adds these assumptions; I avoided them in `locator_close`.
- There is no general lemma `a + b + (c + d) = a + c + (b + d)`; this development has four local variants (DedekindReals.v, integer_fractions.v, CauchyCompleteness.v, and `plus_swap_middle` here). It belongs in `Classes/theory/rings.v`.

**Recommendation.** Adopt.

---

## P3. Arithmetic on Dedekind cuts by extension of continuous operations

**Problem.** In DedekindReals.v each operation came with its own long cut proof: `isdedekindcut_plus` (66 sentences), `_negate` (41), `_meet` and `_join` (56 each, order duals of each other), `_mult` (56, with `mult_lower_rounded`/`mult_upper_rounded`, 19 each, and `mult_located`, 42), and `_limit` (62). The ring laws needed `mult_dedekindreals_assoc_lower` (89) and `mult_dedekindreals_plus_distr_l` (60). Their intermediate goals were hard to follow.

**Mathematics.** Three general results, all proved in the prototype.

1. **Rounded closure** (`isdedekindcut_rounded`). Let `BL, BU : ℚ → Type` be such that both are merely inhabited, `BL q → BU r → q ≤ r`, and for `q < r` merely `BL q` or `BU r`. Then
   `L q := ∃ q' > q, BL q'` and `U r := ∃ r' < r, BU r'` form a Dedekind cut. Roundedness follows from density alone. Transitivity: `q < q' ≤ r' < r`. Locatedness: choose `q < q₁ < r₁ < r` and apply the hypothesis to `q₁ < r₁`. No operation needs its own roundedness proof any more.

2. **Extension** (`extend`). Call `f : ℚ → ℚ → ℚ` *locally uniformly continuous* if on every rational box `[a,b] × [c,d]` it merely has a modulus of uniform continuity. For reals `x, y`, let `BL q` say that `q ≤ f` on some rational box around `(x, y)`, i.e. a box `[a,b] × [c,d]` with `a < x < b` and `c < y < d`, and `BU r` dually.
   - `BL q → BU r → q ≤ r` holds for every `f`: two boxes around `(x, y)` intersect.
   - Inhabitedness and locatedness use local uniform continuity on a box small enough that `f` varies by less than `(r − q)/2` on it. Such a box comes from `cut_approximate` (P2). One then compares `f` at a corner with the midpoint of `q` and `r`.

   By rounded closure, `extend f x y` is a Dedekind real. Further properties:
   - `extend f [a] [b] = [f a b]` (`extend_rational`);
   - `extend` is commutative when `f` is (`extend_comm`);
   - for `f` monotone in both arguments, `q < extend f x y` iff `q < f s t` for some `s < x`, `t < y` (`lower_extend_monotone`).

3. **Continuity and uniqueness.** Two cuts are `e`-close (`dedekind_close`) if `q + e < x` implies `q < y` and vice versa, that is, `|x − y| ≤ e`. Reals that are `e`-close for all `e` are equal (`path_dedekind_close`), and every real is `e`-close to a rational (`merely_dedekind_close_rational`).
   - `extend f` is jointly continuous (`extend_continuous`). Proof: widen a small box around `(x, y)` by `2δ`; the widened box contains a box around every δ-close `(x', y')`, and lower bounds on boxes transfer up to `e/2` (`boxabove_transfer`).
   - Hence continuous functions `ℝ → ℝ` that agree on ℚ are equal (`eq_continuous_rationals`), and likewise separately continuous functions of two or three arguments (`eq_continuous_rationals2`, `…3`).
   - Consequently every identity between such operations on ℚ holds for their extensions (`extend_assoc`, `extend_distr`, the unit and inverse laws). Each proof is `eq_continuous_rationals…`, a small continuity tactic, and `extend_rational`.

Instances: `+`, `·`, `min`, `max` and `(s, t) ↦ −s`. The modulus for `·` on a box comes from `mult_minus_mult_lt_bound`; for `min`/`max` the modulus is `e` itself.

The limit cut fits the same mould: `q < l` iff `q + e + d < x (M e)` for some `e` and `d` is the rounded closure of `q + e < x (M e)`. Only inhabitedness, `q ≤ r` and locatedness remain to be shown (12 + 18 sentences).

**Prototype** (`7de09fb`, `e8d5842`; only `contrib/Analysis/DedekindReals.v`). Public names and statements are kept, including `IsDedekindCut`, `limit_dedekind`, `rational_dedekind_plus/mult`, the order and field instances and `iscomplete_dedekindreals`, so `contrib/Booij2020Thesis.v` and all other files build unchanged. The internal predicates are new: `plus_lower`, `mult_lower`, `BelowProducts` and `limit_lower` are replaced by `BoxAbove`/`BoxBelow` and `limit_below`/`limit_above`.

| | before (after P2) | after P3 |
|---|---|---|
| lines | 1768 | 1797 |
| file time | 9.4 s | 9.2 s |
| file time with P1 | – | 4.1 s |
| longest proofs (sentences) | 89, 66, 62, 60, 58, 56 ×3 | 81 (`isdedekindcut_pos_recip`, unchanged), 58 (`pos_recip_dedekind_inverse`, unchanged), 43 (`isdedekindcut_rounded`), 36 (`iscring_dedekindreals`, 11 laws), 35 (`extend_continuous`) |
| ring laws | 11 separate cut arguments | `extend_assoc`/`extend_distr` (5 sentences each) and one-line instances |
| new results | – | closeness of cuts, continuity of every operation, uniqueness of continuous extensions, monotone characterization |

The length stays about the same because the general framework (rounding, boxes, closeness, continuity, properties of extensions) takes about 500 lines. Each operation now costs a modulus of continuity (1–15 lines) plus, when needed, a description of its cut (16–21 lines). A new operation (absolute value, a polynomial, a clamped function) would cost only its modulus.

**Risks and costs.**
- The proofs of the reciprocal (`isdedekindcut_pos_recip`, `pos_recip_dedekind_inverse`) are untouched. The reciprocal is an *inverse* of a monotone map, not an extension, and fits a different principle: inverting a strictly monotone continuous function. That is a natural follow-up.
- Multiplication is now defined with a margin (`q ≤ f` on a box, then rounded), not as `q < s t` for all points of a box. The two are equivalent, but the internal shape changed.
- The local continuity tactic must use `refine` with fixed arity: with `napply` it made 961 `refine` attempts and cost 2.5 s.

**Recommendation.** Adopt, ideally together with P1 (the stack). Possible follow-ups:
- move closeness of cuts and continuity to the premetric of N2;
- treat the reciprocal by monotone inversion;
- reuse `isdedekindcut_rounded` in `LocatorCuts.v`, whose structural cuts have the same shape.

---

## P4. Picard–Lindelöf: the radius as its own lemma

**Problem.** `picard_lindelof` (52 sentences, 0.65 s) chose the radius `l = min(a, b/K, 1/(2 r_L))`, proved its four bounds, bounded the width of the target interval and assembled the solution, all in one proof.

**Prototype** (`bc38353`, `contrib/Analysis/PicardLindelof.v`):
- `picard_radius K`: `l` with a locator, `0 < l`, `l ≤ a`, `K l ≤ b` and `L l ≤ 1/2` (34 sentences, one bullet per bound);
- `picard_width_bound` (8);
- `picard_lindelof` (9): `picard_bound`, then `picard_radius`, then `picard_solution`.

The statement of `picard_lindelof` is unchanged. File time 3.72 s → 3.36 s, +40/−28 lines.

**Not done.** `BLUEPRINT.md` also suggests moving the integral estimates of `islipschitz_picard_map` (26 sentences, 0.5 s) into `Integral.v`. They are already stated as integral lemmas there (`integral_abs_le`, `integral_minus`); what remains is specific to the Picard map. `abs_le_uniform` (42) is a chain argument about uniformly continuous maps on boxes. It belongs in `FunctionSpace.v` next to `grid_point`, but moving it changes no proof.

**Recommendation.** Adopt.

---

## N1. Concrete models: what pins the universes

`contrib/Analysis/Instantiation.v` only checks the hypotheses, because applying the main results to `Rm := DedekindReals (FracField.F (NatPair.Z nat))` fails. I found four distinct causes.

1. **A global universe in the integers.** `Classes/interfaces/canonical_names.v` declares `Monomorphic Universe Ularge Uhuge`. `natpair_integers.v` eliminates the quotient into `HProp` at `Ularge` (`Zle_HProp` uses `Z_rec2@{Ularge Ularge}`) and fixes instances such as `Z_partial_order'@{Ularge …}`, a workaround from "Coq pre 8.8". Consequently `NatPair.Zle`, `Zlt`, `Zapart` and `Z_abs` all carry the constraint `UN < Ularge` with a *global* `Ularge`. So do `int_dec`, `slow_int_abs` and everything built on them, for instance `rationals_fracfield` has `UZ < Ularge`.
   *Fix:* make `Ularge` a section universe (polymorphic), or drop the annotations and let Rocq 9 infer them.
2. **One universe for an integer and the rings it maps to.** The section `contents` of `Classes/theory/integers.v` fixes `Integers@{U U U U U U U U} Z`. The target-ring universe of `IntegersToRing` is thereby the universe of `Z`, so `int_dec`, `slow_int_abs` and `int_zero_product` apply only to rings in the universe of `Z`. This is why `integer_fractions.v` maps the integers through `IntAbs` instead of `integers_to_ring`.
   *Fix:* give the section two universes, the carrier and the target.
3. **The characteristic proof in `ArchimedeanProperty`.** `ArchimedeanProperty` takes `Achar : FieldCharacteristic F 0` as an argument, and its definition `qinc := rationals_to_field Q F` forces the universe of the target of `RationalsToField` to *equal* the universe of `F`. Its signature contains the constraints `u7 = u9`, `u8 = u12`. The Dedekind reals derive `Achar` differently from `ordered_characteristic_0`, hence `archimedean_property_change_char`. When unifying two such instances, the unifier unfolds the characteristic proofs and generates universe equalities.
   *Fix (upstream):* derive the characteristic inside the class from `OrderedField F`, as the comment in `interfaces/archimedean.v` already suggests. `archimedean_property_change_char` would then go away.
4. **The `Rationals` instance is not cumulative in its target universe.** Elaborated without a type ascription and with universe-polymorphic definitions, `archimedean_dedekindreals Qm …` typechecks. The universe chain is consistent: `Q < R`, target of `RationalsToField` = `R`. But passing it (even through `archimedean_property_change_char`) to `merely_locator_iff_limit Qm Rm` with `(Qrats := rationals_Qm)` still fails with "Cannot enforce u = v because v < u". My hypothesis is that the one term `rationals_Qm` occurs inside the type of `orderedfield_Rm` at one universe instance, used for fields in the universe of ℚ, and is required at the universe of `Rm` by the theorem. With an abstract `Q`, `Qrats` is a section variable and the two uses get independent universes; with a concrete term they cannot, because the classes `RationalsToField`/`Rationals` are not cumulative.
   *Possible fix:* declare these classes `#[universes(cumulative)]`, or let `Rationals` quantify over the target universe inside its fields (it already does for `rationals_to_field`, but not for the instance as a whole). I have not verified this; it needs an experiment on the upstream interfaces.

Causes 1 and 2 are mechanical fixes in `theories/`. Cause 3 is a change to an upstream interface. Cause 4 needs an experiment on the interfaces. **Open question for the user:** is it worth changing the upstream interfaces (`Rationals`, `ArchimedeanProperty`) for this, or should the concrete instantiation stay at "hypotheses checked"?

---

## N2. One notion of closeness and limit (plan, no prototype)

There are three closeness notions, and limits come in three forms:
- `Classes/theory/premetric.v` (`Closeness`, over the axiomatized `assume_rationals.Q`);
- `IsPremetric`/`metric_close` in `MetricSpace.v`;
- `field_close`/`rational_close` in `CauchyCompleteness.v`, plus `dedekind_close` from P3 (a fourth, on cuts);
- limits as `IsLimit` (`interfaces/cauchy.v`: `- e < l - x n < e`), `IsMetricLimit close` (`close e (x n) l`) and `IsApproximationLimit`.

Note that `IsLimit Q F x l` and `IsMetricLimit (field_close Q) x l` are *not* definitionally equal: the difference is taken in the opposite order.

Plan:
- (a) make `field_close` the canonical premetric of an ordered field, and define `rational_close := field_close` with `F := Q` (this needs `rationals_to_field Q Q = id`, which holds propositionally);
- (b) restate `IsLimit` as `IsMetricLimit (field_close Q)`, or prove `islimit_iff_ismetriclimit` once;
- (c) generalize `premetric.v` from `assume_rationals.Q` to an arbitrary `Q`, as `BLUEPRINT.md` suggests;
- (d) give the Dedekind reals the premetric `dedekind_close` from P3; `iscomplete_dedekindreals` then becomes completeness for that premetric.

This would also let the bisection in `LocatorCuts.v` reuse `cauchymodulus_nested` from `IntermediateValue.v`: today one works with `rational_close` in ℚ and the other with `field_close` in an ordered field, which is the only obstacle to sharing.

---

## N3. Small duplicated helpers (list)

Each of these is a two-to-five line lemma proved more than once:
- *Two points of an interval of width < D are D-close:* `field_close_interval` (IntermediateValue), `rational_close_interval` (LocatorCuts), `interval_close` (DedekindReals), `interval_dist_le` (PicardLindelof).
- *`q < q + e` and `q − e < q` for `e : Qpos Q`:* `ltQposQ`/`ltQnegQ` (Locator), `lt_plus_pos`/`minus_pos_lt` (DedekindReals), `lt_plus_qpos`/`lt_minus_qpos` (IntermediateValue).
- *`e/2 < e`:* `qpos_half_lt` (IntermediateValue, in ℚ; FunctionSpace, in F), `pos_quarter_double` (DedekindReals).
- `locator_0`: IntermediateValue and Integral.
- `half_pos`/`half_lt_1`: IntermediateValue and PicardLindelof, with different meanings.
- *A positive rational upper bound from a locator:* `qpos_upper_bound` (IntermediateValue), `qpos_of_upper_bound` (PicardLindelof).
- *A rational bound on a width:* `merely_bound` (IntermediateValue), `merely_rational_bound` (FunctionSpace).
- *Closeness weakening:* `close_weaken` (LocatorDigits) vs `field_close_weaken`.
- *Swapping middle terms:* `minus_plus_minus` in integer_fractions.v and in CauchyCompleteness.v (different statements, same name), `plus_swap_middle` (P2), `mult_swap_middle` (integer_fractions.v).

Recommendation: put the ℚ-level ones in `Classes/theory/rationals.v` (but outside its `Funext`/`Univalence` section, see P2) or `Classes/orders/rationals.v`, put the ring ones in `Classes/theory/rings.v`, and replace the local copies when the files are touched next. None is worth a separate pass.

---

## Investigated and left alone

- **`hexists4` and `char_times_left/right`** (`Classes/orders/archimedean.v`). The shared approximation is already factored out (`archimedean_mult_approx`), and so are the corner lemmas (`lt_mult_corners_l`, `mult_corners_lt_r`). The remaining duplication is the four-corner `meet`/`join` plumbing. Deriving the right lemma from the left by negation needs `meet (−a) (−b) = −join a b` on ℚ, plus reassociation of four corners, and costs about as much as it saves. Restating with a box quantifier (`∀ u ∈ [a,b], w ∈ [c,d], q < u w`) is shorter and would remove the lattice assumption on ℚ, but it loses the finite, decidable corner data that makes the lemma useful for locators. With P1 the two proofs cost 0.1 s each. `hexists4` is just a 4-tuple existential; replacing it by `hexists (fun abcd : Q * Q * Q * Q => …)` changes nothing of substance.
- **The two bisections.** They are different algorithms: an interpolating bisection in F with continuous weights, and a Boolean search in ℚ with an eventually constant sequence. Only the nested-interval bookkeeping is shared, and see N2 for what would let them share it.
- **Universe annotations in `IntervalObject.v`.** Removing all 14 annotations makes the universe signatures grow, e.g. `IsIterationOperator@{i}` becomes `@{u u0 u1}` with `u ≤ u0`; `Local Set Universe Minimization ToSet` does not recover the annotated signatures. So they are needed. However, `ishprop_iteratedmidpoints` and `equiv_iteration_operator_contr_iterated_midpoints` still carry 6 and 8 phantom universes from `funext`/`path_sigma_hprop` in their proofs; `@{}` on them fails with "universes … are unbound". Cosmetic only.
- **`DomainTheory/` annotations.** They implement the predicative universe discipline of TypeTopology (index, carrier, order, statement universes). They are deliberate and documented; nothing to remove.
- **IntermediateValue.v (5.5 s with P1).** No proof above 0.4 s; the time is spread over 988 lines, plus 0.4 s to close the section. Splitting the section would save at most that.

---

## Validation

- Stack (`abooij/claude-locators-track-w`): `bin/build`, `bin/build test` and `bin/build check` pass with Rocq 9.1.
- Each independent commit (`48703c7`, `406066d`, `f4687a4`) was built (`bin/build`, `bin/build test`) on top of the base in its own worktree; `31ed89c` and `1a2ad32` on top of `406066d`.
- Rocq 9.2 and dev: see the message to the coordinating session for the results of `ROCQ_IMAGE=rocq/rocq-prover:9.2 bin/build` and `ROCQ_IMAGE=rocq/rocq-prover:dev bin/build` on the stack.
- No new axioms or admits. Names and statements used by `contrib/Booij2020Thesis.v` are unchanged, so no alias needed updating. `BLUEPRINT.md` is not edited: its weak-spot entries should be updated by whoever adopts the proposals.
