# Techniques from homotopy type theory for the analysis proofs

This report looks for places in the proofs added on `abooij/claude-locators` (base `9f18335`) where a technique from homotopy type theory or a general result of the Coq-HoTT library makes the analysis shorter, more uniform or more conceptual, in the spirit of the located walk of track W (P2 in `PROPOSALS.md` on `abooij/claude-locators-track-w`): one proof, generic in a reflective subuniverse, giving both a structure and a property. Each proposal has a prototype commit on `abooij/claude-locators-track-h`; nothing is merged.

Numbers: *sentences* are counted by a script that splits the source (without comments) at sentence-ending periods, so a tactic chain joined by `;` counts once; it is consistent before and after but differs slightly from the counts in `PROPOSALS.md`. *File times* are `rocq compile -time-file` totals on one core with Rocq 9.1, the minimum of three runs, each file compiled in a worktree containing exactly the base plus that proposal.

The branch stacks the prototypes on the base:

| commit | proposal | applies to the base on its own? |
|---|---|---|
| `3791b90` | H1 gluing with `merely_rec_hset` | yes (built and tested) |
| `2c9e121` | H2 one cut record indexed by a modality | yes (built and tested) |
| `f643b09` | H3 search along surjections | yes, after a trivial rename conflict with H2 in `LocatorCuts.v` (resolved copy built and tested) |
| `450273b` | H4 one walk along `nat` in a reflective subuniverse | yes (built and tested) |
| `96f87d8` | cherry-pick of track W's P2 (`7310aa0`), unchanged | independent of H1–H4 (it applied cleanly on top of them) |
| `d43e68b` | H4 applied to P2's located walk | needs H4 and P2 |

## Summary

| rank | proposal | technique | what it replaces | effect | effort | recommendation |
|---|---|---|---|---|---|---|
| 1 | **H3** search along surjections | bounded search needs only a (-1)-connected map `nat -> X`, not an equivalence | the counting argument that upgrades enumerations to equivalences (`Spaces/Nat/Enumeration.v`), `equiv_nat_rationals_qpos`, `fracfield_avoid`, `equiv_nat_fracfield`, `decidablepaths_qpos` | 261 lines removed, 101 added; `Enumeration.v` 182 → 48 lines (123 → 22 sentences); weaker hypotheses for all locator results; concrete enumerations become one lemma | small: one statement generalized in place in `Misc/BoundedSearch.v`, a rename in the analysis files | adopt |
| 2 | **H4** one walk along `nat` in a reflective subuniverse | induction inside a reflective subuniverse `O`, as a recursion scheme with early exit | four hand-written inductions with the same invariant: `merely_near_point` (`Tr (-1)`), `bisect_invariant` (`Tr (-1)`), `locator_scan` (`purely`), and P2's `located_walk` (any `O`) | the four inductions become one (`O_walk`, 9 sentences, with `O_walk_stop`, 7); instances: 16 → 7, 20 → 12, 22 → 5 + 19, 28 → 19 sentences; net −8 sentences | small | adopt, together with P2 |
| 3 | **H1** gluing with `merely_rec_hset` | a weakly constant map into a set factors through the propositional truncation (Kraus) | two hand-made "unique element of an ad-hoc proposition" constructions in `EuclideanReals.v` | 277 → 260 sentences, −19 lines; 2.80 s → 2.25 s | tiny | adopt |
| 4 | **H2** one cut record indexed by a modality | the same definition in two reflective subuniverses (`Tr (-1)`, `purely`) | the parallel records `IsCut` and `CutStructure` and the componentwise truncation between them | 332 → 316 sentences, −13 lines; the "structural counterpart" of each property becomes literal | small; renames five component names (index aliases updated) | adopt, or keep the old names as abbreviations |

New mathematics: none deep. `O_walk` and the generalized `minimal_n_alt_type` are small general lemmas; the observation behind H3 (search needs only surjectivity, so countability of a type with decidable equality never needs to be upgraded to an equivalence with `nat`) is folklore but makes a whole file unnecessary here.

The report also answers the question about arithmetic on Dedekind cuts by extension of rational operations ("Operations on cuts: the conceptual account" below): there is a more conceptual account than P3's, the interval domain, and the base code already uses its most useful part.

---

## H3. Search along surjections from `nat`

**Technique.** Being a surjection is (-1)-connectedness of a map (`IsSurjection`, i.e. `IsConnMap (Tr (-1))`): every fibre is merely inhabited. Bounded search over a type `X` (`minimal_n_alt_type`) transports a witness forward along `e : nat -> X` and never back, so it only needs every `x` to be merely hit by an index.

**Mathematics.** Let `e : nat -> X` be surjective, `P : X -> Type` decidable and `hexists P`. Then `hexists (P o e)`: from `P x` and merely `e n = x`, merely `P (e n)`. Bounded search over `nat` (`minimal_n`) gives `n` with `P (e n)`, hence `(e n; _) : {x & P x}`. Decidable equality, injectivity and an inverse are not needed.

**What it replaces.** The base states the analysis results for enumerations `Q_eq : nat <~> Q` and `QQpos_eq : nat <~> Q * Qpos Q` (as the upstream `Analysis/Locator.v` did), because `minimal_n_alt_type` took an equivalence. To supply them, the branch added `Spaces/Nat/Enumeration.v` to `theories/`: counting the elements of an unbounded decidable subset of `nat` (`subset_count` and seven lemmas), `equiv_nat_unbounded_subset`, `equiv_nat_enumeration` (a surjection with decidable equality that avoids every initial segment is an equivalence), `nat_bound` and `equiv_nat_prod_enumeration`; plus `decidablepaths_qpos` and `equiv_nat_rationals_qpos` in `Classes/theory/rationals.v` and `fracfield_avoid` and `equiv_nat_fracfield` in `integer_fractions.v`. All of this only turns surjections, which are easy to give, into equivalences, which the search does not need.

**Prototype** (`f643b09`).
- `minimal_n_alt_type` (`Misc/BoundedSearch.v`, an upstream file) is generalized in place: `(e : nat -> X) {e_surj : IsSurjection e}` instead of `(e : nat <~> X)`. The explicit arguments are unchanged, and callers passing an equivalence still work, through the coercion to a function and the instance `conn_map_isequiv`. The proof is shorter (9 sentences instead of 15).
- The analysis files take `(Q_enum : nat -> Q) {IsSurjection Q_enum}` and `(QQpos_enum : nat -> Q * Qpos Q) {IsSurjection QQpos_enum}` (renamed from `Q_eq`, `QQpos_eq`, since they are no longer equivalences). Proofs are unchanged.
- `Enumeration.v` keeps only the enumeration of pairs (`nat_unpair`, `nat_unpair_hit`) and gains `nat_prod_enumerator` with `issurj_nat_prod_enumerator`: surjections onto `X` and `Y` give one onto `X * Y`.
- `rationals_qpos_enumerator` and `issurj_rationals_qpos_enumerator` (`Classes/theory/rationals.v`) build the surjection onto `Q * Q+` from one onto `Q`, reusing the library's existing `Qpos_enumerator` (which was already stated for surjections, through the class `Enumerable`).
- `integer_fractions.v` proves `issurj_fracfield_enumerator` (3 sentences from the existing `fracfield_enumerator_hit`); `Instantiation.v` checks the two surjections for the concrete rationals.

**Effect.** 11 files, +101/−261 lines. `Enumeration.v` 182 → 48 lines, 123 → 22 sentences; `integer_fractions.v` 444 → 433 sentences; `rationals.v` 575 → 565; `BoundedSearch.v` 82 → 76. File times: `Enumeration.v` 0.20 s → 0.12 s, `integer_fractions.v` 1.62 s → 1.45 s, `rationals.v` 1.61 s → 1.56 s, `BoundedSearch.v` 0.15 s → 0.16 s. The statements of all locator results become more general. `minimal_n_alt_type` has 17 universe parameters instead of 15 (from `IsSurjection`).

**Risks.** `minimal_n_alt_type` is an upstream lemma; its new signature is backwards compatible for callers that pass the equivalence positionally, which is all callers in the library and in `contrib/`. The variables `Q_enum`/`QQpos_enum` rename `Q_eq`/`QQpos_eq` in seven files; `BLUEPRINT.md` still describes `Enumeration.v` and the equivalences (not edited, per the rules of this track).

**Overlap with track L.** Track L replaces the enumeration of `Q` in the bounds by a search over `nat`. If that removes `Q_enum` altogether, H3 still applies to `QQpos_enum` (`archimedean_structure`, `locally_nonconstant_rational`), and still removes the counting argument.

**Recommendation.** Adopt.

---

## H4. One walk along `nat` in a reflective subuniverse

**Technique.** Induction on `nat` inside a reflective subuniverse `O`, packaged once as a recursion scheme "iterate a step that may stop early": the state is `L k`, a stop is `U k`, and each step is a value in `O`. For `O = purely` (the identity modality) this is a search that computes where it stops; for `O = Tr (-1)` it proves a property by induction even though no single step can be chosen, because the whole induction runs inside the truncation. This generalizes P2's located walk from steps of a grid in a field to arbitrary step predicates.

**Mathematics.** Let `O` be a reflective subuniverse and `L U : nat -> Type`.
- *Walk* (`O_walk`). If `step : forall k < n, L k -> O (L (S k) + U k)` and `L 0`, then `O ({k & (k < n) * (L k * U k)} + L n)`. Proof: induction on `n`, with `O_rec` and `O_functor`.
- *Walk with a stop* (`O_walk_stop`). If moreover `L n -> U n`, then `O {k & (k <= n) * (L k * U k)}`.

**Instances.** Four inductions in four files had exactly this shape:

| result | file | `O` | `L k` | `U k` | step | sentences |
|---|---|---|---|---|---|---|
| `merely_near_point` | `FunctionSpace.v` | `Tr (-1)` | `p k ≤ z` | `z < p k + d` | cotransitivity of `p (S k) < p k + d` at `z` | 16 → 7 |
| `bisect_invariant` | `IntermediateValue.v` | `Tr (-1)` | `f (z k) < 0 < f (w k)` | `\|f (c k)\| < e` | the bisection step, now the lemma `bisect_step_signs` | 22 → 5 + 19 |
| `locator_scan` | `LocatorDigits.v` | `purely` | `G (a + k - 1) < x` | `x < G (a + k + 1)` | the locator at `G (a + k) < G (a + k + 1)` | 20 → 12 |
| `located_walk` + `located_close` (P2) | `Analysis/Locator.v` | any | `L (q0 + k d)` | `U (q0 + (k + 2) d)` | locatedness at `q0 + (k + 1) d < q0 + (k + 2) d` | 28 → 19 |

Through P2's `located_close`, the trisection of `tight_bound` and the walk of `cut_approximate` in the base are also this walk, so with P2 and H4 every walk along a grid in the development (structure or property) is one induction. `nat_floor` (`LocatorDigits.v`, a decidable search) is another instance with `O = purely`, but rewriting it does not shorten it, so it is left alone.

**Prototype.** `450273b` (`O_walk`, `O_walk_stop` in `Misc/BoundedSearch.v`, next to bounded search; the three instances in the base), and `d43e68b` on top of `96f87d8`, the unchanged cherry-pick of P2: `located_close` uses `O_walk_stop` directly and `located_walk` disappears.

**Effect.** Sentences: `FunctionSpace.v` 342 → 333, `LocatorDigits.v` 279 → 271, `IntermediateValue.v` 571 → 573 (the bisection step becomes its own lemma), `BoundedSearch.v` +16 (the two general lemmas), P2's two lemmas 28 → 19: net −8 sentences. File times: `FunctionSpace.v` 2.66 s → 2.36 s, `IntermediateValue.v` 5.81 s → 5.57 s, `LocatorDigits.v` 1.24 s → 1.25 s, `BoundedSearch.v` 0.15 s → 0.17 s. The gain is less in size than in uniformity: each instance now states only its step, and the invariant-carrying induction, previously written four times with `strip_truncations`/`O_rec` bookkeeping, is written once. In `IntermediateValue.v` the step of the bisection is now a lemma of its own, as `CLAUDE.md` asks for long proofs.

**Risks.** `O_walk` lives in `Misc/BoundedSearch.v`, which now imports `Modalities.ReflectiveSubuniverse` (already a dependency of `Truncations.Core`). `merely_near_point` changes the nesting of its result (`(k <= N) * (L k * U k)` instead of `((k <= N) * L k) * U k`); its one user is adapted.

**Recommendation.** Adopt together with P2.

---

## H1. Gluing restricted morphisms with `merely_rec_hset`

**Technique.** A weakly constant map `f : X -> Y` into a set factors through `merely X` (Kraus, Escardó, Coquand and Altenkirch; `merely_rec_hset` in `Truncations/Constant.v`, with definitional computation rule on `tr`). This is unique choice in its most convenient form: no auxiliary proposition has to be stated.

**What it replaces.** In the proof that the Euclidean reals are homotopy-initial, the morphism on the limits of a subset (`limits_fun`) and on a directed union of subsets (`sup_fun`) were each defined as the first component of the unique element of an ad-hoc proposition, `limits_value y := {s : S & hexists (...)}` and `sup_value y := {s : S & hexists (...)}`, with a 7- and a 9-sentence proof that it is a proposition and a 5-sentence centre. The proof of being a proposition is exactly the weak constancy of the map from witnesses to values.

**Prototype** (`3791b90`). `limits_fun` and `sup_fun` are `merely_rec_hset` applied to the map from witnesses (an approximation in `X` with the given limit; an index `k` with `y ∈ D k`), with the old weak constancy argument as the only obligation; `limits_fun_beta` and `sup_fun_beta` become one line each (`ap` of the function on `path_ishprop`).

**Effect.** `EuclideanReals.v` 506 → 487 lines, 277 → 260 sentences, three local definitions fewer; file time 2.80 s → 2.25 s.

**Risks.** `limits_fun` and `sup_fun` are declared `simpl never`, so that `cbn` in later proofs does not unfold them into `Trunc_rec`.

**Recommendation.** Adopt.

---

## H2. One record for the property and the structure of a cut

**Technique.** One definition indexed by a reflective subuniverse `O`, instantiated at `Tr (-1)` for the property and at the identity modality `purely` for the structure, as P2 does for locatedness.

**Mathematics.** For `L U : Q -> HProp` the components of a Dedekind cut are `BoundedLower O := O {q & L q}`, `BoundedUpper O`, `OpenLower O := forall q, L q -> O {q' & (q < q') * L q'}`, `OpenUpper O`, `CutLocated O := forall q < r, O (L q + U r)`, plus closedness and transitivity. `IsCutIn O` collects them. Since `O_reflector (Tr (-1)) X` is `merely X` and `O_reflector purely X` is `X` definitionally, `IsCutIn (Tr (-1))` is the old `IsCut` (with `hexists`, `hor`) and `IsCutIn purely` the old `CutStructure` (with `sig`, `sum`; `CutLocated purely` is a locator). The conversion "truncate each component" is functoriality in `O`: a family of maps `O X -> O' X` gives `IsCutIn O -> IsCutIn O'` (`iscutin_functor`).

**Prototype** (`2c9e121`, `LocatorCuts.v`, `Booij2020Thesis.v`). `IsCut := IsCutIn (Tr (-1))`, `CutStructure := IsCutIn purely`; `iscut_cutstructure` (13 sentences) is replaced by `iscutin_functor` (one term); the structural names `LowerBound`, `UpperBound`, `LowerRounding`, `UpperRounding`, `CutLocator` become `BoundedLower purely`, ..., `CutLocated purely`. The index entries for these components and for the conversion now point to the generic definitions (two entries each); no other file uses them.

**Effect.** `LocatorCuts.v` 599 → 586 lines, 332 → 316 sentences; file time 1.82 s → 1.78 s (within noise).

**Risks.** Naming: whether the thesis-style names of the structural components should survive as abbreviations (`Definition LowerBound := BoundedLower purely`, which `AGENTS.md` discourages). `IsCut` and `CutStructure` are kept, as the names of the two notions.

**Synergy with P2.** With P2's `located_close`, the approximation of a cut is one lemma for `IsCutIn O`, for every `O`. Nothing in `LocatorCuts.v` needs approximations today, so this was not added.

**Recommendation.** Adopt.

---

## Operations on cuts: the conceptual account

The user found P3's approach (arithmetic as extension of locally uniformly continuous operations, laws by continuity and density) not clearer. There is a more conceptual framing, and the base already uses its most useful part.

**The interval domain.** Call a pair `(L, U)` of predicates on `Q` that is inhabited, rounded and transitive (`L q -> U r -> q < r`) a *pre-real*: a Dedekind cut without locatedness. Order pre-reals by inclusion of both cuts, `x ⊑ y` iff `L x ⊆ L y` and `U x ⊆ U y` ("`y` is more precise"). Rational intervals `[a, b]` are the pre-reals `(q < a, b < r)`, and the pre-reals form (with resizing) a dcpo, the interval domain over `Q`, of which the rational intervals are a basis.

1. *Dedekind reals are the maximal pre-reals.* If `x` is located and `x ⊑ y`, then `y ⊑ x` (`lower_cut_incl_rev`, `upper_cut_incl_rev`), so `x = y`. This is `path_dedekindreals`, which takes exactly the two inclusions `x ⊑ y`.
2. *Operations are extensions of interval arithmetic.* An operation `F` on rational intervals that is monotone for inclusion extends to pre-reals by `q < F̂ (x, y)` iff `q < lo (F I J)` for some rational intervals `I ∋ x`, `J ∋ y`, and dually; this is the Scott-continuous extension to the interval domain. The base's multiplication (`CutBounds`, `BelowProducts`, `AboveProducts`) is this definition for the interval product, and its addition and negation are the same for the interval sum and negation.
3. *Laws need one inclusion only.* Interval arithmetic satisfies commutativity, associativity and the unit laws exactly, and distributivity and the inverse law as inclusions: `I (J + K) ⊆ I J + I K` and `0 ∈ I − I`. For Dedekind reals both sides of a law are maximal, so one inclusion suffices by 1. The base proves `mult_dedekindreals_plus_distr_l` and `plus_dedekindreals_negate_l` exactly like this: one inclusion of each cut, then `path_dedekindreals`.

**What the conceptual account does not remove.** Two things remain analytic, in any framework: (a) the extension of a located pre-real is located only if `F` maps small intervals to small intervals, a local modulus of continuity (P3's hypothesis); (b) the extension commutes with composition, `F̂ (Ĝ (x, y), z) = (F ∘ (G × id))^ (x, y, z)`, only up to a margin: the interval `G I J` lies in the closure, not the interior, of the cut of `Ĝ (x, y)`, so it has to be widened slightly, which again needs continuity of `F`. This margin is the whole content of the base's longest law, `mult_dedekindreals_assoc_lower` (with `small_factor`).

**Assessment.** A generic formalization along these lines (a record of pre-reals, the extension of an inclusion-monotone interval operation with its inhabitedness, roundedness and transitivity proved once, locatedness from a width modulus, functoriality from continuity) would be about as large as P3's framework (some 500 lines) and would share its analytic core; its advantage over P3 is that laws are inclusions of interval arithmetic plus maximality, with no continuity of the extension and no density argument. The `DomainTheory/` development could provide the dcpo structure, but none of the proofs needs suprema of directed families, only the order and maximality. So: the conceptual account explains the base's proofs of the laws (and is worth stating in the file's comments, in terms of `path_dedekindreals`), but a new framework would not make the operations shorter than P3 or the base; the cheapest improvement in this direction is P3's rounded closure for the cut properties, keeping the base's one-inclusion proofs of the laws.

---

## Investigated and rejected

- **`locator` ≃ `locator'` by library equivalences** (`Analysis/Locator.v`). For propositions `A`, `B`, `A + B ≃ {d : DHProp & (d -> A) * (~ d -> B)}` would follow from `Bool ≃ DHProp` and `{b : Bool & if b then A else B} ≃ A + B`, but the chain of equivalences (with univalence for `DHProp`) is no shorter than the existing 30-line proof of `equiv_locator_locator'`, an upstream result. Left alone.
- **Contractible hom types, three times.** `contr_cauchystructurehom_iff`, `contr_subhom_iff` and `contr_convexbodyhom_iff` each prove `Contr A <-> A * (forall a b, f a == f b)` for a type of homomorphisms whose underlying maps determine them. Each is `equiv_contr_inhabited_allpath` (Universes/HProp.v) composed with the characterization of paths between homomorphisms. Rewriting them saves some 15 lines in all, two of them are registered items, and it is a deduplication rather than a technique; left for track N3.
- **Search with approximate decisions.** `archimedean_structure`, `approximate_ivt_locator` and `locally_nonconstant_rational` (and the bounds) build decidable predicates from `locates_right`/`locates_left` and search. A general lemma "if for each `x` we can decide `W x + ~ S x`, then `hexists S` gives `{x & W x}`" (a decidable interpolant between a strong and a weak property, which is what a locator provides for `q < x`) would make these uniform. Estimated gain about 30 lines in `IntermediateValue.v`; it overlaps track L's search, so it is described rather than prototyped.
- **An `O`-generic upgrade from property to structure** (`cutstructure_iscut_locator`: a cut with a locator has the full structure). Bounds and roundedness in `O = purely` need a search, and in `O = Tr (-1)` are trivial; there is no common proof. Track L's searches over `nat` are the right tool.
- **An `O`-generic approximate intermediate value theorem.** Running the bisection invariant in `O = purely` with locators for the values does not remove the final search in `approximate_ivt_locator`, because the stage at which the limit is close enough is only merely known (from continuity).
- **A property version of the exact intermediate value theorem.** Iterating `merely_rational_apart` would need countable choice; the structure (locators) is what makes the iteration possible, so there is no `O`-generic version.
- **The search sequence of `wlpo_bisection`** (`seen`, `search` in `LocatorCuts.v`). It could be defined from the least witness of a bounded search if `Misc/BoundedSearch.v` exported it (`bounded_search` is local there); the gain is about 20 lines and touches an upstream file.
- **`IsCut` versus `IsDedekindCut`.** `iscut_iff_isdedekindcut` repackages roundedness; merging the two would need `DedekindReals.v` to import `LocatorCuts.v`, the wrong direction.
- **Identity of morphisms by the structure identity principle.** `path_cauchyapproximation`, `path_cauchystructurehom`, `path_subhom` and `path_dependentcauchyapproximation` are three-line instances of `path_sigma_hprop` after `issig`; nothing to gain.
- **Initiality.** `HoTTBookReals.v` already derives induction from initiality (Sojakova), `EuclideanReals.v` proves initiality through the fixed point theorem for subdcpos, and `Classes/orders/rationals.v` uses initiality of `Q` to show that every rational is a quotient of naturals. These are already the conceptual proofs.
- **The integration operator** (`Integral.v`). `Integration` is a hypothesis; the Riemann integral is not constructed. Unique choice (as in `limit_complete` and `supremum`) would define it from a merely existing modulus, but proving the axioms (additivity over intervals) is analysis, not a technique; see the open questions.
- **The reciprocal of a Dedekind real** (`isdedekindcut_pos_recip`, `pos_recip_dedekind_inverse`). The cut of `1 / x` is the transport of the cut of `x` along the order-reversing bijection `q ↦ 1 / q` of the positive rationals (`q < 1 / x` iff `x < 1 / q` for `q > 0`), which avoids multiplication of reals in the definition; but the inverse law still needs an approximation argument, and the file is being rewritten by P3. Mentioned as a possible follow-up.

## Side findings

- **`Funext` in the locator results** comes only from `upper_bound`, whose search predicate `locates_left` is the proposition `~ locates_right ...`, which needs `Funext` to be a proposition. `lower_bound`, `locator_limit`, `locator_minus`, `locator_recip`, `locator_meet` and `locator_from_approx` are `Funext`-free, while `upper_bound`, `tight_bound`, `archimedean_structure`, `locator_cotransitive`, `locator_plus`, `locator_times`, and through them `approximate_ivt_locator`, `exact_ivt`, `locator_integral` and `picard_lindelof` carry `Funext`. A search on `is_inr (l r (r + 1) _)`, or any of track L's searches over `nat` that avoid `locates_left`, removes `Funext` from the locator operations; whether the downstream results then become `Funext`-free as well was not checked. Sent to the coordinating session for track L.
- **`Univalence` in signed digits** (`signed_digits_locator`, `merely_locator_iff_limit` and everything downstream) enters through the library's `nat_morphism_order_embedding` (`Classes/orders/nat_int.v`), which `LocatorDigits.v` uses for the order embedding of the integers into the rationals, not through the analysis.

## Open questions for the user

1. H3 changes the signature of the upstream lemma `minimal_n_alt_type` (backwards compatible for positional callers). Acceptable, or should the surjection version be a new lemma next to it?
2. H4: is `Misc/BoundedSearch.v` the right home for `O_walk`, and is the name clear? Alternatives: `Modalities/ReflectiveSubuniverse.v` (would need `Spaces.Nat.Core`), or a short file of recursion schemes in `O`.
3. H2: keep the structural component names (`LowerBound`, ..., `CutLocator`) as abbreviations of the `purely` instances, or use the generic names everywhere as in the prototype?
4. Should the Riemann integral be constructed, so that `Integration` is no longer a hypothesis? Unique choice gives the definition; the axioms need a refinement argument for Riemann sums.

## Validation

- The stack (`d43e68b`): `bin/build`, `bin/build test` and `bin/build check` (with `rocqchk`) pass with Rocq 9.1; `git diff --check` is clean.
- Rocq 9.2 and dev (`ROCQ_IMAGE=rocq/rocq-prover:9.2`, `:dev`, each in its own worktree): the stack builds.
- Each of H1, H2, H3 (after resolving the rename conflict) and H4 was cherry-picked alone onto the base `9f18335` in its own worktree, and `bin/build` and `bin/build test` passed.
- No new axioms or admits. Registered names keep their statements, except that the index entries for the structural cut components and the conversion (H2) point to the generic definitions. `BLUEPRINT.md` is not edited; its rows on `Enumeration.v`, the enumeration hypotheses, the cut components and `iscut_cutstructure` should be updated by whoever adopts H2 and H3.
