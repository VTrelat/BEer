# What costs cvc5 time in BEer's output

Investigation on `beer-lite`, baseline commit `f5e4e03` — the commit the
Grid'5000 campaign measured.

## Method

- **Samples.** Two disjoint stratified samples drawn from the campaign's
  `summary/goals.csv`, by outcome class (`ppTrans-only`, `both`, `BEer-only`,
  `neither`) and by `max_order`, grouped so goals share `.pog` files:
  sample 1 = 453 goals over 64 files, sample 2 = 418 goals over 56 files.
  BEer does not encode every goal (some files hit the encoding timeout), so
  every comparison is taken over the goals both sides produced: 396 and 302.
- **Reference.** ppTrans scripts generated locally with the Atelier B the
  campaign used (24.04.2), `ppTransSmt -n -i <pog> -o <pfx>`; its per-goal
  filenames line up one-to-one with `po_<i>_goal_<j>.smt2`.
- **Solver.** cvc5 1.3.2 (campaign: 1.3.4), `--mbqi`, no `--incremental`,
  5 processes in parallel on 8 cores, so wall times are inflated equally for
  every tag. Two budgets: `--tlimit-per=5000` (campaign parity) and 2000.
- **Prelude.** `:produce-unsat-cores` stripped, as the campaign harness does.

Encoder tags: `base` = `f5e4e03`; `onepoint` = base + one-point elimination;
`full` = onepoint + dead-declaration pruning + assertion dedup + helper sharing;
`trigE` = full + instantiation patterns; `dom` = trigE + `dom`/`ran` as
constructors, i.e. the final state.

## Results

```
                                    sample 1        sample 1        sample 2
                                    @5000 ms        @2000 ms        @2000 ms
                                   (396 goals)     (396 goals)     (302 goals)
baseline f5e4e03                        168             132             104
+ one-point, pruning, dedup, sharing    182             168             123
+ instantiation patterns                193             184             133
+ dom/ran as constructors               244              --             166
                                     (61.6%)                          (55.0%)
```

Against ppTrans on the same 396 goals at 5000 ms, `ppTrans-only` falls from
**152 to 82**:

```
baseline      both 136   BEer-only 32   ppTrans-only 152   neither 76
all changes   both 206   BEer-only 38   ppTrans-only  82   neither 70
```

By type order, the whole of the order-2 deficit closes:

```
order    n    base    now   ppTrans
  0     12     83%    92%     100%
  1    171     57%    70%      83%
  2    179     28%    58%      60%
  3     32     28%    28%      78%
  4      2      0%     0%     100%
```

Step by step, on the goals common to each pair:

```
step                                     sample/budget       n   from    to  gained  lost
encoder changes                          s1 @5000 ms       396    168   182     +26   -12
encoder changes                          s1 @2000 ms       396    132   168     +42    -6
encoder changes                          s2 @2000 ms       302    104   123     +20    -1
patterns                                 s1 @5000 ms       396    182   193     +19    -8
patterns                                 s2 @2000 ms       302    123   133     +14    -4
```

On the goals both settings prove:

```
encoder changes   s1 @5000 ms  156 goals   median 1045 -> 659 ms   1.33x
encoder changes   s1 @2000 ms  126 goals   median 1222 -> 391 ms   2.53x
encoder changes   s2 @2000 ms  103 goals   median 1143 -> 709 ms   1.66x
patterns          s1 @5000 ms  174 goals   median  735 -> 367 ms   1.60x
patterns          s2 @2000 ms  119 goals   median  810 -> 404 ms   1.96x
```

Script size, and encoding cost (sum of per-file wall seconds):

```
              n   median      total    encode
base        396   366.6 KB   399.7 MB   1797 s
onepoint    396   225.1 KB   219.1 MB   1580 s
full        396   201.1 KB   176.8 MB   1742 s
ppTrans     453   178.4 KB   125.5 MB     58 s
base2       302   300.1 KB   214.8 MB   1856 s
full2       310   207.7 KB   127.2 MB   1850 s
```

Encoding cost is unchanged; the smaller terms pay for the extra simplification
work. On sample 2 the changed encoder finished **310** goals against the
baseline's 302 under the same 90 s cap — the size reduction buys a little
coverage as well.

Intermediate step, for attribution — after the four formula-level changes but
*before* patterns and `dom`/`ran` (sample 1, 5000 ms, same 396 goals). At this
point order 2 was still moving the wrong way; `dom`/`ran` is what fixed it:

```
              both  BEer-only  ppTrans-only  neither
base           136         32           152       76
full           149         33           139       75

order    n    base   full   ppTrans
  0     12     83%    83%     100%
  1    171     57%    67%      83%
  2    179     28%    26%      60%
  3     32     28%    34%      78%
  4      2      0%     0%     100%
```

**For the formula-level changes and patterns, the gain shrinks as the budget
grows** (+36 at 2000 ms against +14 at 5000 ms): most of what they buy is
speed, so a longer budget lets the baseline catch up. `dom`/`ran` is not like
that — it removes a quantifier rather than shortening a search, and it gains
+59 at 5000 ms.

## The changes

### 1. One-point elimination (`Encoder/Simplifier.lean`)

`Encoder/Loosening/Rules.lean` states every cast as "there is a value related to
the source", including when the relation is the identity. `castPath.pair` with
two reflexive components emits

```smt
(exists ((fst69 Int) (snd70 Int))
  (and (= pair68 (pair fst69 snd70))
       (and (= fst69 (fst funGraph67)) (= snd70 (snd funGraph67)))))
```

which says no more than `pair68 = funGraph67`, and `castPath.graph` wraps
another existential around it — so the cost compounds with type order. The
same shape appears in `cprod`, whose domain test over `BOOL × INTEGER` reduces
to `∃ a b. p = ⟨a,b⟩`, i.e. `true`.

Rather than special-casing each rule, the simplifier now applies

```
∃ v⃗. … ∧ v = t ∧ …       ⟶   the rest with t for v      (v ∉ fv t)
∀ v⃗. … ⇒ v = t ⇒ …       ⟶   the rest with t for v
∃ a b. … ∧ x = ⟨a,b⟩ ∧ …  ⟶   the rest with fst x / snd x
∀ a b. … ⇒ x = ⟨a,b⟩ ⇒ …  ⟶   the rest with fst x / snd x
```

The last two hold because `Pair` has a single constructor and is therefore
surjective. All four are equivalences: **no incompleteness in either
direction**.

Two details that matter:

- Single-variable equations are tried before pair ones. `p = ⟨a,b⟩` alongside
  `a = fst q, b = snd q` collapses to `p = q` if the components go first, and
  to the strictly larger `fst p = fst q ∧ snd p = snd q` if the pair does.
- Only *duplicable* right-hand sides are substituted (variables, and
  projections/injections built from them), so the rule cannot copy a cast
  helper's whole lambda into a dozen positions and trade quantifiers for size.

`subst` does not rename, so the rule declines to fire when a replacement
mentions a name the remaining conjuncts bind. The guard never fires on either
sample — all 396 scripts are byte-identical with and without it — but source
names are not globally unique (Atelier B numbers binders per scope, which is
why `SMT.saveShadowed` exists), so it is checked rather than assumed.

Option needs no separate rule: `castPath.opt` emits
`∃ v. x! = some v ∧ v = the x`, which the variable rule handles.

### 2. Dead declarations (`SMT.Env.pruneUnused`)

In a median per-goal script, **2032 of 2919 `declare-const`s are mentioned
nowhere else in the file** — 54.8 KB of 230.5 KB, a quarter of the bytes.

Root cause: `POGReader.freshVar` (`POGReader/Basic.lean:53`) names the binders
of the derived operators `x<n>` and calls `addToContext`, so they land in
`B.Env.context`; `encodeTypeContext` copies the whole context into the SMT type
context and `encodeDefs` turns every entry into a `declare-const`. The names
then only ever occur as λ/∀ binders in the emitted terms, where they are
shadowed. Fixing it at the source would mean not registering binder types,
which the encoder's own binder handling relies on; pruning at emission is the
conservative fix.

Only `declare-const` is dropped — a `define-fun` may be the definition a later
`assert` names, and a name occurring solely as a binder rightly does not count
as a use.

### 3. Duplicate assertions

9.4% of the assertions of a per-goal script are exact duplicates: a `.pog`
repeats its `distinct` groups and `finite` facts (the same enumerated set is
`distinct` under every machine that sees it) and obligations repeat hypotheses.
Deduplicated on the B side (`E.distinct`, `E.finite`, `φ.hyps`, `g.hyps`), so
the cast helpers a repeated hypothesis needs are also built only once.

### 4. Sharing the partial-function form of a relation (`castApp`)

Every application of a B function used to introduce its own
`f : τ → Option σ` plus its own copy of `∀ u v. R⟨u,v⟩ ↔ f u = some v`, leaving
the solver to prove the copies equal before using any of them.
`asPartialFun` memoises on the encoded relation, and `loosenShared` does the
same for the loosenings `castApp` performs.

Sharing only fires when the encoded relation is syntactically identical.
`encodeTerm` allocates fresh binder names on every call, so two occurrences of
the same B set term encode to α-equivalent but non-identical SMT terms and are
not shared. Making site lookup α-insensitive, or memoising `encodeTerm` at the
B level, is the remaining work here.

### 5. Instantiation patterns (`SMT/Syntax.lean`)

Worth about as much as the other four together. cvc5 selects triggers itself
when a quantifier carries none, and on this output it selects badly.

`Term.toString` now computes a trigger set when it prints a `forall`: candidate
application terms are collected from the body, the smallest set covering every
bound variable is kept, and the body is wrapped in
`(! … :pattern (…))`. Nothing else in the encoder changes — no new `Term`
constructor, so no new cases in `subst`/`fv`/`bv`/`simplifier`/typing. The
printer becomes `partial`, since a chosen pattern is not a structural subterm
of what is being printed.

Three constraints make a candidate legal, and the third is specific to this
encoder: a trigger must be a term rather than a formula; it must not contain a
binder; and it must not mention a variable bound *outside* the quantifier being
printed. `encodeTerm .all` re-scopes cast helpers as `∀ h. spec ⇒ body`, so
`app!N` is frequently a bound variable rather than a constant, and a pattern
naming it is out of scope where it is written. A first attempt that scanned the
text with a regex got exactly this wrong and produced files cvc5 rejected with
`Symbol 'app!4157' not declared as a variable`.

**Incompleteness.** Triggers *restrict* instantiation, so this errs in the safe
direction: a goal needing an instantiation no pattern matches is lost, none
becomes provable that was not. Measured at 8 lost against 19 gained (sample 1,
5000 ms) and 4 against 14 (sample 2). A quantifier whose binders cannot all be
covered keeps no pattern, leaving cvc5's own choice in place.

Four goals move from `unknown` to cvc5 *error*, all of the
`Could not evaluate … in getValue` class below: the files parse, and patterns
simply get cvc5 far enough to trip its own model-construction bug. No proof is
lost by it.

A textual post-processor over the emitted scripts scores slightly better than
the in-encoder selection (196 against 193 at 5000 ms, 11 goals where they
disagree). The gap is trigger-choice detail and is within the noise of these
counts; it was not tuned further.


### 6. `dom`/`ran` as constructors (`B/Syntax/Basic.lean`, `Encoder/Encoder.lean`)

The largest single change here: +59/-8 at 5000 ms, +35/-2 on the second sample.

`dom` was derived in `POGReader/Builtins.lean` as
`{ x | ∃ y. x ↦ y ∈ R }`.  That expansion happens in the *reader*, which cannot
see which representation the encoder will pick, so it always produced the
relational form — including for a variable flagged as a partial function, where
the domain is simply the points at which it is defined:

```smt
(lambda ((x A)) (not (= (R x) (as none (Option B)))))
```

No quantifier, no helper, no axiom.  That is the payoff the `α → Option β`
representation exists for, and deriving `dom` at read time threw it away at
every occurrence — in a corpus where 400 sampled `.pog` files contain 41547
`dom` and 31404 `ran` nodes, and 383 of the 400 use `dom` at all.

Making them constructors moves the choice into `encodeTerm`, which is where the
representation is known — the same reason `pow` and `closure` are constructors.
The other three cells (`dom` of a relation, `ran` of either) still need the
existential, but are emitted directly rather than through `Collect`/`Exists`,
so they lose the domain guards the derived form wrapped around them.

The derived `B.Term.dom`/`ran` are gone, so `overload`, `tot`, `toFunction` and
`size` inherit the same treatment — `overload` in particular built a `dom`
internally on every use.

Nothing is axiomatised, so unlike a `Site` this carries no completeness risk in
either direction.

## Negative results

### Triggers are at their plateau

Four further axes were tried and none moved the number.

**Coverage is already maximal.** 65% of quantifiers get a pattern; of the rest,
3218 of 3220 sampled have *no legal candidate at all* — their binders occur only
under arithmetic or equality, and SMT-LIB forbids an interpreted symbol at the
head of a trigger. There is nothing to give them.

**`--user-pat=use` recovers nothing.** cvc5's default is `trust`: where a
quantifier carries a user pattern, its own selection is discarded. `use` keeps
both. Result 181 against 181, +1/-1, and **0 of the 9 goals lost to patterns
come back**. So the losses are not "cvc5's own trigger was better" — putting it
back changes nothing.

**Selection policy is a wash** (sample 1, 2000 ms, 396 goals):

```
no patterns                       168   median 616 ms   wall 860 s
smallest covering term (shipped)  184   median 283 ms   wall 612 s
one :pattern clause per term      184   median 309 ms   wall 623 s
largest covering term             182   median 343 ms   wall 632 s
```

**Triggers on the prelude's `bpow` axioms do nothing.** `prelude.smt` is a
fixed text file, so it never passes through the printer and carried no patterns
— and `bpow`'s recursion `bpow a n = a * bpow a (n-1)` is the one family that
can unfold forever, which is why ppTrans pins its `exp` axioms with
`:pattern ((exp x n))`. Adding the analogous patterns: 181 against 181, +0/-0,
on a sample where 274 of 396 goals do use `bpow`. cvc5 already picks
`(bpow a n)` itself. Change reverted.


### The 5359 goals lost to patterns cannot be bought back

The full campaign A/B of `f5e4e03` against `7da3479` moved 5359 goals from
`both prove` to `ppTrans only`. All 5359 are timeouts at the 5000 ms budget, on
*smaller* scripts, so nothing was lost from the encoding — and one of them,
`0015/00350` PO 0 goal 4, is a 3876-byte file that flips on a single
annotation:

```
cvc5 --tlimit-per=5000 --mbqi                     -> unknown  5.08 s
cvc5 --tlimit-per=5000 --mbqi --user-pat=ignore   -> unsat    0.01 s
```

The annotation is the shared partial-function axiom of `b6f1766`, whose
inferred trigger names a constructed pair:

```
(forall ((x129 Int) (x130 Int))
  (! (= (app!123 (pair x129 x130)) (= (app!128 x129) (some x130)))
     :pattern ((app!128 x129) (app!123 (pair x129 x130)))))
```

Rewriting that one trigger by hand identifies the culprit precisely — and it is
not "a constructor over the binders", which is the reading the shape invites:

```
{app!128 x, app!123 (pair x y)}   as emitted        unknown  5 s
{app!123 (pair x y)}              alone             unknown  5 s
{app!128 x, pair x y}             no λ-defined head unknown  5 s
{app!128 x, some y}               constructor!      unsat    0.01 s
no pattern                                          unsat
```

`(some y)` over a binder is fine; `(pair x y)` is fatal. The discriminator is
how many ground terms the element matches — this encoding builds a `Pair` per
relation application, so a `Pair`-sorted element restricts nothing, while
`some`-headed terms are comparatively rare. It is a matching *blowup*, not a
matching loop, with the same signature: the budget goes on enumerating
instances and MBQI is never reached.

Five policies were then measured against `7da3479` on 400-goal samples of each
of three populations — the 5359 regressed, the 26263 newly won, and the 107153
proved under both — one script per goal at campaign settings:

```
policy                                    regressed    won   held   corpus net
B  reject built structure over binders          +78      -       -            -
C  B, plus constructor terms as candidates      +79    -81     -2       -4713
D  C with `some`/`the` only                     +80    -79     -1        ~ C
E  constructor candidates, no rejection          +3     -4      0        -228
F  rewrite only the partial-function axiom       +2      0      0        -103
```

`C` is the interesting one and it fails outright. The `(R (pair u v))` family
is *simultaneously* what loses the 5359 and what wins the 26263: on the 84 won
goals `C` gives up it strips patterns 192 → 34. Suppressing the family recovers
about 20% of a population of 5359 and gives back about 20% of a population 4.9
times larger. Breaking even needs a 4.9:1 recovery-to-loss ratio; `C` manages
1.35:1. `D` differs only in which constructor heads are admissible and lands in
the same place, so the specific rule is not what is wrong — the strategy is.

`E` and `F` are the other direction: leave every candidate in place and let a
better one outrank it (`E`), or rewrite nothing but the one axiom measured to
blow up (`F`). Both are inside the noise floor. `F` rewrites 1584 triggers in
the regressed sample and moves two goals. The reproducer is genuine and
unrepresentative of its own population.

**Only about a third of the regression is patterns at all.** On the regressed
sample `f5e4e03` proves 376 of 404 and `7da3479` proves 6; emitting no patterns
whatever reaches 125. So (125-6)/(376-6) = 32% is attributable to `4596e9c`,
and the remaining 68% belongs to `2036e54`, `b6f1766` or `cfee023`. Not
isolated further.

Two measurement notes for anyone repeating this:

- **`--user-pat=ignore` is not the same as emitting no patterns.** On identical
  goals it scores 92 where a build that emits none scores 125 — it understates
  the trigger ceiling by a quarter, so it is a good diagnostic and a bad
  yardstick.
- **The noise floor is wide.** Across three runs of the same 400 goals under the
  same binary, `7da3479` scored 395/401/399 on the held sample and 314/331/339
  on the won sample. Deltas under about ±2% on `won` are not real, which is why
  `E` and `F` are reported as no-ops rather than as small losses.


### The instantiation strategy is not the lever

The smallest `ppTrans-only` goal in the corpus — `0030/00001` PO 4 goal 2, four
expression nodes, no hypotheses, ppTrans 15.6 ms — looks like an indictment of
`--mbqi`:

```
cvc5 --tlimit-per=5000 --mbqi       po_4_goal_2.smt2  ->  unknown   5.1 s
cvc5 --tlimit-per=5000 --enum-inst  po_4_goal_2.smt2  ->  unsat    0.03 s
cvc5 --tlimit-per=5000              po_4_goal_2.smt2  ->  unknown  0.02 s
```

It is not. Over the sample, `--enum-inst` never adds a goal the `--mbqi` run
does not already get, and costs more wall time (2501 s against 1741 s):

```
union over configurations, 396 goals
base      mbqi 168   enum 149   UNION 168
onepoint  mbqi 170   enum 170   UNION 171
full      mbqi 182   enum 177   UNION 182
```

One effect survives: on the baseline the two strategies differ by 19 goals;
after one-point elimination they agree. The encoding stops being sensitive to
which instantiation strategy runs.

`(set-option :enum-inst true)` in the prelude works only when cvc5 is not given
`--mbqi` on the command line. Given the above there is no reason to add it.

### Trigger benefit is specific to cvc5's E-matching

`:pattern` is standard SMT-LIB 2.6 syntax, but *which* triggers help is an
artefact of the implementation.  z3 4.16 reads only the 75 sample scripts that
avoid higher-order application, and on those patterns cost goals rather than
winning them:

```
              z3 -T:2          z3 -T:5
no patterns    48 unsat        50 unsat
patterns       41 unsat        41 unsat
               +5 / -12        +5 / -14
```

This does not argue against shipping them.  Higher-order logic is not
standardised in SMT-LIB 2.6 or 2.7 — `HO_ALL` and `(@ f x)` are cvc5
extensions, and 329 of 404 emitted scripts use `(@ …)` — so cvc5 is the only
solver that can read most of this output at all.  It does mean the honest claim
is "tuned for cvc5's quantifier instantiation", not "better everywhere".

The split worth documenting for users:

* **solver-independent** — one-point elimination, dead-declaration pruning,
  assertion dedup, helper sharing.  Smaller, logically equivalent formulas,
  committing to no instantiation policy.
* **cvc5-tuned** — instantiation patterns.

### Datatype axioms: cvc5 already has them

Each of these is `unsat` in cvc5 1.3.2 with no extra axioms and no flags, so
asserting them would add instantiation work for nothing:

| property | tested as |
|---|---|
| surjective pairing | `(not (= p (pair (fst p) (snd p))))` |
| pair injectivity | `(= (pair a b) (pair c d))`, `(not (= a c))` |
| Option surjectivity | `(not (= o none))`, `(not (= o (some (the o))))` |
| Option distinctness | `(= (some x) none)` |
| surjective pairing, function-typed field | `(Pair Int (-> Int Bool))` |
| congruence, function-typed field | `(Pair Int (-> (Pair Int Int) Bool))` |

### Higher-order components in datatypes: not a lever

Over the campaign's 800006 goal slots, cvc5 errors total **86** (0.01%):

```
46  Fatal failure within ... TypeEnumeratorInterface                 (beer)
19  Could not evaluate ((as pair (Pair (Pair (Pair (Pair Bool ...    (beer)
16  (error "std::bad_alloc")                                         (beer)
 5  (error "number of arguments does not match the constructor type")(beer)
```

The `Could not evaluate` class is real — cvc5 failing to build a model value
for a deeply nested `Pair` with a function-typed field — but 19 goals cannot
explain a 32-point gap, and a synthetic reproduction (a set of
`Pair Int ((Pair Int Int) -> Bool)` under a quantifier) is `unsat` under every
configuration. The last line is BEer emitting SMT that cvc5 rejects, on 5
goals: a bug report, not an optimisation.

### Relevance filtering would not buy much

Following symbol reachability from the goal keeps a median of 172 of 1110
assertions — but those 172 are the big ones, 74% of the assert bytes. A
relevance filter would cut assertion *count* by 85% and *bytes* by 26%, and it
can only lose proofs.

## The structural gap

ppTrans emits `(set-logic AUFNIRA)`: sets are an uninterpreted sort
(`declare-sort P 1`), membership is an uninterpreted predicate, and the theory
arrives as axioms carrying explicit `:pattern`s. Everything is first order and
E-matchable.

BEer emits `(set-logic HO_ALL)`: a set *is* its characteristic predicate as a
λ-term and `x ∈ S` *is* an application, so every membership beta-reduces to the
unfolded body of the set, and function-typed constants take part in
higher-order unification and extensionality reasoning. Median maximum
s-expression nesting depth over 20 common goals: **BEer 22, ppTrans 16; worst
case 205 against 36**.

The campaign's own cross-tabs put the loss exactly where the λ-encoding bites:

```
no relation type   both 81%   ppTrans-only  7%
relation type      both 14%   ppTrans-only 40%
order 1            both 38%   ppTrans-only 26%
order 3            both  4%   ppTrans-only 55%
order 4            both  4%   ppTrans-only 61%
```

Closing that is a change of encoding strategy, not a change of encoder detail.
The changes above move BEer from 42.4% to 48.7% of the sample at campaign
settings; ppTrans is at 71.3%.

## Caveats

- `Test/EncodingRegressions/run.sh` gives 5/8, unchanged by any of this. The three failures
  (`CartesianProduct`, `PowerSetMembership`, `LambdaAbstraction`, all
  `sat`-expected and answered `unknown`) reproduce on the baseline binary, so
  they predate this work.
- The 5000 ms losses are 12 of 168, 10 of them attributable to one-point
  elimination. Half are timeout-boundary noise — at 2000 ms only 6 goals are
  lost — but three `0009/00186` goals go from 366 ms to unknown, and stay
  unknown under `--enum-inst`. Reverting the pair rule textually on those files
  does not restore them, so it is the aggregate change of shape, not one rule.
  No cause isolated.
- Everything here is measured with cvc5 1.3.2 against a campaign run on 1.3.4.
