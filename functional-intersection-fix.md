# Preserve functional intersections

This plan concerns **intersection**: when both operands are represented by
option-valued functions, their intersection should keep that functional
representation. Union remains relational, because the union of two partial
functions need not be a partial function.

## Status

Implemented and validated on 22 July 2026. The implementation started from
branch `full-proof` at commit `24d9f01`; the original planning snapshot below
is retained as historical context. See `functional-intersection-proof.md` for
the proof architecture, obstacles, and complete validation record.

The repository snapshot inspected while writing the plan was:

- checkout: `/Users/vtrelat/Documents/BEer`;
- branch: `full-proof`;
- commit: `52cf279`;
- the worktree already contained unrelated tracked and untracked changes.

These facts were only a planning snapshot. The implementation session
rechecked the live state and preserved the pre-existing unrelated files.

## Intended result

Suppose two B relations have been encoded at compatible option-function types:

```text
S : rho  -> Option tau
T : rho' -> Option tau'
```

and one representation can be loosened to the other.  The encoder should:

1. choose the looser option-function type as it already does;
2. loosen only the tighter operand when the types differ;
3. compute the intersection as an option-valued function at the chosen type;
4. return that option-function type, rather than its characteristic-predicate
   graph type.

For equal types, the target SMT term is:

```text
lambda x : rho.
  ite (S x = T x) (S x) (none : Option tau)
```

For unequal types with a cast from the type of `S` to the type of `T`, let `S!`
be the existing loosened helper.  The target is:

```text
lambda x : rho'.
  ite (S! x = T x) (S! x) (none : Option tau')
```

The reverse cast direction is handled, as today, by swapping the operands.

The governing semantic identity is:

```text
H x = some y  <->  F x = some y and G x = some y,
```

where `H x := if F x = G x then F x else none`.  Equivalently,

```text
optionGraph H = optionGraph F intersection optionGraph G.
```

This is why intersection may preserve the functional representation.  The
corresponding statement is false for union when `F x` and `G x` are two
different `some` values.

## Scope and non-goals

The required scope is:

- make the equal option/option case of `castInter` return successfully;
- make that case return an option-valued function;
- change the heterogeneous `castInter.fun` case to return an option-valued
  function after loosening one operand;
- prove the operational, typing, freshness, declaration, denotational,
  representation-aware, and scoped contracts for both cases;
- carry the result through `encodeTerm_rep_spec.inter_case` and the top-level
  soundness build;
- add raw-encoder and end-to-end regressions.

The following are deliberately outside this task:

- preserving a functional representation for union, which is unsound in
  general;
- changing the mixed option-function/characteristic-predicate intersection:
  that result remains relational;
- changing the representation preorder, `castPath`, `SupportedSMT`, flag
  selection, or the source typing rules;
- replacing `loosenAux_prf` globally with `loosenAux_impl`;
- refactoring the legacy correctness stack merely to reduce its size;
- editing the thesis.

There is an adjacent, independent issue: an equal option/option union could be
made to succeed by graphifying both operands and returning a relational union.
Do not fold that change into this task unless it is requested explicitly; it
has a separate output policy and proof surface.

## Current behavior to reproduce before editing

Read the live definitions rather than relying on the line numbers from this
snapshot:

- `Encoder/Loosening/Loosening.lean`
  - `castInter` checks type equality before castability;
  - for equal types it accepts only `rho -> bool`;
  - equal `rho -> Option tau` operands therefore take the error branch;
  - `castInter.fun` is reached only through a non-equality cast path;
  - its current result is a predicate on pairs, not an option function;
  - its lambda binder must be checked carefully: the final implementation must
    remove this binder from the global type context with `eraseFromContext`.
- `Encoder/Loosening/Castable.lean`
  - structural reflexivity of `rho -> Option tau` is a `castPath.fun` whose
    codomain path contains `castPath.opt`; it is not an outer `castPath.refl`.
- `Encoder/Loosening/Rules.lean`
  - `loosenAux_prf` intentionally follows the proof-friendly structural path
    and may generate a helper even for structurally reflexive casts.

Before changing code, add or run a tiny executable check showing that, on the
live baseline,

```text
castInter (S, Int -> Option Bool) (T, Int -> Option Bool)
```

takes the equal-type branch.  Record its current result in the session notes.
After the encoder edit, turn the same check into a permanent success regression.

Do not use only a `Triple` theorem with an optional/error postcondition as
evidence that the new path works.  The implementation session must establish
an explicit reduction/evaluation lemma, or an executable test, showing that
the call returns the intended pair rather than throwing.

## Design decisions

### 1. Add a direct option-function branch

In `castInter`, extend the equal-type match with a case of the form:

```lean
| .fun rho (.option tau), _, rfl => ...
```

Construct the guarded option-valued lambda shown above and return
`.fun rho (.option tau)`.

Operational requirements:

- allocate one fresh lambda binder;
- call `eraseFromContext` on that binder before returning;
- emit no helper declaration and no helper specification;
- retain the normal fresh-name/`usedVars` effects of `freshVar`;
- type the `none` branch explicitly at `Option tau` if elaboration needs it.

Do not route equal option types through `loosenAux_prf`: the identity case needs
no semantic helper in the emitted script, and avoiding it keeps the generated
term and proof state simple.

### 2. Preserve the option result in `castInter.fun`

Keep the existing cast direction and helper construction:

```text
S --loosenAux_prf--> S! : rho' -> Option tau'
```

Keep the helper declaration and its specification.  Replace only the final
pair-predicate lambda by the guarded option lambda, return
`rho' -> Option tau'`, and erase its binder from the global type context.

The target codomain match must still reject impossible non-option codomains.
Do not weaken that invariant with a default value for an unrelated SMT type.

### 3. Preserve the existing dispatch policy

For `sigmaS != sigmaT`:

- if `sigmaS` casts to `sigmaT`, loosen `S` and return at `sigmaT`;
- otherwise, if `sigmaT` casts to `sigmaS`, use the existing swapped call;
- otherwise, keep the existing error.

For supported option-function representations, the successful output is thus
the looser of the two option-function types.  Its support witness should come
from the operand already represented at that type.

### 4. Do not change the graph cases

The following continue to return characteristic predicates:

- option-function intersected with a graph predicate;
- graph predicate intersected with an option-function;
- two characteristic predicates.

Although the intersection of a partial function with an arbitrary relation is
again functional, preserving a function in the mixed case requires a different
filtering construction and a larger dispatcher change.  Treat that as a
possible later optimization, not part of this proof.

## Proof architecture

The proof should be built bottom-up.  Do not start by patching the large
`encodeTerm_rep_spec.inter_case` proof.

### Phase 0 - Freeze the baseline

1. Read `AGENTS.md`, but treat any recorded frontier as historical.
2. Record:

   ```sh
   git branch --show-current
   git rev-parse HEAD
   git status --short
   git worktree list
   ```

3. Inventory existing `sorry`, `admit`, named `axiom`, and `#print axioms`
   output in the affected dependency cone.  The fix may add none.
4. Run the focused baseline builds and the existing functional-union
   regression:

   ```sh
   lake build SMT.Reasoning.Basic.EncodeTermRepresentedInter
   lake build SMT.Reasoning.Basic.EncodeTermRepresentedScopedInter
   lake build SMT.Reasoning.EncodeTermRepresented
   ./Test/representation_union.sh
   ```

5. Save the union script hash printed/checked by that regression.  It must not
   change during this task.

If the live code has moved past this plan, update the theorem/file map before
editing; do not mechanically apply stale line-level instructions.

### Phase 1 - Prove the pure option-intersection identity

First isolate the representation-independent mathematics.  Prefer one reusable
lemma near the existing option graph/collapse theory in
`SMT/Reasoning/Representation.lean`, or keep it private in
`EncodeTermRepresentedInter.lean` if it is not useful elsewhere.

For target types `rho` and `tau`, option-function denotations `F`, `G`, and the
denotation `H` of the guarded lambda, prove:

1. `H` belongs to `rho -> Option tau`;
2. for every `x` in `rho`, application of `H` is the intended `ite`;
3. for every `x` and `y`,

   ```text
   H x = some y <-> F x = some y and G x = some y;
   ```

4. `optionGraph rho tau H` is exactly the intersection of the two option
   graphs;
5. if `F` and `G` are supported representations of source relations `X` and
   `Y`, then `H` is a supported option-function representation of `X ∩ Y`.

Reuse, rather than recreate, the existing infrastructure:

- `optionGraph` and `graphCollapse`;
- `optionGraph_mem` and `optionGraph_fapply_eq_zftrue_iff`;
- `mem_predGraph_optionGraph_iff`;
- `predGraph_optionGraph_isPFunc`;
- `optionGraph_graphCollapse` and `graphCollapse_optionGraph`;
- `optionFunctionEquivFunctionalGraph`;
- `RDomCast.optionFunction_graph_retract`;
- `RDomCast.optionFunction_fapply_eq_some_iff`;
- `RDomCastSupported` support/admissibility lemmas.

Two acceptable proof shapes are:

- prove equality of option functions by extensionality and cases on `F x` and
  `G x`; or
- define the semantic result as the collapse of the intersection of the two
  graphs, prove the graph identity, and identify the lambda denotation with
  that collapse pointwise.

Prefer the shorter checked proof.  Do not introduce a new public abstraction
unless it materially shortens both the direct and heterogeneous encoder proofs.

**Gate A:** this phase is complete only when the graph identity and the
`RDomCastSupported` intersection theorem compile independently of the encoder.

### Phase 2 - Implement and prove the direct equal-type branch

Edit `Encoder/Loosening/Loosening.lean` as described above.

In `SMT/Reasoning/Basic/EncodeTermRepresentedInter.lean`, replace the current
option/option contract with a genuinely successful direct theorem.  Generalize
it over supported component representations if the live dispatcher exposes
them:

```text
SupportedSMT alpha rho
SupportedSMT beta  tau
S,T : rho -> Option tau
```

The theorem must establish all of the following for the returned lambda:

- exact result type `rho -> Option tau`;
- SMT typing;
- `usedVars` monotonicity;
- source type-context inclusion;
- keys covered by `usedVars`;
- removal of the lambda binder from the final type context;
- free-variable coverage and target-context respect under every compatible
  valuation;
- denotation under the current valuation;
- the alternative-valuation totality clause needed by the main induction;
- a supported `RDomCast` result for the source intersection.

Use the option-valued lambda proofs in
`SMT/Reasoning/Basic/EncodeTermRepresentedCollect.lean` as templates,
especially `represented_option_lambda_of_pointwise` and
`represented_collect_option_lambda`.  Reuse the guarded-option typing lemma in
`CollectCaseHelpers.lean` if its statement fits; otherwise prove a small local
typing lemma rather than importing the entire collect proof into a lower layer.

Add a small reduction lemma for the wrapper, analogous to the existing direct
predicate reductions, that rewrites the exact `castInter` call to the intended
`freshVar`/`eraseFromContext`/return program.  This prevents the representation
contract from concealing an error path.

**Gate B:** for two equal option-function types, both the executable regression
and the direct theorem must show successful return of an option-function term.

### Phase 3 - Implement and prove the heterogeneous `.fun` branch

Change `castInter.fun` only after Gate B is green.

Prove a focused theorem for the actual non-reflexive route:

```text
S : rho  -> Option tau
T : rho' -> Option tau'
c : (rho -> Option tau) ~> (rho' -> Option tau')
```

where `c` has the structural `.fun`/`.opt` shape selected by `castInterAux`.
The theorem should follow the real encoder program:

1. obtain `S!` and `S!_spec` from `loosenAux_prf`;
2. declare `S!` at the target option-function type;
3. add `S!_spec`;
4. allocate and erase the lambda binder;
5. return the guarded option intersection of `S!` and `T`.

Use `loosenAux_prf_spec_univ`, not a hand-written claim about the helper.  Its
universal adequacy clause is needed twice: once for the current valuation and
once for the alternative valuation in the induction postcondition.

The semantic proof should be factored as:

```text
S! represents the same source relation as S after the chosen cast
optionInter(S!, T) represents graph(S!) intersection graph(T)
therefore the returned option function represents F intersection G
```

Take the support witness for the result from the target-side option-function
representation.  Compose cast paths/retractions using the existing
`RDomCastSupported` lemmas; do not prove path coherence by unfolding all casts.

Add a reverse-direction wrapper theorem by swapping operands and then using
commutativity of set intersection, following the existing graph/chpred reverse
contracts.

The test for this phase must force a genuinely non-reflexive outer `.fun` path.
A suitable source type uses a nested relation as the domain or codomain, with
one nested representation option-valued and the other a characteristic
predicate.  Merely retesting two identical `Int -> Option Int` operands does
not exercise `castInter.fun`.

**Gate C:** the heterogeneous test must return the looser option-function type,
the helper specification must be present and well scoped, and the focused
representation theorem must compile.

### Phase 4 - Repair structural and freshness proofs

Update every proof that unfolds or case-splits on `castInter` or
`castInterAux`.  At the snapshot used for this plan, the main locations were:

- `SMT/Reasoning/Basic/EncodeTermStruct.lean`
  - `castInterAux_state`;
  - `castInterAux_decl`;
  - wrapper-level intersection state/declaration uses.
- `SMT/Reasoning/Basic/EncodeTermBvUsed.lean`
  - `castInter_bv`;
  - `castInterAux_decls_bv`;
  - `castInter_decls_bv`;
  - `castInter_bv_notMem`;
  - `castInterAux_decls_bv_notMem`;
  - `castInter_decls_bv_notMem`.

Check, rather than assume, the following deltas:

- direct option branch: no emitted declaration/specification, one fresh lambda
  name in `usedVars`, and no leaked binder in the final type context;
- heterogeneous branch: the existing loosened helper declaration and
  specification remain, while the returned lambda binder changes from a pair
  to the function domain and is erased from the final context;
- free and bound variables of the new `ite`, equality, applications, and
  explicit `none` are exactly those expected.

Compile each structural file before moving back to semantic proofs.

### Phase 5 - Complete the constructor-facing representation contract

In `SMT/Reasoning/Basic/EncodeTermRepresentedInter.lean`:

1. replace `castInter_option_rep_contract` with the successful direct contract;
2. add the heterogeneous option/option contract if it is not naturally
   subsumed by the direct theorem;
3. update `castInter_supported_rep_contract` so option/option cases select:
   - the direct functional theorem when target types are equal;
   - the forward functional `.fun` theorem when the left casts to the right;
   - the swapped functional theorem when the right casts to the left;
   - the existing incomparable/error theorem otherwise;
4. keep mixed graph/option and predicate cases unchanged;
5. check that the resulting `Nonempty (sigma ~> canonical)` witness is the
   option-function graph cast supplied by the chosen `SupportedSMT` witness;
6. update `encodeTerm_rep_spec.inter_case` only after the lower contract is
   complete.

The main constructor proof should continue to obtain the two encoded operands
from the maplet case, split their supported representations, invoke the
constructor-facing `castInter` contract, and compose the resulting valuation
extension.  It should not need a new source-language hypothesis: intersection
of two represented partial functions is automatically a partial function.

**Gate D:** `encodeTerm_rep_spec.inter_case` must prove a successful functional
result for the option/option branch under a concrete nonempty set of hypotheses;
an error-only proof is not acceptable.

### Phase 6 - Repair scoped generated-code correctness

Update `SMT/Reasoning/Basic/EncodeTermRepresentedScopedInter.lean`.

For the direct branch, prove that:

- the returned lambda is typed in the original declaration envelope;
- no helper declaration/specification is appended;
- its binder is local to the lambda and absent from the final global context;
- the generated chunk delta is exactly empty.

For the heterogeneous branch, prove that:

- the loosened helper declaration and specification form the exact generated
  chunk delta;
- the helper specification is typed and mentions only permitted variables;
- the returned option lambda is typed after that helper declaration;
- the lambda binder is not emitted as a declaration;
- the current and alternative valuation extensions satisfy the helper spec.

Update the option branch of the supported scoped dispatcher and the scoped
intersection constructor theorem.  Reuse its `result_comm`/swap machinery
rather than duplicating the reverse-direction semantics.

**Gate E:** the scoped intersection module and the aggregate represented
soundness theorem must compile, and the exact generated declaration sequence
must be covered by the theorem.

### Phase 7 - Check the canonical/legacy proof stack

Inspect `SMT/Reasoning/Basic/EncodeTermCorrectInter.lean` for proofs that unfold
the complete `castInter` definition:

- `castInter_denotation_aux`;
- `castInter_denotation_direct`;
- `castInter_spec`;
- `encodeTerm_spec.inter_case`;
- any local wrapper reduction or inversion lemma found by search.

Canonical set encodings use characteristic predicates, so the mathematical
content of these proofs should be unchanged.  Nevertheless, the new equality
match case can invalidate `simp`, `split`, and generated-case scripts.  Repair
them without duplicating the representation-aware option proof in the legacy
stack.

Then check the aggregate dispatchers:

- `SMT/Reasoning/EncodeTermRepresented.lean`;
- `SMT/Reasoning/EncodeTermCorrect.lean`;
- `Correctness.lean` and the proof-obligation-level modules reached from it.

### Phase 8 - Add regressions

Add a focused Lean executable, following `Test/UnionRepresentation.lean`, and a
shell driver following `Test/representation_union.sh`.  Suggested names are:

```text
Test/IntersectionRepresentation.lean
Test/representation_intersection.sh
```

The tests must cover:

1. **Raw direct shape**
   - equal `rho -> Option tau` inputs succeed;
   - result type is the same option-function type;
   - result is a lambda over `rho` whose body is the equality-guarded `ite`;
   - no graph predicate on `rho x tau` is returned.
2. **Pointwise semantics**
   - `some y`/`some y` keeps `some y`;
   - `some y`/`some z` with `y != z` gives `none`;
   - `some y`/`none`, `none`/`some y`, and `none`/`none` all give `none`;
   - graph membership agrees exactly with membership in both source graphs.
3. **Heterogeneous option representations**
   - the test forces `castInter.fun`, not the direct equality branch;
   - exactly the required loosened helper/specification is generated;
   - the result type is the looser option-function type.
4. **End-to-end B encoding**
   - construct a proof obligation in which two relation-valued variables are
     both represented as option functions and `f intersection g` occurs;
   - assert that both operands are actually selected for functional
     representation;
   - assert that the encoded intersection remains option-valued;
   - run the generated script through cvc5 with the repository flags
     `--incremental --mbqi` and expect the appropriate result.
5. **No union regression**
   - rerun `Test/representation_union.sh`;
   - require its current byte hash and `unsat` result to remain unchanged.

After the new script is reviewed, pin its generated bytes with a SHA-256 hash
in the regression driver, as the union regression already does.  Do not pin a
hash before checking that the script contains the intended option-valued
intersection and correctly scoped helpers.

## Validation sequence

Use file-level checks while developing, then the authoritative repository
build.  The minimum final sequence is:

```sh
lake build SMT.Reasoning.Basic.EncodeTermStruct
lake build SMT.Reasoning.Basic.EncodeTermBvUsed
lake build SMT.Reasoning.Basic.EncodeTermRepresentedInter
lake build SMT.Reasoning.Basic.EncodeTermRepresentedScopedInter
lake build SMT.Reasoning.EncodeTermRepresented
lake build SMT.Reasoning.EncodeTermCorrect
lake build
./Test/representation_intersection.sh
./Test/representation_union.sh
```

Also run `lake env lean` directly on each new or substantially edited proof
file during development so failures stay local.

For the new semantic lemma, the direct option contract,
`castInter_option_rep_contract`, `encodeTerm_rep_spec.inter_case`, and the
top-level represented theorem, inspect `#print axioms`.  Compare the result
with the recorded baseline.  The fix must introduce no new `sorryAx`, `admit`,
or named axiom.

If the repository has acquired additional maintained examples or CI checks by
the implementation date, run those too.

## Proof-risk order and stop conditions

Work in this order:

1. pure option graph identity;
2. direct encoder success and typing;
3. direct representation semantics;
4. heterogeneous helper adequacy and semantics;
5. structural/freshness proof repair;
6. scoped generated-code proof;
7. constructor and aggregate theorems;
8. end-to-end regression and full build.

Stop and report the precise obstruction instead of weakening a statement if:

- the proposed lambda does not denote graph intersection;
- supported option-function inputs do not provide enough admissibility to show
  the source relations are partial functions;
- `loosenAux_prf_spec_univ` cannot supply helper adequacy under the alternative
  valuation;
- the helper declaration/specification cannot be scoped without an additional
  source hypothesis;
- the only way to close a theorem is to leave the branch throwing;
- any new axiom, `sorry`, or `admit` appears necessary;
- preserving the union regression would require changing union semantics.

In such a case, keep the last green checkpoint and explain which invariant
failed, with the smallest counterexample or unprovable subgoal available.

## Commit discipline for the later session

Do not create commits in the manuscript session.  During implementation:

- use the user-selected branch after rechecking its live state;
- preserve `VTrelat <vincent.trelat@depinfonancy.net>` as sole author;
- add no co-author trailers;
- keep unrelated dirty files out of every commit;
- prefer small commits separating the encoder/semantic core, the proof
  cascade, and regressions;
- do not rewrite or force-push published history without explicit permission.

Possible concise commit subjects are:

```text
fix: preserve functional intersections
prove: verify functional intersections
test: cover functional intersections
```

## Completion criteria

The plan is complete only when all of the following are true:

- equal option-function intersections return successfully;
- the returned representation is option-valued;
- heterogeneous compatible option-function intersections return at the looser
  option-function type;
- the guarded option lambda has the proved pointwise and graph semantics;
- no lambda binder leaks into the global type context;
- helper declarations/specifications are exact and scoped;
- `castInter_supported_rep_contract`, the scoped contract, and
  `encodeTerm_rep_spec.inter_case` cover the successful branches;
- the legacy canonical theorem still builds;
- raw and end-to-end intersection regressions pass;
- the existing union regression is byte-identical and still `unsat`;
- the full `lake build` passes;
- no new axiom, `sorry`, or `admit` is introduced.

## Prompt for the later implementation session

Use this as the opening instruction when the work is triggered:

> Work only in `/Users/vtrelat/Documents/BEer`.  Read
> `functional-intersection-fix.md` completely, recheck the live branch/worktree and
> current definitions, then execute the plan through the full validation
> sequence.  Preserve unrelated changes, add no axioms or sorries, and do not
> edit the thesis.  Do not stop at a partial-correctness theorem: demonstrate
> that the equal option/option intersection branch really returns the intended
> option-valued lambda.
