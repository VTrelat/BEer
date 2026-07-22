# Functional intersection: implementation and proof report

## 1. Result

The refactor is complete. When two B relations are represented by compatible
SMT option-valued functions, their intersection is now represented by an
option-valued function as well.

For operands at the same representation,

```text
F, G : sigma -> Option tau
```

the encoder returns

```text
lambda x : sigma.
  if F x = G x then F x else (none : Option tau)
```

with result type

```text
sigma -> Option tau.
```

It no longer converts this case into the characteristic predicate of a graph.
The equal-type branch emits no helper declarations. If the option-function
types differ but one can be loosened to the other, the tighter operand is
first loosened by the existing helper/specification mechanism and the same
guarded lambda is constructed at the looser endpoint type. The reverse cast
direction is obtained by swapping the operands and using commutativity of
intersection.

Union was deliberately left unchanged. Two partial functions can disagree at
one input, in which case their union is not a partial function. Intersection
cannot introduce such a conflict and can therefore preserve the functional
representation.

This work targets the representation-aware theorem stack. The legacy
`encodeTerm_spec` intersection proof was not repaired, as requested. Its import
was removed from `SMT/Reasoning/Basic.lean`; that obsolete stack can be deleted
in a later cleanup.

## 2. The defect

`castInter` previously treated option-valued functions as graphs. Even when
both inputs had type

```text
sigma -> Option tau,
```

the output had type

```text
(sigma x tau) -> Bool
```

and tested that a candidate pair belonged to both input graphs. This was
extensionally a correct set intersection, but it violated the representation
policy used by the new soundness theorem: a relation known to be functional
should remain encoded as an actual option-valued SMT function whenever the
operation preserves functionality.

The mismatch had two costs. First, later operations lost the compact
functional representation. Second, the representation-aware contracts could
not state that successful option/function intersection returned the selected
option/function endpoint. Repairing only the theorem would therefore have
hidden an encoder defect; the operational encoder had to change first.

## 3. Mathematical core

Let

```text
F, G : A -> Option B
```

and define

```text
H(a) = if F(a) = G(a) then F(a) else none.
```

For every `a : A` and `b : B`,

```text
H(a) = some(b)
  <-> F(a) = some(b) and G(a) = some(b).
```

The forward direction follows because `H(a)` can be `some(b)` only through
the true branch. The guard then gives `F(a) = G(a)`, while the payload gives
`F(a) = some(b)`. Substitution gives the claim for `G`.

For the reverse direction, if both applications equal `some(b)`, the guard is
true and the payload is exactly `some(b)`.

Writing the graph of an option-valued function as

```text
optionGraph(F) = { a |-> b | F(a) = some(b) },
```

the pointwise equivalence gives

```text
optionGraph(H) = optionGraph(F) intersection optionGraph(G).
```

This identity is the semantic bridge between the new SMT lambda and B set
intersection. It also explains why the false case must use a *typed* `none`:
the SMT term has to determine `Option tau`, not merely an unconstrained option
constructor.

## 4. Encoder implementation

The operational change is in `Encoder/Loosening/Loosening.lean`.

### 4.1 Equal option-function types

The reflexive option/function branch now allocates one fresh local binder,
constructs the guarded lambda directly, erases the binder from the global type
context, and returns the original option/function type. No declaration or
specification is added.

The false branch uses `noneCast tau`. A bare `.none` was insufficient because
the term syntax carries an explicitly ascribed option type and several typing
and denotation simplifications depend on that annotation.

### 4.2 Heterogeneous compatible types

Suppose the selected cast direction is

```text
sigmaA -> Option tauA  <=  sigmaB -> Option tauB.
```

The existing `loosenAux_prf` machinery still creates one helper for the casted
left operand and one Boolean specification fixing its semantics. If that
helper is `F!`, the result is now

```text
lambda x : sigmaB.
  if F! x = G x then F! x else (none : Option tauB)
```

at type

```text
sigmaB -> Option tauB.
```

Thus the cast remains explicit and scoped, but the actual intersection no
longer becomes a graph predicate.

### 4.3 Other representation combinations

The characteristic-predicate, graph-cast, mixed-representation, incomparable,
and failure branches retain their previous behavior. In particular, this
change does not alter union encoding.

## 5. Proof reconstruction

The proof repair was carried out from the operational boundary upward. This
kept each failure attributable to one invariant instead of exposing the whole
recursive soundness theorem at once.

### 5.1 Operational shape and state

`SMT/Reasoning/Basic/EncodeTermStruct.lean` now proves both new shapes.

- `castInter_option_state` captures the direct equal-type lambda. It proves
  the returned term and type, unchanged declarations and used-variable state,
  the fresh counter update, and removal of the local binder from the type
  context.
- `castInterAux_state` covers the heterogeneous branch. It records the helper
  and its specification, then the guarded option lambda at the looser type.
- The declaration results were updated through `castInter_option_decl` and the
  corresponding auxiliary declaration theorem.

The important distinction is that the direct branch has no generated global
helper, whereas the heterogeneous branch has exactly the helper/specification
pair already needed by loosening.

### 5.2 Bound variables, used variables, and freshness

`SMT/Reasoning/Basic/EncodeTermBvUsed.lean` was repaired next.

- `castInter_bv` and `castInter_bv_notMem` account for the single lambda
  binder and show it cannot escape into the surrounding term obligations.
- `castInter_optionFun_decls_bv` and
  `castInter_optionFun_decls_bv_notMem` describe the direct option/function
  declaration behavior.
- `castInterAux_decls_bv` and the aggregate `castInter_decls_bv` family were
  updated for the helper plus guarded lambda.

Several early failures here came from simplifying the new `ite` as though it
were the old conjunction over a pair. Expanding the free- and bound-variable
equations for `eq`, `app`, `ite`, and the typed `none` exposed the exact
freshness obligations and made the binder-erasure invariant explicit.

### 5.3 Denotation of the guarded option term

`SMT/Reasoning/Basic/EncodeTermRepresentedInter.lean` contains the semantic
core.

- `denote_ite_option_none_eq_some_iff` proves that a guarded option payload is
  equal to `some w` exactly when the Boolean guard is true and the payload is
  `some w`.
- `denote_ite_option_none_some` packages total denotation, the result option
  type, and that exact `some` behavior.
- `castInter_option_denotation` applies those facts pointwise to the new
  lambda and proves that it represents the B intersection.

The low-level denotation proof splits on the semantic Boolean value of the
guard. In the false case, `none = some(w)` is discharged using disjointness of
the option constructors. In the true case, evaluation reduces to the payload.
This avoids assuming a classical equation about the source relations and
works directly with BEer's PHOAS denotation.

### 5.4 Rebuilding an option-function representation

The old proof ended with a Boolean graph predicate, so it could use the
existing set-predicate representation bridge. The new denotation is itself an
option-valued function. A local bridge,
`represented_optionFunction_of_pointwise`, was therefore added.

It starts from exact pointwise correspondence between `some` results and
source relation pairs. The forward half converts a target `some` result into a
source pair; the backward half turns each source pair into the matching target
application. Functionality follows from the target SMT function, while the
supported endpoint relations transport the domain and range elements. This
produces `RDomCastSupported` directly at

```text
sigma -> Option tau
```

without detouring through a characteristic predicate.

### 5.5 Direct representation contract

`castInter_option_direct_rep_spec` combines:

1. the exact direct operational result;
2. typing of the guarded lambda;
3. binder freshness and context erasure;
4. total denotation of the lambda; and
5. `castInter_option_denotation`.

`castInter_direct_rep_contract` exposes this result to the constructor-facing
contract. Its postcondition states that the encoder succeeds, produces the
option/function endpoint, emits no helper declarations, and represents the B
intersection.

### 5.6 Heterogeneous representation contract

`castInter_fun_rep_spec` and `castInter_fun_rep_contract` handle the forward
cast direction.

The key proof step is not merely that a helper exists. The helper's generated
specification must force it to denote the cast of the original operand under
every satisfying valuation. The proof therefore:

1. invokes the exact loosening contract;
2. extends the renaming context with the helper denotation;
3. proves that the helper specification is true in that extension;
4. re-establishes type-context respect and free-variable coverage for the
   helper and untouched operand;
5. derives the helper's supported option/function representation at the looser
   endpoint; and
6. applies `castInter_option_denotation` to the helper and the other operand.

The generated chunk is proved to contain exactly one helper declaration and
its specification before the final lambda. The reverse theorem
`castInter_fun_rev_rep_contract` reuses the forward theorem after swapping the
operands and then transports the semantic result through commutativity of B
intersection.

### 5.7 Supported dispatch

`castInter_option_rep_contract` covers the equal option/function case, and
`castInter_supported_rep_contract` dispatches across all supported
representation combinations:

- equal option/function types use the direct functional contract;
- forward-compatible option/function types use the heterogeneous helper
  contract;
- reverse-compatible types use its swapped version;
- graph and characteristic-predicate combinations retain their established
  contracts; and
- incomparable types retain the established failure contract.

This is the operational-to-semantic boundary consumed by the recursive term
proof.

### 5.8 Scoped generated declarations

`SMT/Reasoning/Basic/EncodeTermRepresentedScopedInter.lean` establishes the
stronger generated-code contract required by the new main theorem.

The direct option branch proves an empty declaration delta and a lambda that
is typable from the input context alone. The heterogeneous branch proves a
declaration-context trace containing exactly the helper and its specification.
Its guarded semantic theorem is quantified over any super-context and any
renaming that satisfies those generated specifications. Consequently, the
proof does not rely only on the witness valuation used to show satisfiability;
it establishes soundness for every model of the emitted SMT declarations.

The main cases are assembled by `option_scoped_contract` and
`supported_scoped_contract`. The constructor theorem
`EncodeTermRepresentedScopedInter.encodeTerm_rep_scoped.inter_case_from`
combines the two recursive hypotheses, the maplet encoding used internally by
`encodeTerm`, the cast contract, declaration envelopes, free-variable bounds,
and specification typing.

### 5.9 Recursive and aggregate soundness

`encodeTerm_rep_spec.inter_case` plugs the repaired cast contract into the
ordinary representation-aware induction. The recursive dispatcher in
`SMT/Reasoning/EncodeTermRepresented.lean` selects the repaired ordinary and
scoped intersection cases. Both exported theorems build:

```text
encodeTerm_rep_spec
encodeTerm_rep_scoped_spec
```

This is the new main theorem stack requested for the refactor.

## 6. Why the proof was non-local

The encoder edit itself is small, but its return type and syntax are observed
by several independent proof layers. Changing a graph predicate over pairs to
an option-valued lambda changes all of the following at once:

- the returned SMT type;
- the lambda binder type;
- the body syntax (`and` of graph-membership tests versus `ite` over function
  equality);
- free- and bound-variable calculations;
- generated declaration shape;
- the denotation target;
- the representation bridge used at the end of the semantic proof; and
- the scoped model argument for generated helpers.

This is why the proof cascade was much larger than the encoder diff. No theorem
was weakened to accommodate the change: each layer was updated to describe the
new operational result exactly.

## 7. Legacy theorem boundary

The old `EncodeTermCorrectInter` module proves the canonical
`encodeTerm_spec` theorem against the former representation discipline. It was
intentionally not migrated. `SMT/Reasoning/Basic.lean` no longer imports that
module, silencing the obsolete proof path while the representation-aware stack
remains fully checked.

No `sorry`, `admit`, or axiom was added. Repository-wide source counts remained
at the pre-refactor baseline:

```text
sorry lines: 22
admit lines: 33
axiom lines: 32
```

The new semantic and cast contracts report only Lean's standard logical
dependencies:

```text
propext, Classical.choice, Quot.sound
```

The recursive constructor and aggregate theorems still report the repository's
pre-existing `sorryAx` dependencies from other imported proof modules; this
refactor introduces none of them.

## 8. Regression tests

Three new test artifacts exercise the fix.

### 8.1 Raw encoder regression

`Test/IntersectionRepresentation.lean` checks the encoder value directly.

The equal case asserts:

- the result type remains `fun int (option bool)`;
- the exact result is the guarded option lambda;
- no declarations are emitted; and
- the local binder does not remain in the global type context.

The heterogeneous case uses a genuinely non-reflexive outer function cast. Its
domain is itself represented once as an option-valued function and once as a
graph predicate. The test asserts:

- the result uses the looser option/function type;
- exactly one helper declaration and one matching helper specification are
  emitted;
- the helper is retained at the correct type; and
- the result is the guarded option lambda using that helper.

### 8.2 Real Atelier-B POG

`Test/Intersection.pog` declares sets `X` and `Y`, total functions

```text
f, g : X --> Y,
```

and asks BEer to prove

```text
(f intersection g) <: X * Y.
```

The Lean regression confirms that the POG reader marks both operands as
functions and that the decoded goal and hypotheses have the intended shape.
The executable then translates the actual POG. The generated SMT contains the
expected guarded option expression, including an explicitly typed
`(as none (Option Int))`, and cvc5 returns `unsat`.

### 8.3 Executable regression script

`Test/representation_intersection.sh` builds the executable and represented
theorem, runs the raw Lean assertions, translates the real POG, checks the
functional SMT shape, and runs cvc5.

The existing tests were also retained:

- `Test/representation_union.sh` confirms the union SMT output remains exactly
  byte-identical to SHA-256
  `e93a29578ca1ee3d3fb2a175dbf6b3cef135a435855a05bf397c38f75b916a50`
  and remains `unsat`;
- `Test/representation_lambda.sh` confirms the earlier function-as-function
  lambda encoding remains byte-stable and `unsat`.

## 9. Validation record

The following focused proof gates passed:

```text
lake build SMT.Reasoning.Basic.EncodeTermStruct
lake build SMT.Reasoning.Basic.EncodeTermBvUsed
lake build SMT.Reasoning.Basic.EncodeTermRepresentedInter
lake build SMT.Reasoning.Basic.EncodeTermRepresentedScopedInter
lake build SMT.Reasoning.EncodeTermRepresented
```

The executable and aggregate theorem build passed:

```text
lake build BEer SMT.Reasoning.EncodeTermRepresented
```

The executable regressions passed:

```text
./Test/representation_intersection.sh
# Intersection represented script: guarded option-valued function and unsat

./Test/representation_union.sh
# Union represented script: byte-identical and unsat

./Test/representation_lambda.sh
# Lambda represented script: option-valued, byte-stable, and unsat
```

Finally, the authoritative repository-wide validator passed:

```text
lake build
# Build completed successfully (1085 jobs).
```

`git diff --check` also passed. No stale Lean process remained after the build.

## 10. Files changed

- `Encoder/Loosening/Loosening.lean`: functional equal and heterogeneous
  intersection encodings.
- `SMT/Reasoning/Basic/EncodeTermStruct.lean`: exact output, state, context,
  and declaration invariants.
- `SMT/Reasoning/Basic/EncodeTermBvUsed.lean`: bound-variable, used-variable,
  and freshness invariants.
- `SMT/Reasoning/Basic/EncodeTermRepresentedInter.lean`: guarded-option
  denotation, option representation bridge, direct and heterogeneous semantic
  contracts, and recursive intersection case.
- `SMT/Reasoning/Basic/EncodeTermRepresentedScopedInter.lean`: generated-helper
  model semantics, declaration scoping, and scoped recursive intersection
  case.
- `SMT/Reasoning/Basic.lean`: removal of the obsolete
  `EncodeTermCorrectInter` import.
- `Test/IntersectionRepresentation.lean`: raw structural and POG assertions.
- `Test/Intersection.pog`: real functional-intersection proof obligation.
- `Test/representation_intersection.sh`: end-to-end regression.
- `functional-intersection-fix.md`: renamed implementation plan.
- `functional-intersection-proof.md`: this report.

## 11. Final contract

The repaired behavior can be summarized as follows:

```text
If F and G are supported representations of B relations at compatible
option-function types, castInter succeeds at the selected looser
option-function type. Its result denotes exactly the source intersection.
The direct case emits no declarations; a heterogeneous case emits exactly the
cast helper/specification required by loosening, and the result is sound under
every satisfying interpretation of that generated specification.
```

This matches the function-as-function representation principle while keeping
union relational where mathematics requires it.
