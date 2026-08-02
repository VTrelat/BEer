# Representation-aware soundness refactor: proof account

## Status and scope

This document records two connected phases on branch `full-proof`:

1. the original representation-aware soundness proof, built from base commit
   `4f05b509f904c6cd8c5448abd91167de758a90db` through implementation checkpoint
   `52cf279`; and
2. the follow-up redesign that changes source B lambdas from an emitted
   Boolean graph predicate to an emitted option-valued SMT function, while
   retaining the representation-aware theorem as the active soundness API.

The first phase comprised 185 atomic commits and changed 62 files.  Its final
repository-wide validation was run on 2026-07-20.  The lambda follow-up was
implemented in code checkpoint `282a7c2`, with the real-MWE regression added
at `913eac0`, and validated on 2026-07-22.  Its complete proof account is in
Section 16.

The combined result is a representation-indexed soundness theorem for every
successful branch of `encodeTerm`, a Boolean/canonical corollary,
source-to-target and target-to-source valuation constructions for proof
obligations, a concrete regression for the mixed functional/relational union
example, and a direct option-function representation for B lambdas.

The key example is:

```text
f : X --> Y
g : X <-> Y
f ∪ g ⊆ X × Y
```

The source value of `f` is a B relation, but the generated SMT declaration is:

```smt
(declare-const f (-> Int (Option Int)))
```

The source value of `g` remains represented as a characteristic predicate on
pairs.  The proof now permits these two representations to coexist in the
same union without replacing `f` by a canonical relation declaration.

## 1. The original obstruction

The legacy theorem `encodeTerm_spec` starts with the canonical target
valuation `B.RenamingContext.toSMT Δ`.  A B value of type
`set (prod α β)` is canonically tagged as an SMT characteristic predicate:

```text
(α × β) -> Bool
```

The top-level encoder deliberately selects a different type for a relation
known to be functional:

```text
α -> Option β
```

Consequently, the legacy compatibility premise
`RespectsTypeContextOnFV (B.RenamingContext.toSMT Δ) Λ t` cannot be inhabited
when a free variable used by `t` is declared at the option-function type in
`Λ`.  This was not a missing rewrite or a difficult unification problem.  The
theorem's valuation model identified representation with equality of type
tags, while the encoder used two extensionally equivalent representations.

The important decision was therefore to leave the public statement of
`encodeTerm_spec` intact and add a second theorem family.  The new family
relates source and target values through an explicit cast and retraction,
rather than requiring their representations to be definitionally equal.

## 2. The semantic relation that removed the obstruction

### 2.1 Domain agreement through an explicit cast path

`SMT/Reasoning/Representation.lean` introduces the core relation:

```lean
def RDomCast : B.Dom -> SMT.Dom -> Prop
  | ⟨X, alpha, _⟩, ⟨Y, sigma, _⟩ =>
      ∃ c : sigma ~> alpha.toSMTType,
        retract alpha (castZF_apply c Y) = X
```

The path `c` is data.  It records the actual representation transition used
by the semantic proof.  Keeping it explicit was necessary in pair, set,
application, and binder proofs; replacing it with the proposition `σ ⊑ τ`
would repeatedly lose the path required by `castZF_apply`.

Three layers are used:

- `RDomCast` stores the cast/retraction equation.
- `RDomCastAdmissible` also records that values in quantified domains have
  preimages at the selected binder representation.
- `RDomCastSupported` additionally restricts the source/target type pair to
  the representation grammar described by `BType.SupportedSMT`.

`BType.SupportedSMT` contains the canonical cases and the genuinely
heterogeneous option-function case.  This prevents an arbitrary castable SMT
type from entering the induction theorem merely because a low-level cast path
can be constructed.

The file proves the basic laws immediately:

- canonical source values have a canonical supported representative;
- reflexive agreement recovers the old `RDom` relation;
- agreement is stable under equality on either side;
- `int` and `bool` force reflexive target representations;
- products compose component relations;
- supported set predicates expose membership equivalences;
- values can be projected from represented tuples;
- structural cast paths with the same endpoints are equal.

Path uniqueness, proved as `castPath.eq_of_endpoints`, was especially useful.
It allowed a stored admissibility witness to be transported to the exact path
selected later by the encoder without appealing informally to proof
irrelevance.

### 2.2 Valuation agreement only where the term needs it

The pointwise relations are lifted to valuations as:

```text
RValuationCast
RValuationCastAdmissible
RValuationCastSupported
```

and then restricted to source free variables by the corresponding `OnFV`
forms.  This restriction is essential.  Generated helper names and bound
variables must be assigned during recursive proofs, but unrelated source
names must not become accidental theorem premises.

`ExtendsOnSourceFVCast` is the representation-aware replacement for the old
equality-based extension predicate.  Update and extension lemmas show that a
binder assignment can be added while preserving the relation on the original
free-variable scope.

## 3. The function/graph bridge

The option representation is justified semantically, not by the presence of
a name in `B.Env.flags`.

The bridge uses two operations already suggested by the existing cast
machinery:

```text
optionGraph    : (α -> Option β) -> ((α × β) -> Bool)
graphCollapse  : functional ((α × β) -> Bool) -> (α -> Option β)
```

The main equations are proved in `Representation.lean`:

```text
optionGraph (graphCollapse R) = R       when R is functional
graphCollapse (optionGraph F) = F
```

The implementation reuses the repository's set-theoretic function and graph
machinery.  It proves typing of `optionGraph` and `graphCollapse`, proves that
the graph of every option-valued function is a partial function, and proves
the retraction equation needed by `RDomCastSupported`.

This bridge supports both directions required later:

1. A functional source relation can be collapsed to an option-valued target
   function.
2. Any option-valued target function can be graphed to reconstruct the source
   relation.

The first direction requires actual source functionhood.  The second obtains
functionhood from the target type itself.  At no point does a bare flag prove
that an arbitrary relation is functional.

## 4. The representation-aware encoder contract

`SMT/Reasoning/EncodeTermRepresentedDefs.lean` defines the induction contract
used by every constructor proof.

### 4.1 Ordinary postcondition

`EncodeTermRepPost` preserves all operational facts required by the legacy
proof while replacing equality of denotations by supported representation
agreement.  Its successful branch records:

- monotonicity of used names;
- extension of the SMT type context;
- coverage of source variables;
- a cast path from the emitted type to the canonical source type;
- typing of the emitted SMT term;
- constructor-specific output shape where composition needs it;
- freshness/noninterference of unrelated used names;
- an extended target valuation;
- source and target type-context compatibility;
- a target denotation at the emitted type;
- `RDomCastSupported` between the source and target denotations;
- totality under every alternative related source/target valuation.

The alternative-valuation clause is `EncodeTermRepTotal`.  It explicitly
requires the initial target valuation's domain to lie in the input type
context.  This replaced an unsound legacy attempt to infer domain containment
from a one-sided extension relation.

The operational and semantic parts were separated into
`EncodeTermRepSemanticPost` and the existing structural state theorem.  This
kept repetitive state bookkeeping out of the semantic constructor proofs.

### 4.2 Declaration-aware scoped postcondition

Quantifiers, collections, Lambda terms, equality, membership, union,
intersection, and application can generate helper declarations and
specification bodies.  Some helpers are moved beneath binders by the encoder.
An ordinary existential totality statement is too weak at that boundary: it
only shows that one convenient assignment exists, whereas the quantified body
must be sound for every typed assignment satisfying the generated helper
specifications.

The proof therefore introduced a declaration-aware layer:

- `DeclarationContextTrace` relates emitted declarations to context entries.
- `DeclarationContextEnvelope` permits irrelevant operational residue while
  retaining a clean semantic base.
- `ScopedContextExtends` describes the context visible under moved helpers.
- `ScopedSpecsTyping` proves generated specification bodies are Boolean.
- `SpecBodiesTrue` records satisfaction of those bodies by a valuation.
- `EncodeTermRepScopedTotal` strengthens alternative totality with a
  satisfying helper assignment.
- `EncodeTermRepGuardedSound` proves soundness for every typed assignment that
  satisfies the helper guards.
- `EncodeTermRepScopedPostFrom` allows a proof to be replayed below an already
  generated clean declaration prefix.

This layer was the main architectural cost of the refactor.  The difficult
part was not merely proving that a graph and option function denote the same
relation.  It was retaining that fact after helper declarations were created,
reordered, scoped under binders, and replayed under alternative valuations.

## 5. The three proof gates

### 5.1 Gate A: represented variables

The variable case established that the new valuation relation solves the
original problem directly.

For a canonical variable, the proof uses the canonical supported
representative.  For a source relation represented as
`α -> Option β`, the target valuation already contains a related target value.
The variable encoder returns that target variable and type; the
`RValuationCastSupportedOnFV` premise supplies exactly the cast/retraction
equation needed by the postcondition.

No impossible canonical `RespectsTypeContextOnFV` premise is reintroduced.
This gate is represented by the early checkpoints `30b7f74` and `117df08`.

### 5.2 Gate B: heterogeneous union

The union proof had to combine operands whose target representations differ:

- `f` is an option-valued function;
- `g` is a characteristic predicate on pairs.

The encoder exposes the option function as a graph predicate, then applies the
ordinary predicate union.  The proof follows the actual `castUnion` and
`loosenAux` execution path.  It proves:

- totality of the direct predicate union;
- totality of the generated graph form;
- typing and truth of graph helper specifications;
- equality of membership after casting both operands to the selected common
  predicate representation;
- retraction of the result to the source B union;
- the corresponding property for every alternative related valuation.

This gate closed at `85fddcd`, then received the declaration-aware scoped
companions needed by quantified clients.  Later composition checkpoints
separated raw union semantics from helper tracing so the proof could be reused
for intersection and membership.

### 5.3 Gate C: universal quantification

The `all` case exposed the deepest invariant.  The domain is encoded first,
its element representation is decomposed into binder components, flags may
select option-valued function components, body-generated declarations are
moved under the quantifier, and falsity must be transported in both directions
under arbitrary alternative valuations.

The raw theorem retains the explicit semantic contract
`EncodeTermAllBinderAdmissible`.  For every successful binder-type selection,
the contract says:

1. each selected component belongs to `BType.SupportedSMT`; and
2. every value in the source quantified domain has a preimage at the selected
   tuple representation.

This is a real condition.  Membership in a set of relations does not imply
that every relation in the set is functional, so an option-function binder
cannot be justified by a flag alone.

The final hard theorem is
`encodeTerm_rep_spec.all_case_and_scoped_of_oracle_or_unflagged`.  It accepts
one of two honest witnesses:

```text
EncodeTermAllBinderAdmissible
or
every bound name is absent from E.flags
```

In the unflagged branch, `SMTFlagTypeRel.list_eq_of_not_mem` proves that the
encoder-selected component list is exactly the decomposition of the encoded
domain's element representation.  Supported component types follow from the
domain relation.  For alternative valuations, the theorem now carries the
actual encoded domain denotation and its `RDomCastSupported` witness;
`RDomCastSupported.setPred_binder_admissible_of_type_eq` then supplies binder
preimages at the exact selected tuple path.

The body proof uses the scoped helper contracts described above.  It handles
empty and nonempty domains, constructs and updates source/target binder
valuations, transports counterexamples through cast and retraction, and
retains helper specification truth under the quantifier.

The first vertical gate was established at `b58b917`; the full scoped and
compositional version closed through `ea43e79`, `587135b`, and `e76933d`.

## 6. Completing every encoder branch

After the three gates, the theorem family was completed constructor by
constructor.

### 6.1 Homomorphic and base cases

Integers, Booleans, arithmetic, comparisons, maplets, logical connectives,
base sets, and straightforward set formers mostly reuse canonical cast laws.
The proofs still retain the generalized postcondition and alternative
valuation clause so they compose with heterogeneous parents.

### 6.2 Membership, equality, and application

These cases are representation-sensitive because an operand may be a set
predicate, option-valued function, pair, or generated helper.  The proof added
exact membership-cast lemmas and pointwise application equivalences, then
proved declaration-aware companions for helper-producing branches.

Application required a direct bridge between option-function application and
membership in its graph.  Equality required both operands to be loosened to a
common supported representation before target equality could be reflected
back to source equality.

### 6.3 Powerset, Cartesian product, and partial-function spaces

Powersets and Cartesian products required representation decomposition and
tuple projection lemmas.  The partial-function-space case proves that the
target predicate characterizes source relations with the expected domain,
range, and functionality properties under supported casts.

### 6.4 Collection and Lambda

Collection was the largest proof after `all`.  It combines:

- a represented domain;
- a tuple of fresh binders;
- substitution into the predicate;
- option payload extraction for function-valued components;
- guarded helper Lambda terms;
- source membership reconstruction;
- context and declaration re-scoping;
- alternative-valuation totality.

The proof was deliberately split into semantic, operational, tuple, payload,
and context lemmas.  The shared tuple-binder bridge was then reused by Lambda
and universal quantification.  The final collect proof closed at `77c6b48`.

In the first phase, Lambda reused the same domain and binder machinery but
preserved a functional graph predicate as the result.  Its last blockers were
operational helper scope, body totality under substitution, and retention of
generated declarations.  Those were isolated in the sequence ending at
`375078c`.  The 2026-07-22 follow-up changed this result representation to an
option-valued function; Section 16 explains the replacement proof and the
consumer cascade.

### 6.5 Public recursion and corollaries

`SMT/Reasoning/EncodeTermRepresented.lean` simultaneously assembles:

```text
EncodeTermRepIH t
EncodeTermRepScopedFromIH t
```

by structural recursion.  Pairing the ordinary and scoped induction avoids a
global circular hypothesis: each constructor receives both contracts only for
its strict subterms.

The public theorem is:

```lean
theorem encodeTerm_rep_spec
    (binder_admissible : EncodeTermAllBinderAdmissible)
    (wd_t : B.Term.WellDefined t) :
    EncodeTermRepIH t
```

`EncodeTermRepPost.rdom_of_result_type_eq` recovers the legacy `RDom`
conclusion whenever the emitted result type is canonical.  For predicates,
cast-path inversion forces the emitted type to `SMTType.bool`, yielding
`EncodeTermRepPost.bool_canonical` and the public
`encodeTerm_rep_bool_spec` corollary.

The existing public statement of `encodeTerm_spec` was not weakened or
rewritten.  In the follow-up, it was removed from the active `Correctness.lean`
import closure rather than repaired for the new Lambda output.  The
representation-aware theorem is now the active endpoint; legacy proof removal
is intentionally deferred to a separate cleanup.

## 7. Proof-obligation closure

`SMT/Reasoning/ProofObligationRepresented.lean` connects the raw term theorem
to contexts and assumptions produced by the decoder and top-level encoder.

### 7.1 Representation context selected by `encodeTypeContext`

`BType.selectedSMTType?` mirrors the encoder's branch exactly:

- unflagged bindings use `tau.toSMTType`;
- flagged binary relations use
  `fun alpha.toSMTType (option beta.toSMTType)`;
- a flag on any other source type is rejected.

`B.Env.RepresentationContext E Gamma` relates every source binding to the
selected target binding.  The Hoare theorem
`encode_type_context_representation_context` proves that a successful
`encodeTypeContext E` constructs such a context.

### 7.2 Source valuation to selected target valuation

`B.Dom.exists_selectedSMT_supported` chooses a target representative:

- canonical values use `d.canonicalSMT`;
- a genuinely functional flagged relation uses `graphCollapse`.

`B.Env.exists_selectedValuationOn` applies this pointwise on a finite scope.
`exists_selectedValuation_for_term` specializes it to the free variables of a
term and returns all premises consumed by `encodeTerm_rep_spec`:

- supported valuation agreement;
- source and target context compatibility;
- no assignments outside the term scope;
- target valuation domain containment.

### 7.3 Selected target valuation back to a source valuation

`B.Env.exists_sourceValuationOn` uses
`supported_target_preimage` to reconstruct a source value for every selected
target value.  In the option-function branch, the reconstructed source value
is the graph of the target function.

`exists_sourceValuation_for_term` also proves source well-formedness,
free-variable coverage, and semantic functionhood for every assigned flagged
value.  This gives the converse valuation direction needed to transport a
target countermodel back to the B semantics.

### 7.4 Functionhood comes from asserted hypotheses

The decoder's total-function hypothesis is not necessarily the direct term:

```text
f ∈ X ⇸ Y
```

For `Test/Union.pog` it is a collection over a partial-function domain:

```text
f ∈ { h ∈ X ⇸ Y | totality predicate }
```

The proof therefore covers both forms.

`B.Dom.isFunctional_of_true_pfun_membership` inverts a true direct membership
predicate and extracts membership in the denoted partial-function space.

`B.Dom.isFunctional_of_true_collect_pfun_membership` first descends from true
collection membership to membership in the collection domain, then applies
the same partial-function argument.  The proof uses the collection denotation
inversion lemmas and weakens the concrete domain/range sets to their ambient B
types.

The final assumption predicate is deliberately named
`AssignedFlagsHaveFunctionHypotheses`.  It quantifies only over names actually
assigned by the source valuation.  Together with typed and true assumptions,
`flaggedValuesFunctional_of_function_hypotheses` derives the semantic
`FlaggedValuesFunctional` premise required by target valuation construction.

## 8. The false global flag invariant and its repair

An initially plausible invariant was:

```text
every name in E.flags is present in E.context
```

This is false for decoded proof obligations.

Inspection of `Test/Union.pog` produced global flags such as internal
`x37`, `x28`, `x11`, and `x2` that are bound helpers created while decoding
builtins.  They are intentionally not global source variables and therefore
have no global context entry.  Requiring every global flag to be typed would
reject a valid decoder state and would hide the actual representation
boundary.

The repair has three parts:

1. Binder admissibility for the concrete universal term is term-local:
   its bound variable must not occur in `E.flags`.
2. Function hypotheses are required only for flagged values assigned by the
   source valuation.
3. PO-local flags are checked separately against `po.localContext`.

`B.ProofObligation.extendEnv` is the shared constructor for combining PO-local
bindings and flags with the global environment.  The encoder now calls this
definition instead of duplicating its body.  A direct comparison between the
old inline construction and the shared definition produced byte-identical
Union SMT output.

`FlagsInContext` and `extendEnv_flagsInContext` remain useful sufficient
lemmas for environments that really satisfy the stronger invariant, but the
concrete Union closure does not falsely claim that all decoder helper flags do.

This correction was decisive: it replaced a convenient but false global
statement with the exact local facts used by the proof.

## 9. Concrete functional-union closure

`SMT/Reasoning/ProofObligationUnion.lean` defines the exact source term:

```lean
B.Term.functionalUnionSubset z f g X Y
```

which expands to:

```text
forall z in f ∪ g, z in X × Y
```

The file builds ordinary and scoped represented induction hypotheses for:

- the heterogeneous union `f ∪ g`; and
- membership of `z` in `X × Y`.

`encodeTerm_rep_spec.functionalUnionSubset_case` then instantiates the honest
unflagged-binder branch of the generalized universal theorem.

`B.ProofObligation.exists_selectedValuation_for_functionalUnionSubset`
composes typed, true PO assumptions with the source-to-target valuation
construction.  It is the explicit connection from the function hypothesis on
`f` to the represented valuation consumed by the concrete term theorem.

## 10. Proof-discovered encoder defects

The initial plan asked for unchanged encoder output.  During the proof, several
existing encoder behaviors were found to violate the operational or scoping
invariants needed for soundness.  They were reported and repaired in separate
atomic commits.  Examples include:

- constraining generated membership helpers;
- scoping intersection and equality helpers correctly;
- scoping relation application helpers;
- canonicalizing powerset relations;
- rejecting unscoped binder helpers;
- aligning function-valued collection binders;
- declaring tuple-helper universes;
- composing scoped membership envelopes.

These are real encoder fixes, so byte-for-byte equality with the original base
commit is not a truthful completion claim.  The preserved property is the
intended representation boundary: `f` remains an option-valued function, `g`
remains a relation predicate, and the canonical public theorem was not changed
to force a different script.

For the final PO-environment refactor itself, the old inline environment
construction and the new shared `extendEnv` construction were run on the same
decoded Union input and compared byte for byte; they were identical.

The committed regression pins the resulting full script by SHA-256:

```text
e93a29578ca1ee3d3fb2a175dbf6b3cef135a435855a05bf397c38f75b916a50
```

A local ignored file named `Test/Union_ho.smt` was found to contain an older,
duplicated encoding with different fresh names and assertions.  It was not
treated as an authoritative baseline and was not modified.

## 11. Regression test

The regression consists of:

- `Test/Union.mch`;
- `Test/Union.pog`;
- `Test/UnionRepresentation.lean`;
- `Test/representation_union.sh`.

The Lean structural test checks that:

- `f` is selected for function representation;
- `g` is not selected for function representation;
- both still have source relation type `set (prod int int)`;
- every PO-local flag has a PO-local context binding;
- decoder-bound helper flags outside the global context are present, guarding
  against reintroducing the false global invariant;
- the expected functional-union quantified goal is decoded;
- the assumptions contain either a direct or collection-over-`pfun`
  function hypothesis for `f`;
- the quantified Union binder is unflagged.

The shell regression then:

1. builds `BEer` and `SMT.Reasoning.ProofObligationUnion`;
2. runs the structural Lean test;
3. generates the full Union SMT script;
4. checks the exact SHA-256 of the generated bytes;
5. runs cvc5 with `--incremental --mbqi --tlimit-per=3000`;
6. requires the exact solver result `unsat`.

The final output is:

```text
Union representation structure: ok
Union represented script: byte-identical and unsat
```

## 12. Validation evidence

### 12.1 Builds

The following checks succeeded during the final tranche:

```text
lake env lean B/Environment.lean
lake env lean Encoder/Encoder.lean
lake env lean SMT/Reasoning/ProofObligationRepresented.lean
lake env lean SMT/Reasoning/ProofObligationUnion.lean
lake env lean --run Test/UnionRepresentation.lean
lake build Correctness
lake build
```

The cold integrated rebuild compiled the complete reasoning dependency graph,
including the expensive represented universal module, and completed all 1093
jobs successfully.  The final repository-wide build completed all 1096 jobs
successfully after the regression files were tracked.

### 12.2 Placeholder and named-axiom inventory

The exact token-bearing line inventory was compared between base
`4f05b50` and implementation head `52cf279`:

```text
sorry lines: base=22 head=22
admit lines: base=33 head=33
axiom lines: base=32 head=32
added placeholder/axiom lines: none
```

At that checkpoint the project had seven named axiom declarations. The
now-orphaned variable-scoping axiom module has since been retired; the
remaining declarations are:

```text
encoder_wp_admit_hasflag_empty_a1
encoder_spec_body_fv_in_ex_binders_or_renaming
castMembership_fresh_in_declared
encoder_all_result_well_typed
```

No new `sorry`, `admit`, or `axiom` was introduced by this branch.

### 12.3 `#print axioms`

The historical audit reported named dependencies for the legacy correctness
dispatcher. That dispatcher has since been retired. The current public
representation-aware audit is:

```text
encodeTerm_rep_spec and encodeTerm_rep_bool_spec:
  propext, sorryAx, Classical.choice, Quot.sound

encodeTerm_rep_spec.functionalUnionSubset_case:
  propext, sorryAx, Classical.choice, Quot.sound

exists_selectedValuation_for_functionalUnionSubset:
  propext, sorryAx, Classical.choice, Quot.sound
```

This distinction matters.  The extension is placeholder-neutral and adds no
named axiom, but the repository is not globally free of `sorryAx`; the new
theorems inherit it from the pre-existing semantic foundation.  Claiming an
absolutely axiom-free final theorem would therefore overstate the current
repository.  The concrete Union endpoint does, however, avoid all seven named
project axioms listed above.

### 12.4 Output and solver

The old inline and new shared PO environment constructors generated identical
raw Union scripts.  The full generated script matched the committed hash and
cvc5 returned:

```text
unsat
```

with the repository flags `--incremental --mbqi`.

## 13. Final theorem and file map

The main public theorem surface is:

| Declaration | Purpose |
| --- | --- |
| `encodeTerm_rep_spec` | Representation-aware soundness for every well-defined source term |
| `encodeTerm_rep_scoped_spec` | Clean-prefix companion for recursively scoped clients |
| `encodeTerm_rep_bool_spec` | Boolean result with exact SMT Boolean type and legacy `RDom` conclusion |
| `encode_type_context_representation_context` | Top-level context encoding selects supported target representations |
| `B.Env.exists_selectedValuation_for_term` | Build a represented target valuation from a source valuation |
| `B.Env.exists_sourceValuation_for_term` | Reconstruct a source valuation from a selected target valuation |
| `B.ProofObligation.flaggedValuesFunctional_of_assumptions` | Derive functionhood from typed, true PO assumptions |
| `encodeTerm_rep_spec.functionalUnionSubset_case` | Concrete represented soundness for `f ∪ g ⊆ X × Y` |
| `B.ProofObligation.exists_selectedValuation_for_functionalUnionSubset` | Connect the concrete PO assumptions to its selected target valuation |

The main implementation files are:

- `SMT/Reasoning/Representation.lean`: cast relations, supported
  representations, graph/collapse bridge, valuation relations.
- `SMT/Reasoning/EncodeTermRepresentedDefs.lean`: ordinary and scoped
  postconditions, declaration traces, helper guards, induction contracts.
- `SMT/Reasoning/Basic/EncodeTermRepresented*.lean`: constructor proofs.
- `SMT/Reasoning/EncodeTermRepresented.lean`: paired recursive assembly and
  canonical/Boolean corollaries.
- `SMT/Reasoning/ProofObligationRepresented.lean`: selected contexts,
  valuation construction in both directions, and semantic functionhood from
  assumptions.
- `SMT/Reasoning/ProofObligationUnion.lean`: concrete Union closure.
- `Test/UnionRepresentation.lean` and `Test/representation_union.sh`: decoded
  structure, exact output, and solver regression.

## 14. Selected checkpoint chronology

The branch used small commits throughout.  The full sequence is available
with:

```sh
git log --reverse --oneline 4f05b50..full-proof
```

The main milestones are:

| Commit | Milestone |
| --- | --- |
| `30b7f74` | Add representation agreement |
| `117df08` | Close represented variables |
| `85fddcd` | Close heterogeneous union |
| `b58b917` | Establish represented quantifiers |
| `e6b41fc` | Compose represented terms |
| `88f70aa` | Expose binder admissibility |
| `ea43e79` | Close represented universal quantification |
| `77c6b48` | Close represented collection soundness |
| `412f6b1` | Cover represented Lambda |
| `110a2c2` | Assemble represented recursion |
| `4a2eaf3` | Expose public represented recursion |
| `6761307` | Recover Boolean soundness |
| `95a8ab6` | Define the selected representation context |
| `dc52e66` | Construct selected target valuations |
| `14463c5` | Reconstruct source valuations |
| `e76933d` | Discharge binders and functionhood from PO assumptions |
| `52cf279` | Add the functional-union script regression |

## 15. What made the proof go through

The decisive steps were conceptual rather than tactical:

1. Treat the canonical theorem's incompatible valuation premise as a theorem
   design problem, not a proof-search problem.
2. Store the cast path explicitly and restrict it with a supported
   representation grammar.
3. Prove the function/graph bijection once and reuse it in variables, union,
   application, binders, and PO valuation construction.
4. Strengthen totality before binder migration so alternative valuations are
   available exactly where counterexample transport needs them.
5. Track generated declarations and specification truth explicitly instead of
   assuming helper names remain globally scoped.
6. Pair ordinary and scoped recursion so each constructor receives both
   contracts for strict subterms without a circular global hypothesis.
7. Derive functionhood from true source hypotheses, never from flags alone.
8. Reject the false global `FlagsInContext` invariant after inspecting the
   concrete decoder output, and replace it with assigned-value and term-local
   conditions.
9. Match the decoder's actual collection-over-`pfun` total-function term
   instead of proving only the simpler direct membership shape.
10. Keep proof-discovered encoder defects in isolated commits and pin the final
    script with a structural, byte-level, and solver-level regression.

That combination closed the original representation mismatch without
weakening `encodeTerm_spec`, without forcing functional free variables back to
canonical relation declarations, and without adding new placeholders or
project axioms.  The later Lambda redesign preserves those principles but does
intentionally change the emitted representation of source Lambda terms, as
detailed next.

## 16. Follow-up: encode B lambdas as SMT functions

### 16.1 What changed, and what did not

The source semantics did not change.  In B, a lambda still denotes a set of
ordered pairs and therefore has a relation type:

```text
λ vs ∈ D . P : set (tau × beta)
```

The change is solely to its SMT representation.  Before this follow-up, the
encoder materialized the graph directly as a characteristic predicate:

```text
lambda xy : Pair sigma gamma .
  D'(fst xy) and snd xy = P'[fst xy / vs]

type: Pair sigma gamma -> Bool
```

The new encoder preserves functionhood in the target type:

```text
lambda x : sigma .
  ite (D' x)
      (some (P'[x / vs]))
      (none : Option gamma)

type: sigma -> Option gamma
```

For a multi-variable source lambda, `x` is the encoded tuple.  The existing
`toDestPair` and `substList` operations destructure it and substitute its
components for `vs`.  There is no semantic choice outside the source domain:
the result is exactly `none` there.

This is the target-level meaning of "encode functions as functions".  It does
not assert that B itself ceases to model functions as functional relations.
The representation-aware relation bridges the option function back to the B
set of pairs by taking its graph and retracting endpoint representations.

The implementation in `Encoder/Encoder.lean` is deliberately small.  It:

1. encodes `D` and requires a characteristic predicate type;
2. installs the source binders while encoding `P`;
3. preserves the existing declaration-snapshot check, so `P` cannot leak
   helper declarations out of the lambda;
4. allocates one fresh tuple argument `x : sigma`;
5. substitutes `toDestPair vs x` into `P'`;
6. removes `x` from the operational context; and
7. returns the option-valued lambda and its function type.

The old pair argument `xy : Pair sigma gamma`, conjunction, and output-equality
test disappear from this branch.

### 16.2 Why the supported-representation grammar had to become recursive

The earlier `BType.SupportedSMT.optionFun` constructor fixed both endpoints to
their canonical SMT encodings.  That was sufficient for a flagged free
variable selected by `encodeTypeContext`, but it was not closed under the new
lambda rule.  A lambda can itself consume or return a value whose recursively
encoded representation is non-canonical.

The constructor is therefore now structurally recursive:

```lean
| optionFun {alpha beta : BType} {sigma tau : SMTType} :
    SupportedSMT alpha sigma ->
    SupportedSMT beta tau ->
    SupportedSMT (set (alpha × beta))
      (SMTType.fun sigma (SMTType.option tau))
```

This change is more than a type-signature relaxation.  The proof had to show
that all semantic operations remain natural under independently represented
domain and codomain values.  The corresponding updates in
`SMT/Reasoning/Representation.lean` include:

- decomposition of an option representation into source endpoint types,
  target endpoint types, and supported witnesses;
- construction of the canonical graph path by composing the two endpoint
  paths;
- binder admissibility at the paired endpoint representation;
- graph-cast preimage and truth lemmas for non-canonical endpoints;
- application-through-cast equivalences for `some` and `none`;
- supported graph casts between option representations;
- injectivity of the option graph; and
- `RDomCastSupported.cast_eq_iff` for comparing values represented through
  different supported option-function types.

The key naturality statement is that graphing after endpoint casts agrees with
casting the original graph.  It is used in both directions: a true point of a
cast graph yields represented source endpoints, and a represented source pair
whose option function returns `some` yields a true point of the cast graph.

### 16.3 The semantic proof of the new lambda

The central theorem is
`represented_lambda_option_of_total_body` in
`SMT/Reasoning/Basic/EncodeTermRepresentedLambda.lean`.  Its conclusion is an
`RDomCastSupported` witness between:

- the B relation denoted by the source lambda; and
- the SMT option-valued function denoted by the emitted target lambda.

The proof proceeds pointwise, but both directions are necessary.

For a target application returning `some b`:

1. invert the denotation of the target lambda to the denotation of its body at
   the queried argument;
2. invert the `ite`/`some`/`none` result, proving that the encoded domain test
   was true;
3. use the represented set-predicate relation to recover a source domain value
   `x` represented by the target argument;
4. transport the body induction hypothesis through tuple destruction and
   substitution;
5. recover the source body value represented by `b`; and
6. use the B lambda membership theorem to show `(x, P x)` belongs to the source
   graph.

For a pair `(x, p)` in the source lambda graph:

1. invert source lambda membership to obtain `x ∈ D` and the source body
   equation;
2. use supported domain surjectivity to choose a target representative `a` of
   `x`;
3. run the represented body theorem under the source and target binder
   updates;
4. show the encoded domain application at `a` is true;
5. evaluate the target `ite` to `some` of the represented body result; and
6. prove that applying the target function to `a` returns that `some` value.

`RDomCastSupported.optionFunction_of_pointwise` packages these two pointwise
directions into the final option-function representation witness.

Several smaller lemmas were needed to make that proof compositional:

- `denote_ite_some_none_eq_some_iff` characterizes the successful payload
  branch exactly;
- `denote_ite_some_none_some_implies_true` extracts the domain guard;
- `lambda_option_domain_denote_of_lambda_denote` recovers the encoded domain
  denotation from a denoting target lambda;
- `represented_lambda_option_subst_at_domain` connects tuple substitution to
  the body induction hypothesis;
- `B.denote_lambda_member_iff` and
  `B.denote_lambda_member_domain` expose the source graph semantics; and
- `B.denote_lambda_seed_body_exists` obtains the first successful source body
  evaluation needed to unlock the induction hypothesis's universal totality
  clause.

The seed-body step matters because `EncodeTermRepTotal` is conditional on one
successful source evaluation.  For a nonempty domain, a member provides the
seed.  For an empty domain, the proof uses the canonical tuple value only to
establish body totality; the emitted lambda still returns `none` everywhere.

### 16.4 Rebuilding the operational and scoped lambda contracts

The raw constructor theorem in
`EncodeTermRepresentedLambdaRaw.lean` was rebuilt around the new target shape.
It still proves both the ordinary and declaration-scoped postconditions in one
run.  The operational part tracks:

- the exact fresh tuple argument and its type;
- restoration of the surrounding type context after body encoding;
- the absence of leaked body declarations;
- free- and bound-variable containment for the substituted body;
- used-name monotonicity and freshness;
- target typing at `sigma -> Option gamma`;
- source/target valuation extension; and
- totality for arbitrary related valuations, not just the valuation chosen by
  the constructive semantic branch.

The scoped half is essential when the lambda is placed below a quantifier or a
generated helper.  It retains the declaration trace and proves that every
visible helper specification is well typed and true under the arbitrary
valuation consumed by the parent proof.

`EncodeTermStruct.lean` and `EncodeTermBvUsed.lean` were updated in parallel so
the generic structural facts describe the actual fresh-variable and binder
shape.  This prevented the semantic proof from silently relying on the old
pair/Boolean syntax.

### 16.5 Consumer migration

Changing the constructor was only the first step.  Every consumer that could
receive a lambda result had to accept the option representation and preserve
the source meaning.

#### Application

Application now consumes the option function directly.  Its proof relates
`some` payloads to membership in the represented source graph, transports
arguments through supported endpoint casts, and retains the failure behavior
outside the function domain.

#### Membership

`Encoder/Loosening/Loosening.lean` now factors option membership into two
operations:

- `castMembership.optionForward` casts a pair to the function's endpoint
  representation and checks `S(fst p) = some (snd p)`;
- `castMembership.optionCommon` first moves an option function to a common
  supported endpoint representation and then invokes the forward rule.

The four endpoint-cast directions reuse these operations instead of carrying
four subtly different helper encodings.  The exact and representation-aware
membership proofs were generalized to match.

#### Equality and collection

Equality can compare option functions only after moving both operands to a
common supported representation.  Collection must preserve option-valued
components inside tuples and must reconstruct their graphs when the source
semantics expects sets of pairs.  Their ordinary and scoped proofs were
updated without reintroducing a canonical-only coercion.

#### Union and intersection

Union and intersection deliberately do **not** return an option function.  The
union of two partial functions need not be functional: if both contain a
different output for the same input, the set-theoretic union contains both
pairs.  Intersection also remains a relation operation.  Therefore these
consumers graph option operands and return a characteristic predicate on
pairs.

The direct equal-type option branch now calls `castUnion.fun` or
`castInter.fun`, just like the heterogeneous branch.  The generated graph
binder is erased from the operational context after construction.  The proof
families cover:

- option/option operands;
- option/predicate and predicate/option operands;
- forward and reverse cast directions;
- arbitrary supported endpoint representations;
- incomparable representations that must fail; and
- ordinary as well as declaration-scoped execution.

The scoped contracts are stronger than existence of a convenient helper
assignment.  `option_helper_guarded` proves that **every** typed assignment
satisfying the emitted helper specification denotes the correct graph.  The
large `fun_scoped_contract` then composes that fact with the actual
`castUnion.fun` execution, exact declaration delta, context trace, fresh graph
binder, output typing, and both constructive and guarded semantic clauses.
The intersection proof mirrors the same argument with conjunction and source
intersection membership.

#### Quantifiers and powersets

The universal proof uses the recursively supported option endpoints when an
option-valued domain supplies tuple binders.  It obtains binder preimages at
the paired endpoint representation rather than assuming canonical component
types.

The final full build exposed one downstream hole in powerset dispatch.  Its
graph branch still pattern-matched an option representation as though the
constructor arguments were canonical B types.  Both
`encodePowTail_graph_rep_spec` and the scoped `graph_scoped_contract` were
generalized to explicit target endpoint types `sigma`, `tau` and supported
witnesses.  The graph helper now has type

```text
Pair sigma tau -> Bool
```

and the direct powerset continuation uses the supported product
representation, not a forced canonical pair.  This was the only failure found
by the first repository-wide build after the main Lambda, union, and
intersection proofs had compiled.

### 16.6 The active theorem after the redesign

The Lean entry point remains:

```lean
theorem encodeTerm_rep_spec
    (binder_admissible : EncodeTermAllBinderAdmissible)
    (wd_t : B.Term.WellDefined t) :
    EncodeTermRepIH t
```

Its representation grammar is now wider, so its mathematical content is:

> Let a well-typed, well-defined B term `t : alpha` denote `X` under a source
> valuation.  Let the supplied SMT valuation represent the source valuation on
> the free variables of `t`, using supported representations.  If `encodeTerm`
> succeeds with `t' : sigma`, then the final context types `t'`, generated
> names and declarations satisfy the operational freshness invariants, and
> there is an extended SMT valuation under which `t'` denotes `Y` together
> with a supported cast path `c : sigma ~> alpha.toSMTType` such that
> `retract alpha (castZF_apply c Y) = X`.  The same conclusion is available
> for every related alternative valuation satisfying generated helper
> specifications.

For a source lambda, `sigma` is now an option-function type whose argument and
payload recursively represent the source domain and result.  Its cast path is
the graph path assembled from the endpoint paths.

For a source predicate, the existing Boolean inversion still forces
`sigma = SMTType.bool`, so `encodeTerm_rep_bool_spec` continues to recover the
exact Boolean target type and the legacy `RDom` conclusion.

The legacy canonical theorem was intentionally not repaired.  `Correctness.lean`
now imports `SMT.Reasoning.EncodeTermRepresented` and the concrete union
closure, but not `SMT.Reasoning.EncodeTermCorrect`.  The old files remain for a
later dependency-extraction and deletion session.

### 16.7 Validation of the follow-up

The final Lean checks were:

```sh
lake env lean SMT/Reasoning/Basic/EncodeTermRepresentedLambda.lean
lake env lean SMT/Reasoning/Basic/EncodeTermRepresentedLambdaRaw.lean
lake env lean SMT/Reasoning/Basic/EncodeTermRepresentedUnion.lean
lake env lean SMT/Reasoning/Basic/EncodeTermRepresentedInter.lean
lake env lean SMT/Reasoning/Basic/EncodeTermRepresentedScopedUnion.lean
lake env lean SMT/Reasoning/Basic/EncodeTermRepresentedScopedInter.lean
lake env lean SMT/Reasoning/Basic/EncodeTermRepresentedSet.lean
lake env lean SMT/Reasoning/Basic/EncodeTermRepresentedScopedSet.lean
lake build
```

The repository-wide build completed all 1086 jobs successfully.  The long
represented universal module compiled in 780 seconds; its output contained
only existing linter warnings.

The token-bearing source inventory was unchanged from `52cf279`:

```text
                 52cf279   follow-up
sorry lines            22          22
admit lines            33          33
axiom lines            32          32
```

No added line contains `sorry`, `admit`, or a named `axiom` declaration.

The current `#print axioms` output after retiring the source-domain
containment axiom is:

```text
encodeTerm_rep_spec and encodeTerm_rep_scoped_spec:
  propext, sorryAx, Classical.choice, Quot.sound

encodeTerm_rep_spec.functionalUnionSubset_case:
  propext, sorryAx, Classical.choice, Quot.sound
```

This is exactly the inherited distinction already recorded in Section 12:
the follow-up adds no placeholder or project axiom, but the repository's
pre-existing semantic foundation means the public theorem is not globally
`sorryAx`-free.

Two real proof-obligation examples exercise the result.

First, the heterogeneous union regression still reports:

```text
Union representation structure: ok
Union represented script: byte-identical and unsat
```

Its pinned SHA-256 remains:

```text
e93a29578ca1ee3d3fb2a175dbf6b3cef135a435855a05bf397c38f75b916a50
```

Second, `Test/Demo2.pog` contains Atelier B's `id(1..ub)`.  The reader lowers
`id` to a B lambda, making it a direct end-to-end test of the redesigned
constructor.  The regenerated SMT contains the characteristic fragment:

```smt
(ite (and (<= 1 (fst ...)) (<= (fst ...) ub))
     (some (fst ...))
     (as none (Option Int)))
```

cvc5 returns `unsat` with `--incremental --mbqi`.  The new regression
`Test/representation_lambda.sh` checks that option-valued shape, pins the
generated bytes, and runs the solver.  The new SHA-256 is:

```text
1a8f044573d706732577665376cbe871c5a3a6a0e4ab9df0408114725990b5dd
```

For comparison, the old checked-in graph-predicate output for the same MWE
has SHA-256
`2c6613d7487cc799438c5662bee8ef850e9279dbe5421035f27dc2de5aaf1142`.
The byte change is expected and directly witnesses the representation
redesign.

The repeatable behavioral commands are:

```sh
./Test/representation_union.sh
./Test/representation_lambda.sh
```

### 16.8 Follow-up file map

| Area | Main files | Role |
| --- | --- | --- |
| Encoder | `Encoder/Encoder.lean` | Emit `sigma -> Option gamma` for B lambdas |
| Consumers | `Encoder/Loosening/Loosening.lean` | Normalize application, membership, union, and intersection paths |
| Representation | `SMT/Reasoning/Representation.lean` | Recursive option endpoints and graph naturality |
| Lambda semantics | `EncodeTermRepresentedLambda.lean` | Pointwise option-function/source-graph equivalence |
| Lambda execution | `EncodeTermRepresentedLambdaRaw.lean` | Ordinary and scoped constructor contract |
| Union/intersection | `EncodeTermRepresentedUnion.lean`, `EncodeTermRepresentedInter.lean`, scoped companions | Graph option operands without claiming the result is functional |
| Membership/application | `EncodeTermRepresentedMem.lean`, `EncodeTermRepresentedApp.lean` | Consume option functions under supported casts |
| Binders/collection | `EncodeTermRepresentedAll.lean`, `EncodeTermRepresentedCollect*.lean`, `EncodeTermRepresentedBinders.lean` | Preserve recursive endpoint and scoped-helper invariants |
| Structural facts | `EncodeTermStruct.lean`, `EncodeTermBvUsed.lean` | Match the new emitted syntax and fresh-name behavior |
| Powerset closure | `EncodeTermRepresentedSet.lean`, `EncodeTermRepresentedScopedSet.lean` | Graph arbitrary supported option endpoints |
| Active API | `Correctness.lean` | Import represented soundness, silence the legacy dispatcher |
| Regression | `Test/representation_lambda.sh` | Check real Lambda output bytes, shape, and `unsat` result |

### 16.9 Final boundary

The redesign reaches the intended boundary:

- a source lambda is emitted as a real option-valued SMT function;
- nested endpoint representations remain supported;
- application and membership consume that function directly;
- relation operations graph it only when the source operation can destroy
  functionhood;
- the main representation-aware theorem and its scoped companion cover the
  changed output;
- the concrete union theorem remains valid; and
- the legacy canonical proof is outside the active import path, without being
  repaired or prematurely deleted.

The remaining cleanup is intentionally separate: extract the few semantic
lemmas still imported from the legacy `EncodeTermCorrect*` family, then remove
that family and its inherited proof artifacts.  It is not part of this
soundness-preserving Lambda refactor.
