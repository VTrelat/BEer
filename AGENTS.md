# Prompt for a Lean Proof Agent Working on BEer

This file is intended to be pasted to an agent that will finish the last proof obligations of the BEer project.

Repository root: `/Users/vtrelat/Documents/BEer`

## Mission

You are working inside the BEer repository, a Lean 4 project that translates Atelier B proof-obligation files (`.pog`) into SMT-LIB v2.7 (`.smt`) through a certified higher-order encoding.

Your goal is to finish the last missing pieces of the correctness proof of the encoder. The active frontier is the theorem `encodeTerm_spec` in `SMT/Reasoning/EncodeTermCorrect.lean`. These are the very last active, non-commented proof cases.

Do not change theorem statements or add axioms. Default assumption: do not change encoder behavior unless the proof reveals a genuine implementation bug or an actually missing encoder branch. Prefer proving with the current architecture and extracting auxiliary lemmas when proofs become too heavy.

## What BEer Does

BEer takes a B proof obligation, parses it, builds an internal B AST, encodes the B terms into SMT terms, and emits an SMT-LIB file.

The main entry point is:

- `Main.lean`

The rough pipeline is:

1. Read a `.pog` file with `readPOG`.
2. Translate the parsed file to a `B.Env` with `POGtoB`.
3. Encode the resulting B environment with `encode`.
4. Serialize the SMT environment to an SMT-LIB file with `EncoderState.toSMTFile`.
5. Prepend the SMT prelude.

The package is named `B` in `lakefile.lean`, and depends in particular on:

- `mathlib`
- `ZFLean`

## Core Source Language: B

The main first-order B syntax is in:

- `B/Syntax/Basic.lean`

The B term constructors relevant to `encodeTerm` are:

- atoms: `var`, `int`, `bool`
- arithmetic/pairs: `maplet`, `add`, `sub`, `mul`, `le`
- logic: `and`, `not`, `eq`
- basic sets: `ℤ`, `𝔹`
- set operators: `mem`, `collect`, `pow`, `cprod`, `union`, `inter`, `card`
- functions: `app`, `lambda`, `pfun`
- extrema/quantification: `min`, `max`, `all`

Important B notations:

- `↦ᴮ`, `+ᴮ`, `-ᴮ`, `*ᴮ`, `≤ᴮ`
- `∧ᴮ`, `¬ᴮ`, `=ᴮ`
- `∈ᴮ`, `𝒫ᴮ`, `⨯ᴮ`, `∪ᴮ`, `∩ᴮ`
- `@ᴮ`, `⇸ᴮ`, `|S|ᴮ`

B types are in:

- `B/Typing/Basic.lean`

The source type universe is:

- `BType.int`
- `BType.bool`
- `BType.set α`
- `BType.prod α β`

The source environment is:

- `B/Environment.lean`

`B.Env` contains the typed B context, flags, fresh variable counter, definitions, hypotheses, distinctness assumptions, finiteness assumptions, and proof obligations.

## Target Language: SMT

The target syntax is in:

- `SMT/Syntax.lean`
- `SMT/Typing.lean`

Important SMT types include:

- `.bool`
- `.int`
- `.unit`
- `.fun α β`
- `.option α`
- `.pair α β`

Important SMT terms include:

- variables/constants/applications
- binders: `lambda`, `forall`, `exists`
- logic: `eq`, `and`, `or`, `not`, `imp`, `ite`
- data: `some`, `the`, `none`, `pair`, `fst`, `snd`, `distinct`
- arithmetic: `le`, `add`, `sub`, `mul`

The SMT typing notation is `⊢ˢ`.

## Encoding Strategy

The main encoder is:

- `Encoder/Encoder.lean`

The type translation is:

- `Encoder/Basic.lean`

Specifically:

- `BType.int` maps to `.int`
- `BType.bool` maps to `.bool`
- `BType.set α` maps to `.fun α.toSMTType .bool`
- `BType.prod α β` maps to `.pair α.toSMTType β.toSMTType`

This means ordinary B sets are encoded as characteristic predicates.

There is also an important second representation for relations and partial functions:

- a partial function can appear as `.fun α (.option β)`
- a relation/graph can appear as `.fun (.pair α β) .bool`

The repository uses a "loosening" mechanism to move between compatible SMT representations. This is central for the remaining difficult cases.

Relevant files:

- `Encoder/Loosening/Castable.lean`
- `Encoder/Loosening/Rules.lean`
- `Encoder/Loosening/Loosening.lean`
- `SMT/Reasoning/LooseningDefs.lean`
- `SMT/Reasoning/Basic/LoosenAuxSpec.lean`
- `SMT/Reasoning/Basic/LoosenAuxExact/`

Important concepts:

- `α ⊑ β` means SMT type `α` can be loosened/cast to `β`
- `α ~> β` is an explicit cast path
- `loosen` and `loosenAux_prf` produce fresh SMT variables plus specifications that assert semantic adequacy of the cast

Important cast helpers already used by `encodeTerm`:

- `castEq`
- `castApp`
- `castMembership`
- `castUnion`
- `castInter`

## Semantic Infrastructure

The key semantic bridge is in:

- `SMT/Reasoning/Defs.lean`

This file proves and defines:

- `BType_iso_SMTType`
- `BType.canonicalIsoSMTType`
- `retract`
- `RDom`, written `≘ᶻ`
- `RValuation`
- renaming-context transport from B to SMT

The meaning of `≘ᶻ` is:

- a B semantic object `⟨X, τ, _⟩` and an SMT semantic object `⟨X', τ', _⟩` satisfy `⟨X, τ, _⟩ ≘ᶻ ⟨X', τ', _⟩`
- iff `τ' = τ.toSMTType`
- and `retract τ X' = X`

This relation is the final semantic postcondition in `encodeTerm_spec`.

Renaming-context invariants are also fundamental. In particular:

- `RenamingContext.CoversFV`
- `RenamingContext.Extends`
- `RenamingContext.ExtendsOnSourceFV`
- `B.CoversUsedVars`

The proof repeatedly threads fresh-variable and renaming information through recursive calls to `encodeTerm`.

## Proof Architecture

The main correctness theorem is:

- `SMT/Reasoning/EncodeTermCorrect.lean`

Theorem:

- `encodeTerm_spec`

It is a proof by induction on B terms. For a well-typed B term `t`, it states that if:

- the source typing `E.context ⊢ᴮ t : α` holds,
- a B renaming context covers the free variables of `t`,
- an SMT renaming context extends the source renaming on source free variables,
- the SMT context is well-formed relative to the encoder state,
- and the source denotation `⟦t.abstract ...⟧ᴮ` is `some ⟨T, α, hT⟩`,

then running `encodeTerm t E` succeeds and returns:

- an SMT term `t'`,
- type `σ = α.toSMTType`,
- a typing proof `Γ' ⊢ˢ t' : σ`,
- an extended renaming context `Δ'`,
- and an SMT denotation `denT'` such that `⟨T, α, hT⟩ ≘ᶻ denT'`.

The proof style is monadic and uses the repo's MVCGen-style proof combinators and tactics:

- `mintro`
- `mpure`
- `mspec`
- `mpure_intro`

The completed cases are split across:

- `SMT/Reasoning/Basic/EncodeTermCorrectBase.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectArith.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectBool.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectSet.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectMem.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectEq.lean`

Already completed and usable as templates:

- `ℤ_case`
- `𝔹_case`
- `var_case`
- `int_case`
- `bool_case`
- `maplet_case`
- `add_case`
- `sub_case`
- `mul_case`
- `le_case`
- `min_case`
- `max_case`
- `card_case`
- `and_case`
- `not_case`
- `pow_case`
- `cprod_case`
- `mem_case`

Useful refactoring examples already present:

- `EncodeTermCorrectArith.Arith.denote_inv` in `SMT/Reasoning/Basic/EncodeTermCorrectArith.lean`
- `cprod_case_denotation_aux` in `SMT/Reasoning/Basic/EncodeTermCorrectSet.lean`

When a semantic tail becomes too large, prefer extracting a private auxiliary lemma immediately before the theorem rather than raising heartbeats aggressively.

## Exact Remaining Frontier

Among the active, non-commented proof obligations for the encoder correctness theorem, the remaining frontier is exactly the last 8 cases.

They are:

1. `encodeTerm_spec.eq_case`
2. `encodeTerm_spec.union_case`
3. `encodeTerm_spec.inter_case`
4. `encodeTerm_spec.app_case`
5. `encodeTerm_spec.pfun_case`
6. `encodeTerm_spec.collect_case`
7. `encodeTerm_spec.lambda_case`
8. `encodeTerm_spec.all_case`

Current repository status:

- In `SMT/Reasoning/EncodeTermCorrect.lean`, the main theorem still has 7 `sorry` branches:
  - `union`
  - `inter`
  - `app`
  - `pfun`
  - `collect`
  - `lambda`
  - `all`
- `eq` is no longer a top-level `sorry` branch, but `SMT/Reasoning/Basic/EncodeTermCorrectEq.lean` still contains 3 `admit`s inside `encodeTerm_spec.eq_case`

So the practical last-mile frontier is 8 unfinished cases, even though only 7 remain as direct `sorry` branches in the top-level theorem.

## Important Caveat About the Remaining Cases

Do not assume every remaining case is only a proof problem.

At the time of this snapshot:

- `Encoder/Loosening/Loosening.lean` still has `castUnion.*` branches that `throw "Not implemented."`
- `Encoder/Loosening/Loosening.lean` still has `castInterAux` that `throw "Not implemented yet."`

Therefore:

- `union_case` and `inter_case` are not just missing proofs
- they likely also require implementing or repairing encoder support for union/inter before the correctness proof can possibly be finished

Treat this as part of the last frontier, not as an accidental side issue.

## What Makes the Remaining Cases Hard

### `eq_case`

This case is about equality after unifying or loosening both sides to a compatible SMT representation. Expect to use:

- `castEq`
- `loosenAux_prf_spec`
- `RDom`
- `retract`
- canonical isomorphism/retraction lemmas from `SMT/Reasoning/Defs.lean`

### `union_case` and `inter_case`

These cases depend on cast-aware set/function/graph unification. They will interact with:

- characteristic predicates
- graph encodings
- cast paths
- `castUnion` / `castInter`

Because the encoder helpers are currently incomplete, these cases may require both implementation and proof.

### `app_case`

This case is about application across several representational regimes:

- application of characteristic predicates
- application of partial functions
- application of graph encodings converted into functions

Expect to use:

- `castApp`
- loosen auxiliary specs
- semantic lemmas connecting graph and function views

### `pfun_case`

This case uses the loosening layer heavily. The encoder may loosen domain/codomain sets into graph-style predicates and then builds a characteristic predicate for the space of partial functions.

This case is likely to require:

- `loosen`
- `loosenAux_prf_spec`
- graph/characteristic-predicate cast lemmas
- reasoning about fresh constants introduced by `declareConst` and `addSpec`

### `collect_case`, `lambda_case`, `all_case`

These are the binder-heavy cases. They involve:

- lists of bound variables `vs`
- source substitution through `substList`
- temporary context extension and rollback
- `freshVarList`
- `Function.updates`
- PHOAS abstraction and denotation under extended valuations
- possible special treatment of flagged variables

These cases are likely the hardest proof obligations left in the repository.

## Special Note on Flags

`B.Env` contains `flags`, and `encodeTypeContext` treats flagged variables specially.

In particular, flagged source variables of B type `set (prod α β)` are inserted into the SMT context as:

- `.fun α.toSMTType (.option β.toSMTType)`

This means some source sets of pairs are intentionally treated as partial functions on the SMT side. This matters for:

- `app_case`
- `pfun_case`
- `collect_case`
- `lambda_case`
- `all_case`

Do not ignore flags when the source binder domain or applied term can denote a flagged identifier.

## How to Work Effectively in This Repo

1. Read `SMT/Reasoning/EncodeTermCorrect.lean` first to understand the exact theorem statement and induction structure.
2. Read the corresponding branch in `Encoder/Encoder.lean` before proving a case.
3. Reuse nearby completed case proofs instead of inventing a new proof style.
4. Prefer LSP/MCP inspection over blind tactic search.
5. When a proof tail becomes huge, extract a `private theorem` immediately before the main case theorem.
6. Keep theorem statements unchanged.
7. Do not add axioms or use `admit`/`sorry` in finished work.
8. Lower proof complexity by trimming unused hypotheses in extracted auxiliary lemmas.
9. Prefer proving the hard semantic direction first.
10. Be ready to implement missing encoder pieces for `union` and `inter` before attempting their proof.

## Suggested Order of Attack

Recommended order:

1. Finish `eq_case`
2. Implement and prove `union_case`
3. Implement and prove `inter_case`
4. Prove `app_case`
5. Prove `pfun_case`
6. Prove `collect_case`
7. Prove `lambda_case`
8. Prove `all_case`

Rationale:

- `eq_case` is already isolated and almost complete
- `union` and `inter` likely need encoder work, so surface those issues early
- `app` and `pfun` sit on top of loosening/cast infrastructure needed by the binder cases
- `collect`, `lambda`, and `all` are the deepest binder proofs and should be attacked after the cast machinery is stable

## Files You Should Read First

Start with these:

- `README.md`
- `Main.lean`
- `Encoder/Basic.lean`
- `Encoder/Encoder.lean`
- `Encoder/Loosening/Castable.lean`
- `Encoder/Loosening/Rules.lean`
- `Encoder/Loosening/Loosening.lean`
- `SMT/Reasoning/Defs.lean`
- `SMT/Reasoning/LooseningDefs.lean`
- `SMT/Reasoning/Basic/StateSpecs.lean`
- `SMT/Reasoning/Basic/LoosenAuxSpec.lean`
- `SMT/Reasoning/EncodeTermCorrect.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectArith.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectBool.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectSet.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectMem.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectEq.lean`

## Validation Policy

Prefer incremental verification:

1. Check the edited file with Lean/LSP after each local step.
2. Use file-level checks before any full build.
3. Keep proofs free of new `sorry` or `admit`.

Good local targets:

- `lake env lean SMT/Reasoning/Basic/EncodeTermCorrectEq.lean`
- `lake env lean SMT/Reasoning/EncodeTermCorrect.lean`

Use project-wide builds only after local file checks are green.

## Final Objective

Finish the BEer encoder correctness proof by removing the remaining admits/sorries at the end of `encodeTerm_spec`.

Success means:

- `encodeTerm_spec.eq_case` is complete
- the remaining 7 top-level `sorry` branches in `SMT/Reasoning/EncodeTermCorrect.lean` are replaced by proved case theorems
- if necessary, `castUnion` and `castInter` are implemented and proved correct enough for the final theorem
- no new axioms are introduced
- the active proof frontier for `encodeTerm_spec` is gone

## Short Version

You are finishing the BEer proof project. BEer certifies the translation from B proof obligations to SMT-LIB through a Lean formalization over ZF semantics. The main theorem is `encodeTerm_spec`. Almost all cases are done. The only remaining active frontier is the last 8 cases: `eq`, `union`, `inter`, `app`, `pfun`, `collect`, `lambda`, and `all`. Reuse the completed `encodeTerm_spec.*_case` proofs as templates, respect the existing monadic proof style, rely on `SMT/Reasoning/Defs.lean` and the loosening infrastructure, and be aware that `union` and `inter` are currently blocked by unfinished encoder helpers in `Encoder/Loosening/Loosening.lean`.

## Imported Claude Cowork project instructions

# Prompt for a Lean Proof Agent Working on BEer

This file is intended to be pasted to an agent that will finish the last proof obligations of the BEer project.

Repository root: `/Users/vtrelat/Documents/BEer`

## Mission

You are working inside the BEer repository, a Lean 4 project that translates Atelier B proof-obligation files (`.pog`) into SMT-LIB v2.7 (`.smt`) through a certified higher-order encoding.

Your goal is to finish the last missing pieces of the correctness proof of the encoder. The active frontier is the theorem `encodeTerm_spec` in `SMT/Reasoning/EncodeTermCorrect.lean`. These are the very last active, non-commented proof cases.

Do not change theorem statements or add axioms. Default assumption: do not change encoder behavior unless the proof reveals a genuine implementation bug or an actually missing encoder branch. Prefer proving with the current architecture and extracting auxiliary lemmas when proofs become too heavy.

## What BEer Does

BEer takes a B proof obligation, parses it, builds an internal B AST, encodes the B terms into SMT terms, and emits an SMT-LIB file.

The main entry point is:

- `Main.lean`

The rough pipeline is:

1. Read a `.pog` file with `readPOG`.
2. Translate the parsed file to a `B.Env` with `POGtoB`.
3. Encode the resulting B environment with `encode`.
4. Serialize the SMT environment to an SMT-LIB file with `EncoderState.toSMTFile`.
5. Prepend the SMT prelude.

The package is named `B` in `lakefile.lean`, and depends in particular on:

- `mathlib`
- `ZFLean`

## Core Source Language: B

The main first-order B syntax is in:

- `B/Syntax/Basic.lean`

The B term constructors relevant to `encodeTerm` are:

- atoms: `var`, `int`, `bool`
- arithmetic/pairs: `maplet`, `add`, `sub`, `mul`, `le`
- logic: `and`, `not`, `eq`
- basic sets: `ℤ`, `𝔹`
- set operators: `mem`, `collect`, `pow`, `cprod`, `union`, `inter`, `card`
- functions: `app`, `lambda`, `pfun`
- extrema/quantification: `min`, `max`, `all`

Important B notations:

- `↦ᴮ`, `+ᴮ`, `-ᴮ`, `*ᴮ`, `≤ᴮ`
- `∧ᴮ`, `¬ᴮ`, `=ᴮ`
- `∈ᴮ`, `𝒫ᴮ`, `⨯ᴮ`, `∪ᴮ`, `∩ᴮ`
- `@ᴮ`, `⇸ᴮ`, `|S|ᴮ`

B types are in:

- `B/Typing/Basic.lean`

The source type universe is:

- `BType.int`
- `BType.bool`
- `BType.set α`
- `BType.prod α β`

The source environment is:

- `B/Environment.lean`

`B.Env` contains the typed B context, flags, fresh variable counter, definitions, hypotheses, distinctness assumptions, finiteness assumptions, and proof obligations.

## Target Language: SMT

The target syntax is in:

- `SMT/Syntax.lean`
- `SMT/Typing.lean`

Important SMT types include:

- `.bool`
- `.int`
- `.unit`
- `.fun α β`
- `.option α`
- `.pair α β`

Important SMT terms include:

- variables/constants/applications
- binders: `lambda`, `forall`, `exists`
- logic: `eq`, `and`, `or`, `not`, `imp`, `ite`
- data: `some`, `the`, `none`, `pair`, `fst`, `snd`, `distinct`
- arithmetic: `le`, `add`, `sub`, `mul`

The SMT typing notation is `⊢ˢ`.

## Encoding Strategy

The main encoder is:

- `Encoder/Encoder.lean`

The type translation is:

- `Encoder/Basic.lean`

Specifically:

- `BType.int` maps to `.int`
- `BType.bool` maps to `.bool`
- `BType.set α` maps to `.fun α.toSMTType .bool`
- `BType.prod α β` maps to `.pair α.toSMTType β.toSMTType`

This means ordinary B sets are encoded as characteristic predicates.

There is also an important second representation for relations and partial functions:

- a partial function can appear as `.fun α (.option β)`
- a relation/graph can appear as `.fun (.pair α β) .bool`

The repository uses a "loosening" mechanism to move between compatible SMT representations. This is central for the remaining difficult cases.

Relevant files:

- `Encoder/Loosening/Castable.lean`
- `Encoder/Loosening/Rules.lean`
- `Encoder/Loosening/Loosening.lean`
- `SMT/Reasoning/LooseningDefs.lean`
- `SMT/Reasoning/Basic/LoosenAuxSpec.lean`
- `SMT/Reasoning/Basic/LoosenAuxExact/`

Important concepts:

- `α ⊑ β` means SMT type `α` can be loosened/cast to `β`
- `α ~> β` is an explicit cast path
- `loosen` and `loosenAux_prf` produce fresh SMT variables plus specifications that assert semantic adequacy of the cast

Important cast helpers already used by `encodeTerm`:

- `castEq`
- `castApp`
- `castMembership`
- `castUnion`
- `castInter`

## Semantic Infrastructure

The key semantic bridge is in:

- `SMT/Reasoning/Defs.lean`

This file proves and defines:

- `BType_iso_SMTType`
- `BType.canonicalIsoSMTType`
- `retract`
- `RDom`, written `≘ᶻ`
- `RValuation`
- renaming-context transport from B to SMT

The meaning of `≘ᶻ` is:

- a B semantic object `⟨X, τ, _⟩` and an SMT semantic object `⟨X', τ', _⟩` satisfy `⟨X, τ, _⟩ ≘ᶻ ⟨X', τ', _⟩`
- iff `τ' = τ.toSMTType`
- and `retract τ X' = X`

This relation is the final semantic postcondition in `encodeTerm_spec`.

Renaming-context invariants are also fundamental. In particular:

- `RenamingContext.CoversFV`
- `RenamingContext.Extends`
- `RenamingContext.ExtendsOnSourceFV`
- `B.CoversUsedVars`

The proof repeatedly threads fresh-variable and renaming information through recursive calls to `encodeTerm`.

## Proof Architecture

The main correctness theorem is:

- `SMT/Reasoning/EncodeTermCorrect.lean`

Theorem:

- `encodeTerm_spec`

It is a proof by induction on B terms. For a well-typed B term `t`, it states that if:

- the source typing `E.context ⊢ᴮ t : α` holds,
- a B renaming context covers the free variables of `t`,
- an SMT renaming context extends the source renaming on source free variables,
- the SMT context is well-formed relative to the encoder state,
- and the source denotation `⟦t.abstract ...⟧ᴮ` is `some ⟨T, α, hT⟩`,

then running `encodeTerm t E` succeeds and returns:

- an SMT term `t'`,
- type `σ = α.toSMTType`,
- a typing proof `Γ' ⊢ˢ t' : σ`,
- an extended renaming context `Δ'`,
- and an SMT denotation `denT'` such that `⟨T, α, hT⟩ ≘ᶻ denT'`.

The proof style is monadic and uses the repo's MVCGen-style proof combinators and tactics:

- `mintro`
- `mpure`
- `mspec`
- `mpure_intro`

The completed cases are split across:

- `SMT/Reasoning/Basic/EncodeTermCorrectBase.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectArith.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectBool.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectSet.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectMem.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectEq.lean`

Already completed and usable as templates:

- `ℤ_case`
- `𝔹_case`
- `var_case`
- `int_case`
- `bool_case`
- `maplet_case`
- `add_case`
- `sub_case`
- `mul_case`
- `le_case`
- `min_case`
- `max_case`
- `card_case`
- `and_case`
- `not_case`
- `pow_case`
- `cprod_case`
- `mem_case`

Useful refactoring examples already present:

- `EncodeTermCorrectArith.Arith.denote_inv` in `SMT/Reasoning/Basic/EncodeTermCorrectArith.lean`
- `cprod_case_denotation_aux` in `SMT/Reasoning/Basic/EncodeTermCorrectSet.lean`

When a semantic tail becomes too large, prefer extracting a private auxiliary lemma immediately before the theorem rather than raising heartbeats aggressively.

## Exact Remaining Frontier

Among the active, non-commented proof obligations for the encoder correctness theorem, the remaining frontier is exactly the last 8 cases.

They are:

1. `encodeTerm_spec.eq_case`
2. `encodeTerm_spec.union_case`
3. `encodeTerm_spec.inter_case`
4. `encodeTerm_spec.app_case`
5. `encodeTerm_spec.pfun_case`
6. `encodeTerm_spec.collect_case`
7. `encodeTerm_spec.lambda_case`
8. `encodeTerm_spec.all_case`

Current repository status:

- In `SMT/Reasoning/EncodeTermCorrect.lean`, the main theorem still has 7 `sorry` branches:
  - `union`
  - `inter`
  - `app`
  - `pfun`
  - `collect`
  - `lambda`
  - `all`
- `eq` is no longer a top-level `sorry` branch, but `SMT/Reasoning/Basic/EncodeTermCorrectEq.lean` still contains 3 `admit`s inside `encodeTerm_spec.eq_case`

So the practical last-mile frontier is 8 unfinished cases, even though only 7 remain as direct `sorry` branches in the top-level theorem.

## Important Caveat About the Remaining Cases

Do not assume every remaining case is only a proof problem.

At the time of this snapshot:

- `Encoder/Loosening/Loosening.lean` still has `castUnion.*` branches that `throw "Not implemented."`
- `Encoder/Loosening/Loosening.lean` still has `castInterAux` that `throw "Not implemented yet."`

Therefore:

- `union_case` and `inter_case` are not just missing proofs
- they likely also require implementing or repairing encoder support for union/inter before the correctness proof can possibly be finished

Treat this as part of the last frontier, not as an accidental side issue.

## What Makes the Remaining Cases Hard

### `eq_case`

This case is about equality after unifying or loosening both sides to a compatible SMT representation. Expect to use:

- `castEq`
- `loosenAux_prf_spec`
- `RDom`
- `retract`
- canonical isomorphism/retraction lemmas from `SMT/Reasoning/Defs.lean`

### `union_case` and `inter_case`

These cases depend on cast-aware set/function/graph unification. They will interact with:

- characteristic predicates
- graph encodings
- cast paths
- `castUnion` / `castInter`

Because the encoder helpers are currently incomplete, these cases may require both implementation and proof.

### `app_case`

This case is about application across several representational regimes:

- application of characteristic predicates
- application of partial functions
- application of graph encodings converted into functions

Expect to use:

- `castApp`
- loosen auxiliary specs
- semantic lemmas connecting graph and function views

### `pfun_case`

This case uses the loosening layer heavily. The encoder may loosen domain/codomain sets into graph-style predicates and then builds a characteristic predicate for the space of partial functions.

This case is likely to require:

- `loosen`
- `loosenAux_prf_spec`
- graph/characteristic-predicate cast lemmas
- reasoning about fresh constants introduced by `declareConst` and `addSpec`

### `collect_case`, `lambda_case`, `all_case`

These are the binder-heavy cases. They involve:

- lists of bound variables `vs`
- source substitution through `substList`
- temporary context extension and rollback
- `freshVarList`
- `Function.updates`
- PHOAS abstraction and denotation under extended valuations
- possible special treatment of flagged variables

These cases are likely the hardest proof obligations left in the repository.

## Special Note on Flags

`B.Env` contains `flags`, and `encodeTypeContext` treats flagged variables specially.

In particular, flagged source variables of B type `set (prod α β)` are inserted into the SMT context as:

- `.fun α.toSMTType (.option β.toSMTType)`

This means some source sets of pairs are intentionally treated as partial functions on the SMT side. This matters for:

- `app_case`
- `pfun_case`
- `collect_case`
- `lambda_case`
- `all_case`

Do not ignore flags when the source binder domain or applied term can denote a flagged identifier.

## How to Work Effectively in This Repo

1. Read `SMT/Reasoning/EncodeTermCorrect.lean` first to understand the exact theorem statement and induction structure.
2. Read the corresponding branch in `Encoder/Encoder.lean` before proving a case.
3. Reuse nearby completed case proofs instead of inventing a new proof style.
4. Prefer LSP/MCP inspection over blind tactic search.
5. When a proof tail becomes huge, extract a `private theorem` immediately before the main case theorem.
6. Keep theorem statements unchanged.
7. Do not add axioms or use `admit`/`sorry` in finished work.
8. Lower proof complexity by trimming unused hypotheses in extracted auxiliary lemmas.
9. Prefer proving the hard semantic direction first.
10. Be ready to implement missing encoder pieces for `union` and `inter` before attempting their proof.

## Suggested Order of Attack

Recommended order:

1. Finish `eq_case`
2. Implement and prove `union_case`
3. Implement and prove `inter_case`
4. Prove `app_case`
5. Prove `pfun_case`
6. Prove `collect_case`
7. Prove `lambda_case`
8. Prove `all_case`

Rationale:

- `eq_case` is already isolated and almost complete
- `union` and `inter` likely need encoder work, so surface those issues early
- `app` and `pfun` sit on top of loosening/cast infrastructure needed by the binder cases
- `collect`, `lambda`, and `all` are the deepest binder proofs and should be attacked after the cast machinery is stable

## Files You Should Read First

Start with these:

- `README.md`
- `Main.lean`
- `Encoder/Basic.lean`
- `Encoder/Encoder.lean`
- `Encoder/Loosening/Castable.lean`
- `Encoder/Loosening/Rules.lean`
- `Encoder/Loosening/Loosening.lean`
- `SMT/Reasoning/Defs.lean`
- `SMT/Reasoning/LooseningDefs.lean`
- `SMT/Reasoning/Basic/StateSpecs.lean`
- `SMT/Reasoning/Basic/LoosenAuxSpec.lean`
- `SMT/Reasoning/EncodeTermCorrect.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectArith.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectBool.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectSet.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectMem.lean`
- `SMT/Reasoning/Basic/EncodeTermCorrectEq.lean`

## Validation Policy

Prefer incremental verification:

1. Check the edited file with Lean/LSP after each local step.
2. Use file-level checks before any full build.
3. Keep proofs free of new `sorry` or `admit`.

Good local targets:

- `lake env lean SMT/Reasoning/Basic/EncodeTermCorrectEq.lean`
- `lake env lean SMT/Reasoning/EncodeTermCorrect.lean`

Use project-wide builds only after local file checks are green.

## Final Objective

Finish the BEer encoder correctness proof by removing the remaining admits/sorries at the end of `encodeTerm_spec`.

Success means:

- `encodeTerm_spec.eq_case` is complete
- the remaining 7 top-level `sorry` branches in `SMT/Reasoning/EncodeTermCorrect.lean` are replaced by proved case theorems
- if necessary, `castUnion` and `castInter` are implemented and proved correct enough for the final theorem
- no new axioms are introduced
- the active proof frontier for `encodeTerm_spec` is gone

## Short Version

You are finishing the BEer proof project. BEer certifies the translation from B proof obligations to SMT-LIB through a Lean formalization over ZF semantics. The main theorem is `encodeTerm_spec`. Almost all cases are done. The only remaining active frontier is the last 8 cases: `eq`, `union`, `inter`, `app`, `pfun`, `collect`, `lambda`, and `all`. Reuse the completed `encodeTerm_spec.*_case` proofs as templates, respect the existing monadic proof style, rely on `SMT/Reasoning/Defs.lean` and the loosening infrastructure, and be aware that `union` and `inter` are currently blocked by unfinished encoder helpers in `Encoder/Loosening/Loosening.lean`.
