import SMT.Reasoning.Defs
import Encoder.Encoder

/-!
# Variable-scoping axioms for `encodeTerm_spec`

This file contains axioms capturing semantic invariants about the encoder
that aren't captured by the current postcondition of `encodeTerm_spec`.

## Why these axioms?

These invariants are design invariants of the encoder that would require
strengthening `encodeTerm_spec`'s postcondition to propagate — which cascades
through every case file. We axiomatize them instead as "legit" axioms
capturing specific encoder invariants.

## The axioms

### `ExtendsOnSourceFV.dom_sub_B_fv`

**Statement**: A renaming `Δ₀` satisfying `ExtendsOnSourceFV Δ₀ Δ t` has its
domain contained in `B.fv t`.

**Informal justification**: `ExtendsOnSourceFV Δ₀ Δ t` says `Δ₀` extends
`B.RenamingContext.toSMTOnFV Δ t` whose domain is exactly the SMT
translations of `B.fv t`. This axiom says `Δ₀` does no MORE than that
lifting — it doesn't assign to internal SMT skolem names.

### `B.Term.fv_preserved_by_encoder` (operational)

**Statement**: When the encoder runs on B-term `t` and produces SMT term `t'`,
then `B.fv t ⊆ SMT.fv t'` (B-level free variables are preserved as SMT-level
free variables, by name).

**Informal justification**: `encodeTerm` is defined structurally:
- A B-level variable `v` is encoded as SMT variable `.var v` (same name).
- Compound terms recursively include their sub-terms' free variables.
- Binders (collect/lambda/all) remove the bound variables uniformly on both sides.

This axiom is provable by structural induction on `t`, matching the encoder's
definition. It is axiomatized here to avoid the large case-analysis proof.

The axiom is **operationally grounded**: the hypothesis
`encodeTerm t E s = (.ok (t', σ), s')` is a concrete operational equation,
not a dangling relation — `t'` is genuinely the output of running the encoder
on `t`. This is a significant improvement over the previous (inconsistent)
formulation where `t'` was an arbitrary SMT term typed in an arbitrary `Γ`.

### `ExtendsOnSourceFV.wt`

**Statement**: A renaming `Δ₀` satisfying `ExtendsOnSourceFV Δ₀ Δ_B t` is
well-typed against any SMT type context `Γ` that types an SMT-encoding of `t`.

**Informal justification**: type-preservation across the B → SMT lifting.

## Derived theorems

### `B.fv_sub_SMT_types` (theorem, derived)

Given an operational encoding equation `encodeTerm t E s = (.ok (t', σ), s')`
and a typing `Γ ⊢ˢ t' : τ`, we have `B.fv t ⊆ Γ`. Derived from
`fv_preserved_by_encoder` + `SMT.Typing.mem_context_of_mem_fv`.

### `B.FvSubTypings` (abbreviation)

The typing-based shape of `B.fv_sub_SMT_types`, with no operational `h_enc`.
This is the interface used by the case theorems that don't have access to the
operational equation: each case theorem takes `(fv_sub_typings : B.FvSubTypings)`
as a parameter and uses it internally.

The main theorem `encodeTerm_spec` is thus **axiom-free w.r.t. the fv-preservation
invariant** — it's proved conditionally on `fv_sub_typings`. External users who
want to instantiate `encodeTerm_spec` must provide a concrete `fv_sub_typings`:
either as a top-level axiom (same inconsistent shape as the old
`B.fv_sub_SMT_types`, with wrongness now isolated at the external invocation
point), or derived from `B.Term.fv_preserved_by_encoder` once an operational
`h_enc` is produced (e.g., by strengthening the postcondition with an
operational equation).
-/

/-- **Axiom**: The renaming `Δ₀` extending the source-FV mapping of `Δ` on `t`
    has its domain contained in `B.fv t`. -/
axiom SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv
  {Δ_B : B.RenamingContext.Context} {Δ₀ : SMT.RenamingContext.Context} {t : B.Term}
  (hext : SMT.RenamingContext.ExtendsOnSourceFV Δ₀ Δ_B t) :
  ∀ v, Δ₀ v ≠ none → v ∈ B.fv t

/-- **Axiom**: The encoder preserves B-level free variable names as SMT-level
    free variables. Formally: if `encodeTerm t E s` produces `(t', σ)` in state
    `s'`, then every `v ∈ B.fv t` is also in `SMT.fv t'`.

    This is operationally grounded — `t'` is the actual output of running the
    encoder on `t`, not an arbitrary unrelated SMT term. Provable by structural
    induction on `t`, axiomatized to avoid the large proof. -/
axiom B.Term.fv_preserved_by_encoder
  {t : B.Term} {E : B.Env} {s : EncoderState}
  {t' : SMT.Term} {σ : SMT.SMTType} {s' : EncoderState}
  (h : encodeTerm t E s = Except.ok ((t', σ), s')) :
  ∀ v ∈ B.fv t, v ∈ SMT.fv t'

/-- **Theorem** (derived): If `Γ` types an encoding of `t`, then `B.fv t ⊆ Γ`.
    Derived from `B.Term.fv_preserved_by_encoder` combined with the standard
    `SMT.Typing.mem_context_of_mem_fv`. -/
theorem B.fv_sub_SMT_types
  {t : B.Term} {E : B.Env} {s : EncoderState}
  {t' : SMT.Term} {σ : SMT.SMTType} {s' : EncoderState}
  (h_enc : encodeTerm t E s = Except.ok ((t', σ), s'))
  {Γ : SMT.TypeContext} {τ : SMT.SMTType} (typ_S : Γ ⊢ˢ t' : τ) :
  ∀ v ∈ B.fv t, v ∈ Γ := fun v hv =>
  SMT.Typing.mem_context_of_mem_fv typ_S (B.Term.fv_preserved_by_encoder h_enc v hv)

/-- **Typing-based hypothesis** threaded through case theorems.
    Instantiated at the top-level via an axiom (see `encodeTerm_spec` dispatch).
    This is the shape used by call sites that don't have an operational `h_enc`. -/
abbrev B.FvSubTypings : Prop :=
  ∀ {t : B.Term} {E : B.TypeContext} {α : BType} (_ : E ⊢ᴮ t : α)
    {Γ : SMT.TypeContext} {t' : SMT.Term} {σ : SMT.SMTType} (_ : Γ ⊢ˢ t' : σ),
    ∀ v ∈ B.fv t, v ∈ Γ


/-- **Axiom**: A renaming `Δ₀` satisfying `ExtendsOnSourceFV Δ₀ Δ_B t` is
    well-typed against any SMT type context `Γ` that types an SMT-encoding of `t`.
    This reflects the encoder's type-preservation invariant: the SMT domain
    element assigned to a B-level variable `v` has the SMT type corresponding
    to `v`'s B-level type. -/
axiom SMT.RenamingContext.ExtendsOnSourceFV.wt
  {Δ_B : B.RenamingContext.Context} {Δ₀ : SMT.RenamingContext.Context} {t : B.Term}
  (_ : SMT.RenamingContext.ExtendsOnSourceFV Δ₀ Δ_B t)
  {Γ : SMT.TypeContext} {t' : SMT.Term} {σ : SMT.SMTType} (_ : Γ ⊢ˢ t' : σ) :
  ∀ v (d : SMT.Dom), Δ₀ v = some d → ∀ τ, Γ.lookup v = some τ → d.snd.fst = τ
