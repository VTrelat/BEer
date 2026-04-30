import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.LoosenAuxSpec.Refl
import SMT.Reasoning.Basic.LoosenAuxSpec.Pair
import SMT.Reasoning.Basic.LoosenAuxSpec.Opt
import SMT.Reasoning.Basic.LoosenAuxSpec.Graph
import SMT.Reasoning.Basic.LoosenAuxSpec.Chpred
import SMT.Reasoning.Basic.LoosenAuxSpec.Fun

open Std.Do SMT ZFSet


open Classical

/--
Generic forall-commutation of `Triple` with arbitrary index `ι` for the encoder
monad `Encoder = StateT EncoderState (Except String)`. Useful to lift Δ-parametric
specifications into Δ-universal specifications by re-indexing the family.
-/
theorem Triple_forall_post_encoder.{u₁} {α : Type} {ι : Sort u₁} (x : Encoder α)
    (P : Assertion (.arg EncoderState (.except String .pure)))
    (Q : ι → α → Assertion (.arg EncoderState (.except String .pure)))
    (h : ∀ i, Triple x P (Q i, ExceptConds.true)) :
    Triple x P (fun a => SPred.«forall» (fun i => Q i a), ExceptConds.true) := by
  intro st pst
  show (((WP.wp x).apply _) st).down
  rw [show WP.wp x
        = PredTrans.pushArg (fun s => WP.wp (x s)) from rfl,
      PredTrans.pushArg_apply]
  beta_reduce
  have hi : ∀ i, ((WP.wp x).apply (Q i, ExceptConds.true) st).down :=
    fun i => h i st pst
  conv at hi =>
    intro i
    rw [show WP.wp x
          = PredTrans.pushArg (fun s => WP.wp (x s)) from rfl,
        PredTrans.pushArg_apply]
    beta_reduce
  -- Reduce wp on `Except String _` to a match on `x st`.
  have key : ∀ Q', ((WP.wp (x st)).apply Q').down = match x st with
              | .ok r => (Q'.1 r).down
              | .error e => (Q'.2.1 e).down := by
    intro Q'
    simp [WP.wp]
    cases x st <;> rfl
  rw [key]
  cases hxst : x st with
  | ok r =>
    show (∀ i, _)
    intro i
    have := hi i
    rw [key, hxst] at this
    exact this
  | error _ => trivial

-- set_option maxHeartbeats 1000000 in
@[spec]
theorem loosenAux_prf_spec
  {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} {name : String}
  {x : SMT.Term} {α β : SMTType}
  (typ_x : Λ ⊢ˢ x : α) (𝕔 : α ~> β)
  («Δ» : RenamingContext.Context)
  (hx  : RenamingContext.CoversFV «Δ» x) :
  ⦃ fun ⟨E, Λ'⟩ => ⌜ Λ' = Λ ∧ E.freshvarsc = n ∧ Λ'.keys ⊆ E.usedVars ∧ E.usedVars = used⌝ ⦄
    loosenAux_prf name 𝕔 x
  ⦃ ⇓? ⟨x!, x!_spec⟩ ⟨E', Γ'⟩ =>
     ⌜ n ≤ E'.freshvarsc ∧
       Λ.insert x! β ⊆ Γ' ∧ x! ∉ Λ ∧
       x! ∉ used ∧
       used ⊆ E'.usedVars ∧
       AList.keys Γ' ⊆ E'.usedVars ∧
       (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
       (Λ.insert x! β) ⊢ˢ (.var x!) : β ∧
       (Λ.insert x! β) ⊢ˢ x!_spec : .bool ∧
       Γ' ⊢ˢ (.var x!) : β ∧
       Γ' ⊢ˢ x!_spec : .bool ∧
       SMT.fv x!_spec ⊆ SMT.fv x ∪ {x!} ∧
       -- Denotation adequacy: x! denotes the forward cast of the denotation of x,
       -- and φ holds (is zftrue) in every admissible renaming.
        ∀ (X : SMT.Dom), ⟦x.abstract «Δ» hx⟧ˢ = some X →
          ∃ (Φ X! : SMT.Dom)
            (_ : ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!)) (fun v hv ↦ by
              rw [fv, List.mem_singleton] at hv
              rw [hv, Function.update_self, Option.isSome_some])⟧ˢ = some X!)
            (hφ : RenamingContext.CoversFV (Function.update «Δ» x! (some X!)) x!_spec)
            (_ : ⟦x!_spec.abstract (Function.update «Δ» x! (some X!)) hφ⟧ˢ = some Φ),
            (Φ.2.1 = SMTType.bool) ∧
            (Φ.1 = zftrue ∧ (X.1.pair X!.1) ∈ (castZF_of_path 𝕔).1) ∧
            (∀ (Y : SMT.Dom) (_ : Y.2.1 = β)
              (hφY : RenamingContext.CoversFV (Function.update «Δ» x! (some Y)) x!_spec),
              (⟦x!_spec.abstract (Function.update «Δ» x! (some Y)) hφY⟧ˢ).isSome = true) ⌝ ⦄ := by
  generalize_proofs pf
  revert «Δ» hx pf
  induction 𝕔 generalizing x Λ n used name with
    | @refl α hα =>
      intro «Δ» hx pf
      exact loosenAux_prf_spec.refl «Δ» hα typ_x hx pf
    | @pair α β α' β' pα pβ pα_ih pβ_ih =>
      intro «Δ» hx pf
      refine loosenAux_prf_spec.pair «Δ» pα pβ pf ?_ ?_ typ_x hx
      · exact fun a hx => pα_ih a «Δ» hx pf
      · exact fun a hx => pβ_ih a «Δ» hx pf
    | @opt α α' hα ih =>
      intro «Δ» hx pf
      exact loosenAux_prf_spec.opt «Δ» pf hα ih typ_x hx
    | @graph α β α' β' pα pβ pα_ih pβ_ih =>
      intro «Δ» hx pf
      exact loosenAux_prf_spec.graph «Δ» pf pα pβ pα_ih pβ_ih typ_x hx
    | @chpred α α' p ih =>
      intro «Δ» hx pf
      exact loosenAux_prf_spec.chpred «Δ» pf p ih typ_x hx
    | @«fun» α β α' β' hβ pα pβ pα_ih pβ_ih =>
      intro «Δ» hx pf
      exact loosenAux_prf_spec.fun «Δ» pf hβ pα pβ pα_ih pβ_ih typ_x hx

/--
Δ-universal version of `loosenAux_prf_spec`: the adequacy clause is universally
quantified over the renaming context `«Δ»`, the cover proof `hx`, and the proof
`pf` of `(Function.update Δ x! (some X!) v).isSome = true` for `v ∈ fv (.var x!)`.

This version is needed by downstream consumers (e.g.
`castMembership_spec` Branch 2) that need to reason at multiple `Δ`s
without re-running the encoder. Derived from `loosenAux_prf_spec` by direct
WP unfolding for the encoder monad.
-/
theorem loosenAux_prf_spec_univ
  {Λ : SMT.TypeContext} {n : ℕ} {used : List SMT.𝒱} {name : String}
  {x : SMT.Term} {α β : SMTType}
  (typ_x : Λ ⊢ˢ x : α) (𝕔 : α ~> β) :
  ⦃ fun ⟨E, Λ'⟩ => ⌜ Λ' = Λ ∧ E.freshvarsc = n ∧ Λ'.keys ⊆ E.usedVars ∧ E.usedVars = used⌝ ⦄
    loosenAux_prf name 𝕔 x
  ⦃ ⇓? ⟨x!, x!_spec⟩ ⟨E', Γ'⟩ =>
     ⌜ n ≤ E'.freshvarsc ∧
       Λ.insert x! β ⊆ Γ' ∧ x! ∉ Λ ∧
       x! ∉ used ∧
       used ⊆ E'.usedVars ∧
       AList.keys Γ' ⊆ E'.usedVars ∧
       (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
       (Λ.insert x! β) ⊢ˢ (.var x!) : β ∧
       (Λ.insert x! β) ⊢ˢ x!_spec : .bool ∧
       Γ' ⊢ˢ (.var x!) : β ∧
       Γ' ⊢ˢ x!_spec : .bool ∧
       SMT.fv x!_spec ⊆ SMT.fv x ∪ {x!} ∧
       -- Δ-universal denotation adequacy clause.
       ∀ («Δ» : RenamingContext.Context)
         (hx : RenamingContext.CoversFV «Δ» x)
         (pf : ∀ (x_! : SMT.𝒱) (X! : SMT.Dom),
           ∀ v ∈ SMT.fv (Term.var x_!),
             (Function.update «Δ» x_! (some X!) v).isSome = true),
       ∀ (X : SMT.Dom), ⟦x.abstract «Δ» hx⟧ˢ = some X →
         ∃ (Φ X! : SMT.Dom)
           (_ : ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!))
             (pf x! X!)⟧ˢ = some X!)
           (hφ : RenamingContext.CoversFV (Function.update «Δ» x! (some X!)) x!_spec)
           (_ : ⟦x!_spec.abstract (Function.update «Δ» x! (some X!)) hφ⟧ˢ = some Φ),
           (Φ.2.1 = SMTType.bool) ∧
           (Φ.1 = zftrue ∧ (X.1.pair X!.1) ∈ (castZF_of_path 𝕔).1) ∧
           (∀ (Y : SMT.Dom) (_ : Y.2.1 = β)
             (hφY : RenamingContext.CoversFV (Function.update «Δ» x! (some Y)) x!_spec),
             (⟦x!_spec.abstract (Function.update «Δ» x! (some Y)) hφY⟧ˢ).isSome = true) ⌝ ⦄ := by
  -- Strategy: directly unfold the Triple/wp definition for the concrete encoder
  -- monad and deduce the universal-Δ post pointwise from `loosenAux_prf_spec`.
  -- For `Encoder = StateT EncoderState (Except String)`, `wp⟦x⟧ Q st` reduces
  -- to a match on `x.run st`, and the post is `SPred.pure (...)` (flat ULift Prop).
  intro st pst
  -- Reduce both the goal and the per-Δ instances of `loosenAux_prf_spec` to a
  -- match on `loosenAux_prf name 𝕔 x st : Except _ _`.
  have key : ∀ (Q' : PostCond _ (.arg EncoderState (.except String .pure))),
      (wp⟦loosenAux_prf name 𝕔 x⟧ Q' st).down =
        match (loosenAux_prf name 𝕔 x st : Except _ _) with
        | .ok r => (Q'.1 r.1 r.2).down
        | .error e => (Q'.2.1 e).down := by
    intro Q'
    simp [WP.wp]
    cases (loosenAux_prf name 𝕔 x st : Except _ _) <;> rfl
  -- The Δ-instances of loosenAux_prf_spec.
  have hi : ∀ («Δ» : RenamingContext.Context)
              (hx : RenamingContext.CoversFV «Δ» x),
              (wp⟦loosenAux_prf name 𝕔 x⟧
                (PostCond.mayThrow fun ⟨x_!, x_!_spec⟩ ⟨E', Γ'⟩ =>
                  ⌜n ≤ E'.freshvarsc ∧
                   Λ.insert x_! β ⊆ Γ' ∧ x_! ∉ Λ ∧
                   x_! ∉ used ∧
                   used ⊆ E'.usedVars ∧
                   AList.keys Γ' ⊆ E'.usedVars ∧
                   (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
                   (Λ.insert x_! β) ⊢ˢ (.var x_!) : β ∧
                   (Λ.insert x_! β) ⊢ˢ x_!_spec : .bool ∧
                   Γ' ⊢ˢ (.var x_!) : β ∧
                   Γ' ⊢ˢ x_!_spec : .bool ∧
                   SMT.fv x_!_spec ⊆ SMT.fv x ∪ {x_!} ∧
                   ∀ (X : SMT.Dom), ⟦x.abstract «Δ» hx⟧ˢ = some X →
                     ∃ (Φ X! : SMT.Dom)
                       (_ : ⟦(Term.var x_!).abstract (Function.update «Δ» x_! (some X!)) (fun v hv ↦ by
                         rw [fv, List.mem_singleton] at hv
                         rw [hv, Function.update_self, Option.isSome_some])⟧ˢ = some X!)
                       (hφ : RenamingContext.CoversFV (Function.update «Δ» x_! (some X!)) x_!_spec)
                       (_ : ⟦x_!_spec.abstract (Function.update «Δ» x_! (some X!)) hφ⟧ˢ = some Φ),
                       (Φ.2.1 = SMTType.bool) ∧
                       (Φ.1 = zftrue ∧ (X.1.pair X!.1) ∈ (castZF_of_path 𝕔).1) ∧
                       (∀ (Y : SMT.Dom) (_ : Y.2.1 = β)
                         (hφY : RenamingContext.CoversFV (Function.update «Δ» x_! (some Y)) x_!_spec),
                         (⟦x_!_spec.abstract (Function.update «Δ» x_! (some Y)) hφY⟧ˢ).isSome = true)⌝)
                st).down :=
    fun «Δ» hx => loosenAux_prf_spec (Λ := Λ) (n := n) (used := used) (name := name)
      typ_x 𝕔 «Δ» hx st pst
  -- Reduce hi via key.
  conv at hi => intro «Δ» hx; rw [key]
  -- Reduce the Goal via key.
  show (wp⟦loosenAux_prf name 𝕔 x⟧ _ st).down
  rw [key]
  -- Case-split on the program result.
  cases hxst : (loosenAux_prf name 𝕔 x st : Except _ _) with
  | ok r =>
    obtain ⟨⟨x!, x!_spec⟩, ⟨E', Γ'⟩⟩ := r
    -- Use a dummy Δ to obtain the structural facts.
    let Δdummy : RenamingContext.Context :=
      (fun _ => some ⟨ZFSet.zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩)
    have hcov_dummy : RenamingContext.CoversFV Δdummy x := by
      intro v hv
      show (some _).isSome = true
      simp
    have hd := hi Δdummy hcov_dummy
    rw [hxst] at hd
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, _⟩ := hd
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ?_⟩
    -- Δ-universal adequacy.
    intro «Δ» hx pf X hX_den
    have hΔ := hi «Δ» hx
    rw [hxst] at hΔ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hadq⟩ := hΔ
    obtain ⟨Φ, X!, h_var, hφ, h_spec, h_typeΦ, h_castmem, htotalY⟩ := hadq X hX_den
    refine ⟨Φ, X!, ?_, hφ, h_spec, h_typeΦ, h_castmem, htotalY⟩
    -- The variable abstract uses the inline pf; convert via proof irrelevance.
    convert h_var
  | error _ => trivial
