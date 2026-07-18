import SMT.Reasoning.Basic.EncodeTermRepresentedAll

open Std.Do B SMT ZFSet

/-!
# Representation-aware soundness for `encodeTerm`

This file assembles the constructor proofs into the public recursive theorem.
The small adapters below keep the recursion independent of a particular local
binder prefix: constructor proofs may establish the operational root contract,
while binder clients receive the clean-prefix contract.
-/

/-- A clean-prefix induction hypothesis contains its root instance. -/
theorem EncodeTermRepScopedFromIH.to_root.{u}
    {t : B.Term} (h : EncodeTermRepScopedFromIH.{u} t) :
    EncodeTermRepScopedIH.{u} t := by
  intro E Lambda alpha typ_t Xi Xi_fv Theta0 related used
    Theta0_none Theta0_dom T hT den_t vars_used Lambda_inv bv_nodup
    respects fv_in_Lambda wf n decl
  exact h E typ_t Xi_fv related Theta0_none Theta0_dom den_t vars_used
    Lambda_inv bv_nodup respects fv_in_Lambda wf
    (DeclarationContextEnvelope.refl Lambda) fv_in_Lambda
    (ScopedSpecsTyping.nil Lambda) (n := n) (decl := decl)

/-- The generic clean-prefix companion specializes to the Boolean companion
needed by quantified and collection bodies. -/
theorem EncodeTermRepScopedFromIH.to_bool.{u}
    {t : B.Term} (h : EncodeTermRepScopedFromIH.{u} t) :
    EncodeTermRepScopedBoolFromIH.{u} t := by
  intro E Lambda typ_t Xi Xi_fv Theta0 related used Theta0_none
    Theta0_dom T hT den_t vars_used Lambda_inv bv_nodup respects
    fv_in_Lambda wf Base Dpre input_envelope fv_in_Base Dpre_typing
    n decl
  exact h E typ_t Xi_fv related Theta0_none Theta0_dom den_t vars_used
    Lambda_inv bv_nodup respects fv_in_Lambda wf input_envelope
    fv_in_Base Dpre_typing (n := n) (decl := decl)

/-- Combine an ordinary semantic theorem, its operational scoped root theorem,
and the representation-independent declaration bound.  The result can be
replayed beneath any clean declaration prefix. -/
theorem EncodeTermRepScopedIH.to_from.{u}
    {t : B.Term}
    (ordinary : EncodeTermRepIH.{u} t)
    (root : EncodeTermRepScopedIH.{u} t) :
    EncodeTermRepScopedFromIH.{u} t := by
  intro E Lambda alpha typ_t Xi Xi_fv Theta0 related used
    Theta0_none Theta0_dom T hT den_t vars_used Lambda_inv bv_nodup
    respects fv_in_Lambda wf Base Dpre input_envelope fv_in_Base
    Dpre_typing n decl
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_keys, rfl, rfl⟩ := pre
  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (ordinary E typ_t Xi_fv related Theta0_none Theta0_dom den_t
        vars_used Lambda_inv bv_nodup respects fv_in_Lambda wf
        (n := St.env.freshvarsc))
      (root E typ_t Xi_fv related Theta0_none Theta0_dom den_t
        vars_used Lambda_inv bv_nodup respects fv_in_Lambda wf
        (n := St.env.freshvarsc) (decl := St.env.declarations)))
    (encodeTerm_decl E typ_t vars_used Lambda_inv bv_nodup
      (n := St.env.freshvarsc) (decl := St.env.declarations)))
  rename_i out
  obtain ⟨t', sigma⟩ := out
  mrename_i post
  mintro ∀St'
  mpure post
  obtain ⟨⟨ordinary_post, root_post⟩, decl_info⟩ := post
  obtain ⟨_, _, _, _, _, typ_t', _, _, _⟩ := ordinary_post
  mpure_intro
  exact EncodeTermRepScopedPostFrom.of_root typ_t Lambda_inv
    input_envelope fv_in_Base Dpre_typing typ_t' decl_info root_post
