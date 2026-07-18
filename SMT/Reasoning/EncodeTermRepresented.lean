import SMT.Reasoning.Basic.EncodeTermRepresentedAll
import SMT.Reasoning.Basic.EncodeTermRepresentedCollectRaw
import SMT.Reasoning.Basic.EncodeTermRepresentedLambdaRaw
import SMT.Reasoning.Basic.EncodeTermRepresentedPFun

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

/-- The root declaration-aware theorem specializes to the Boolean root
contract consumed by collection bodies. -/
theorem EncodeTermRepScopedIH.to_bool.{u}
    {t : B.Term} (h : EncodeTermRepScopedIH.{u} t) :
    EncodeTermRepScopedBoolIH.{u} t := by
  intro E Lambda typ_t Xi Xi_fv Theta0 related used Theta0_none
    Theta0_dom T hT den_t vars_used Lambda_inv bv_nodup respects
    fv_in_Lambda wf n decl
  exact h E typ_t Xi_fv related Theta0_none Theta0_dom den_t
    vars_used Lambda_inv bv_nodup respects fv_in_Lambda wf
    (n := n) (decl := decl)

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

/-- Assemble the ordinary representation-aware theorem by structural
recursion, assuming the independently recursive declaration-aware contract.
This separation keeps semantic representation reasoning out of the generated
helper scoping induction. -/
theorem encodeTerm_rep_spec.of_scoped.{u}
    (binder_admissible : EncodeTermAllBinderAdmissible.{u})
    (scoped_ih : ∀ t : B.Term, EncodeTermRepScopedFromIH.{u} t)
    (t : B.Term) (wd_t : B.Term.WellDefined.{u} t) :
    EncodeTermRepIH.{u} t := by
  induction t with
  | var v => exact encodeTerm_rep_spec.var_case v
  | int i => exact encodeTerm_rep_spec.int_case i
  | bool b => exact encodeTerm_rep_spec.bool_case b
  | maplet x y x_ih y_ih =>
      exact encodeTerm_rep_spec.maplet_case x y
        (x_ih wd_t.1) (y_ih wd_t.2)
  | add x y x_ih y_ih =>
      exact encodeTerm_rep_spec.checked_int_case
        .add x y (x_ih wd_t.1) (y_ih wd_t.2)
  | sub x y x_ih y_ih =>
      exact encodeTerm_rep_spec.checked_int_case
        .sub x y (x_ih wd_t.1) (y_ih wd_t.2)
  | mul x y x_ih y_ih =>
      exact encodeTerm_rep_spec.checked_int_case
        .mul x y (x_ih wd_t.1) (y_ih wd_t.2)
  | le x y x_ih y_ih =>
      exact encodeTerm_rep_spec.le_case x y
        (x_ih wd_t.1) (y_ih wd_t.2)
  | and x y x_ih y_ih =>
      exact encodeTerm_rep_spec.checked_bool_case
        .and x y (x_ih wd_t.1) (y_ih wd_t.2)
  | not x x_ih =>
      exact encodeTerm_rep_spec.not_case x (x_ih wd_t)
  | eq x y x_ih y_ih =>
      exact encodeTerm_rep_spec.eq_case x y
        (x_ih wd_t.1) (y_ih wd_t.2)
  | «ℤ» => exact encodeTerm_rep_spec.ℤ_case
  | 𝔹 => exact encodeTerm_rep_spec.𝔹_case
  | mem x S x_ih S_ih =>
      exact encodeTerm_rep_spec.mem_case x S
        (x_ih wd_t.1) (S_ih wd_t.2)
  | collect vs D P D_ih P_ih =>
      exact encodeTerm_rep_spec.collect_case vs D P
        (D_ih wd_t.1) (P_ih wd_t.2)
        ((scoped_ih P).to_root.to_bool)
  | pow S S_ih =>
      exact encodeTerm_rep_spec.pow_case S (S_ih wd_t)
  | cprod S T S_ih T_ih =>
      exact encodeTerm_rep_spec.cprod_case S T
        (S_ih wd_t.1) (T_ih wd_t.2)
  | union S T S_ih T_ih =>
      exact encodeTerm_rep_spec.union_case S T
        (S_ih wd_t.1) (T_ih wd_t.2)
  | inter S T S_ih T_ih =>
      exact encodeTerm_rep_spec.inter_case S T
        (S_ih wd_t.1) (T_ih wd_t.2)
  | card S S_ih =>
      exact encodeTerm_rep_spec.card_case S (S_ih wd_t.1)
  | app f x f_ih x_ih =>
      exact encodeTerm_rep_spec.app_case f x
        (f_ih wd_t.1) (x_ih wd_t.2.1)
  | lambda vs D P D_ih P_ih =>
      exact encodeTerm_rep_spec.lambda_case vs D P
        (D_ih wd_t.1) (P_ih wd_t.2) (scoped_ih P).to_root
  | pfun A B A_ih B_ih =>
      exact encodeTerm_rep_spec.pfun_case A B
        (A_ih wd_t.1) (B_ih wd_t.2)
  | min S S_ih =>
      exact encodeTerm_rep_spec.min_case S (S_ih wd_t.1)
  | max S S_ih =>
      exact encodeTerm_rep_spec.max_case S (S_ih wd_t.1)
  | all vs D P D_ih P_ih =>
      exact encodeTerm_rep_spec.all_case vs D P
        (D_ih wd_t.1) (P_ih wd_t.2) (scoped_ih P).to_bool
        binder_admissible wd_t.2
