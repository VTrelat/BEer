import SMT.Reasoning.Basic.EncodeTermRepresentedAll
import SMT.Reasoning.Basic.EncodeTermRepresentedCollectRaw
import SMT.Reasoning.Basic.EncodeTermRepresentedLambdaRaw
import SMT.Reasoning.Basic.EncodeTermRepresentedPFun
import SMT.Reasoning.Basic.EncodeTermRepresentedScopedArith
import SMT.Reasoning.Basic.EncodeTermRepresentedScopedInter
import SMT.Reasoning.Basic.EncodeTermRepresentedScopedLe
import SMT.Reasoning.Basic.EncodeTermRepresentedScopedMem
import SMT.Reasoning.Basic.EncodeTermRepresentedScopedSet
import SMT.Reasoning.Basic.EncodeTermRepresentedScopedUnion
import SMT.Reasoning.Basic.EncodeTermRepresentedScopedUnsupported

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

/-- A Boolean clean-prefix contract is a generic clean-prefix contract when
typing forces every occurrence of the term to have Boolean result type. -/
theorem EncodeTermRepScopedBoolFromIH.to_from_of_result_type.{u}
    {t : B.Term} (h : EncodeTermRepScopedBoolFromIH.{u} t)
    (result_type : ∀ {Gamma : B.TypeContext} {alpha : BType},
      Gamma ⊢ᴮ t : alpha → alpha = BType.bool) :
    EncodeTermRepScopedFromIH.{u} t := by
  intro E Lambda alpha typ_t Xi Xi_fv Theta0 related used
    Theta0_none Theta0_dom T hT den_t vars_used Lambda_inv bv_nodup
    respects fv_in_Lambda wf Base Dpre input_envelope fv_in_Base
    Dpre_typing n decl
  have alpha_eq : alpha = BType.bool := result_type typ_t
  subst alpha
  exact h E typ_t Xi_fv related Theta0_none Theta0_dom den_t vars_used
    Lambda_inv bv_nodup respects fv_in_Lambda wf input_envelope
    fv_in_Base Dpre_typing (n := n) (decl := decl)

/-- General-result wrapper for checked integer operations.  Their constructor
proof is stated at `int`; source typing inversion supplies that equality for
the generic clean-prefix recursion. -/
theorem encodeTerm_rep_scoped.checked_int_case_from_general.{u}
    (op : EncodeTermRepresentedArith.CheckedOp)
    (x y : B.Term)
    (x_ih : EncodeTermRepIH.{u} x)
    (y_ih : EncodeTermRepIH.{u} y)
    (x_scoped : EncodeTermRepScopedFromIH.{u} x)
    (y_scoped : EncodeTermRepScopedFromIH.{u} y) :
    EncodeTermRepScopedFromIH.{u} (op.term x y) := by
  intro E Lambda alpha typ_t Xi Xi_fv Theta0 related used
    Theta0_none Theta0_dom T hT den_t vars_used Lambda_inv bv_nodup
    respects fv_in_Lambda wf Base Dpre input_envelope fv_in_Base
    Dpre_typing n decl
  have alpha_eq : alpha = BType.int := (op.typingE typ_t).1
  subst alpha
  exact encodeTerm_rep_scoped.checked_int_case_from op x y x_ih y_ih
    x_scoped y_scoped E typ_t Xi_fv related Theta0_none Theta0_dom den_t
    vars_used Lambda_inv bv_nodup respects fv_in_Lambda wf input_envelope
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
        ((scoped_ih D).to_root)
        ((scoped_ih P).to_bool)
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
        (D_ih wd_t.1) (P_ih wd_t.2)
        (scoped_ih D).to_root (scoped_ih P)
  | pfun A B A_ih B_ih =>
      exact encodeTerm_rep_spec.pfun_case A B
        (A_ih wd_t.1) (B_ih wd_t.2)
  | min S S_ih =>
      exact encodeTerm_rep_spec.min_case S (S_ih wd_t.1)
  | max S S_ih =>
      exact encodeTerm_rep_spec.max_case S (S_ih wd_t.1)
  | all vs D P D_ih P_ih =>
      exact encodeTerm_rep_spec.all_case vs D P
        (D_ih wd_t.1) (scoped_ih D).to_root (P_ih wd_t.2)
        (scoped_ih P).to_bool binder_admissible wd_t.2

/-- Simultaneously assemble ordinary representation soundness and its
clean-prefix declaration-aware companion.  The paired induction avoids a
global circular hypothesis: every constructor receives both contracts for
its strict subterms, and binder roots are replayed beneath arbitrary clean
prefixes only after their ordinary result has been established. -/
private theorem encodeTerm_rep_spec_and_scoped.{u}
    (binder_admissible : EncodeTermAllBinderAdmissible.{u})
    (t : B.Term) (wd_t : B.Term.WellDefined.{u} t) :
    EncodeTermRepIH.{u} t ∧ EncodeTermRepScopedFromIH.{u} t := by
  induction t with
  | var v =>
      exact ⟨encodeTerm_rep_spec.var_case v,
        encodeTerm_rep_scoped.var_case_from v⟩
  | int i =>
      exact ⟨encodeTerm_rep_spec.int_case i,
        encodeTerm_rep_scoped.int_case_from i⟩
  | bool b =>
      exact ⟨encodeTerm_rep_spec.bool_case b,
        encodeTerm_rep_scoped.bool_case_from b⟩
  | maplet x y x_ih y_ih =>
      obtain ⟨x_ordinary, x_scoped⟩ := x_ih wd_t.1
      obtain ⟨y_ordinary, y_scoped⟩ := y_ih wd_t.2
      exact ⟨encodeTerm_rep_spec.maplet_case x y x_ordinary y_ordinary,
        encodeTerm_rep_scoped.maplet_case_from x y x_ordinary y_ordinary
          x_scoped y_scoped⟩
  | add x y x_ih y_ih =>
      obtain ⟨x_ordinary, x_scoped⟩ := x_ih wd_t.1
      obtain ⟨y_ordinary, y_scoped⟩ := y_ih wd_t.2
      refine ⟨encodeTerm_rep_spec.checked_int_case
          .add x y x_ordinary y_ordinary, ?_⟩
      simpa only [EncodeTermRepresentedArith.CheckedOp.term] using
        encodeTerm_rep_scoped.checked_int_case_from_general
          .add x y x_ordinary y_ordinary x_scoped y_scoped
  | sub x y x_ih y_ih =>
      obtain ⟨x_ordinary, x_scoped⟩ := x_ih wd_t.1
      obtain ⟨y_ordinary, y_scoped⟩ := y_ih wd_t.2
      refine ⟨encodeTerm_rep_spec.checked_int_case
          .sub x y x_ordinary y_ordinary, ?_⟩
      simpa only [EncodeTermRepresentedArith.CheckedOp.term] using
        encodeTerm_rep_scoped.checked_int_case_from_general
          .sub x y x_ordinary y_ordinary x_scoped y_scoped
  | mul x y x_ih y_ih =>
      obtain ⟨x_ordinary, x_scoped⟩ := x_ih wd_t.1
      obtain ⟨y_ordinary, y_scoped⟩ := y_ih wd_t.2
      refine ⟨encodeTerm_rep_spec.checked_int_case
          .mul x y x_ordinary y_ordinary, ?_⟩
      simpa only [EncodeTermRepresentedArith.CheckedOp.term] using
        encodeTerm_rep_scoped.checked_int_case_from_general
          .mul x y x_ordinary y_ordinary x_scoped y_scoped
  | le x y x_ih y_ih =>
      obtain ⟨x_ordinary, x_scoped⟩ := x_ih wd_t.1
      obtain ⟨y_ordinary, y_scoped⟩ := y_ih wd_t.2
      exact ⟨encodeTerm_rep_spec.le_case x y x_ordinary y_ordinary,
        encodeTerm_rep_scoped.le_case_from x y x_ordinary y_ordinary
          x_scoped y_scoped⟩
  | and x y x_ih y_ih =>
      obtain ⟨x_ordinary, x_scoped⟩ := x_ih wd_t.1
      obtain ⟨y_ordinary, y_scoped⟩ := y_ih wd_t.2
      refine ⟨encodeTerm_rep_spec.checked_bool_case
          .and x y x_ordinary y_ordinary, ?_⟩
      apply EncodeTermRepScopedBoolFromIH.to_from_of_result_type
      · simpa only [EncodeTermRepresentedBool.CheckedOp.term] using
          encodeTerm_rep_scoped.checked_bool_case_from
            .and x y x_ordinary y_ordinary x_scoped.to_bool y_scoped.to_bool
      · intro Gamma alpha typ_t
        simpa only [EncodeTermRepresentedBool.CheckedOp.term] using
          (EncodeTermRepresentedBool.CheckedOp.typingE (op := .and) typ_t).1
  | not x x_ih =>
      obtain ⟨x_ordinary, x_scoped⟩ := x_ih wd_t
      refine ⟨encodeTerm_rep_spec.not_case x x_ordinary, ?_⟩
      apply EncodeTermRepScopedBoolFromIH.to_from_of_result_type
      · exact encodeTerm_rep_scoped.not_case_from x x_ordinary
          x_scoped.to_bool
      · intro Gamma alpha typ_t
        exact (B.Typing.notE typ_t).1
  | eq x y x_ih y_ih =>
      obtain ⟨x_ordinary, x_scoped⟩ := x_ih wd_t.1
      obtain ⟨y_ordinary, y_scoped⟩ := y_ih wd_t.2
      refine ⟨encodeTerm_rep_spec.eq_case x y x_ordinary y_ordinary, ?_⟩
      apply EncodeTermRepScopedBoolFromIH.to_from_of_result_type
      · exact encodeTerm_rep_scoped.eq_case_from x y x_ordinary y_ordinary
          x_scoped y_scoped
      · intro Gamma alpha typ_t
        exact (B.Typing.eqE typ_t).1
  | «ℤ» =>
      exact ⟨encodeTerm_rep_spec.ℤ_case,
        encodeTerm_rep_scoped.ℤ_case_from⟩
  | 𝔹 =>
      exact ⟨encodeTerm_rep_spec.𝔹_case,
        encodeTerm_rep_scoped.𝔹_case_from⟩
  | mem x S x_ih S_ih =>
      obtain ⟨x_ordinary, x_scoped⟩ := x_ih wd_t.1
      obtain ⟨S_ordinary, S_scoped⟩ := S_ih wd_t.2
      refine ⟨encodeTerm_rep_spec.mem_case x S x_ordinary S_ordinary, ?_⟩
      apply EncodeTermRepScopedBoolFromIH.to_from_of_result_type
      · exact encodeTerm_rep_scoped.mem_case_from x S x_ordinary S_ordinary
          x_scoped S_scoped
      · intro Gamma alpha typ_t
        exact (B.Typing.memE typ_t).1
  | collect vs D P D_ih P_ih =>
      obtain ⟨D_ordinary, D_scoped⟩ := D_ih wd_t.1
      obtain ⟨P_ordinary, P_scoped⟩ := P_ih wd_t.2
      let ordinary := encodeTerm_rep_spec.collect_case vs D P
        D_ordinary P_ordinary D_scoped.to_root P_scoped.to_bool
      let root := encodeTerm_rep_scoped.collect_case vs D P
        D_ordinary P_ordinary D_scoped.to_root P_scoped.to_bool
      exact ⟨ordinary, EncodeTermRepScopedIH.to_from ordinary root⟩
  | pow S S_ih =>
      obtain ⟨S_ordinary, S_scoped⟩ := S_ih wd_t
      exact ⟨encodeTerm_rep_spec.pow_case S S_ordinary,
        EncodeTermRepresentedScopedSet.encodeTerm_rep_scoped.pow_case_from
          S S_ordinary S_scoped⟩
  | cprod S T S_ih T_ih =>
      obtain ⟨S_ordinary, S_scoped⟩ := S_ih wd_t.1
      obtain ⟨T_ordinary, T_scoped⟩ := T_ih wd_t.2
      exact ⟨encodeTerm_rep_spec.cprod_case S T S_ordinary T_ordinary,
        encodeTerm_rep_scoped.cprod_case_from S T S_ordinary T_ordinary
          S_scoped T_scoped⟩
  | union S T S_ih T_ih =>
      obtain ⟨S_ordinary, S_scoped⟩ := S_ih wd_t.1
      obtain ⟨T_ordinary, T_scoped⟩ := T_ih wd_t.2
      exact ⟨encodeTerm_rep_spec.union_case S T S_ordinary T_ordinary,
        EncodeTermRepresentedScopedUnion.encodeTerm_rep_scoped.union_case_from
          S T S_ordinary T_ordinary S_scoped T_scoped⟩
  | inter S T S_ih T_ih =>
      obtain ⟨S_ordinary, S_scoped⟩ := S_ih wd_t.1
      obtain ⟨T_ordinary, T_scoped⟩ := T_ih wd_t.2
      exact ⟨encodeTerm_rep_spec.inter_case S T S_ordinary T_ordinary,
        EncodeTermRepresentedScopedInter.encodeTerm_rep_scoped.inter_case_from
          S T S_ordinary T_ordinary S_scoped T_scoped⟩
  | card S S_ih =>
      obtain ⟨S_ordinary, S_scoped⟩ := S_ih wd_t.1
      exact ⟨encodeTerm_rep_spec.card_case S S_ordinary,
        encodeTerm_rep_scoped.card_case_from S S_ordinary S_scoped⟩
  | app f x f_ih x_ih =>
      obtain ⟨f_ordinary, f_scoped⟩ := f_ih wd_t.1
      obtain ⟨x_ordinary, x_scoped⟩ := x_ih wd_t.2.1
      exact ⟨encodeTerm_rep_spec.app_case f x f_ordinary x_ordinary,
        encodeTerm_rep_scoped.app_case_from f x f_ordinary x_ordinary
          f_scoped x_scoped⟩
  | lambda vs D P D_ih P_ih =>
      obtain ⟨D_ordinary, D_scoped⟩ := D_ih wd_t.1
      obtain ⟨P_ordinary, P_scoped⟩ := P_ih wd_t.2
      let ordinary := encodeTerm_rep_spec.lambda_case vs D P
        D_ordinary P_ordinary D_scoped.to_root P_scoped
      let root := encodeTerm_rep_scoped.lambda_case vs D P
        D_ordinary P_ordinary D_scoped.to_root P_scoped
      exact ⟨ordinary, EncodeTermRepScopedIH.to_from ordinary root⟩
  | pfun A B A_ih B_ih =>
      obtain ⟨A_ordinary, A_scoped⟩ := A_ih wd_t.1
      obtain ⟨B_ordinary, B_scoped⟩ := B_ih wd_t.2
      exact ⟨encodeTerm_rep_spec.pfun_case A B A_ordinary B_ordinary,
        encodeTerm_rep_scoped.pfun_case_from A B A_ordinary B_ordinary
          A_scoped B_scoped⟩
  | min S S_ih =>
      obtain ⟨S_ordinary, S_scoped⟩ := S_ih wd_t.1
      exact ⟨encodeTerm_rep_spec.min_case S S_ordinary,
        encodeTerm_rep_scoped.min_case_from S S_ordinary S_scoped⟩
  | max S S_ih =>
      obtain ⟨S_ordinary, S_scoped⟩ := S_ih wd_t.1
      exact ⟨encodeTerm_rep_spec.max_case S S_ordinary,
        encodeTerm_rep_scoped.max_case_from S S_ordinary S_scoped⟩
  | all vs D P D_ih P_ih =>
      obtain ⟨D_ordinary, D_scoped⟩ := D_ih wd_t.1
      obtain ⟨P_ordinary, P_scoped⟩ := P_ih wd_t.2
      let ordinary := encodeTerm_rep_spec.all_case vs D P
        D_ordinary D_scoped.to_root P_ordinary P_scoped.to_bool
        binder_admissible wd_t.2
      let root := encodeTerm_rep_scoped.all_case vs D P
        D_ordinary D_scoped.to_root P_ordinary P_scoped.to_bool
        binder_admissible wd_t.2
      exact ⟨ordinary, EncodeTermRepScopedIH.to_from ordinary root⟩

/-- Public representation-aware soundness theorem for every well-defined
source term. -/
theorem encodeTerm_rep_spec.{u}
    (binder_admissible : EncodeTermAllBinderAdmissible.{u})
    {t : B.Term} (wd_t : B.Term.WellDefined.{u} t) :
    EncodeTermRepIH.{u} t :=
  (encodeTerm_rep_spec_and_scoped binder_admissible t wd_t).1

/-- Public clean-prefix companion used by clients that recursively place an
encoded term beneath generated binders. -/
theorem encodeTerm_rep_scoped_spec.{u}
    (binder_admissible : EncodeTermAllBinderAdmissible.{u})
    {t : B.Term} (wd_t : B.Term.WellDefined.{u} t) :
    EncodeTermRepScopedFromIH.{u} t :=
  (encodeTerm_rep_spec_and_scoped binder_admissible t wd_t).2
