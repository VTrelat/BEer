import SMT.Reasoning.Basic.EncodeTermRepresentedBase
import SMT.Reasoning.Basic.EncodeTermBvUsed
import SMT.Reasoning.Basic.EncodeTermCorrectBool

open Std.Do B SMT ZFSet Classical

/-! # Representation-aware Boolean operators -/

namespace EncodeTermRepresentedBool

inductive CheckedOp where
  | and

namespace CheckedOp

def term : CheckedOp → B.Term → B.Term → B.Term
  | .and => (· ∧ᴮ ·)

def smtTerm : CheckedOp → SMT.Term → SMT.Term → SMT.Term
  | .and => .and

noncomputable def eval : CheckedOp → ZFSet → ZFSet → ZFSet
  | .and => (· ⋀ᶻ ·)

def label : CheckedOp → String
  | .and => "and"

def run (op : CheckedOp) (x y : B.Term) (E : B.Env) :
    Encoder (SMT.Term × SMTType) := do
  let ⟨x', .bool⟩ ← encodeTerm x E |
    throw s!"encodeTerm:{op.label}: Expected a boolean, got {← encodeTerm x E}"
  let ⟨y', .bool⟩ ← encodeTerm y E |
    throw s!"encodeTerm:{op.label}: Expected a boolean, got {← encodeTerm y E}"
  return (op.smtTerm x' y', .bool)

theorem encodeTerm_eq_run (op : CheckedOp) (x y : B.Term) (E : B.Env) :
    encodeTerm (op.term x y) E = op.run x y E := by
  cases op <;> rfl

@[simp]
theorem fv_term (op : CheckedOp) (x y : B.Term) :
    B.fv (op.term x y) = B.fv x ++ B.fv y := by
  cases op <;> rfl

@[simp]
theorem bv_term (op : CheckedOp) (x y : B.Term) :
    B.bv (op.term x y) = B.bv x ++ B.bv y := by
  cases op <;> rfl

@[simp]
theorem vars_term (op : CheckedOp) (x y : B.Term) :
    (op.term x y).vars = (B.fv x ++ B.fv y) ∪ (B.bv x ++ B.bv y) := by
  simp [B.Term.vars]

theorem notMem_vars_term (op : CheckedOp) {v : B.𝒱} {x y : B.Term} :
    v ∉ (op.term x y).vars ↔ v ∉ x.vars ∧ v ∉ y.vars := by
  cases op <;> simp only [term, B.Term.notMem_vars_and]

theorem typingE {Γ : B.TypeContext} {x y : B.Term} {α : BType}
    {op : CheckedOp} (h : Γ ⊢ᴮ op.term x y : α) :
    α = .bool ∧ Γ ⊢ᴮ x : .bool ∧ Γ ⊢ᴮ y : .bool := by
  cases op
  exact B.Typing.andE h

theorem typing {Γ : B.TypeContext} (op : CheckedOp) {x y : B.Term}
    (hx : Γ ⊢ᴮ x : .bool) (hy : Γ ⊢ᴮ y : .bool) :
    Γ ⊢ᴮ op.term x y : .bool := by
  cases op
  exact B.Typing.and hx hy

theorem denote_inv.{u} (op : CheckedOp) {Γ : B.TypeContext}
    {x y : B.Term} (_typ_t : Γ ⊢ᴮ op.term x y : .bool)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (op.term x y), («Δ» v).isSome = true)
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.bool⟧ᶻ}
    (den_t : ⟦(op.term x y).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨BType.bool, hT⟩⟩) :
    ∃ X, ∃ hX : X ∈ ⟦BType.bool⟧ᶻ,
      ⟦x.abstract «Δ» (fun v hv => Δ_fv v (by
        rw [fv_term, List.mem_append]
        exact Or.inl hv))⟧ᴮ = some ⟨X, ⟨BType.bool, hX⟩⟩ ∧
      ∃ Y, ∃ hY : Y ∈ ⟦BType.bool⟧ᶻ,
        ⟦y.abstract «Δ» (fun v hv => Δ_fv v (by
          rw [fv_term, List.mem_append]
          exact Or.inr hv))⟧ᴮ = some ⟨Y, ⟨BType.bool, hY⟩⟩ ∧
        op.eval X Y = T := by
  cases op
  simp only [term, eval] at den_t ⊢
  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, αx, hX⟩, den_x, hrest⟩ := den_t
  cases αx <;> first
    | rw [Option.bind_eq_some_iff] at hrest
    | exact absurd hrest (by simp)
  obtain ⟨⟨Y, βx, hY⟩, den_y, hout⟩ := hrest
  cases βx <;> first
    | rw [Option.some_inj] at hout
    | exact absurd hout (by simp)
  injection hout with T_eq _
  refine ⟨X, hX, ?_, Y, hY, ?_, ?_⟩
  · simpa only [proof_irrel_heq] using den_x
  · simpa only [proof_irrel_heq] using den_y
  · exact T_eq

theorem smt_typing {Γ : SMT.TypeContext} (op : CheckedOp)
    {x y : SMT.Term} (hx : Γ ⊢ˢ x : .bool) (hy : Γ ⊢ˢ y : .bool) :
    Γ ⊢ˢ op.smtTerm x y : .bool := by
  cases op
  exact SMT.Typing.and Γ x y hx hy

theorem eval_mem.{u} (op : CheckedOp) {X Y : ZFSet.{u}}
    (hX : X ∈ ZFSet.𝔹) (hY : Y ∈ ZFSet.𝔹) :
    op.eval X Y ∈ ZFSet.𝔹 := by
  cases op
  exact overloadBinOp_mem hX hY

theorem rdomCast_eval.{u} (op : CheckedOp)
    {X Y X' Y' : ZFSet.{u}}
    {hX : X ∈ ⟦BType.bool⟧ᶻ} {hY : Y ∈ ⟦BType.bool⟧ᶻ}
    {hX' : X' ∈ ⟦SMTType.bool⟧ᶻ} {hY' : Y' ∈ ⟦SMTType.bool⟧ᶻ}
    (hx : RDomCast (⟨X, BType.bool, hX⟩ : B.Dom)
      (⟨X', SMTType.bool, hX'⟩ : SMT.Dom))
    (hy : RDomCast (⟨Y, BType.bool, hY⟩ : B.Dom)
      (⟨Y', SMTType.bool, hY'⟩ : SMT.Dom)) :
    RDomCast
      (⟨op.eval X Y, BType.bool, op.eval_mem hX hY⟩ : B.Dom)
      (⟨op.eval X' Y', SMTType.bool, op.eval_mem hX' hY'⟩ :
        SMT.Dom) := by
  have hx' := (RDomCast.iff_RDom_of_type_eq (α := BType.bool) rfl).mp hx
  have hy' := (RDomCast.iff_RDom_of_type_eq (α := BType.bool) rfl).mp hy
  rw [RDom] at hx' hy'
  obtain ⟨_, hxret⟩ := hx'
  obtain ⟨_, hyret⟩ := hy'
  apply RDom.toRDomCast
  rw [RDom]
  refine ⟨rfl, ?_⟩
  cases op
  dsimp [eval, retract] at hxret hyret ⊢
  rw [hxret, hyret]

end CheckedOp
end EncodeTermRepresentedBool

set_option maxHeartbeats 3000000 in
theorem encodeTerm_rep_spec.checked_bool_case.{u}
    (op : EncodeTermRepresentedBool.CheckedOp)
    (x y : B.Term)
    (x_ih : EncodeTermRepIH.{u} x)
    (y_ih : EncodeTermRepIH.{u} y)
    (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (typ_t : E.context ⊢ᴮ op.term x y : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (op.term x y), («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastOnFV «Δ» Δ₀ (op.term x y))
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (den_t : ⟦(op.term x y).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (vars_used : ∀ v ∈ (op.term x y).vars, v ∈ used)
    (Λ_inv : ∀ v ∈ (op.term x y).vars,
      v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv (op.term x y)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (op.term x y))
    (fv_in_Λ : ∀ v ∈ B.fv (op.term x y), v ∈ Λ)
    (wf : B.RenWF E.context «Δ»)
    {n : ℕ} :
    ⦃fun ⟨E0, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (op.term x y) E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepPost (op.term x y) α Λ «Δ» Δ₀ used T hT
        E t' σ E' Γ'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [EncodeTermRepresentedBool.CheckedOp.encodeTerm_eq_run]
  unfold EncodeTermRepresentedBool.CheckedOp.run

  obtain ⟨rfl, typ_x, typ_y⟩ := op.typingE typ_t
  obtain ⟨X, hX, den_x, Y, hY, den_y, T_eq⟩ :=
    op.denote_inv (op.typing typ_x typ_y) Δ_fv den_t
  subst T

  have fv_x_sub : B.fv x ⊆ B.fv (op.term x y) := by
    intro v hv
    rw [op.fv_term, List.mem_append]
    exact Or.inl hv
  have fv_y_sub : B.fv y ⊆ B.fv (op.term x y) := by
    intro v hv
    rw [op.fv_term, List.mem_append]
    exact Or.inr hv
  have hx_bv_nodup : (B.bv x).Nodup := by
    have h := bv_nodup
    rw [op.bv_term, List.nodup_append] at h
    exact h.1
  have hy_bv_nodup : (B.bv y).Nodup := by
    have h := bv_nodup
    rw [op.bv_term, List.nodup_append] at h
    exact h.2.1
  have hxy_bv_disj : ∀ a ∈ B.bv x, ∀ b ∈ B.bv y, a ≠ b := by
    have h := bv_nodup
    rw [op.bv_term, List.nodup_append] at h
    exact h.2.2

  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (x_ih E typ_x
        (fun v hv => Δ_fv v (fv_x_sub hv))
        (related.mono_fv fv_x_sub)
        Δ₀_none_out Δ₀_dom den_x
        (fun v hv => vars_used v (by
          rw [op.vars_term]
          simp only [List.mem_union_iff, List.mem_append]
          rcases B.Term.mem_vars_iff.mp hv with h | h
          · exact .inl (.inl h)
          · exact .inr (.inl h)))
        (fun v hv => Λ_inv v (by
          rw [op.vars_term]
          simp only [List.mem_union_iff, List.mem_append]
          rcases B.Term.mem_vars_iff.mp hv with h | h
          · exact .inl (.inl h)
          · exact .inr (.inl h)))
        hx_bv_nodup (respects.mono_fv fv_x_sub)
        (fun v hv => fv_in_Λ v (fv_x_sub hv)) wf
        (n := St.env.freshvarsc))
      (encodeTerm_bv_used E (t := x) (used := St.env.usedVars)
        (n := St.env.freshvarsc) (decl := St.env.declarations)))
    (encodeTerm_bv_notMem_used E (t := x) (used := St.env.usedVars)
      (n := St.env.freshvarsc) (decl := St.env.declarations)))
  clear x_ih
  rename_i out_x
  obtain ⟨x_enc, σx⟩ := out_x
  mrename_i pre
  mintro ∀Stx
  mpure pre
  dsimp at pre
  obtain ⟨⟨⟨used_sub_x, types_sub_x, keys_sub_x, x_used,
      path_x, typ_x_enc, _shape_x, x_preserves,
      Δx, hcov_x, Δx_ext, _related_x, Δx_none, _respects_x,
      target_respects_x, Δx_dom,
      denX, hden_x, hdenX_type, X_rel, x_total⟩,
      bv_x_used, _⟩,
      bv_x_not_used, _⟩ := pre
  rcases denX with ⟨Xenc, σX, hXenc⟩
  dsimp at hdenX_type
  subst σX
  obtain ⟨cx⟩ := path_x
  have hσx : σx = SMTType.bool := castPath.source_eq_bool cx
  subst σx

  have related_y : RValuationCastOnFV «Δ» Δx y :=
    (related.mono_fv fv_y_sub).of_extends Δx_ext
  have respects_y : B.RenamingContext.RespectsTypeContextOnFV
      Δx Stx.types y :=
    respects.of_extends Δx_ext types_sub_x fv_y_sub fv_in_Λ

  mspec y_ih E typ_y
    (fun v hv => Δ_fv v (fv_y_sub hv)) related_y
    Δx_none Δx_dom den_y
    (fun v hv => used_sub_x (vars_used v (by
      rw [op.vars_term]
      simp only [List.mem_union_iff, List.mem_append]
      rcases B.Term.mem_vars_iff.mp hv with h | h
      · exact .inl (.inr h)
      · exact .inr (.inr h))))
    (fun v hv hΓ => by
      have hv_parent : v ∈ (op.term x y).vars := by
        rw [op.vars_term]
        simp only [List.mem_union_iff, List.mem_append]
        rcases B.Term.mem_vars_iff.mp hv with h | h
        · exact .inl (.inr h)
        · exact .inr (.inr h)
      by_cases hv_Λ : v ∈ St.types
      · exact Λ_inv v hv_parent hv_Λ
      · have hv_vars_x : v ∈ B.Term.vars x := by
          by_contra hnot
          exact absurd hΓ
            (x_preserves v (vars_used v hv_parent) hv_Λ hnot)
        rcases B.Term.mem_vars_iff.mp hv_vars_x with hx_fv | hx_bv
        · exact B.Typing.typed_by_fv typ_x hx_fv
        · rcases B.Term.mem_vars_iff.mp hv with hy_fv | hy_bv
          · exact absurd (B.Typing.typed_by_fv typ_y hy_fv)
              (B.Typing.bv_notMem_context typ_x v hx_bv)
          · exact absurd rfl (hxy_bv_disj v hx_bv v hy_bv))
    hy_bv_nodup respects_y
    (fun v hv => AList.mem_of_subset types_sub_x
      (fv_in_Λ v (fv_y_sub hv))) wf
    (n := Stx.env.freshvarsc)
  clear y_ih
  rename_i out_y
  obtain ⟨y_enc, σy⟩ := out_y
  mrename_i pre
  mintro ∀Sty
  mpure pre
  dsimp at pre
  obtain ⟨used_sub_y, types_sub_y, keys_sub_y, y_used,
    path_y, typ_y_enc, _shape_y, y_preserves,
    Δy, hcov_y, Δy_ext, _related_y, Δy_none, _respects_y,
    target_respects_y, Δy_dom,
    denY, hden_y, hdenY_type, Y_rel, y_total⟩ := pre
  rcases denY with ⟨Yenc, σY, hYenc⟩
  dsimp at hdenY_type
  subst σY
  obtain ⟨cy⟩ := path_y
  have hσy : σy = SMTType.bool := castPath.source_eq_bool cy
  subst σy

  have bv_x_not_final : ∀ v ∈ SMT.bv x_enc, v ∉ Sty.types :=
    fun v hv => y_preserves v (bv_x_used v hv)
      (SMT.Typing.bv_notMem_context typ_x_enc v hv)
      (by
        rw [B.Term.notMem_vars_iff]
        refine ⟨?_, ?_⟩
        · intro hfy
          exact SMT.Typing.bv_notMem_context typ_x_enc v hv
            (AList.mem_of_subset types_sub_x
              (fv_in_Λ v (fv_y_sub hfy)))
        · intro hby
          exact bv_x_not_used v hv
            (St_used_eq ▸ vars_used v (by
              rw [op.vars_term]
              simp only [List.mem_union_iff, List.mem_append]
              exact .inr (.inr hby))))
  have typ_x_final : Sty.types ⊢ˢ x_enc : SMTType.bool :=
    SMT.Typing.weakening types_sub_y typ_x_enc bv_x_not_final
  have hcov_x_final : RenamingContext.CoversFV Δy x_enc :=
    RenamingContext.coversFV_of_extends_of_coversFV Δy_ext hcov_x
  have hden_x_final :
      ⟦x_enc.abstract Δy hcov_x_final⟧ˢ =
        some (⟨Xenc, SMTType.bool, hXenc⟩ : SMT.Dom) := by
    have hagree :=
      RenamingContext.agreesOnFV_of_extends_of_coversFV Δy_ext hcov_x
    have hcongr := RenamingContext.denote_congr_of_agreesOnFV
      (t := x_enc) (h1 := hcov_x_final) (h2 := hcov_x) hagree
    simpa [RenamingContext.denote] using hcongr.trans hden_x
  have target_respects_x_final :
      SMT.RenamingContext.RespectsTypeContextOnFV Δy Sty.types x_enc :=
    target_respects_x.of_extends Δy_ext types_sub_y typ_x_enc

  mspec Std.Do.Spec.pure
  mpure_intro
  have Δy_ext₀ := RenamingContext.extends_trans Δy_ext Δx_ext
  and_intros
  · intro v hv
    exact used_sub_y (used_sub_x (by simpa [St_used_eq] using hv))
  · exact fun _ h => types_sub_y (types_sub_x h)
  · exact keys_sub_y
  · intro v hv
    rw [op.fv_term, List.mem_append] at hv
    exact hv.elim (fun h => used_sub_y (x_used v h)) (fun h => y_used v h)
  · exact ⟨castPath.reflexive SMTType.bool⟩
  · exact op.smt_typing typ_x_final typ_y_enc
  · cases op <;> trivial
  · intro v hv hΛ hvars hΓ
    rw [op.notMem_vars_term] at hvars
    have hv_not_Stx : v ∉ Stx.types := by
      intro hΓx
      by_cases hv_St : v ∈ St.types
      · exact hΛ hv_St
      · exact x_preserves v (by simpa [St_used_eq] using hv)
          hv_St hvars.1 hΓx
    exact y_preserves v (used_sub_x (by simpa [St_used_eq] using hv))
      hv_not_Stx hvars.2 hΓ
  · refine ⟨Δy, ?_, Δy_ext₀, related.of_extends Δy_ext₀,
      Δy_none, ?_, ?_, Δy_dom, ?_⟩
    · intro v hv
      cases op <;> simp only [EncodeTermRepresentedBool.CheckedOp.smtTerm,
        SMT.fv, List.mem_append] at hv
      exact hv.elim (hcov_x_final v) (hcov_y v)
    · exact respects.of_extends Δy_ext₀
        (fun _ h => types_sub_y (types_sub_x h)) (fun _ h => h) fv_in_Λ
    · intro v τ hv hlookup
      cases op <;> simp only [EncodeTermRepresentedBool.CheckedOp.smtTerm,
        SMT.fv, List.mem_append] at hv
      exact hv.elim
        (fun hx => target_respects_x_final hx hlookup)
        (fun hy => target_respects_y hy hlookup)
    · let denOp : SMT.Dom.{u} :=
        ⟨op.eval Xenc Yenc, SMTType.bool, op.eval_mem hXenc hYenc⟩
      refine ⟨denOp, ?_, rfl, ?_, ?_⟩
      · cases op <;> simp [denOp,
          EncodeTermRepresentedBool.CheckedOp.smtTerm,
          EncodeTermRepresentedBool.CheckedOp.eval,
          SMT.Term.abstract, SMT.denote, hden_x_final, hden_y]
      · simpa [denOp] using op.rdomCast_eval X_rel Y_rel
      · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt wf_alt
          Δ₀_alt_none respects_alt Δ₀_alt_dom T_alt hT_alt den_t_alt
        obtain ⟨X_alt, hX_alt, den_x_alt, Y_alt, hY_alt,
            den_y_alt, T_alt_eq⟩ :=
          op.denote_inv (op.typing typ_x typ_y) Δ_fv_alt den_t_alt
        subst T_alt

        have Δ₀_alt_none_x : ∀ v ∉ Stx.env.usedVars,
            Δ₀_alt v = none := by
          intro v hv
          by_contra hne
          have hv_Λ := Δ₀_alt_dom v hne
          have hv_used : v ∈ used := by
            simpa [← St_used_eq] using St_sub hv_Λ
          exact hv (used_sub_x hv_used)
        obtain ⟨Δx_alt, hcov_x_alt, denX_alt, Δx_alt_ext,
            _related_x_alt, Δx_alt_none, _respects_x_alt,
            target_respects_x_alt, Δx_alt_dom,
            hden_x_alt, hdenX_alt_type, X_alt_rel⟩ :=
          x_total Δ_alt
            (fun v hv => Δ_fv_alt v (fv_x_sub hv)) Δ₀_alt
            (related_alt.mono_fv fv_x_sub) wf_alt Δ₀_alt_none_x
            (respects_alt.mono_fv fv_x_sub) Δ₀_alt_dom
            X_alt hX_alt den_x_alt
        rcases denX_alt with ⟨Xenc_alt, σX_alt, hXenc_alt⟩
        dsimp at hdenX_alt_type
        subst σX_alt

        have Δx_alt_none_y : ∀ v ∉ Sty.env.usedVars,
            Δx_alt v = none := by
          intro v hv
          apply Δx_alt_none v
          intro hvx
          exact hv (used_sub_y hvx)
        have related_alt_y : RValuationCastOnFV Δ_alt Δx_alt y :=
          (related_alt.mono_fv fv_y_sub).of_extends Δx_alt_ext
        have respects_alt_y :
            B.RenamingContext.RespectsTypeContextOnFV
              Δx_alt Stx.types y :=
          respects_alt.of_extends Δx_alt_ext types_sub_x
            fv_y_sub fv_in_Λ
        obtain ⟨Δy_alt, hcov_y_alt, denY_alt, Δy_alt_ext,
            _related_y_alt, Δy_alt_none, _respects_y_alt,
            target_respects_y_alt, Δy_alt_dom,
            hden_y_alt, hdenY_alt_type, Y_alt_rel⟩ :=
          y_total Δ_alt
            (fun v hv => Δ_fv_alt v (fv_y_sub hv)) Δx_alt
            related_alt_y wf_alt Δx_alt_none_y respects_alt_y
            Δx_alt_dom Y_alt hY_alt den_y_alt
        rcases denY_alt with ⟨Yenc_alt, σY_alt, hYenc_alt⟩
        dsimp at hdenY_alt_type
        subst σY_alt

        have hcov_x_alt_final : RenamingContext.CoversFV Δy_alt x_enc :=
          RenamingContext.coversFV_of_extends_of_coversFV
            Δy_alt_ext hcov_x_alt
        have hden_x_alt_final :
            ⟦x_enc.abstract Δy_alt hcov_x_alt_final⟧ˢ =
              some (⟨Xenc_alt, SMTType.bool, hXenc_alt⟩ : SMT.Dom) := by
          have hagree :=
            RenamingContext.agreesOnFV_of_extends_of_coversFV
              Δy_alt_ext hcov_x_alt
          have hcongr := RenamingContext.denote_congr_of_agreesOnFV
            (t := x_enc) (h1 := hcov_x_alt_final)
            (h2 := hcov_x_alt) hagree
          simpa [RenamingContext.denote] using hcongr.trans hden_x_alt
        have target_respects_x_alt_final :
            SMT.RenamingContext.RespectsTypeContextOnFV
              Δy_alt Sty.types x_enc :=
          target_respects_x_alt.of_extends
            Δy_alt_ext types_sub_y typ_x_enc
        have hcov_op_alt : RenamingContext.CoversFV Δy_alt
            (op.smtTerm x_enc y_enc) := by
          intro v hv
          cases op <;> simp only [EncodeTermRepresentedBool.CheckedOp.smtTerm,
            SMT.fv, List.mem_append] at hv
          exact hv.elim (hcov_x_alt_final v) (hcov_y_alt v)
        have Δy_alt_ext₀ :=
          RenamingContext.extends_trans Δy_alt_ext Δx_alt_ext
        let denOpAlt : SMT.Dom.{u} :=
          ⟨op.eval Xenc_alt Yenc_alt, SMTType.bool,
            op.eval_mem hXenc_alt hYenc_alt⟩
        refine ⟨Δy_alt, hcov_op_alt, denOpAlt, Δy_alt_ext₀,
          related_alt.of_extends Δy_alt_ext₀, Δy_alt_none, ?_,
          ?_, Δy_alt_dom, ?_, rfl, ?_⟩
        · exact respects_alt.of_extends Δy_alt_ext₀
            (fun _ h => types_sub_y (types_sub_x h))
            (fun _ h => h) fv_in_Λ
        · intro v τ hv hlookup
          cases op <;> simp only [EncodeTermRepresentedBool.CheckedOp.smtTerm,
            SMT.fv, List.mem_append] at hv
          exact hv.elim
            (fun hx => target_respects_x_alt_final hx hlookup)
            (fun hy => target_respects_y_alt hy hlookup)
        · cases op <;> simp [denOpAlt,
            EncodeTermRepresentedBool.CheckedOp.smtTerm,
            EncodeTermRepresentedBool.CheckedOp.eval,
            SMT.Term.abstract, SMT.denote, hden_x_alt_final,
            hden_y_alt]
        · simpa [denOpAlt] using
            op.rdomCast_eval X_alt_rel Y_alt_rel

private theorem denote_not_inv.{u} {Γ : B.TypeContext} {x : B.Term}
    (_typ_t : Γ ⊢ᴮ ¬ᴮ x : .bool)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (¬ᴮ x), («Δ» v).isSome = true)
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.bool⟧ᶻ}
    (den_t : ⟦(¬ᴮ x).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨BType.bool, hT⟩⟩) :
    ∃ X, ∃ hX : X ∈ ⟦BType.bool⟧ᶻ,
      ⟦x.abstract «Δ» (fun v hv => Δ_fv v (by
        simpa [B.fv] using hv))⟧ᴮ =
          some ⟨X, ⟨BType.bool, hX⟩⟩ ∧
      (¬ᶻ X) = T := by
  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, αx, hX⟩, den_x, hout⟩ := den_t
  cases αx <;> first
    | rw [Option.some_inj] at hout
    | exact absurd hout (by simp)
  injection hout with T_eq _
  refine ⟨X, hX, ?_, T_eq⟩
  simpa only [proof_irrel_heq] using den_x

private theorem rdomCast_not.{u}
    {X X' : ZFSet.{u}}
    {hX : X ∈ ⟦BType.bool⟧ᶻ} {hX' : X' ∈ ⟦SMTType.bool⟧ᶻ}
    (hx : RDomCast (⟨X, BType.bool, hX⟩ : B.Dom)
      (⟨X', SMTType.bool, hX'⟩ : SMT.Dom)) :
    RDomCast
      (⟨¬ᶻ X, BType.bool, overloadUnaryOp_mem⟩ : B.Dom)
      (⟨¬ᶻ X', SMTType.bool, overloadUnaryOp_mem⟩ : SMT.Dom) := by
  have hx' := (RDomCast.iff_RDom_of_type_eq (α := BType.bool) rfl).mp hx
  rw [RDom] at hx'
  obtain ⟨_, hxret⟩ := hx'
  apply RDom.toRDomCast
  rw [RDom]
  refine ⟨rfl, ?_⟩
  dsimp [retract] at hxret ⊢
  rw [hxret]

set_option maxHeartbeats 1600000 in
theorem encodeTerm_rep_spec.not_case.{u}
    (x : B.Term)
    (x_ih : EncodeTermRepIH.{u} x)
    (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (typ_t : E.context ⊢ᴮ ¬ᴮ x : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (¬ᴮ x), («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastOnFV «Δ» Δ₀ (¬ᴮ x))
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (den_t : ⟦(¬ᴮ x).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (vars_used : ∀ v ∈ (¬ᴮ x).vars, v ∈ used)
    (Λ_inv : ∀ v ∈ (¬ᴮ x).vars, v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv (¬ᴮ x)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (¬ᴮ x))
    (fv_in_Λ : ∀ v ∈ B.fv (¬ᴮ x), v ∈ Λ)
    (wf : B.RenWF E.context «Δ»)
    {n : ℕ} :
    ⦃fun ⟨E0, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (¬ᴮ x) E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepPost (¬ᴮ x) α Λ «Δ» Δ₀ used T hT
        E t' σ E' Γ'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm]

  obtain ⟨rfl, typ_x⟩ := B.Typing.notE typ_t
  obtain ⟨X, hX, den_x, T_eq⟩ :=
    denote_not_inv (B.Typing.not typ_x) Δ_fv den_t
  subst T

  have fv_x_sub : B.fv x ⊆ B.fv (¬ᴮ x) := by
    intro v hv
    simpa [B.fv] using hv
  have hx_bv_nodup : (B.bv x).Nodup := by
    simpa [B.bv] using bv_nodup

  mspec x_ih E typ_x
    (fun v hv => Δ_fv v (fv_x_sub hv))
    (related.mono_fv fv_x_sub)
    Δ₀_none_out Δ₀_dom den_x
    (fun v hv => vars_used v (by
      simpa [B.Term.vars, B.fv, B.bv] using hv))
    (fun v hv => Λ_inv v (by
      simpa [B.Term.vars, B.fv, B.bv] using hv))
    hx_bv_nodup (respects.mono_fv fv_x_sub)
    (fun v hv => fv_in_Λ v (fv_x_sub hv)) wf
    (n := St.env.freshvarsc)
  clear x_ih
  rename_i out_x
  obtain ⟨x_enc, σx⟩ := out_x
  mrename_i pre
  mintro ∀Stx
  mpure pre
  dsimp at pre
  obtain ⟨used_sub_x, types_sub_x, keys_sub_x, x_used,
    path_x, typ_x_enc, _shape_x, x_preserves,
    Δx, hcov_x, Δx_ext, _related_x, Δx_none, _respects_x,
    target_respects_x, Δx_dom,
    denX, hden_x, hdenX_type, X_rel, x_total⟩ := pre
  rcases denX with ⟨Xenc, σX, hXenc⟩
  dsimp at hdenX_type
  subst σX
  obtain ⟨cx⟩ := path_x
  have hσx : σx = SMTType.bool := castPath.source_eq_bool cx
  subst σx

  mspec Std.Do.Spec.pure
  mpure_intro
  have hcov_not : RenamingContext.CoversFV Δx (SMT.Term.not x_enc) := by
    intro v hv
    exact hcov_x v (by simpa [SMT.fv] using hv)
  and_intros
  · intro v hv
    exact used_sub_x (by simpa [St_used_eq] using hv)
  · exact types_sub_x
  · exact keys_sub_x
  · intro v hv
    exact x_used v (by simpa [B.fv] using hv)
  · exact ⟨castPath.reflexive SMTType.bool⟩
  · exact SMT.Typing.not Stx.types x_enc typ_x_enc
  · trivial
  · intro v hv hΛ hvars hΓ
    rw [B.Term.notMem_vars_not] at hvars
    exact x_preserves v (by simpa [St_used_eq] using hv) hΛ hvars hΓ
  · refine ⟨Δx, hcov_not, Δx_ext, related.of_extends Δx_ext,
      Δx_none, ?_, ?_, Δx_dom, ?_⟩
    · exact respects.of_extends Δx_ext types_sub_x
        (fun _ h => h) fv_in_Λ
    · intro v τ hv hlookup
      exact target_respects_x (by simpa [SMT.fv] using hv) hlookup
    · let denNot : SMT.Dom.{u} :=
        ⟨¬ᶻ Xenc, SMTType.bool, overloadUnaryOp_mem⟩
      refine ⟨denNot, ?_, rfl, ?_, ?_⟩
      · simp [denNot, SMT.Term.abstract, SMT.denote, hden_x]
      · simpa [denNot] using rdomCast_not X_rel
      · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt wf_alt
          Δ₀_alt_none respects_alt Δ₀_alt_dom T_alt hT_alt den_t_alt
        obtain ⟨X_alt, hX_alt, den_x_alt, T_alt_eq⟩ :=
          denote_not_inv (B.Typing.not typ_x) Δ_fv_alt den_t_alt
        subst T_alt
        obtain ⟨Δx_alt, hcov_x_alt, denX_alt, Δx_alt_ext,
            _related_x_alt, Δx_alt_none, respects_x_alt,
            target_respects_x_alt, Δx_alt_dom,
            hden_x_alt, hdenX_alt_type, X_alt_rel⟩ :=
          x_total Δ_alt
            (fun v hv => Δ_fv_alt v (fv_x_sub hv)) Δ₀_alt
            (related_alt.mono_fv fv_x_sub) wf_alt Δ₀_alt_none
            (respects_alt.mono_fv fv_x_sub) Δ₀_alt_dom
            X_alt hX_alt den_x_alt
        rcases denX_alt with ⟨Xenc_alt, σX_alt, hXenc_alt⟩
        dsimp at hdenX_alt_type
        subst σX_alt
        have hcov_not_alt : RenamingContext.CoversFV Δx_alt
            (SMT.Term.not x_enc) := by
          intro v hv
          exact hcov_x_alt v (by simpa [SMT.fv] using hv)
        let denNotAlt : SMT.Dom.{u} :=
          ⟨¬ᶻ Xenc_alt, SMTType.bool, overloadUnaryOp_mem⟩
        refine ⟨Δx_alt, hcov_not_alt, denNotAlt, Δx_alt_ext,
          related_alt.of_extends Δx_alt_ext, Δx_alt_none, ?_,
          ?_, Δx_alt_dom, ?_, rfl, ?_⟩
        · simpa [B.fv] using respects_x_alt
        · intro v τ hv hlookup
          exact target_respects_x_alt
            (by simpa [SMT.fv] using hv) hlookup
        · simp [denNotAlt, SMT.Term.abstract, SMT.denote, hden_x_alt]
        · simpa [denNotAlt] using rdomCast_not X_alt_rel
