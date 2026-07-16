import SMT.Reasoning.Basic.EncodeTermRepresentedBase
import SMT.Reasoning.Basic.EncodeTermBvUsed
import SMT.Reasoning.Basic.EncodeTermCorrectArith

open Std.Do B SMT ZFSet Classical

/-! # Representation-aware arithmetic and pair constructors -/

namespace EncodeTermRepresentedArith

inductive CheckedOp where
  | add
  | sub
  | mul

namespace CheckedOp

def term : CheckedOp → B.Term → B.Term → B.Term
  | .add => (· +ᴮ ·)
  | .sub => (· -ᴮ ·)
  | .mul => (· *ᴮ ·)

def smtTerm : CheckedOp → SMT.Term → SMT.Term → SMT.Term
  | .add => .add
  | .sub => .sub
  | .mul => .mul

noncomputable def eval : CheckedOp → ZFSet → ZFSet → ZFSet
  | .add => (· +ᶻ ·)
  | .sub => (· -ᶻ ·)
  | .mul => (· *ᶻ ·)

def label : CheckedOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"

def run (op : CheckedOp) (x y : B.Term) (E : B.Env) :
    Encoder (SMT.Term × SMTType) := do
  let ⟨x', .int⟩ ← encodeTerm x E |
    throw s!"encodeTerm:{op.label}: Expected an integer, got {← encodeTerm x E}"
  let ⟨y', .int⟩ ← encodeTerm y E |
    throw s!"encodeTerm:{op.label}: Expected an integer, got {← encodeTerm y E}"
  return (op.smtTerm x' y', .int)

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
  cases op <;> simp only [term, B.Term.notMem_vars_add,
    B.Term.notMem_vars_sub, B.Term.notMem_vars_mul]

theorem typingE {Γ : B.TypeContext} {x y : B.Term} {α : BType}
    {op : CheckedOp} (h : Γ ⊢ᴮ op.term x y : α) :
    α = .int ∧ Γ ⊢ᴮ x : .int ∧ Γ ⊢ᴮ y : .int := by
  cases op with
  | add => exact B.Typing.addE h
  | sub => exact B.Typing.subE h
  | mul => exact B.Typing.mulE h

theorem typing {Γ : B.TypeContext} (op : CheckedOp) {x y : B.Term}
    (hx : Γ ⊢ᴮ x : .int) (hy : Γ ⊢ᴮ y : .int) :
    Γ ⊢ᴮ op.term x y : .int := by
  cases op
  · exact B.Typing.add hx hy
  · exact B.Typing.sub hx hy
  · exact B.Typing.mul hx hy

theorem denote_inv.{u} (op : CheckedOp) {Γ : B.TypeContext}
    {x y : B.Term} (typ_t : Γ ⊢ᴮ op.term x y : .int)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (op.term x y), («Δ» v).isSome = true)
    {T : ZFSet.{u}} {hT : T ∈ ⟦BType.int⟧ᶻ}
    (den_t : ⟦(op.term x y).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨BType.int, hT⟩⟩) :
    ∃ X, ∃ hX : X ∈ ⟦BType.int⟧ᶻ,
      ⟦x.abstract «Δ» (fun v hv => Δ_fv v (by
        rw [fv_term, List.mem_append]
        exact Or.inl hv))⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩ ∧
      ∃ Y, ∃ hY : Y ∈ ⟦BType.int⟧ᶻ,
        ⟦y.abstract «Δ» (fun v hv => Δ_fv v (by
          rw [fv_term, List.mem_append]
          exact Or.inr hv))⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩ ∧
        op.eval X Y = T := by
  cases op with
  | add =>
      simpa [term, eval] using
        EncodeTermCorrectArith.Arith.denote_inv
          (.add) typ_t Δ_fv den_t
  | sub =>
      simpa [term, eval] using
        EncodeTermCorrectArith.Arith.denote_inv
          (.sub) typ_t Δ_fv den_t
  | mul =>
      simpa [term, eval] using
        EncodeTermCorrectArith.Arith.denote_inv
          (.mul) typ_t Δ_fv den_t

theorem smt_typing {Γ : SMT.TypeContext} (op : CheckedOp)
    {x y : SMT.Term} (hx : Γ ⊢ˢ x : .int) (hy : Γ ⊢ˢ y : .int) :
    Γ ⊢ˢ op.smtTerm x y : .int := by
  cases op
  · exact SMT.Typing.add Γ x y hx hy
  · exact SMT.Typing.sub Γ x y hx hy
  · exact SMT.Typing.mul Γ x y hx hy

theorem eval_mem.{u} (op : CheckedOp) {X Y : ZFSet.{u}}
    (hX : X ∈ ZFSet.Int) (hY : Y ∈ ZFSet.Int) :
    op.eval X Y ∈ ZFSet.Int := by
  cases op <;> exact overloadBinOp_mem hX hY

theorem rdomCast_eval.{u} (op : CheckedOp)
    {X Y X' Y' : ZFSet.{u}}
    {hX : X ∈ ⟦BType.int⟧ᶻ} {hY : Y ∈ ⟦BType.int⟧ᶻ}
    {hX' : X' ∈ ⟦SMTType.int⟧ᶻ} {hY' : Y' ∈ ⟦SMTType.int⟧ᶻ}
    (hx : RDomCast (⟨X, BType.int, hX⟩ : B.Dom)
      (⟨X', SMTType.int, hX'⟩ : SMT.Dom))
    (hy : RDomCast (⟨Y, BType.int, hY⟩ : B.Dom)
      (⟨Y', SMTType.int, hY'⟩ : SMT.Dom)) :
    RDomCast
      (⟨op.eval X Y, BType.int, op.eval_mem hX hY⟩ : B.Dom)
      (⟨op.eval X' Y', SMTType.int, op.eval_mem hX' hY'⟩ :
        SMT.Dom) := by
  have hx' := (RDomCast.iff_RDom_of_type_eq (α := BType.int) rfl).mp hx
  have hy' := (RDomCast.iff_RDom_of_type_eq (α := BType.int) rfl).mp hy
  rw [RDom] at hx' hy'
  obtain ⟨_, hxret⟩ := hx'
  obtain ⟨_, hyret⟩ := hy'
  apply RDom.toRDomCast
  rw [RDom]
  refine ⟨rfl, ?_⟩
  cases op <;> simp [eval, retract] at hxret hyret ⊢ <;>
    simp_all only

end CheckedOp
end EncodeTermRepresentedArith

private theorem encodeTerm_le_via_maplet (x y : B.Term) (E : B.Env) :
    encodeTerm (x ≤ᴮ y) E = (do
      let ⟨p, _⟩ ← encodeTerm (x ↦ᴮ y) E
      match p with
      | .pair x' y' => return (.le x' y', SMTType.bool)
      | _ => throw "encodeTerm:le: impossible maplet result") := by
  simp [encodeTerm]

private theorem denote_pair_inv.{u}
    {x y : SMT.Term} {Θ : SMT.RenamingContext.Context.{u}}
    (hcov : RenamingContext.CoversFV Θ (SMT.Term.pair x y))
    {d : SMT.Dom.{u}}
    (hden : ⟦(SMT.Term.pair x y).abstract Θ hcov⟧ˢ = some d) :
    ∃ (dx dy : SMT.Dom.{u}),
      ⟦x.abstract Θ (fun v hv => hcov v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv))⟧ˢ = some dx ∧
      ⟦y.abstract Θ (fun v hv => hcov v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv))⟧ˢ = some dy ∧
      d = ⟨dx.fst.pair dy.fst, SMTType.pair dx.snd.fst dy.snd.fst,
        ZFSet.pair_mem_prod.mpr ⟨dx.snd.snd, dy.snd.snd⟩⟩ := by
  rw [SMT.Term.abstract, SMT.denote, Option.pure_def,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at hden
  obtain ⟨dx, hdx, hrest⟩ := hden
  rw [Option.bind_eq_some_iff] at hrest
  obtain ⟨dy, hdy, hout⟩ := hrest
  refine ⟨dx, dy, ?_, ?_, ?_⟩
  · simpa only [proof_irrel_heq] using hdx
  · simpa only [proof_irrel_heq] using hdy
  · simpa using hout.symm

private theorem rdomCast_le.{u}
    {X Y X' Y' : ZFSet.{u}}
    {hX : X ∈ ZFSet.Int} {hY : Y ∈ ZFSet.Int}
    {hX' : X' ∈ ZFSet.Int} {hY' : Y' ∈ ZFSet.Int}
    (hx : RDomCast (⟨X, BType.int, hX⟩ : B.Dom)
      (⟨X', SMTType.int, hX'⟩ : SMT.Dom))
    (hy : RDomCast (⟨Y, BType.int, hY⟩ : B.Dom)
      (⟨Y', SMTType.int, hY'⟩ : SMT.Dom)) :
    RDomCast
      (⟨X ≤ᶻ Y, BType.bool, overloadBinOp_mem hX hY⟩ : B.Dom)
      (⟨X' ≤ᶻ Y', SMTType.bool, overloadBinOp_mem hX' hY'⟩ : SMT.Dom) := by
  have hx' := (RDomCast.iff_RDom_of_type_eq (α := BType.int) rfl).mp hx
  have hy' := (RDomCast.iff_RDom_of_type_eq (α := BType.int) rfl).mp hy
  rw [RDom] at hx' hy'
  obtain ⟨_, hxret⟩ := hx'
  obtain ⟨_, hyret⟩ := hy'
  dsimp [retract] at hxret hyret ⊢
  subst X'
  subst Y'
  exact RDom.toRDomCast ⟨rfl, rfl⟩

set_option maxHeartbeats 2000000 in
theorem encodeTerm_rep_spec.maplet_case.{u}
    (x y : B.Term)
    (x_ih : EncodeTermRepIH.{u} x)
    (y_ih : EncodeTermRepIH.{u} y)
    (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (typ_t : E.context ⊢ᴮ x ↦ᴮ y : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (x ↦ᴮ y), («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastAdmissibleOnFV «Δ» Δ₀ (x ↦ᴮ y))
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (den_t : ⟦(x ↦ᴮ y).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (vars_used : ∀ v ∈ (x ↦ᴮ y).vars, v ∈ used)
    (Λ_inv : ∀ v ∈ (x ↦ᴮ y).vars, v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv (x ↦ᴮ y)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (x ↦ᴮ y))
    (fv_in_Λ : ∀ v ∈ B.fv (x ↦ᴮ y), v ∈ Λ)
    (wf : B.RenWF E.context «Δ»)
    {n : ℕ} :
    ⦃fun ⟨E0, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (x ↦ᴮ y) E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepPost (x ↦ᴮ y) α Λ «Δ» Δ₀ used T hT
        E t' σ E' Γ'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm]

  apply B.Typing.mapletE at typ_t
  obtain ⟨αx, βx, rfl, typ_x, typ_y⟩ := typ_t

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, α', hX⟩, den_x, hrest⟩ := den_t
  dsimp at hrest
  rw [Option.bind_eq_some_iff] at hrest
  obtain ⟨⟨Y, β', hY⟩, den_y, hout⟩ := hrest
  rw [Option.some_inj] at hout
  dsimp at hout
  injection hout with T_eq type_eq
  subst T
  injection type_eq with pair_type_eq _
  injection pair_type_eq with α'_eq β'_eq
  subst α' β'

  have fv_x_sub : B.fv x ⊆ B.fv (x ↦ᴮ y) := by
    intro v hv
    simpa [B.fv] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y)
  have fv_y_sub : B.fv y ⊆ B.fv (x ↦ᴮ y) := by
    intro v hv
    simpa [B.fv] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y)
  have hx_bv_nodup : (B.bv x).Nodup := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.1
  have hy_bv_nodup : (B.bv y).Nodup := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.2.1
  have hxy_bv_disj : ∀ a ∈ B.bv x, ∀ b ∈ B.bv y, a ≠ b := by
    have h := bv_nodup
    simp only [B.bv, List.nodup_append] at h
    exact h.2.2

  mspec (Std.Do.Triple.and _
    (Std.Do.Triple.and _
      (x_ih E typ_x
        (fun v hv => Δ_fv v (fv_x_sub hv))
        (related.mono_fv fv_x_sub)
        Δ₀_none_out Δ₀_dom den_x
        (fun v hv => vars_used v (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact .inl h))
        (fun v hv => Λ_inv v (by
          simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
            List.mem_append] at hv ⊢
          rcases hv with h | h <;> [left; right] <;> exact .inl h))
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

  have related_y : RValuationCastAdmissibleOnFV «Δ» Δx y :=
    (related.mono_fv fv_y_sub).of_extends Δx_ext
  have respects_y : B.RenamingContext.RespectsTypeContextOnFV
      Δx Stx.types y :=
    respects.of_extends Δx_ext types_sub_x fv_y_sub fv_in_Λ

  mspec y_ih E typ_y
    (fun v hv => Δ_fv v (fv_y_sub hv)) related_y
    Δx_none Δx_dom den_y
    (fun v hv => used_sub_x (vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
        List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)))
    (fun v hv hΓ => by
      have hv_maplet : v ∈ (x ↦ᴮ y).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
          List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_Λ : v ∈ St.types
      · exact Λ_inv v hv_maplet hv_Λ
      · have hv_vars_x : v ∈ B.Term.vars x := by
          by_contra hnot
          exact absurd hΓ
            (x_preserves v (vars_used v hv_maplet) hv_Λ hnot)
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
              simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv,
                List.mem_append]
              right
              right
              exact hby)))
  have typ_x_final : Sty.types ⊢ˢ x_enc : σx :=
    SMT.Typing.weakening types_sub_y typ_x_enc bv_x_not_final
  have hcov_x_final : RenamingContext.CoversFV Δy x_enc :=
    RenamingContext.coversFV_of_extends_of_coversFV Δy_ext hcov_x
  have hden_x_final :
      ⟦x_enc.abstract Δy hcov_x_final⟧ˢ =
        some (⟨Xenc, σx, hXenc⟩ : SMT.Dom) := by
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
    rw [B.fv, List.mem_append] at hv
    exact hv.elim (fun h => used_sub_y (x_used v h)) (fun h => y_used v h)
  · exact ⟨castPath.pair cx cy⟩
  · apply SMT.Typing.pair
    · exact typ_x_final
    · exact typ_y_enc
  · exact ⟨x_enc, y_enc, σx, σy, rfl, rfl⟩
  · intro v hv hΛ hvars hΓ
    rw [B.Term.notMem_vars_maplet] at hvars
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
      rw [SMT.fv, List.mem_append] at hv
      exact hv.elim (hcov_x_final v) (hcov_y v)
    · exact respects.of_extends Δy_ext₀
        (fun _ h => types_sub_y (types_sub_x h)) (fun _ h => h) fv_in_Λ
    · intro v τ hv hlookup
      rw [SMT.fv, List.mem_append] at hv
      exact hv.elim
        (fun hx => target_respects_x_final hx hlookup)
        (fun hy => target_respects_y hy hlookup)
    · let denPair : SMT.Dom.{u} :=
        ⟨Xenc.pair Yenc, SMTType.pair σx σy,
          ZFSet.pair_mem_prod.mpr ⟨hXenc, hYenc⟩⟩
      refine ⟨denPair, ?_, rfl, ?_, ?_⟩
      · simp only [denPair, SMT.Term.abstract, SMT.denote, Option.pure_def,
          Option.bind_eq_bind, hden_x_final, Option.bind_some, hden_y]
      · simpa [denPair, RDomCastAdmissible] using
          RDomCast.pair X_rel.toRDomCast Y_rel.toRDomCast
      · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt wf_alt
          Δ₀_alt_none respects_alt Δ₀_alt_dom T_alt hT_alt den_t_alt
        rw [B.Term.abstract, B.denote, Option.pure_def,
          Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t_alt
        obtain ⟨⟨X_alt, α_alt, hX_alt⟩, den_x_alt, hrest_alt⟩ :=
          den_t_alt
        dsimp at hrest_alt
        rw [Option.bind_eq_some_iff] at hrest_alt
        obtain ⟨⟨Y_alt, β_alt, hY_alt⟩, den_y_alt, hout_alt⟩ :=
          hrest_alt
        rw [Option.some_inj] at hout_alt
        dsimp at hout_alt
        injection hout_alt with T_alt_eq type_alt_eq
        subst T_alt
        injection type_alt_eq with pair_alt_eq _
        injection pair_alt_eq with α_alt_eq β_alt_eq
        subst α_alt β_alt

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
        have related_alt_y : RValuationCastAdmissibleOnFV Δ_alt Δx_alt y :=
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
              some (⟨Xenc_alt, σx, hXenc_alt⟩ : SMT.Dom) := by
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
        have hcov_pair_alt : RenamingContext.CoversFV Δy_alt
            (SMT.Term.pair x_enc y_enc) := by
          intro v hv
          rw [SMT.fv, List.mem_append] at hv
          exact hv.elim (hcov_x_alt_final v) (hcov_y_alt v)
        have Δy_alt_ext₀ :=
          RenamingContext.extends_trans Δy_alt_ext Δx_alt_ext
        let denPairAlt : SMT.Dom.{u} :=
          ⟨Xenc_alt.pair Yenc_alt, SMTType.pair σx σy,
            ZFSet.pair_mem_prod.mpr ⟨hXenc_alt, hYenc_alt⟩⟩
        refine ⟨Δy_alt, hcov_pair_alt, denPairAlt, Δy_alt_ext₀,
          related_alt.of_extends Δy_alt_ext₀, Δy_alt_none, ?_,
          ?_, Δy_alt_dom, ?_, rfl, ?_⟩
        · exact respects_alt.of_extends Δy_alt_ext₀
            (fun _ h => types_sub_y (types_sub_x h))
            (fun _ h => h) fv_in_Λ
        · intro v τ hv hlookup
          rw [SMT.fv, List.mem_append] at hv
          exact hv.elim
            (fun hx => target_respects_x_alt_final hx hlookup)
            (fun hy => target_respects_y_alt hy hlookup)
        · simp only [denPairAlt, SMT.Term.abstract, SMT.denote,
            Option.pure_def, Option.bind_eq_bind, hden_x_alt_final,
            Option.bind_some, hden_y_alt]
        · simpa [denPairAlt, RDomCastAdmissible] using
            RDomCast.pair X_alt_rel.toRDomCast Y_alt_rel.toRDomCast

set_option maxHeartbeats 3000000 in
theorem encodeTerm_rep_spec.checked_int_case.{u}
    (op : EncodeTermRepresentedArith.CheckedOp)
    (x y : B.Term)
    (x_ih : EncodeTermRepIH.{u} x)
    (y_ih : EncodeTermRepIH.{u} y)
    (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (typ_t : E.context ⊢ᴮ op.term x y : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (op.term x y), («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastAdmissibleOnFV «Δ» Δ₀ (op.term x y))
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
  rw [EncodeTermRepresentedArith.CheckedOp.encodeTerm_eq_run]
  unfold EncodeTermRepresentedArith.CheckedOp.run

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
  have hσx : σx = SMTType.int := castPath.source_eq_int cx
  subst σx

  have related_y : RValuationCastAdmissibleOnFV «Δ» Δx y :=
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
  have hσy : σy = SMTType.int := castPath.source_eq_int cy
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
  have typ_x_final : Sty.types ⊢ˢ x_enc : SMTType.int :=
    SMT.Typing.weakening types_sub_y typ_x_enc bv_x_not_final
  have hcov_x_final : RenamingContext.CoversFV Δy x_enc :=
    RenamingContext.coversFV_of_extends_of_coversFV Δy_ext hcov_x
  have hden_x_final :
      ⟦x_enc.abstract Δy hcov_x_final⟧ˢ =
        some (⟨Xenc, SMTType.int, hXenc⟩ : SMT.Dom) := by
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
  · exact ⟨castPath.reflexive SMTType.int⟩
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
      cases op <;> simp only [EncodeTermRepresentedArith.CheckedOp.smtTerm,
        SMT.fv, List.mem_append] at hv
      all_goals exact hv.elim (hcov_x_final v) (hcov_y v)
    · exact respects.of_extends Δy_ext₀
        (fun _ h => types_sub_y (types_sub_x h)) (fun _ h => h) fv_in_Λ
    · intro v τ hv hlookup
      cases op <;> simp only [EncodeTermRepresentedArith.CheckedOp.smtTerm,
        SMT.fv, List.mem_append] at hv
      all_goals
        exact hv.elim
          (fun hx => target_respects_x_final hx hlookup)
          (fun hy => target_respects_y hy hlookup)
    · let denOp : SMT.Dom.{u} :=
        ⟨op.eval Xenc Yenc, SMTType.int, op.eval_mem hXenc hYenc⟩
      refine ⟨denOp, ?_, rfl, ?_, ?_⟩
      · cases op <;> simp [denOp,
          EncodeTermRepresentedArith.CheckedOp.smtTerm,
          EncodeTermRepresentedArith.CheckedOp.eval,
          SMT.Term.abstract, SMT.denote, hden_x_final, hden_y]
      · simpa [denOp, RDomCastAdmissible] using
          op.rdomCast_eval X_rel.toRDomCast Y_rel.toRDomCast
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
        have related_alt_y : RValuationCastAdmissibleOnFV Δ_alt Δx_alt y :=
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
              some (⟨Xenc_alt, SMTType.int, hXenc_alt⟩ : SMT.Dom) := by
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
          cases op <;> simp only [EncodeTermRepresentedArith.CheckedOp.smtTerm,
            SMT.fv, List.mem_append] at hv
          all_goals exact hv.elim (hcov_x_alt_final v) (hcov_y_alt v)
        have Δy_alt_ext₀ :=
          RenamingContext.extends_trans Δy_alt_ext Δx_alt_ext
        let denOpAlt : SMT.Dom.{u} :=
          ⟨op.eval Xenc_alt Yenc_alt, SMTType.int,
            op.eval_mem hXenc_alt hYenc_alt⟩
        refine ⟨Δy_alt, hcov_op_alt, denOpAlt, Δy_alt_ext₀,
          related_alt.of_extends Δy_alt_ext₀, Δy_alt_none, ?_,
          ?_, Δy_alt_dom, ?_, rfl, ?_⟩
        · exact respects_alt.of_extends Δy_alt_ext₀
            (fun _ h => types_sub_y (types_sub_x h))
            (fun _ h => h) fv_in_Λ
        · intro v τ hv hlookup
          cases op <;> simp only [EncodeTermRepresentedArith.CheckedOp.smtTerm,
            SMT.fv, List.mem_append] at hv
          all_goals
            exact hv.elim
              (fun hx => target_respects_x_alt_final hx hlookup)
              (fun hy => target_respects_y_alt hy hlookup)
        · cases op <;> simp [denOpAlt,
            EncodeTermRepresentedArith.CheckedOp.smtTerm,
            EncodeTermRepresentedArith.CheckedOp.eval,
            SMT.Term.abstract, SMT.denote, hden_x_alt_final,
            hden_y_alt]
        · simpa [denOpAlt, RDomCastAdmissible] using
            op.rdomCast_eval X_alt_rel.toRDomCast Y_alt_rel.toRDomCast

set_option maxHeartbeats 3000000 in
theorem encodeTerm_rep_spec.le_case.{u}
    (x y : B.Term)
    (x_ih : EncodeTermRepIH.{u} x)
    (y_ih : EncodeTermRepIH.{u} y)
    (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
    (typ_t : E.context ⊢ᴮ x ≤ᴮ y : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv (x ≤ᴮ y), («Δ» v).isSome = true)
    {Δ₀ : SMT.RenamingContext.Context.{u}}
    (related : RValuationCastAdmissibleOnFV «Δ» Δ₀ (x ≤ᴮ y))
    {used : List SMT.𝒱}
    (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
    (Δ₀_dom : ∀ v, Δ₀ v ≠ none → v ∈ Λ)
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (den_t : ⟦(x ≤ᴮ y).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩)
    (vars_used : ∀ v ∈ (x ≤ᴮ y).vars, v ∈ used)
    (Λ_inv : ∀ v ∈ (x ≤ᴮ y).vars, v ∈ Λ → v ∈ E.context)
    (bv_nodup : (B.bv (x ≤ᴮ y)).Nodup)
    (respects : B.RenamingContext.RespectsTypeContextOnFV
      Δ₀ Λ (x ≤ᴮ y))
    (fv_in_Λ : ∀ v ∈ B.fv (x ≤ᴮ y), v ∈ Λ)
    (wf : B.RenWF E.context «Δ»)
    {n : ℕ} :
    ⦃fun ⟨E0, Λ'⟩ ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (x ≤ᴮ y) E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜EncodeTermRepPost (x ≤ᴮ y) α Λ «Δ» Δ₀ used T hT
        E t' σ E' Γ'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm_le_via_maplet]

  apply B.Typing.leE at typ_t
  obtain ⟨rfl, typ_x, typ_y⟩ := typ_t
  obtain ⟨X, hX, den_x, Y, hY, den_y, T_eq⟩ :=
    EncodeTermCorrectArith.Arith.denote_inv
      (.le) (B.Typing.le typ_x typ_y) Δ_fv den_t
  subst T

  let Δ_fv_pair : ∀ v ∈ B.fv (x ↦ᴮ y), («Δ» v).isSome = true :=
    fun v hv => Δ_fv v (by simpa [B.fv] using hv)
  have den_pair :
      ⟦(x ↦ᴮ y).abstract «Δ» Δ_fv_pair⟧ᴮ =
        some ⟨X.pair Y, ⟨BType.int ×ᴮ BType.int,
          ZFSet.pair_mem_prod.mpr ⟨hX, hY⟩⟩⟩ := by
    rw [B.Term.abstract, B.denote, Option.pure_def,
      Option.bind_eq_bind]
    have den_x' :
        ⟦x.abstract «Δ» (fun v hv => Δ_fv_pair v (by
          rw [B.fv, List.mem_append]
          exact Or.inl hv))⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩ := by
      simpa only [proof_irrel_heq] using den_x
    have den_y' :
        ⟦y.abstract «Δ» (fun v hv => Δ_fv_pair v (by
          rw [B.fv, List.mem_append]
          exact Or.inr hv))⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩ := by
      simpa only [proof_irrel_heq] using den_y
    rw [den_x', Option.bind_some, den_y']
    rfl

  mspec encodeTerm_rep_spec.maplet_case x y x_ih y_ih E
    (B.Typing.maplet typ_x typ_y) Δ_fv_pair
    (by simpa [B.fv] using related)
    Δ₀_none_out Δ₀_dom den_pair
    (fun v hv => vars_used v (by
      simpa [B.Term.vars, B.fv, B.bv] using hv))
    (fun v hv => Λ_inv v (by
      simpa [B.Term.vars, B.fv, B.bv] using hv))
    (by simpa [B.bv] using bv_nodup)
    (by simpa [B.fv] using respects)
    (fun v hv => fv_in_Λ v (by simpa [B.fv] using hv)) wf
    (n := St.env.freshvarsc)
  rename_i out_pair
  obtain ⟨p, σp⟩ := out_pair
  mrename_i pre
  mintro ∀St'
  mpure pre
  dsimp at pre
  obtain ⟨used_sub, types_sub, keys_sub, covers_used,
    path_pair, typ_pair, shape_pair, preserves,
    Δp, hcov_pair, Δp_ext, related_p, Δp_none, respects_p,
    target_respects_p, Δp_dom,
    denPair, hden_pair, hdenPair_type, pair_rel, pair_total⟩ := pre
  obtain ⟨x_enc, y_enc, σx_shape, σy_shape, hp, hσp⟩ := shape_pair
  subst p
  subst σp
  focus
    rw [hσp] at path_pair typ_pair pair_total
    obtain ⟨σx, σy, hpair_type, typ_x_enc, typ_y_enc⟩ :=
      SMT.Typing.pairE typ_pair
    injection hpair_type with hσx_type hσy_type
    subst σx
    subst σy
    obtain ⟨cpair⟩ := path_pair
    obtain ⟨hσx, hσy⟩ := castPath.source_pair_eq_int cpair
    subst σx_shape
    subst σy_shape

    have hcov_x : RenamingContext.CoversFV Δp x_enc := by
      intro v hv
      exact hcov_pair v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inl hv)
    have hcov_y : RenamingContext.CoversFV Δp y_enc := by
      intro v hv
      exact hcov_pair v (by
        rw [SMT.fv, List.mem_append]
        exact Or.inr hv)
    obtain ⟨denX, denY, hden_x_enc, hden_y_enc, denPair_eq⟩ :=
      denote_pair_inv hcov_pair hden_pair
    rw [denPair_eq] at hσp pair_rel
    rcases denX with ⟨Xenc, τx, hXenc⟩
    rcases denY with ⟨Yenc, τy, hYenc⟩
    dsimp at hσp
    injection hσp with hτx hτy
    subst τx
    subst τy
    have component_rel := RDomCast.of_pair
      (hX := hX) (hY := hY) (hX' := hXenc) (hY' := hYenc)
      (by simpa using pair_rel.toRDomCast)
    have X_rel := component_rel.1
    have Y_rel := component_rel.2

    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    · exact used_sub
    · exact types_sub
    · exact keys_sub
    · simpa [B.fv] using covers_used
    · exact ⟨castPath.reflexive SMTType.bool⟩
    · exact SMT.Typing.le St'.types x_enc y_enc typ_x_enc typ_y_enc
    · trivial
    · simpa [B.Term.vars, B.fv, B.bv] using preserves
    · refine ⟨Δp, ?_, Δp_ext, (by simpa [B.fv] using related_p),
        Δp_none, (by simpa [B.fv] using respects_p), ?_, Δp_dom, ?_⟩
      · intro v hv
        rw [SMT.fv, List.mem_append] at hv
        exact hv.elim (hcov_x v) (hcov_y v)
      · intro v τ hv hlookup
        exact target_respects_p (by simpa [SMT.fv] using hv) hlookup
      · let denLe : SMT.Dom.{u} :=
          ⟨Xenc ≤ᶻ Yenc, SMTType.bool,
            overloadBinOp_mem hXenc hYenc⟩
        refine ⟨denLe, ?_, rfl, ?_, ?_⟩
        · simp [denLe, SMT.Term.abstract, SMT.denote,
            hden_x_enc, hden_y_enc]
        · simpa [denLe, RDomCastAdmissible] using
            rdomCast_le X_rel Y_rel
        · intro Δ_alt Δ_fv_alt Δ₀_alt related_alt wf_alt
            Δ₀_alt_none respects_alt Δ₀_alt_dom T_alt hT_alt den_t_alt
          obtain ⟨X_alt, hX_alt, den_x_alt, Y_alt, hY_alt,
              den_y_alt, T_alt_eq⟩ :=
            EncodeTermCorrectArith.Arith.denote_inv
              (.le) (B.Typing.le typ_x typ_y) Δ_fv_alt den_t_alt
          subst T_alt
          let Δ_fv_pair_alt :
              ∀ v ∈ B.fv (x ↦ᴮ y), (Δ_alt v).isSome = true :=
            fun v hv => Δ_fv_alt v (by simpa [B.fv] using hv)
          have den_pair_alt :
              ⟦(x ↦ᴮ y).abstract Δ_alt Δ_fv_pair_alt⟧ᴮ =
                some ⟨X_alt.pair Y_alt,
                  ⟨BType.int ×ᴮ BType.int,
                    ZFSet.pair_mem_prod.mpr ⟨hX_alt, hY_alt⟩⟩⟩ := by
            rw [B.Term.abstract, B.denote, Option.pure_def,
              Option.bind_eq_bind]
            have den_x_alt' :
                ⟦x.abstract Δ_alt (fun v hv => Δ_fv_pair_alt v (by
                  rw [B.fv, List.mem_append]
                  exact Or.inl hv))⟧ᴮ =
                  some ⟨X_alt, ⟨BType.int, hX_alt⟩⟩ := by
              simpa only [proof_irrel_heq] using den_x_alt
            have den_y_alt' :
                ⟦y.abstract Δ_alt (fun v hv => Δ_fv_pair_alt v (by
                  rw [B.fv, List.mem_append]
                  exact Or.inr hv))⟧ᴮ =
                  some ⟨Y_alt, ⟨BType.int, hY_alt⟩⟩ := by
              simpa only [proof_irrel_heq] using den_y_alt
            rw [den_x_alt', Option.bind_some, den_y_alt']
            rfl
          obtain ⟨Δp_alt, hcov_pair_alt, denPairAlt, Δp_alt_ext,
              related_p_alt, Δp_alt_none, respects_p_alt,
              target_respects_p_alt, Δp_alt_dom,
              hden_pair_alt, hdenPairAlt_type, pair_alt_rel⟩ :=
            pair_total Δ_alt Δ_fv_pair_alt Δ₀_alt
              (by simpa [B.fv] using related_alt) wf_alt Δ₀_alt_none
              (by simpa [B.fv] using respects_alt) Δ₀_alt_dom
              (X_alt.pair Y_alt)
              (ZFSet.pair_mem_prod.mpr ⟨hX_alt, hY_alt⟩) den_pair_alt
          have hcov_x_alt : RenamingContext.CoversFV Δp_alt x_enc := by
            intro v hv
            exact hcov_pair_alt v (by
              rw [SMT.fv, List.mem_append]
              exact Or.inl hv)
          have hcov_y_alt : RenamingContext.CoversFV Δp_alt y_enc := by
            intro v hv
            exact hcov_pair_alt v (by
              rw [SMT.fv, List.mem_append]
              exact Or.inr hv)
          obtain ⟨denXAlt, denYAlt, hden_x_alt_enc,
              hden_y_alt_enc, denPairAlt_eq⟩ :=
            denote_pair_inv hcov_pair_alt hden_pair_alt
          rw [denPairAlt_eq] at hdenPairAlt_type pair_alt_rel
          rcases denXAlt with ⟨Xenc_alt, τx_alt, hXenc_alt⟩
          rcases denYAlt with ⟨Yenc_alt, τy_alt, hYenc_alt⟩
          dsimp at hdenPairAlt_type
          injection hdenPairAlt_type with hτx_alt hτy_alt
          subst τx_alt
          subst τy_alt
          have component_alt_rel := RDomCast.of_pair
            (hX := hX_alt) (hY := hY_alt)
            (hX' := hXenc_alt) (hY' := hYenc_alt)
            (by simpa using pair_alt_rel.toRDomCast)
          let denLeAlt : SMT.Dom.{u} :=
            ⟨Xenc_alt ≤ᶻ Yenc_alt, SMTType.bool,
              overloadBinOp_mem hXenc_alt hYenc_alt⟩
          have hcov_le_alt : RenamingContext.CoversFV Δp_alt
              (SMT.Term.le x_enc y_enc) := by
            intro v hv
            rw [SMT.fv, List.mem_append] at hv
            exact hv.elim (hcov_x_alt v) (hcov_y_alt v)
          refine ⟨Δp_alt, hcov_le_alt, denLeAlt, Δp_alt_ext,
            (by simpa [B.fv] using related_p_alt), Δp_alt_none,
            (by simpa [B.fv] using respects_p_alt), ?_, Δp_alt_dom,
            ?_, rfl, ?_⟩
          · intro v τ hv hlookup
            exact target_respects_p_alt
              (by simpa [SMT.fv] using hv) hlookup
          · simp [denLeAlt, SMT.Term.abstract, SMT.denote,
              hden_x_alt_enc, hden_y_alt_enc]
          · simpa [denLeAlt, RDomCastAdmissible] using
              rdomCast_le component_alt_rel.1 component_alt_rel.2
