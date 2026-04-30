import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Axioms

open Std.Do B SMT ZFSet Classical

namespace EncodeTermCorrectArith.Arith

inductive BinOp where
  | add
  | sub
  | mul
  | le

namespace BinOp

def term : BinOp → B.Term → B.Term → B.Term
  | .add => (· +ᴮ ·)
  | .sub => (· -ᴮ ·)
  | .mul => (· *ᴮ ·)
  | .le => (· ≤ᴮ ·)

def resultType : BinOp → BType
  | .add | .sub | .mul => .int
  | .le => .bool

open Classical in
noncomputable def eval : BinOp → ZFSet → ZFSet → ZFSet
  | .add => (· +ᶻ ·)
  | .sub => (· -ᶻ ·)
  | .mul => (· *ᶻ ·)
  | .le => (· ≤ᶻ ·)

theorem typingE {Γ : B.TypeContext} {x y : B.Term} {op : BinOp} :
    Γ ⊢ᴮ op.term x y : op.resultType → Γ ⊢ᴮ x : .int ∧ Γ ⊢ᴮ y : .int := by
  cases op <;> intro h
  · exact (Typing.addE h).2
  · exact (Typing.subE h).2
  · exact (Typing.mulE h).2
  · exact (Typing.leE h).2

def leftFVCert {x y : B.Term} {«Δ» : B.𝒱 → Option B.Dom}
    (op : BinOp) (Δ_fv : ∀ v ∈ B.fv (op.term x y), («Δ» v).isSome = true) :
    ∀ v ∈ B.fv x, («Δ» v).isSome = true := by
  cases op
  all_goals
    intro v hv
    exact Δ_fv v (by rw [term, B.fv, List.mem_append]; exact Or.inl hv)

def rightFVCert {x y : B.Term} {«Δ» : B.𝒱 → Option B.Dom}
    (op : BinOp) (Δ_fv : ∀ v ∈ B.fv (op.term x y), («Δ» v).isSome = true) :
    ∀ v ∈ B.fv y, («Δ» v).isSome = true := by
  cases op
  all_goals
    intro v hv
    exact Δ_fv v (by rw [term, B.fv, List.mem_append]; exact Or.inr hv)

end BinOp

theorem denote_inv.{u_1} (op : BinOp) {Γ : B.TypeContext} {x y : B.Term}
    (typ_t : Γ ⊢ᴮ op.term x y : op.resultType) {«Δ» : B.𝒱 → Option B.Dom}
    (Δ_fv : ∀ v ∈ B.fv (op.term x y), («Δ» v).isSome = true)
    {T : ZFSet.{u_1}} {hT : T ∈ ⟦op.resultType⟧ᶻ}
    (den_t : ⟦(op.term x y).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨op.resultType, hT⟩⟩) :
    ∃ X, ∃ hX : X ∈ ⟦BType.int⟧ᶻ,
      ⟦x.abstract «Δ» (op.leftFVCert Δ_fv)⟧ᴮ = some ⟨X, ⟨BType.int, hX⟩⟩ ∧
        ∃ Y, ∃ hY : Y ∈ ⟦BType.int⟧ᶻ,
          ⟦y.abstract «Δ» (op.rightFVCert Δ_fv)⟧ᴮ = some ⟨Y, ⟨BType.int, hY⟩⟩ ∧
            op.eval X Y = T := by
  classical
  obtain ⟨typ_x, typ_y⟩ := op.typingE typ_t
  cases op <;> simp [BinOp.term, BinOp.resultType, BinOp.eval] at typ_t den_t ⊢
  all_goals
    rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
    obtain ⟨⟨X, αx, hX⟩, den_x, eq⟩ := den_t
    have := denote_welltyped_eq
      (t := x.abstract («Δ» := «Δ»)
        (fun v hv ↦ Δ_fv v (by
          simpa [BinOp.term, B.fv, List.mem_append] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y))))
      ?_ den_x
    on_goal 2 =>
      use Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, .int
      exact @Typing.of_abstract (B.Dom) («Δ» := «Δ») ?_ x Γ .int
        (fun v hv ↦ Δ_fv v (by
          simpa [BinOp.term, B.fv, List.mem_append] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y)))
        typ_x
    dsimp at this
    subst αx

    dsimp at eq
    rw [Option.bind_eq_some_iff] at eq
    obtain ⟨⟨Y, βx, hY⟩, den_y, eq⟩ := eq
    have := denote_welltyped_eq
      (t := y.abstract («Δ» := «Δ»)
        (fun v hv ↦ Δ_fv v (by
          simpa [BinOp.term, B.fv, List.mem_append] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y))))
      ?_ den_y
    on_goal 2 =>
      use Γ.abstract («Δ» := «Δ»), WFTC.of_abstract, .int
      exact @Typing.of_abstract (B.Dom) («Δ» := «Δ») ?_ y Γ .int
        (fun v hv ↦ Δ_fv v (by
          simpa [BinOp.term, B.fv, List.mem_append] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y)))
        typ_y
    dsimp at this
    subst βx

    rw [Option.some_inj] at eq
    injection eq with T_eq _
    refine ⟨X, ?_⟩
    constructor
    · exact ⟨hX, den_x⟩
    · refine ⟨Y, ?_⟩
      constructor
      · exact ⟨hY, den_y⟩
      · exact T_eq

end EncodeTermCorrectArith.Arith

theorem encodeTerm_spec.maplet.{u_1} {Λ : SMT.TypeContext} (x y : B.Term)
  (x_ih : ∀ (E : B.Env) {α : BType}, E.context ⊢ᴮ x : α →
    ∀ {«Δ» : B.𝒱 → Option B.Dom} (Δ_fv : ∀ v ∈ B.fv x, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
      {hT : T ∈ ⟦α⟧ᶻ}, ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ → ∀ {n : ℕ},
          ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
            encodeTerm x E
          ⦃⇓? (t', σ) ⟨E', Γ'⟩ =>
            ⌜n ≤ E'.freshvarsc ∧
                E'.freshvarsc ≤  Γ'.keys.length ∧
                  Γ' = Λ ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                          ∃ denT',
                            ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                              ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄)
  (y_ih : ∀ (E : B.Env) {α : BType}, E.context ⊢ᴮ y : α →
    ∀ {«Δ» : B.𝒱 → Option B.Dom} (Δ_fv : ∀ v ∈ B.fv y, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
      {hT : T ∈ ⟦α⟧ᶻ}, ⟦y.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ → ∀ {n : ℕ},
        ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
          encodeTerm y E
        ⦃⇓? (t', σ) ⟨E', Γ'⟩ =>
          ⌜n ≤ E'.freshvarsc ∧
              E'.freshvarsc ≤  Γ'.keys.length ∧
                Γ' = Λ ∧
                  σ = α.toSMTType ∧
                    Γ' ⊢ˢ t' : σ ∧
                      ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                        ∃ denT',
                          ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                            ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄)
  (E : B.Env) {α : BType} (typ_t : E.context ⊢ᴮ x ↦ᴮ y : α) {«Δ» : B.𝒱 → Option B.Dom}
  (Δ_fv : ∀ v ∈ B.fv (x ↦ᴮ y), («Δ» v).isSome = true) {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x ↦ᴮ y).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) {n : ℕ} :
  ⦃fun ⟨E, Λ'⟩ => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
    encodeTerm (x ↦ᴮ y) E
  ⦃⇓? (t', σ) ⟨E', Γ'⟩ =>
    ⌜n ≤ E'.freshvarsc ∧
        E'.freshvarsc ≤  Γ'.keys.length ∧
          Γ' = Λ ∧
            σ = α.toSMTType ∧
              Γ' ⊢ˢ t' : σ ∧
                ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                  ∃ denT',
                    ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀σ
  mpure pre
  obtain ⟨rfl, hlen⟩ := pre
  rw [encodeTerm]

  apply Typing.mapletE at typ_t
  obtain ⟨α, β, rfl, typ_x, typ_y⟩ := typ_t

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, α', hX⟩, den_x, eq⟩ := den_t
  dsimp at eq
  rw [Option.bind_eq_some_iff] at eq
  obtain ⟨⟨Y, β', hY⟩, den_y, eq⟩ := eq
  rw [Option.some_inj] at eq
  dsimp at eq
  injection eq with T_eq heq
  subst T
  injection heq with eq heq
  injection eq with α'_eq β'_eq
  subst α' β'

  specialize x_ih (n := n) E typ_x («Δ» := «Δ») (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inl hv)) den_x
  mspec x_ih
  rename_i out_x
  obtain ⟨x_enc, α'⟩ := out_x
  mrename_i pre
  mintro ∀σ_x
  mpure pre
  dsimp at pre
  obtain ⟨n_le_σ_x_freshc, σ_x_freshc_le, σ_types_eq, rfl, typ_x_enc, hΔ_x_enc, ⟨Xenc, _, hXenc⟩, den_x_enc, ⟨rfl, retract_α_X_enc_eq_X⟩⟩ := pre

  specialize y_ih (n := σ_x.env.freshvarsc) E typ_y («Δ» := «Δ») (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inr hv)) den_y
  mspec y_ih
  rename_i out_y
  obtain ⟨y_enc, β'⟩ := out_y
  mrename_i pre
  mintro ∀σ_y
  mpure pre
  dsimp at pre
  obtain ⟨n_le, σ_y_freshc_le, pre, rfl, typ_y_enc, hΔ_y_enc, ⟨Yenc, _, hYenc⟩, den_y_enc, ⟨rfl, retract_β_Y_enc_eq_Y⟩⟩ := pre

  mspec Std.Do.Spec.pure
  mpure_intro
  and_intros
  · trans σ_x.env.freshvarsc
    · exact n_le_σ_x_freshc
    · exact n_le
  · exact σ_y_freshc_le
  · exact pre
  · congr
  · apply Typing.pair
    · rw [pre, ←σ_types_eq]
      exact typ_x_enc
    · exact typ_y_enc
  · exists ?_
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hΔ_x_enc v hv
      · exact hΔ_y_enc v hv
    · use ⟨Xenc.pair Yenc, α.toSMTType.pair β.toSMTType, by rw [SMTType.toZFSet, pair_mem_prod]; exact ⟨hXenc, hYenc⟩⟩
      and_intros
      · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, den_x_enc, Option.bind_some, den_y_enc]
        rfl
      · congr
      · unfold retract
        rw [π₁_pair, π₂_pair, pair_inj]
        exact ⟨retract_α_X_enc_eq_X, retract_β_Y_enc_eq_Y⟩

theorem encodeTerm_spec.add.{u_1} {Λ : SMT.TypeContext} (x y : B.Term)
  (x_ih : ∀ (E : B.Env) {α : BType}, E.context ⊢ᴮ x : α →
    ∀ {«Δ» : B.𝒱 → Option B.Dom} (Δ_fv : ∀ v ∈ B.fv x, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
      {hT : T ∈ ⟦α⟧ᶻ}, ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ → ∀ {n : ℕ},
        ⦃fun ⟨E, Λ'⟩ => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
          encodeTerm x E
        ⦃⇓? (t', σ) ⟨E', Γ'⟩ =>
          ⌜n ≤ E'.freshvarsc ∧
              E'.freshvarsc ≤  Γ'.keys.length ∧
                Γ' = Λ ∧
                  σ = α.toSMTType ∧
                    Γ' ⊢ˢ t' : σ ∧
                      ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                        ∃ denT',
                          ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                            ⟨T, α, hT⟩ ≘ᶻ denT'⌝⦄)
  (y_ih : ∀ (E : B.Env) {α : BType}, E.context ⊢ᴮ y : α →
    ∀ {«Δ» : B.𝒱 → Option B.Dom} (Δ_fv : ∀ v ∈ B.fv y, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
      {hT : T ∈ ⟦α⟧ᶻ}, ⟦y.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ → ∀ {n : ℕ},
        ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
          encodeTerm y E
        ⦃⇓? (t', σ) ⟨E', Γ'⟩ =>
          ⌜n ≤ E'.freshvarsc ∧
              E'.freshvarsc ≤  Γ'.keys.length ∧
                Γ' = Λ ∧
                  σ = α.toSMTType ∧
                    Γ' ⊢ˢ t' : σ ∧
                      ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                        ∃ denT',
                          ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                            ⟨T, α, hT⟩ ≘ᶻ denT'⌝⦄)
  (E : B.Env) {α : BType} (typ_t : E.context ⊢ᴮ x +ᴮ y : α) {«Δ» : B.𝒱 → Option B.Dom}
  (Δ_fv : ∀ v ∈ B.fv (x +ᴮ y), («Δ» v).isSome = true) {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x +ᴮ y).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) {n : ℕ} :
  ⦃fun ⟨E, Λ'⟩ => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤  Λ'.keys.length⌝⦄
    encodeTerm (x +ᴮ y) E
  ⦃⇓? (t', σ) ⟨E', Γ'⟩ =>
    ⌜n ≤ E'.freshvarsc ∧
        E'.freshvarsc ≤  Γ'.keys.length ∧
          Γ' = Λ ∧
            σ = α.toSMTType ∧
              Γ' ⊢ˢ t' : σ ∧
                ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                  ∃ denT',
                    ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀σ
  mpure pre
  rw [encodeTerm]

  apply B.Typing.addE at typ_t
  obtain ⟨rfl, typ_x, typ_y⟩ := typ_t

  obtain ⟨X, hX, den_x, Y, hY, den_y, T_eq⟩ :=
    EncodeTermCorrectArith.Arith.denote_inv
      (op := .add) (Γ := E.context) (x := x) (y := y) («Δ» := «Δ»)
      (typ_t := B.Typing.add typ_x typ_y) (Δ_fv := Δ_fv) (T := T) (hT := hT) den_t
  subst T

  specialize x_ih (n := n) E typ_x («Δ» := «Δ»)
    (EncodeTermCorrectArith.Arith.BinOp.leftFVCert (x := x) (y := y) (op := .add) Δ_fv)
    den_x
  mspec x_ih
  rename_i out_x
  obtain ⟨x_enc, α'⟩ := out_x
  mrename_i pre
  mintro ∀σ_x
  mpure pre
  dsimp at pre
  obtain ⟨n_le, σ_x_freshc_le, rfl, rfl, typ_x_enc, hΔ_x_enc, ⟨Xenc, _, hXenc⟩, den_x_enc, ⟨rfl, retract_α_X_enc_eq_X⟩⟩ := pre

  conv =>
    enter [2,1,1]
    rw [BType.toSMTType]
    dsimp

  specialize y_ih (n := σ_x.env.freshvarsc) E typ_y («Δ» := «Δ»)
    (EncodeTermCorrectArith.Arith.BinOp.rightFVCert (x := x) (y := y) (op := .add) Δ_fv)
    den_y
  mspec y_ih
  rename_i out_y
  obtain ⟨y_enc, β'⟩ := out_y
  mrename_i pre
  mintro ∀σ_y
  mpure pre
  dsimp at pre
  obtain ⟨σ_x_freshc_le_σ_y_freshc, σ_y_freshc_le, pre, rfl, typ_y_enc, hΔ_y_enc, ⟨Yenc, _, hYenc⟩, den_y_enc, ⟨rfl, retract_β_Y_enc_eq_Y⟩⟩ := pre

  mspec Std.Do.Spec.pure
  mpure_intro
  and_intros
  · trans σ_x.env.freshvarsc
    · exact n_le
    · exact σ_x_freshc_le_σ_y_freshc
  · exact σ_y_freshc_le
  · exact pre
  · congr
  · apply SMT.Typing.add
    · rw [pre]
      exact typ_x_enc
    · exact typ_y_enc
  · exists ?_
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hΔ_x_enc v hv
      · exact hΔ_y_enc v hv
    · use ⟨Xenc +ᶻ Yenc, .int, overloadBinOp_mem hXenc hYenc⟩
      and_intros
      · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, den_x_enc, Option.bind_some, den_y_enc]
        rfl
      · congr
      · dsimp [retract] at retract_α_X_enc_eq_X retract_β_Y_enc_eq_Y ⊢
        subst Xenc Yenc
        rfl

theorem encodeTerm_spec.sub.{u_1} {Λ : SMT.TypeContext} (x y : B.Term)
  (x_ih :
    ∀ (E : B.Env) {α : BType},
      E.context ⊢ᴮ x : α →
        ∀ {«Δ» : B.𝒱 → _root_.Option B.Dom} (Δ_fv : ∀ v ∈ B.fv x, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
          {hT : T ∈ ⟦α⟧ᶻ},
          ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
            ∀ {n : ℕ},
              ⦃fun x =>
                match x with
                | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ (AList.keys Λ').length⌝⦄
                encodeTerm x E ⦃PostCond.mayThrow fun x x_1 =>
                  match x with
                  | (t', σ) =>
                    match x_1 with
                    | { env := E', types := Γ' } =>
                      ⌜n ≤ E'.freshvarsc ∧
                          E'.freshvarsc ≤ (AList.keys Γ').length ∧
                            Γ' = Λ ∧
                              σ = α.toSMTType ∧
                                Γ' ⊢ˢ t' : σ ∧
                                  ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                                    ∃ denT',
                                      ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄)
  (y_ih :
    ∀ (E : B.Env) {α : BType},
      E.context ⊢ᴮ y : α →
        ∀ {«Δ» : B.𝒱 → _root_.Option B.Dom} (Δ_fv : ∀ v ∈ B.fv y, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
          {hT : T ∈ ⟦α⟧ᶻ},
          ⟦y.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
            ∀ {n : ℕ},
              ⦃fun x =>
                match x with
                | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ (AList.keys Λ').length⌝⦄
                encodeTerm y E ⦃PostCond.mayThrow fun x x_1 =>
                  match x with
                  | (t', σ) =>
                    match x_1 with
                    | { env := E', types := Γ' } =>
                      ⌜n ≤ E'.freshvarsc ∧
                          E'.freshvarsc ≤ (AList.keys Γ').length ∧
                            Γ' = Λ ∧
                              σ = α.toSMTType ∧
                                Γ' ⊢ˢ t' : σ ∧
                                  ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                                    ∃ denT',
                                      ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄)
  (E : B.Env) {α : BType} (typ_t : E.context ⊢ᴮ x -ᴮ y : α) {«Δ» : B.𝒱 → _root_.Option B.Dom}
  (Δ_fv : ∀ v ∈ B.fv (x -ᴮ y), («Δ» v).isSome = true) {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x -ᴮ y).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ (AList.keys Λ').length⌝⦄
    encodeTerm (x -ᴮ y) E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜n ≤ E'.freshvarsc ∧
              E'.freshvarsc ≤ (AList.keys Γ').length ∧
                Γ' = Λ ∧
                  σ = α.toSMTType ∧
                    Γ' ⊢ˢ t' : σ ∧
                      ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                        ∃ denT',
                          ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀σ
  mpure pre
  rw [encodeTerm]
  apply B.Typing.subE at typ_t
  obtain ⟨rfl, typ_x, typ_y⟩ := typ_t
  obtain ⟨X, hX, den_x, Y, hY, den_y, T_eq⟩ :=
    EncodeTermCorrectArith.Arith.denote_inv
      (op := .sub) (Γ := E.context) (x := x) (y := y) («Δ» := «Δ»)
      (typ_t := B.Typing.sub typ_x typ_y) (Δ_fv := Δ_fv) (T := T) (hT := hT) den_t
  subst T

  specialize x_ih (n := n) E typ_x («Δ» := «Δ»)
    (EncodeTermCorrectArith.Arith.BinOp.leftFVCert (x := x) (y := y) (op := .sub) Δ_fv)
    den_x
  mspec x_ih
  rename_i out_x
  obtain ⟨x_enc, α'⟩ := out_x
  mrename_i pre
  mintro ∀σ_x
  mpure pre
  dsimp at pre
  obtain ⟨n_le, σ_x_freshc_le, rfl, rfl, typ_x_enc, hΔ_x_enc, ⟨Xenc, _, hXenc⟩, den_x_enc, ⟨rfl, retract_α_X_enc_eq_X⟩⟩ := pre
  conv =>
    enter [2,1,1]
    rw [BType.toSMTType]
    dsimp

  specialize y_ih (n := σ_x.env.freshvarsc) E typ_y («Δ» := «Δ»)
    (EncodeTermCorrectArith.Arith.BinOp.rightFVCert (x := x) (y := y) (op := .sub) Δ_fv)
    den_y
  mspec y_ih
  rename_i out_y
  obtain ⟨y_enc, β'⟩ := out_y
  mrename_i pre
  mintro ∀σ_y
  mpure pre
  dsimp at pre
  obtain ⟨σ_x_freshc_le_σ_y_freshc, σ_y_freshc_le, pre, rfl, typ_y_enc, hΔ_y_enc, ⟨Yenc, _, hYenc⟩, den_y_enc, ⟨rfl, retract_β_Y_enc_eq_Y⟩⟩ := pre
  mspec Std.Do.Spec.pure
  mpure_intro

  and_intros
  · trans σ_x.env.freshvarsc
    · exact n_le
    · exact σ_x_freshc_le_σ_y_freshc
  · exact σ_y_freshc_le
  · exact pre
  · rfl
  · apply SMT.Typing.sub
    · rw [pre]
      exact typ_x_enc
    · exact typ_y_enc
  · exists ?_
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hΔ_x_enc v hv
      · exact hΔ_y_enc v hv
    · use ⟨Xenc -ᶻ Yenc, .int, overloadBinOp_mem hXenc hYenc⟩
      and_intros
      · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, den_x_enc, Option.bind_some, den_y_enc]
        rfl
      · congr
      · dsimp [retract] at retract_α_X_enc_eq_X retract_β_Y_enc_eq_Y ⊢
        subst Xenc Yenc
        rfl

theorem encodeTerm_spec.mul.{u_1} {Λ : SMT.TypeContext} (x y : B.Term)
  (x_ih :
    ∀ (E : B.Env) {α : BType},
      E.context ⊢ᴮ x : α →
        ∀ {«Δ» : B.𝒱 → _root_.Option B.Dom} (Δ_fv : ∀ v ∈ B.fv x, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
          {hT : T ∈ ⟦α⟧ᶻ},
          ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
            ∀ {n : ℕ},
              ⦃fun x =>
                match x with
                | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ (AList.keys Λ').length⌝⦄
                encodeTerm x E ⦃PostCond.mayThrow fun x x_1 =>
                  match x with
                  | (t', σ) =>
                    match x_1 with
                    | { env := E', types := Γ' } =>
                      ⌜n ≤ E'.freshvarsc ∧
                          E'.freshvarsc ≤ (AList.keys Γ').length ∧
                            Γ' = Λ ∧
                              σ = α.toSMTType ∧
                                Γ' ⊢ˢ t' : σ ∧
                                  ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                                    ∃ denT',
                                      ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄)
  (y_ih :
    ∀ (E : B.Env) {α : BType},
      E.context ⊢ᴮ y : α →
        ∀ {«Δ» : B.𝒱 → _root_.Option B.Dom} (Δ_fv : ∀ v ∈ B.fv y, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
          {hT : T ∈ ⟦α⟧ᶻ},
          ⟦y.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
            ∀ {n : ℕ},
              ⦃fun x =>
                match x with
                | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ (AList.keys Λ').length⌝⦄
                encodeTerm y E ⦃PostCond.mayThrow fun x x_1 =>
                  match x with
                  | (t', σ) =>
                    match x_1 with
                    | { env := E', types := Γ' } =>
                      ⌜n ≤ E'.freshvarsc ∧
                          E'.freshvarsc ≤ (AList.keys Γ').length ∧
                            Γ' = Λ ∧
                              σ = α.toSMTType ∧
                                Γ' ⊢ˢ t' : σ ∧
                                  ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                                    ∃ denT',
                                      ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄)
  (E : B.Env) {α : BType} (typ_t : E.context ⊢ᴮ x *ᴮ y : α) {«Δ» : B.𝒱 → _root_.Option B.Dom}
  (Δ_fv : ∀ v ∈ B.fv (x *ᴮ y), («Δ» v).isSome = true) {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x *ᴮ y).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ n ≤ (AList.keys Λ').length⌝⦄
    encodeTerm (x *ᴮ y) E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜n ≤ E'.freshvarsc ∧
              E'.freshvarsc ≤ (AList.keys Γ').length ∧
                Γ' = Λ ∧
                  σ = α.toSMTType ∧
                    Γ' ⊢ˢ t' : σ ∧
                      ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
                        ∃ denT',
                          ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀σ
  mpure pre
  rw [encodeTerm]
  apply B.Typing.mulE at typ_t
  obtain ⟨rfl, typ_x, typ_y⟩ := typ_t
  obtain ⟨X, hX, den_x, Y, hY, den_y, T_eq⟩ :=
    EncodeTermCorrectArith.Arith.denote_inv
      (op := .mul) (Γ := E.context) (x := x) (y := y) («Δ» := «Δ»)
      (typ_t := B.Typing.mul typ_x typ_y) (Δ_fv := Δ_fv) (T := T) (hT := hT) den_t
  subst T

  specialize x_ih (n := n) E typ_x («Δ» := «Δ»)
    (EncodeTermCorrectArith.Arith.BinOp.leftFVCert (x := x) (y := y) (op := .mul) Δ_fv)
    den_x
  mspec x_ih
  rename_i out_x
  obtain ⟨x_enc, α'⟩ := out_x
  mrename_i pre
  mintro ∀σ_x
  mpure pre
  dsimp at pre
  obtain ⟨n_le, σ_x_freshc_le, rfl, rfl, typ_x_enc, hΔ_x_enc, ⟨Xenc, _, hXenc⟩, den_x_enc, ⟨rfl, retract_α_X_enc_eq_X⟩⟩ := pre
  conv =>
    enter [2,1,1]
    rw [BType.toSMTType]
    dsimp

  specialize y_ih (n := σ_x.env.freshvarsc) E typ_y («Δ» := «Δ»)
    (EncodeTermCorrectArith.Arith.BinOp.rightFVCert (x := x) (y := y) (op := .mul) Δ_fv)
    den_y
  mspec y_ih
  rename_i out_y
  obtain ⟨y_enc, β'⟩ := out_y
  mrename_i pre
  mintro ∀σ_y
  mpure pre
  dsimp at pre
  obtain ⟨σ_x_freshc_le_σ_y_freshc, σ_y_freshc_le, pre, rfl, typ_y_enc, hΔ_y_enc, ⟨Yenc, _, hYenc⟩, den_y_enc, ⟨rfl, retract_β_Y_enc_eq_Y⟩⟩ := pre
  mspec Std.Do.Spec.pure
  mpure_intro
  and_intros
  · trans σ_x.env.freshvarsc
    · exact n_le
    · exact σ_x_freshc_le_σ_y_freshc
  · exact σ_y_freshc_le
  · exact pre
  · rfl
  · apply SMT.Typing.mul
    · rw [pre]
      exact typ_x_enc
    · exact typ_y_enc
  · exists ?_
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hΔ_x_enc v hv
      · exact hΔ_y_enc v hv
    · use ⟨Xenc *ᶻ Yenc, .int, overloadBinOp_mem hXenc hYenc⟩
      and_intros
      · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, den_x_enc, Option.bind_some, den_y_enc]
        rfl
      · congr
      · dsimp [retract] at retract_α_X_enc_eq_X retract_β_Y_enc_eq_Y ⊢
        subst Xenc Yenc
        rfl

theorem encodeTerm_spec.maplet_case.{u} (fv_sub_typings : B.FvSubTypings) (x y : B.Term)
  (x_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ x : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv x, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» x →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ x.vars, v ∈ used) →
                      (∀ v ∈ x.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm x E ⦃PostCond.mayThrow fun x_1 x_2 =>
                              match x_1 with
                              | (t', σ) =>
                                match x_2 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars x ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv x → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» x ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv x, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt x →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦x.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (y_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ y : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv y, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» y →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦y.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ y.vars, v ∈ used) →
                      (∀ v ∈ y.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm y E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars y ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv y → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» y ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv y, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt y →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦y.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (E : B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ x ↦ᴮ y : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv (x ↦ᴮ y), («Δ» v).isSome = true) {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (x ↦ᴮ y)) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x ↦ᴮ y).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ (x ↦ᴮ y).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (x ↦ᴮ y).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (x ↦ᴮ y) E ⦃PostCond.mayThrow fun x_1 x_2 =>
      match x_1 with
      | (t', σ) =>
        match x_2 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (x ↦ᴮ y) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv (x ↦ᴮ y) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (x ↦ᴮ y) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv (x ↦ᴮ y), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (x ↦ᴮ y) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(x ↦ᴮ y).abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                    ∃ Δ'_alt,
                                                      ∃ (hcov_alt : RenamingContext.CoversFV Δ'_alt t'),
                                                        ∃ denT_alt,
                                                          RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                                                            (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                              (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                              ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                                                ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄ := by
  mstart
  mintro pre ∀σ
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm]

  apply Typing.mapletE at typ_t
  obtain ⟨αx, βx, rfl, typ_x, typ_y⟩ := typ_t

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at den_t
  obtain ⟨⟨X, α', hX⟩, den_x, eq⟩ := den_t
  dsimp at eq
  rw [Option.bind_eq_some_iff] at eq
  obtain ⟨⟨Y, β', hY⟩, den_y, eq⟩ := eq
  rw [Option.some_inj] at eq
  dsimp at eq
  injection eq with T_eq heq
  subst T
  injection heq with eq heq
  injection eq with α'_eq β'_eq
  subst α' β'

  have Δ₀_ext_x : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» x := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [B.fv] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y)) Δ₀_ext
  have Δ₀_ext_y : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» y := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [B.fv] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y)) Δ₀_ext

  mspec x_ih (E := E) (Λ := σ.types) (α := αx) typ_x
    («Δ» := «Δ»)
    (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inl hv))
    (Δ₀ := Δ₀) Δ₀_ext_x (used := used) Δ₀_none_out (T := X) (hT := hX)
    den_x (fun v hv => vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (fun v hv => Λ_inv v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (n := σ.env.freshvarsc)
  clear x_ih
  rename_i out_x
  obtain ⟨x_enc, σx⟩ := out_x
  mrename_i pre
  mintro ∀σ_x
  mpure pre
  dsimp at pre
  obtain ⟨St_used_sub_St', St_eq_St', St'_sub, x_cov_St', rfl, typ_x_enc, x_preserves,
    Δ', Δ'_covers_x, Δ'_extends_Δ₀, Δ'_ext_x, Δ'_none_out,
    ⟨Xenc, _, hXenc⟩, den_x_enc, ⟨rfl, retract_α_Xenc_eq_X⟩, x_ih_total⟩ := pre

  have Δ'_ext_y : RenamingContext.ExtendsOnSourceFV Δ' «Δ» y := by
    exact RenamingContext.extendsOnSourceFV_of_extends Δ'_extends_Δ₀ Δ₀_ext_y

  mspec y_ih (E := E) (Λ := σ_x.types) (α := βx) typ_y
    («Δ» := «Δ»)
    (fun v hv ↦ Δ_fv v (by rw [B.fv, List.mem_append]; exact Or.inr hv))
    (Δ₀ := Δ') Δ'_ext_y (used := σ_x.env.usedVars) Δ'_none_out (T := Y) (hT := hY)
    den_y (fun v hv => St_used_sub_St' (vars_used v (by
      simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
      rcases hv with h | h <;> [left; right] <;> exact .inr h)))
    (fun v hv hΛ => by
      have hv_maplet : v ∈ (x ↦ᴮ y).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      -- Need v ∈ E.context. Either v ∈ σ.types (use Λ_inv) or v ∉ σ.types (use x_preserves → v ∈ B.fv x → typing)
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_maplet hv_St
      · -- v ∉ σ.types but v ∈ σ_x.types: x_preserves contrapositive gives v ∈ B.fv x
        have hv_fv_x : v ∈ B.fv x := by
          by_contra h_neg
          exact absurd hΛ (x_preserves v (vars_used v hv_maplet) hv_St h_neg)
        exact _root_.B.Typing.typed_by_fv typ_x hv_fv_x)
    (n := σ_x.env.freshvarsc)
  clear y_ih
  rename_i out_y
  obtain ⟨y_enc, σy⟩ := out_y
  mrename_i pre
  mintro ∀σ_y
  mpure pre
  dsimp at pre
  obtain ⟨St'_used_sub_St'', St'_eq_St'', St''_sub, y_cov_St'', rfl, typ_y_enc, y_preserves,
    Δ'', Δ''_covers_y, Δ''_extends_Δ', Δ''_ext_y, Δ''_none_out,
    ⟨Yenc, _, hYenc⟩, den_y_enc, ⟨rfl, retract_β_Yenc_eq_Y⟩, y_ih_total⟩ := pre

  have typ_x_in_final : σ_y.types ⊢ˢ x_enc : αx.toSMTType :=
    Typing.weakening St'_eq_St'' typ_x_enc

  have hΔ_x_final : RenamingContext.CoversFV Δ'' x_enc := by
    exact RenamingContext.coversFV_of_extends_of_coversFV Δ''_extends_Δ' Δ'_covers_x
  have den_x_enc_final : ⟦x_enc.abstract Δ'' hΔ_x_final⟧ˢ = some ⟨Xenc, ⟨αx.toSMTType, hXenc⟩⟩ := by
    have hag_x : RenamingContext.AgreesOnFV Δ'' Δ' x_enc := by
      exact RenamingContext.agreesOnFV_of_extends_of_coversFV Δ''_extends_Δ' Δ'_covers_x
    have hden_x_congr := RenamingContext.denote_congr_of_agreesOnFV
      (t := x_enc) (h1 := hΔ_x_final) (h2 := Δ'_covers_x) hag_x
    simpa [RenamingContext.denote] using hden_x_congr.trans den_x_enc

  mspec Std.Do.Spec.pure
  mpure_intro
  and_intros
  · intro v hv
    exact St'_used_sub_St'' (St_used_sub_St' (by simpa [St_used_eq] using hv))
  · exact fun _ h => St'_eq_St'' (St_eq_St' h)
  · exact St''_sub
  · intro v hv
    rw [B.fv, List.mem_append] at hv
    rcases hv with hv | hv
    · exact St'_used_sub_St'' (x_cov_St' v hv)
    · exact y_cov_St'' v hv
  · rfl
  · apply Typing.pair
    · exact typ_x_in_final
    · exact typ_y_enc
  · -- preserves_types
    intro v hv h1 h2
    rw [B.fv, List.mem_append] at h2; push_neg at h2
    exact y_preserves v (St_used_sub_St' (by simpa [St_used_eq] using hv))
      (fun h_in => h1 (by
        by_contra h_not
        exact absurd h_in (x_preserves v (by simpa [St_used_eq] using hv) h_not h2.1)))
      h2.2
  · refine ⟨Δ'', ?_, ?_⟩
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hΔ_x_final v hv
      · exact Δ''_covers_y v hv
    · and_intros
      · exact RenamingContext.extends_trans Δ''_extends_Δ' Δ'_extends_Δ₀
      · exact RenamingContext.extendsOnSourceFV_of_extends
          (RenamingContext.extends_trans Δ''_extends_Δ' Δ'_extends_Δ₀) Δ₀_ext
      · exact Δ''_none_out
      · use ⟨Xenc.pair Yenc, αx.toSMTType.pair βx.toSMTType, by rw [SMTType.toZFSet, pair_mem_prod]; exact ⟨hXenc, hYenc⟩⟩
        and_intros
        · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, den_x_enc_final, Option.bind_some, den_y_enc]
          rfl
        · congr
        · unfold retract
          rw [π₁_pair, π₂_pair, pair_inj]
          exact ⟨retract_α_Xenc_eq_X, retract_β_Yenc_eq_Y⟩
        · -- alt universality for maplet
          intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
          -- Decompose B-denotation of (x ↦ᴮ y) under alt valuation
          have den_t_alt' := den_t_alt
          rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind,
            Option.bind_eq_some_iff] at den_t_alt'
          obtain ⟨⟨X_alt, α_alt, hX_alt⟩, den_x_alt, eq_alt⟩ := den_t_alt'
          dsimp at eq_alt
          rw [Option.bind_eq_some_iff] at eq_alt
          obtain ⟨⟨Y_alt, β_alt, hY_alt⟩, den_y_alt, eq_alt⟩ := eq_alt
          rw [Option.some_inj] at eq_alt
          dsimp at eq_alt
          injection eq_alt with T_alt_eq heq_alt
          subst T_alt
          injection heq_alt with eq_alt heq_alt
          injection eq_alt with α_alt_eq β_alt_eq
          subst α_alt β_alt
          -- Build restricted base for x IH: zero outside σ_x.usedVars
          set Δ₀_alt_x : SMT.RenamingContext.Context :=
            fun v => if v ∈ σ_x.env.usedVars then Δ₀_alt v else none with Δ₀_alt_x_def
          -- ExtendsOnSourceFV Δ₀_alt_x Δ_alt x
          have Δ₀_alt_x_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_x Δ_alt x := by
            have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
              (hsub := by intro v hv; simpa [B.fv] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y))
              Δ₀_alt_ext
            intro v d hv
            simp only [Δ₀_alt_x_def]
            have hv_fv_x : v ∈ B.fv x := by
              by_contra hv_not
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
            have hv_used : v ∈ σ_x.env.usedVars :=
              St_used_sub_St' (vars_used v (by
                simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append]
                left; left; exact hv_fv_x))
            rw [if_pos hv_used]
            exact hsrc hv
          -- none_out for Δ₀_alt_x at σ_x
          have Δ₀_alt_x_none : ∀ v ∉ σ_x.env.usedVars, Δ₀_alt_x v = none := by
            intro v hv; simp only [Δ₀_alt_x_def]; rw [if_neg hv]
          have Δ₀_alt_x_wt : ∀ v (d : SMT.Dom), Δ₀_alt_x v = some d → ∀ τ, σ_x.types.lookup v = some τ → d.snd.fst = τ := by
            intro v d hv τ hτ
            simp only [Δ₀_alt_x_def] at hv
            split_ifs at hv with h
            exact Δ₀_alt_wt v d hv τ (AList.mem_lookup_iff.mpr (St'_eq_St'' (AList.mem_lookup_iff.mp hτ)))
          -- Call x_ih_total
          obtain ⟨Δ'_alt_x, hcov_alt_x, denT_x_alt, hext_alt_x,
            Δ'_alt_x_none_out, Δ'_alt_x_wt_out, den_x_alt_enc, hRDom_x_alt, _⟩ :=
            x_ih_total Δ_alt
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inl hv))
              Δ₀_alt_x Δ₀_alt_x_ext Δ₀_alt_x_none Δ₀_alt_x_wt X_alt hX_alt den_x_alt
          -- Build hybrid base for y IH: Δ₀_alt priority, else Δ'_alt_x (guarded by type context)
          set Δ₀_alt_y : SMT.RenamingContext.Context :=
            fun v => match Δ₀_alt v with
              | some d => some d
              | none => if v ∈ σ_x.types then Δ'_alt_x v else none
            with Δ₀_alt_y_def
          -- ExtendsOnSourceFV Δ₀_alt_y Δ_alt y
          have Δ₀_alt_y_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_y Δ_alt y := by
            have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
              (hsub := by intro v hv; simpa [B.fv] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y))
              Δ₀_alt_ext
            intro v d hv
            simp only [Δ₀_alt_y_def]
            have hΔ₀_val := hsrc hv
            simp [hΔ₀_val]
          -- none_out for Δ₀_alt_y at σ_y
          have Δ₀_alt_y_none : ∀ v ∉ σ_y.env.usedVars, Δ₀_alt_y v = none := by
            intro v hv
            simp only [Δ₀_alt_y_def]
            have h1 : Δ₀_alt v = none := Δ₀_alt_none_out v hv
            simp only [h1]
            have hv_types : v ∉ σ_x.types :=
              fun h => hv (St'_used_sub_St'' (St'_sub (AList.mem_keys.mp h)))
            simp [if_neg hv_types]
          -- wt for Δ₀_alt_y
          have Δ₀_alt_y_wt : ∀ v (d : SMT.Dom), Δ₀_alt_y v = some d → ∀ τ, σ_y.types.lookup v = some τ → d.snd.fst = τ := by
            intro v d hv τ hτ
            simp only [Δ₀_alt_y_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d' =>
              simp [hΔ] at hv
              subst hv
              exact Δ₀_alt_wt v d' hΔ τ hτ
            | none =>
              simp [hΔ] at hv
              obtain ⟨h_mem, hv⟩ := hv
              apply Δ'_alt_x_wt_out v d hv
              obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr h_mem)
              have h_lkp_y := AList.lookup_of_subset St'_eq_St'' hτ'
              rw [hτ] at h_lkp_y; cases h_lkp_y; exact hτ'
          -- Call y_ih_total
          obtain ⟨Δ'_alt_y, hcov_alt_y, denT_y_alt, hext_alt_y,
            Δ'_alt_y_none_out, Δ'_alt_y_wt_out, den_y_alt_enc, hRDom_y_alt, Δ'_alt_y_dom_out⟩ :=
            y_ih_total Δ_alt
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inr hv))
              Δ₀_alt_y Δ₀_alt_y_ext Δ₀_alt_y_none Δ₀_alt_y_wt Y_alt hY_alt den_y_alt
          -- Define final Δ'_alt: Δ₀_alt priority, else Δ'_alt_y
          set Δ'_alt : SMT.RenamingContext.Context :=
            fun v => match Δ₀_alt v with | some d => some d | none => Δ'_alt_y v
            with Δ'_alt_def
          -- Coverage for Δ'_alt on fv(x_enc.pair y_enc)
          have hcov_pair_alt : RenamingContext.CoversFV Δ'_alt (x_enc.pair y_enc) := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d => simp
            | none =>
              rw [SMT.fv, List.mem_append] at hv
              rcases hv with hv | hv
              · have hx_some : (Δ'_alt_x v).isSome = true := hcov_alt_x v hv
                have hv_types : v ∈ σ_x.types := SMT.Typing.mem_context_of_mem_fv typ_x_enc hv
                have hΔ₀_alt_y_v : Δ₀_alt_y v = Δ'_alt_x v := by
                  simp [Δ₀_alt_y_def, h, if_pos hv_types]
                obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hx_some
                have : Δ₀_alt_y v = some dx := by rw [hΔ₀_alt_y_v, hdx]
                have := hext_alt_y this
                rw [this]; simp
              · exact hcov_alt_y v hv
          -- Δ'_alt agrees with Δ'_alt_x on fv(x_enc)
          have hagree_x : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_x x_enc := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d =>
              -- v ∈ fv(x_enc) ⟹ v ∈ σ_x.usedVars ⟹ Δ₀_alt_x v = some d
              have hv_σx : v ∈ σ_x.env.usedVars := by
                by_contra hv_not
                exact absurd (Δ'_covers_x v hv) (by simp [Δ'_none_out v hv_not])
              have : Δ₀_alt_x v = some d := by simp [Δ₀_alt_x_def, if_pos hv_σx, h]
              symm; exact hext_alt_x this
            | none =>
              have hv_types : v ∈ σ_x.types := SMT.Typing.mem_context_of_mem_fv typ_x_enc hv
              have hΔ₀_alt_y_v : Δ₀_alt_y v = Δ'_alt_x v := by
                simp [Δ₀_alt_y_def, h, if_pos hv_types]
              have hx_some : (Δ'_alt_x v).isSome = true := hcov_alt_x v hv
              obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hx_some
              have h₁ : Δ₀_alt_y v = some dx := by rw [hΔ₀_alt_y_v, hdx]
              rw [hext_alt_y h₁, hdx]
          -- Δ'_alt agrees with Δ'_alt_y on fv(y_enc)
          have hagree_y : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_y y_enc := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d =>
              have : Δ₀_alt_y v = some d := by simp [Δ₀_alt_y_def, h]
              symm; exact hext_alt_y this
            | none => rfl
          -- x_enc denotes under Δ'_alt
          have hcov_x_in_alt : RenamingContext.CoversFV Δ'_alt x_enc := by
            intro v hv
            exact hcov_pair_alt v (by rw [SMT.fv, List.mem_append]; exact Or.inl hv)
          have den_x_alt_final :
              ⟦x_enc.abstract Δ'_alt hcov_x_in_alt⟧ˢ = some denT_x_alt := by
            have := RenamingContext.denote_congr_of_agreesOnFV
              (t := x_enc) (h1 := hcov_x_in_alt) (h2 := hcov_alt_x) hagree_x
            simpa [RenamingContext.denote] using this.trans den_x_alt_enc
          -- y_enc denotes under Δ'_alt
          have hcov_y_in_alt : RenamingContext.CoversFV Δ'_alt y_enc := by
            intro v hv
            exact hcov_pair_alt v (by rw [SMT.fv, List.mem_append]; exact Or.inr hv)
          have den_y_alt_final :
              ⟦y_enc.abstract Δ'_alt hcov_y_in_alt⟧ˢ = some denT_y_alt := by
            have := RenamingContext.denote_congr_of_agreesOnFV
              (t := y_enc) (h1 := hcov_y_in_alt) (h2 := hcov_alt_y) hagree_y
            simpa [RenamingContext.denote] using this.trans den_y_alt_enc
          -- Build the result
          obtain ⟨Xenc_alt, σ_x_alt, hXenc_alt⟩ := denT_x_alt
          obtain ⟨Yenc_alt, σ_y_alt, hYenc_alt⟩ := denT_y_alt
          obtain ⟨rfl, retract_x_alt⟩ := hRDom_x_alt
          obtain ⟨rfl, retract_y_alt⟩ := hRDom_y_alt
          refine ⟨Δ'_alt, hcov_pair_alt,
            ⟨Xenc_alt.pair Yenc_alt, αx.toSMTType.pair βx.toSMTType,
              by rw [SMTType.toZFSet, pair_mem_prod]; exact ⟨hXenc_alt, hYenc_alt⟩⟩,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          -- Extends Δ'_alt Δ₀_alt
          · intro v d hv; simp only [Δ'_alt_def, hv]
          -- Vanishing Δ'_alt outside E'.usedVars
          · intro v hv; simp only [Δ'_alt_def, Δ₀_alt_none_out v hv, Δ'_alt_y_none_out v hv]
          -- Well-typedness: output wt
          · intro v d hv τ hτ
            simp only [Δ'_alt_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d' => simp [hΔ] at hv; subst hv; exact Δ₀_alt_wt v d' hΔ τ hτ
            | none => simp [hΔ] at hv; exact Δ'_alt_y_wt_out v d hv τ hτ
          -- Denotation of (x_enc.pair y_enc) under Δ'_alt
          · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind,
              den_x_alt_final, Option.bind_some, den_y_alt_final]
            rfl
          -- RDom
          · constructor
            · congr
            · unfold retract
              rw [π₁_pair, π₂_pair, pair_inj]
              exact ⟨retract_x_alt, retract_y_alt⟩
          -- dom_out
          · intro v hv
            simp only [Δ'_alt_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d =>
              exact fv_sub_typings (B.Typing.maplet typ_x typ_y)
                (SMT.Typing.pair _ _ _ _ _ typ_x_in_final typ_y_enc) v
                (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext v
                  (by rw [hΔ]; simp))
            | none => simp [hΔ] at hv; exact Δ'_alt_y_dom_out v hv

theorem encodeTerm_spec.add_case.{u} (fv_sub_typings : B.FvSubTypings) (x y : B.Term)
  (x_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ x : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv x, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» x →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ x.vars, v ∈ used) →
                      (∀ v ∈ x.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm x E ⦃PostCond.mayThrow fun x_1 x_2 =>
                              match x_1 with
                              | (t', σ) =>
                                match x_2 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars x ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv x → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» x ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv x, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt x →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦x.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (y_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ y : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv y, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» y →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦y.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ y.vars, v ∈ used) →
                      (∀ v ∈ y.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm y E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars y ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv y → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» y ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv y, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt y →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦y.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (E : B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ x +ᴮ y : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv (x +ᴮ y), («Δ» v).isSome = true) {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (x +ᴮ y)) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x +ᴮ y).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ (x +ᴮ y).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (x +ᴮ y).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (x +ᴮ y) E ⦃PostCond.mayThrow fun x_1 x_2 =>
      match x_1 with
      | (t', σ) =>
        match x_2 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (x +ᴮ y) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv (x +ᴮ y) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (x +ᴮ y) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv (x +ᴮ y), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (x +ᴮ y) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(x +ᴮ y).abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                    ∃ Δ'_alt,
                                                      ∃ (hcov_alt : RenamingContext.CoversFV Δ'_alt t'),
                                                        ∃ denT_alt,
                                                          RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                                                            (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                              (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                              ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                                                ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄ := by
  mstart
  mintro pre ∀σ
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm]

  apply B.Typing.addE at typ_t
  obtain ⟨rfl, typ_x, typ_y⟩ := typ_t
  obtain ⟨X, hX, den_x, Y, hY, den_y, T_eq⟩ :=
    EncodeTermCorrectArith.Arith.denote_inv
      (op := .add) (Γ := E.context) (x := x) (y := y) («Δ» := «Δ»)
      (typ_t := B.Typing.add typ_x typ_y) (Δ_fv := Δ_fv) (T := T) (hT := hT) den_t
  subst T

  have Δ₀_ext_x : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» x := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [B.fv] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y)) Δ₀_ext
  have Δ₀_ext_y : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» y := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [B.fv] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y)) Δ₀_ext

  mspec x_ih (E := E) (Λ := σ.types) (α := .int) typ_x
    («Δ» := «Δ»)
    (EncodeTermCorrectArith.Arith.BinOp.leftFVCert (x := x) (y := y) (op := .add) Δ_fv)
    (Δ₀ := Δ₀) Δ₀_ext_x (used := used) Δ₀_none_out (T := X) (hT := hX)
    den_x (fun v hv => vars_used v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (fun v hv => Λ_inv v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (n := σ.env.freshvarsc)
  clear x_ih
  rename_i out_x
  obtain ⟨x_enc, σx⟩ := out_x
  mrename_i pre
  mintro ∀σ_x
  mpure pre
  dsimp at pre
  obtain ⟨St_used_sub_St', St_eq_St', St'_sub, x_cov_St', rfl, typ_x_enc, x_preserves,
    Δ', Δ'_covers_x, Δ'_extends_Δ₀, Δ'_ext_x, Δ'_none_out,
    ⟨Xenc, _, hXenc⟩, den_x_enc, ⟨rfl, retract_α_Xenc_eq_X⟩, x_ih_total⟩ := pre

  have Δ'_ext_y : RenamingContext.ExtendsOnSourceFV Δ' «Δ» y := by
    exact RenamingContext.extendsOnSourceFV_of_extends Δ'_extends_Δ₀ Δ₀_ext_y

  rw [BType.toSMTType]
  mspec y_ih (E := E) (Λ := σ_x.types) (α := .int) typ_y
    («Δ» := «Δ»)
    (EncodeTermCorrectArith.Arith.BinOp.rightFVCert (x := x) (y := y) (op := .add) Δ_fv)
    (Δ₀ := Δ') Δ'_ext_y (used := σ_x.env.usedVars) Δ'_none_out (T := Y) (hT := hY)
    den_y (fun v hv => St_used_sub_St' (vars_used v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inr h)))
    (fun v hv hΛ => by
      have hv_add : v ∈ (x +ᴮ y).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_add hv_St
      · have hv_fv_x : v ∈ B.fv x := by
          by_contra h_neg
          exact absurd hΛ (x_preserves v (vars_used v hv_add) hv_St h_neg)
        exact _root_.B.Typing.typed_by_fv typ_x hv_fv_x)
    (n := σ_x.env.freshvarsc)
  clear y_ih
  rename_i out_y
  obtain ⟨y_enc, σy⟩ := out_y
  mrename_i pre
  mintro ∀σ_y
  mpure pre
  dsimp at pre
  obtain ⟨St'_used_sub_St'', St'_eq_St'', St''_sub, y_cov_St'', rfl, typ_y_enc, y_preserves,
    Δ'', Δ''_covers_y, Δ''_extends_Δ', Δ''_ext_y, Δ''_none_out,
    ⟨Yenc, _, hYenc⟩, den_y_enc, ⟨rfl, retract_β_Yenc_eq_Y⟩, y_ih_total⟩ := pre

  have typ_x_in_final : σ_y.types ⊢ˢ x_enc : .int :=
    Typing.weakening St'_eq_St'' typ_x_enc

  have hΔ_x_final : RenamingContext.CoversFV Δ'' x_enc := by
    exact RenamingContext.coversFV_of_extends_of_coversFV Δ''_extends_Δ' Δ'_covers_x
  have den_x_enc_final : ⟦x_enc.abstract Δ'' hΔ_x_final⟧ˢ = some ⟨Xenc, ⟨SMTType.int, hXenc⟩⟩ := by
    have hag_x : RenamingContext.AgreesOnFV Δ'' Δ' x_enc := by
      exact RenamingContext.agreesOnFV_of_extends_of_coversFV Δ''_extends_Δ' Δ'_covers_x
    have hden_x_congr := RenamingContext.denote_congr_of_agreesOnFV
      (t := x_enc) (h1 := hΔ_x_final) (h2 := Δ'_covers_x) hag_x
    simpa [RenamingContext.denote] using hden_x_congr.trans den_x_enc

  mspec Std.Do.Spec.pure
  mpure_intro
  and_intros
  · intro v hv
    exact St'_used_sub_St'' (St_used_sub_St' (by simpa [St_used_eq] using hv))
  · exact fun _ h => St'_eq_St'' (St_eq_St' h)
  · exact St''_sub
  · intro v hv
    rw [B.fv, List.mem_append] at hv
    rcases hv with hv | hv
    · exact St'_used_sub_St'' (x_cov_St' v hv)
    · exact y_cov_St'' v hv
  · trivial
  · apply SMT.Typing.add
    · exact typ_x_in_final
    · exact typ_y_enc
  · -- preserves_types
    intro v hv h1 h2
    rw [B.fv, List.mem_append] at h2; push_neg at h2
    exact y_preserves v (St_used_sub_St' (by simpa [St_used_eq] using hv))
      (fun h_in => h1 (by
        by_contra h_not
        exact absurd h_in (x_preserves v (by simpa [St_used_eq] using hv) h_not h2.1)))
      h2.2
  · refine ⟨Δ'', ?_, ?_⟩
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hΔ_x_final v hv
      · exact Δ''_covers_y v hv
    · and_intros
      · exact RenamingContext.extends_trans Δ''_extends_Δ' Δ'_extends_Δ₀
      · exact RenamingContext.extendsOnSourceFV_of_extends
          (RenamingContext.extends_trans Δ''_extends_Δ' Δ'_extends_Δ₀) Δ₀_ext
      · exact Δ''_none_out
      · use ⟨Xenc +ᶻ Yenc, .int, overloadBinOp_mem hXenc hYenc⟩
        and_intros
        · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, den_x_enc_final, Option.bind_some, den_y_enc]
          rfl
        · congr
        · dsimp [retract] at retract_α_Xenc_eq_X retract_β_Yenc_eq_Y ⊢
          subst Xenc Yenc
          rfl
        · -- alt universality for add
          intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
          -- Decompose B-denotation of (x +ᴮ y) under alt valuation
          have hΔ_alt_fv_add : ∀ v ∈ B.fv (x +ᴮ y), (Δ_alt v).isSome = true := by
            intro v hv; exact Δ_fv_alt v hv
          obtain ⟨X_alt, hX_alt, den_x_alt, Y_alt, hY_alt, den_y_alt, T_alt_eq⟩ :=
            EncodeTermCorrectArith.Arith.denote_inv
              (op := .add) (Γ := E.context) (x := x) (y := y) («Δ» := Δ_alt)
              (typ_t := B.Typing.add typ_x typ_y) (Δ_fv := hΔ_alt_fv_add) (T := T_alt) (hT := hT_alt)
              den_t_alt
          subst T_alt
          -- Build restricted base for x IH: zero outside σ_x.usedVars
          set Δ₀_alt_x : SMT.RenamingContext.Context :=
            fun v => if v ∈ σ_x.env.usedVars then Δ₀_alt v else none with Δ₀_alt_x_def
          -- ExtendsOnSourceFV Δ₀_alt_x Δ_alt x
          have Δ₀_alt_x_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_x Δ_alt x := by
            have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
              (hsub := by intro v hv; simpa [B.fv] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y))
              Δ₀_alt_ext
            intro v d hv
            simp only [Δ₀_alt_x_def]
            have hv_fv_x : v ∈ B.fv x := by
              by_contra hv_not
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
            have hv_used : v ∈ σ_x.env.usedVars :=
              St_used_sub_St' (vars_used v (by
                simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append]
                left; left; exact hv_fv_x))
            rw [if_pos hv_used]
            exact hsrc hv
          -- none_out for Δ₀_alt_x at σ_x
          have Δ₀_alt_x_none : ∀ v ∉ σ_x.env.usedVars, Δ₀_alt_x v = none := by
            intro v hv; simp only [Δ₀_alt_x_def]; rw [if_neg hv]
          have Δ₀_alt_x_wt : ∀ v (d : SMT.Dom), Δ₀_alt_x v = some d → ∀ τ, σ_x.types.lookup v = some τ → d.snd.fst = τ := by
            intro v d hv τ hτ
            simp only [Δ₀_alt_x_def] at hv
            split_ifs at hv with h
            exact Δ₀_alt_wt v d hv τ (AList.mem_lookup_iff.mpr (St'_eq_St'' (AList.mem_lookup_iff.mp hτ)))
          -- Call x_ih_total
          obtain ⟨Δ'_alt_x, hcov_alt_x, denT_x_alt, hext_alt_x,
            Δ'_alt_x_none_out, Δ'_alt_x_wt_out, den_x_alt_enc, hRDom_x_alt, _⟩ :=
            x_ih_total Δ_alt
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inl hv))
              Δ₀_alt_x Δ₀_alt_x_ext Δ₀_alt_x_none Δ₀_alt_x_wt X_alt hX_alt den_x_alt
          -- Build hybrid base for y IH: Δ₀_alt priority, else Δ'_alt_x (guarded by type context)
          set Δ₀_alt_y : SMT.RenamingContext.Context :=
            fun v => match Δ₀_alt v with
              | some d => some d
              | none => if v ∈ σ_x.types then Δ'_alt_x v else none
            with Δ₀_alt_y_def
          -- ExtendsOnSourceFV Δ₀_alt_y Δ_alt y
          have Δ₀_alt_y_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_y Δ_alt y := by
            have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
              (hsub := by intro v hv; simpa [B.fv] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y))
              Δ₀_alt_ext
            intro v d hv
            simp only [Δ₀_alt_y_def]
            have hΔ₀_val := hsrc hv
            simp [hΔ₀_val]
          -- none_out for Δ₀_alt_y at σ_y
          have Δ₀_alt_y_none : ∀ v ∉ σ_y.env.usedVars, Δ₀_alt_y v = none := by
            intro v hv
            simp only [Δ₀_alt_y_def]
            have h1 : Δ₀_alt v = none := Δ₀_alt_none_out v hv
            simp only [h1]
            have hv_types : v ∉ σ_x.types :=
              fun h => hv (St'_used_sub_St'' (St'_sub (AList.mem_keys.mp h)))
            simp [if_neg hv_types]
          -- wt for Δ₀_alt_y
          have Δ₀_alt_y_wt : ∀ v (d : SMT.Dom), Δ₀_alt_y v = some d → ∀ τ, σ_y.types.lookup v = some τ → d.snd.fst = τ := by
            intro v d hv τ hτ
            simp only [Δ₀_alt_y_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d' =>
              simp [hΔ] at hv
              subst hv
              exact Δ₀_alt_wt v d' hΔ τ hτ
            | none =>
              simp [hΔ] at hv
              obtain ⟨h_mem, hv⟩ := hv
              apply Δ'_alt_x_wt_out v d hv
              obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr h_mem)
              have h_lkp_y := AList.lookup_of_subset St'_eq_St'' hτ'
              rw [hτ] at h_lkp_y; cases h_lkp_y; exact hτ'
          -- Call y_ih_total
          obtain ⟨Δ'_alt_y, hcov_alt_y, denT_y_alt, hext_alt_y,
            Δ'_alt_y_none_out, Δ'_alt_y_wt_out, den_y_alt_enc, hRDom_y_alt, Δ'_alt_y_dom_out⟩ :=
            y_ih_total Δ_alt
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inr hv))
              Δ₀_alt_y Δ₀_alt_y_ext Δ₀_alt_y_none Δ₀_alt_y_wt Y_alt hY_alt den_y_alt
          -- Define final Δ'_alt: Δ₀_alt priority, else Δ'_alt_y
          set Δ'_alt : SMT.RenamingContext.Context :=
            fun v => match Δ₀_alt v with | some d => some d | none => Δ'_alt_y v
            with Δ'_alt_def
          -- Coverage for Δ'_alt on fv(x_enc.add y_enc)
          have hcov_add_alt : RenamingContext.CoversFV Δ'_alt (x_enc.add y_enc) := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d => simp
            | none =>
              rw [SMT.fv, List.mem_append] at hv
              rcases hv with hv | hv
              · have hx_some : (Δ'_alt_x v).isSome = true := hcov_alt_x v hv
                have hv_types : v ∈ σ_x.types := SMT.Typing.mem_context_of_mem_fv typ_x_enc hv
                have hΔ₀_alt_y_v : Δ₀_alt_y v = Δ'_alt_x v := by
                  simp [Δ₀_alt_y_def, h, if_pos hv_types]
                obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hx_some
                have : Δ₀_alt_y v = some dx := by rw [hΔ₀_alt_y_v, hdx]
                have := hext_alt_y this
                rw [this]; simp
              · exact hcov_alt_y v hv
          -- Δ'_alt agrees with Δ'_alt_x on fv(x_enc)
          have hagree_x : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_x x_enc := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d =>
              -- v ∈ fv(x_enc) ⟹ v ∈ σ_x.usedVars ⟹ Δ₀_alt_x v = some d
              have hv_σx : v ∈ σ_x.env.usedVars := by
                by_contra hv_not
                exact absurd (Δ'_covers_x v hv) (by simp [Δ'_none_out v hv_not])
              have : Δ₀_alt_x v = some d := by simp [Δ₀_alt_x_def, if_pos hv_σx, h]
              symm; exact hext_alt_x this
            | none =>
              have hv_types : v ∈ σ_x.types := SMT.Typing.mem_context_of_mem_fv typ_x_enc hv
              have hΔ₀_alt_y_v : Δ₀_alt_y v = Δ'_alt_x v := by
                simp [Δ₀_alt_y_def, h, if_pos hv_types]
              have hx_some : (Δ'_alt_x v).isSome = true := hcov_alt_x v hv
              obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hx_some
              have h₁ : Δ₀_alt_y v = some dx := by rw [hΔ₀_alt_y_v, hdx]
              rw [hext_alt_y h₁, hdx]
          -- Δ'_alt agrees with Δ'_alt_y on fv(y_enc)
          have hagree_y : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_y y_enc := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d =>
              have : Δ₀_alt_y v = some d := by simp [Δ₀_alt_y_def, h]
              symm; exact hext_alt_y this
            | none => rfl
          -- x_enc denotes under Δ'_alt
          have hcov_x_in_alt : RenamingContext.CoversFV Δ'_alt x_enc := by
            intro v hv
            exact hcov_add_alt v (by rw [SMT.fv, List.mem_append]; exact Or.inl hv)
          have den_x_alt_final :
              ⟦x_enc.abstract Δ'_alt hcov_x_in_alt⟧ˢ = some denT_x_alt := by
            have := RenamingContext.denote_congr_of_agreesOnFV
              (t := x_enc) (h1 := hcov_x_in_alt) (h2 := hcov_alt_x) hagree_x
            simpa [RenamingContext.denote] using this.trans den_x_alt_enc
          -- y_enc denotes under Δ'_alt
          have hcov_y_in_alt : RenamingContext.CoversFV Δ'_alt y_enc := by
            intro v hv
            exact hcov_add_alt v (by rw [SMT.fv, List.mem_append]; exact Or.inr hv)
          have den_y_alt_final :
              ⟦y_enc.abstract Δ'_alt hcov_y_in_alt⟧ˢ = some denT_y_alt := by
            have := RenamingContext.denote_congr_of_agreesOnFV
              (t := y_enc) (h1 := hcov_y_in_alt) (h2 := hcov_alt_y) hagree_y
            simpa [RenamingContext.denote] using this.trans den_y_alt_enc
          -- Build the result
          obtain ⟨Xenc_alt, σ_x_alt, hXenc_alt⟩ := denT_x_alt
          obtain ⟨Yenc_alt, σ_y_alt, hYenc_alt⟩ := denT_y_alt
          obtain ⟨rfl, retract_x_alt⟩ := hRDom_x_alt
          obtain ⟨rfl, retract_y_alt⟩ := hRDom_y_alt
          refine ⟨Δ'_alt, hcov_add_alt,
            ⟨Xenc_alt +ᶻ Yenc_alt, .int, overloadBinOp_mem hXenc_alt hYenc_alt⟩,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          -- Extends Δ'_alt Δ₀_alt
          · intro v d hv; simp only [Δ'_alt_def, hv]
          -- Vanishing Δ'_alt outside E'.usedVars
          · intro v hv; simp only [Δ'_alt_def, Δ₀_alt_none_out v hv, Δ'_alt_y_none_out v hv]
          -- Well-typedness: output wt
          · intro v d hv τ hτ
            simp only [Δ'_alt_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d' => simp [hΔ] at hv; subst hv; exact Δ₀_alt_wt v d' hΔ τ hτ
            | none => simp [hΔ] at hv; exact Δ'_alt_y_wt_out v d hv τ hτ
          -- Denotation of (x_enc.add y_enc) under Δ'_alt
          · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind,
              den_x_alt_final, Option.bind_some, den_y_alt_final]
            rfl
          -- RDom
          · constructor
            · rfl
            · dsimp [retract] at retract_x_alt retract_y_alt ⊢
              rw [retract_x_alt, retract_y_alt]
              rfl
          -- dom_out
          · intro v hv
            simp only [Δ'_alt_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d =>
              exact fv_sub_typings (B.Typing.add typ_x typ_y)
                (SMT.Typing.add _ _ _ typ_x_in_final typ_y_enc) v
                (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext v
                  (by rw [hΔ]; simp))
            | none => simp [hΔ] at hv; exact Δ'_alt_y_dom_out v hv

theorem encodeTerm_spec.sub_case.{u} (fv_sub_typings : B.FvSubTypings) (x y : B.Term)
  (x_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ x : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv x, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» x →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ x.vars, v ∈ used) →
                      (∀ v ∈ x.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm x E ⦃PostCond.mayThrow fun x_1 x_2 =>
                              match x_1 with
                              | (t', σ) =>
                                match x_2 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars x ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv x → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» x ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv x, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt x →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦x.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (y_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ y : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv y, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» y →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦y.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ y.vars, v ∈ used) →
                      (∀ v ∈ y.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm y E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars y ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv y → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» y ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv y, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt y →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦y.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (E : B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ x -ᴮ y : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv (x -ᴮ y), («Δ» v).isSome = true) {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (x -ᴮ y)) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x -ᴮ y).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ (x -ᴮ y).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (x -ᴮ y).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (x -ᴮ y) E ⦃PostCond.mayThrow fun x_1 x_2 =>
      match x_1 with
      | (t', σ) =>
        match x_2 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (x -ᴮ y) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv (x -ᴮ y) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (x -ᴮ y) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv (x -ᴮ y), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (x -ᴮ y) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(x -ᴮ y).abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                    ∃ Δ'_alt,
                                                      ∃ (hcov_alt : RenamingContext.CoversFV Δ'_alt t'),
                                                        ∃ denT_alt,
                                                          RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                                                            (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                              (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                              ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                                                ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄ := by
  mstart
  mintro pre ∀σ
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm]

  apply B.Typing.subE at typ_t
  obtain ⟨rfl, typ_x, typ_y⟩ := typ_t
  obtain ⟨X, hX, den_x, Y, hY, den_y, T_eq⟩ :=
    EncodeTermCorrectArith.Arith.denote_inv
      (op := .sub) (Γ := E.context) (x := x) (y := y) («Δ» := «Δ»)
      (typ_t := B.Typing.sub typ_x typ_y) (Δ_fv := Δ_fv) (T := T) (hT := hT) den_t
  subst T

  have Δ₀_ext_x : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» x := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [B.fv] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y)) Δ₀_ext
  have Δ₀_ext_y : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» y := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [B.fv] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y)) Δ₀_ext

  mspec x_ih (E := E) (Λ := σ.types) (α := .int) typ_x
    («Δ» := «Δ»)
    (EncodeTermCorrectArith.Arith.BinOp.leftFVCert (x := x) (y := y) (op := .sub) Δ_fv)
    (Δ₀ := Δ₀) Δ₀_ext_x (used := used) Δ₀_none_out (T := X) (hT := hX)
    den_x (fun v hv => vars_used v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (fun v hv => Λ_inv v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (n := σ.env.freshvarsc)
  clear x_ih
  rename_i out_x
  obtain ⟨x_enc, σx⟩ := out_x
  mrename_i pre
  mintro ∀σ_x
  mpure pre
  dsimp at pre
  obtain ⟨St_used_sub_St', St_eq_St', St'_sub, x_cov_St', rfl, typ_x_enc, x_preserves,
    Δ', Δ'_covers_x, Δ'_extends_Δ₀, Δ'_ext_x, Δ'_none_out,
    ⟨Xenc, _, hXenc⟩, den_x_enc, ⟨rfl, retract_α_Xenc_eq_X⟩, x_ih_total⟩ := pre

  have Δ'_ext_y : RenamingContext.ExtendsOnSourceFV Δ' «Δ» y := by
    exact RenamingContext.extendsOnSourceFV_of_extends Δ'_extends_Δ₀ Δ₀_ext_y

  rw [BType.toSMTType]
  mspec y_ih (E := E) (Λ := σ_x.types) (α := .int) typ_y
    («Δ» := «Δ»)
    (EncodeTermCorrectArith.Arith.BinOp.rightFVCert (x := x) (y := y) (op := .sub) Δ_fv)
    (Δ₀ := Δ') Δ'_ext_y (used := σ_x.env.usedVars) Δ'_none_out (T := Y) (hT := hY)
    den_y (fun v hv => St_used_sub_St' (vars_used v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inr h)))
    (fun v hv hΛ => by
      have hv_sub : v ∈ (x -ᴮ y).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_sub hv_St
      · have hv_fv_x : v ∈ B.fv x := by
          by_contra h_neg
          exact absurd hΛ (x_preserves v (vars_used v hv_sub) hv_St h_neg)
        exact _root_.B.Typing.typed_by_fv typ_x hv_fv_x)
    (n := σ_x.env.freshvarsc)
  clear y_ih
  rename_i out_y
  obtain ⟨y_enc, σy⟩ := out_y
  mrename_i pre
  mintro ∀σ_y
  mpure pre
  dsimp at pre
  obtain ⟨St'_used_sub_St'', St'_eq_St'', St''_sub, y_cov_St'', rfl, typ_y_enc, y_preserves,
    Δ'', Δ''_covers_y, Δ''_extends_Δ', Δ''_ext_y, Δ''_none_out,
    ⟨Yenc, _, hYenc⟩, den_y_enc, ⟨rfl, retract_β_Yenc_eq_Y⟩, y_ih_total⟩ := pre

  have typ_x_in_final : σ_y.types ⊢ˢ x_enc : .int :=
    Typing.weakening St'_eq_St'' typ_x_enc

  have hΔ_x_final : RenamingContext.CoversFV Δ'' x_enc := by
    exact RenamingContext.coversFV_of_extends_of_coversFV Δ''_extends_Δ' Δ'_covers_x
  have den_x_enc_final : ⟦x_enc.abstract Δ'' hΔ_x_final⟧ˢ = some ⟨Xenc, ⟨SMTType.int, hXenc⟩⟩ := by
    have hag_x : RenamingContext.AgreesOnFV Δ'' Δ' x_enc := by
      exact RenamingContext.agreesOnFV_of_extends_of_coversFV Δ''_extends_Δ' Δ'_covers_x
    have hden_x_congr := RenamingContext.denote_congr_of_agreesOnFV
      (t := x_enc) (h1 := hΔ_x_final) (h2 := Δ'_covers_x) hag_x
    simpa [RenamingContext.denote] using hden_x_congr.trans den_x_enc

  mspec Std.Do.Spec.pure
  mpure_intro
  and_intros
  · intro v hv
    exact St'_used_sub_St'' (St_used_sub_St' (by simpa [St_used_eq] using hv))
  · exact fun _ h => St'_eq_St'' (St_eq_St' h)
  · exact St''_sub
  · intro v hv
    rw [B.fv, List.mem_append] at hv
    rcases hv with hv | hv
    · exact St'_used_sub_St'' (x_cov_St' v hv)
    · exact y_cov_St'' v hv
  · trivial
  · apply SMT.Typing.sub
    · exact typ_x_in_final
    · exact typ_y_enc
  · -- preserves_types
    intro v hv h1 h2
    rw [B.fv, List.mem_append] at h2; push_neg at h2
    exact y_preserves v (St_used_sub_St' (by simpa [St_used_eq] using hv))
      (fun h_in => h1 (by
        by_contra h_not
        exact absurd h_in (x_preserves v (by simpa [St_used_eq] using hv) h_not h2.1)))
      h2.2
  · refine ⟨Δ'', ?_, ?_⟩
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hΔ_x_final v hv
      · exact Δ''_covers_y v hv
    · and_intros
      · exact RenamingContext.extends_trans Δ''_extends_Δ' Δ'_extends_Δ₀
      · exact RenamingContext.extendsOnSourceFV_of_extends
          (RenamingContext.extends_trans Δ''_extends_Δ' Δ'_extends_Δ₀) Δ₀_ext
      · exact Δ''_none_out
      · use ⟨Xenc -ᶻ Yenc, .int, overloadBinOp_mem hXenc hYenc⟩
        and_intros
        · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, den_x_enc_final, Option.bind_some, den_y_enc]
          rfl
        · congr
        · dsimp [retract] at retract_α_Xenc_eq_X retract_β_Yenc_eq_Y ⊢
          subst Xenc Yenc
          rfl
        · -- alt universality for sub
          intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
          -- Decompose B-denotation of (x -ᴮ y) under alt valuation
          have hΔ_alt_fv_sub : ∀ v ∈ B.fv (x -ᴮ y), (Δ_alt v).isSome = true := by
            intro v hv; exact Δ_fv_alt v hv
          obtain ⟨X_alt, hX_alt, den_x_alt, Y_alt, hY_alt, den_y_alt, T_alt_eq⟩ :=
            EncodeTermCorrectArith.Arith.denote_inv
              (op := .sub) (Γ := E.context) (x := x) (y := y) («Δ» := Δ_alt)
              (typ_t := B.Typing.sub typ_x typ_y) (Δ_fv := hΔ_alt_fv_sub) (T := T_alt) (hT := hT_alt)
              den_t_alt
          subst T_alt
          -- Build restricted base for x IH: zero outside σ_x.usedVars
          set Δ₀_alt_x : SMT.RenamingContext.Context :=
            fun v => if v ∈ σ_x.env.usedVars then Δ₀_alt v else none with Δ₀_alt_x_def
          -- ExtendsOnSourceFV Δ₀_alt_x Δ_alt x
          have Δ₀_alt_x_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_x Δ_alt x := by
            have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
              (hsub := by intro v hv; simpa [B.fv] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y))
              Δ₀_alt_ext
            intro v d hv
            simp only [Δ₀_alt_x_def]
            have hv_fv_x : v ∈ B.fv x := by
              by_contra hv_not
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
            have hv_used : v ∈ σ_x.env.usedVars :=
              St_used_sub_St' (vars_used v (by
                simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append]
                left; left; exact hv_fv_x))
            rw [if_pos hv_used]
            exact hsrc hv
          -- none_out for Δ₀_alt_x at σ_x
          have Δ₀_alt_x_none : ∀ v ∉ σ_x.env.usedVars, Δ₀_alt_x v = none := by
            intro v hv; simp only [Δ₀_alt_x_def]; rw [if_neg hv]
          have Δ₀_alt_x_wt : ∀ v (d : SMT.Dom), Δ₀_alt_x v = some d → ∀ τ, σ_x.types.lookup v = some τ → d.snd.fst = τ := by
            intro v d hv τ hτ
            simp only [Δ₀_alt_x_def] at hv
            split_ifs at hv with h
            exact Δ₀_alt_wt v d hv τ (AList.mem_lookup_iff.mpr (St'_eq_St'' (AList.mem_lookup_iff.mp hτ)))
          -- Call x_ih_total
          obtain ⟨Δ'_alt_x, hcov_alt_x, denT_x_alt, hext_alt_x,
            Δ'_alt_x_none_out, Δ'_alt_x_wt_out, den_x_alt_enc, hRDom_x_alt, _⟩ :=
            x_ih_total Δ_alt
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inl hv))
              Δ₀_alt_x Δ₀_alt_x_ext Δ₀_alt_x_none Δ₀_alt_x_wt X_alt hX_alt den_x_alt
          -- Build hybrid base for y IH: Δ₀_alt priority, else Δ'_alt_x (guarded by type context)
          set Δ₀_alt_y : SMT.RenamingContext.Context :=
            fun v => match Δ₀_alt v with
              | some d => some d
              | none => if v ∈ σ_x.types then Δ'_alt_x v else none
            with Δ₀_alt_y_def
          -- ExtendsOnSourceFV Δ₀_alt_y Δ_alt y
          have Δ₀_alt_y_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_y Δ_alt y := by
            have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
              (hsub := by intro v hv; simpa [B.fv] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y))
              Δ₀_alt_ext
            intro v d hv
            simp only [Δ₀_alt_y_def]
            have hΔ₀_val := hsrc hv
            simp [hΔ₀_val]
          -- none_out for Δ₀_alt_y at σ_y
          have Δ₀_alt_y_none : ∀ v ∉ σ_y.env.usedVars, Δ₀_alt_y v = none := by
            intro v hv
            simp only [Δ₀_alt_y_def]
            have h1 : Δ₀_alt v = none := Δ₀_alt_none_out v hv
            simp only [h1]
            have hv_types : v ∉ σ_x.types :=
              fun h => hv (St'_used_sub_St'' (St'_sub (AList.mem_keys.mp h)))
            simp [if_neg hv_types]
          -- wt for Δ₀_alt_y
          have Δ₀_alt_y_wt : ∀ v (d : SMT.Dom), Δ₀_alt_y v = some d → ∀ τ, σ_y.types.lookup v = some τ → d.snd.fst = τ := by
            intro v d hv τ hτ
            simp only [Δ₀_alt_y_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d' =>
              simp [hΔ] at hv
              subst hv
              exact Δ₀_alt_wt v d' hΔ τ hτ
            | none =>
              simp [hΔ] at hv
              obtain ⟨h_mem, hv⟩ := hv
              apply Δ'_alt_x_wt_out v d hv
              obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr h_mem)
              have h_lkp_y := AList.lookup_of_subset St'_eq_St'' hτ'
              rw [hτ] at h_lkp_y; cases h_lkp_y; exact hτ'
          -- Call y_ih_total
          obtain ⟨Δ'_alt_y, hcov_alt_y, denT_y_alt, hext_alt_y,
            Δ'_alt_y_none_out, Δ'_alt_y_wt_out, den_y_alt_enc, hRDom_y_alt, Δ'_alt_y_dom_out⟩ :=
            y_ih_total Δ_alt
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inr hv))
              Δ₀_alt_y Δ₀_alt_y_ext Δ₀_alt_y_none Δ₀_alt_y_wt Y_alt hY_alt den_y_alt
          -- Define final Δ'_alt: Δ₀_alt priority, else Δ'_alt_y
          set Δ'_alt : SMT.RenamingContext.Context :=
            fun v => match Δ₀_alt v with | some d => some d | none => Δ'_alt_y v
            with Δ'_alt_def
          -- Coverage for Δ'_alt on fv(x_enc.sub y_enc)
          have hcov_sub_alt : RenamingContext.CoversFV Δ'_alt (x_enc.sub y_enc) := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d => simp
            | none =>
              rw [SMT.fv, List.mem_append] at hv
              rcases hv with hv | hv
              · have hx_some : (Δ'_alt_x v).isSome = true := hcov_alt_x v hv
                have hv_types : v ∈ σ_x.types := SMT.Typing.mem_context_of_mem_fv typ_x_enc hv
                have hΔ₀_alt_y_v : Δ₀_alt_y v = Δ'_alt_x v := by
                  simp [Δ₀_alt_y_def, h, if_pos hv_types]
                obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hx_some
                have : Δ₀_alt_y v = some dx := by rw [hΔ₀_alt_y_v, hdx]
                have := hext_alt_y this
                rw [this]; simp
              · exact hcov_alt_y v hv
          -- Δ'_alt agrees with Δ'_alt_x on fv(x_enc)
          have hagree_x : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_x x_enc := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d =>
              -- v ∈ fv(x_enc) ⟹ v ∈ σ_x.usedVars ⟹ Δ₀_alt_x v = some d
              have hv_σx : v ∈ σ_x.env.usedVars := by
                by_contra hv_not
                exact absurd (Δ'_covers_x v hv) (by simp [Δ'_none_out v hv_not])
              have : Δ₀_alt_x v = some d := by simp [Δ₀_alt_x_def, if_pos hv_σx, h]
              symm; exact hext_alt_x this
            | none =>
              have hv_types : v ∈ σ_x.types := SMT.Typing.mem_context_of_mem_fv typ_x_enc hv
              have hΔ₀_alt_y_v : Δ₀_alt_y v = Δ'_alt_x v := by
                simp [Δ₀_alt_y_def, h, if_pos hv_types]
              have hx_some : (Δ'_alt_x v).isSome = true := hcov_alt_x v hv
              obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hx_some
              have h₁ : Δ₀_alt_y v = some dx := by rw [hΔ₀_alt_y_v, hdx]
              rw [hext_alt_y h₁, hdx]
          -- Δ'_alt agrees with Δ'_alt_y on fv(y_enc)
          have hagree_y : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_y y_enc := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d =>
              have : Δ₀_alt_y v = some d := by simp [Δ₀_alt_y_def, h]
              symm; exact hext_alt_y this
            | none => rfl
          -- x_enc denotes under Δ'_alt
          have hcov_x_in_alt : RenamingContext.CoversFV Δ'_alt x_enc := by
            intro v hv
            exact hcov_sub_alt v (by rw [SMT.fv, List.mem_append]; exact Or.inl hv)
          have den_x_alt_final :
              ⟦x_enc.abstract Δ'_alt hcov_x_in_alt⟧ˢ = some denT_x_alt := by
            have := RenamingContext.denote_congr_of_agreesOnFV
              (t := x_enc) (h1 := hcov_x_in_alt) (h2 := hcov_alt_x) hagree_x
            simpa [RenamingContext.denote] using this.trans den_x_alt_enc
          -- y_enc denotes under Δ'_alt
          have hcov_y_in_alt : RenamingContext.CoversFV Δ'_alt y_enc := by
            intro v hv
            exact hcov_sub_alt v (by rw [SMT.fv, List.mem_append]; exact Or.inr hv)
          have den_y_alt_final :
              ⟦y_enc.abstract Δ'_alt hcov_y_in_alt⟧ˢ = some denT_y_alt := by
            have := RenamingContext.denote_congr_of_agreesOnFV
              (t := y_enc) (h1 := hcov_y_in_alt) (h2 := hcov_alt_y) hagree_y
            simpa [RenamingContext.denote] using this.trans den_y_alt_enc
          -- Build the result
          obtain ⟨Xenc_alt, σ_x_alt, hXenc_alt⟩ := denT_x_alt
          obtain ⟨Yenc_alt, σ_y_alt, hYenc_alt⟩ := denT_y_alt
          obtain ⟨rfl, retract_x_alt⟩ := hRDom_x_alt
          obtain ⟨rfl, retract_y_alt⟩ := hRDom_y_alt
          refine ⟨Δ'_alt, hcov_sub_alt,
            ⟨Xenc_alt -ᶻ Yenc_alt, .int, overloadBinOp_mem hXenc_alt hYenc_alt⟩,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          -- Extends Δ'_alt Δ₀_alt
          · intro v d hv; simp only [Δ'_alt_def, hv]
          -- Vanishing Δ'_alt outside E'.usedVars
          · intro v hv; simp only [Δ'_alt_def, Δ₀_alt_none_out v hv, Δ'_alt_y_none_out v hv]
          -- Well-typedness: output wt
          · intro v d hv τ hτ
            simp only [Δ'_alt_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d' => simp [hΔ] at hv; subst hv; exact Δ₀_alt_wt v d' hΔ τ hτ
            | none => simp [hΔ] at hv; exact Δ'_alt_y_wt_out v d hv τ hτ
          -- Denotation of (x_enc.sub y_enc) under Δ'_alt
          · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind,
              den_x_alt_final, Option.bind_some, den_y_alt_final]
            rfl
          -- RDom
          · constructor
            · rfl
            · dsimp [retract] at retract_x_alt retract_y_alt ⊢
              rw [retract_x_alt, retract_y_alt]
              rfl
          -- dom_out
          · intro v hv
            simp only [Δ'_alt_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d =>
              exact fv_sub_typings (B.Typing.sub typ_x typ_y)
                (SMT.Typing.sub _ _ _ typ_x_in_final typ_y_enc) v
                (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext v
                  (by rw [hΔ]; simp))
            | none => simp [hΔ] at hv; exact Δ'_alt_y_dom_out v hv

theorem encodeTerm_spec.mul_case.{u} (fv_sub_typings : B.FvSubTypings) (x y : B.Term)
  (x_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ x : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv x, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» x →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ x.vars, v ∈ used) →
                      (∀ v ∈ x.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm x E ⦃PostCond.mayThrow fun x_1 x_2 =>
                              match x_1 with
                              | (t', σ) =>
                                match x_2 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars x ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv x → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» x ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv x, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt x →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦x.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (y_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ y : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv y, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» y →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦y.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ y.vars, v ∈ used) →
                      (∀ v ∈ y.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm y E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars y ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv y → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» y ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv y, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt y →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦y.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (E : B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ x *ᴮ y : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv (x *ᴮ y), («Δ» v).isSome = true) {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (x *ᴮ y)) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x *ᴮ y).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ (x *ᴮ y).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (x *ᴮ y).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (x *ᴮ y) E ⦃PostCond.mayThrow fun x_1 x_2 =>
      match x_1 with
      | (t', σ) =>
        match x_2 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (x *ᴮ y) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv (x *ᴮ y) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (x *ᴮ y) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv (x *ᴮ y), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (x *ᴮ y) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(x *ᴮ y).abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                    ∃ Δ'_alt,
                                                      ∃ (hcov_alt : RenamingContext.CoversFV Δ'_alt t'),
                                                        ∃ denT_alt,
                                                          RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                                                            (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                              (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                              ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                                                ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄ := by
  mstart
  mintro pre ∀σ
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm]

  apply B.Typing.mulE at typ_t
  obtain ⟨rfl, typ_x, typ_y⟩ := typ_t
  obtain ⟨X, hX, den_x, Y, hY, den_y, T_eq⟩ :=
    EncodeTermCorrectArith.Arith.denote_inv
      (op := .mul) (Γ := E.context) (x := x) (y := y) («Δ» := «Δ»)
      (typ_t := B.Typing.mul typ_x typ_y) (Δ_fv := Δ_fv) (T := T) (hT := hT) den_t
  subst T

  have Δ₀_ext_x : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» x := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [B.fv] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y)) Δ₀_ext
  have Δ₀_ext_y : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» y := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [B.fv] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y)) Δ₀_ext

  mspec x_ih (E := E) (Λ := σ.types) (α := .int) typ_x
    («Δ» := «Δ»)
    (EncodeTermCorrectArith.Arith.BinOp.leftFVCert (x := x) (y := y) (op := .mul) Δ_fv)
    (Δ₀ := Δ₀) Δ₀_ext_x (used := used) Δ₀_none_out (T := X) (hT := hX)
    den_x (fun v hv => vars_used v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (fun v hv => Λ_inv v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (n := σ.env.freshvarsc)
  clear x_ih
  rename_i out_x
  obtain ⟨x_enc, σx⟩ := out_x
  mrename_i pre
  mintro ∀σ_x
  mpure pre
  dsimp at pre
  obtain ⟨St_used_sub_St', St_eq_St', St'_sub, x_cov_St', rfl, typ_x_enc, x_preserves,
    Δ', Δ'_covers_x, Δ'_extends_Δ₀, Δ'_ext_x, Δ'_none_out,
    ⟨Xenc, _, hXenc⟩, den_x_enc, ⟨rfl, retract_α_Xenc_eq_X⟩, x_ih_total⟩ := pre

  have Δ'_ext_y : RenamingContext.ExtendsOnSourceFV Δ' «Δ» y := by
    exact RenamingContext.extendsOnSourceFV_of_extends Δ'_extends_Δ₀ Δ₀_ext_y

  rw [BType.toSMTType]
  mspec y_ih (E := E) (Λ := σ_x.types) (α := .int) typ_y
    («Δ» := «Δ»)
    (EncodeTermCorrectArith.Arith.BinOp.rightFVCert (x := x) (y := y) (op := .mul) Δ_fv)
    (Δ₀ := Δ') Δ'_ext_y (used := σ_x.env.usedVars) Δ'_none_out (T := Y) (hT := hY)
    den_y (fun v hv => St_used_sub_St' (vars_used v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inr h)))
    (fun v hv hΛ => by
      have hv_mul : v ∈ (x *ᴮ y).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_mul hv_St
      · have hv_fv_x : v ∈ B.fv x := by
          by_contra h_neg
          exact absurd hΛ (x_preserves v (vars_used v hv_mul) hv_St h_neg)
        exact _root_.B.Typing.typed_by_fv typ_x hv_fv_x)
    (n := σ_x.env.freshvarsc)
  clear y_ih
  rename_i out_y
  obtain ⟨y_enc, σy⟩ := out_y
  mrename_i pre
  mintro ∀σ_y
  mpure pre
  dsimp at pre
  obtain ⟨St'_used_sub_St'', St'_eq_St'', St''_sub, y_cov_St'', rfl, typ_y_enc, y_preserves,
    Δ'', Δ''_covers_y, Δ''_extends_Δ', Δ''_ext_y, Δ''_none_out,
    ⟨Yenc, _, hYenc⟩, den_y_enc, ⟨rfl, retract_β_Yenc_eq_Y⟩, y_ih_total⟩ := pre

  have typ_x_in_final : σ_y.types ⊢ˢ x_enc : .int :=
    Typing.weakening St'_eq_St'' typ_x_enc

  have hΔ_x_final : RenamingContext.CoversFV Δ'' x_enc := by
    exact RenamingContext.coversFV_of_extends_of_coversFV Δ''_extends_Δ' Δ'_covers_x
  have den_x_enc_final : ⟦x_enc.abstract Δ'' hΔ_x_final⟧ˢ = some ⟨Xenc, ⟨SMTType.int, hXenc⟩⟩ := by
    have hag_x : RenamingContext.AgreesOnFV Δ'' Δ' x_enc := by
      exact RenamingContext.agreesOnFV_of_extends_of_coversFV Δ''_extends_Δ' Δ'_covers_x
    have hden_x_congr := RenamingContext.denote_congr_of_agreesOnFV
      (t := x_enc) (h1 := hΔ_x_final) (h2 := Δ'_covers_x) hag_x
    simpa [RenamingContext.denote] using hden_x_congr.trans den_x_enc

  mspec Std.Do.Spec.pure
  mpure_intro
  and_intros
  · intro v hv
    exact St'_used_sub_St'' (St_used_sub_St' (by simpa [St_used_eq] using hv))
  · exact fun _ h => St'_eq_St'' (St_eq_St' h)
  · exact St''_sub
  · intro v hv
    rw [B.fv, List.mem_append] at hv
    rcases hv with hv | hv
    · exact St'_used_sub_St'' (x_cov_St' v hv)
    · exact y_cov_St'' v hv
  · trivial
  · apply SMT.Typing.mul
    · exact typ_x_in_final
    · exact typ_y_enc
  · -- preserves_types
    intro v hv h1 h2
    rw [B.fv, List.mem_append] at h2; push_neg at h2
    exact y_preserves v (St_used_sub_St' (by simpa [St_used_eq] using hv))
      (fun h_in => h1 (by
        by_contra h_not
        exact absurd h_in (x_preserves v (by simpa [St_used_eq] using hv) h_not h2.1)))
      h2.2
  · refine ⟨Δ'', ?_, ?_⟩
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hΔ_x_final v hv
      · exact Δ''_covers_y v hv
    · and_intros
      · exact RenamingContext.extends_trans Δ''_extends_Δ' Δ'_extends_Δ₀
      · exact RenamingContext.extendsOnSourceFV_of_extends
          (RenamingContext.extends_trans Δ''_extends_Δ' Δ'_extends_Δ₀) Δ₀_ext
      · exact Δ''_none_out
      · use ⟨Xenc *ᶻ Yenc, .int, overloadBinOp_mem hXenc hYenc⟩
        and_intros
        · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, den_x_enc_final, Option.bind_some, den_y_enc]
          rfl
        · congr
        · dsimp [retract] at retract_α_Xenc_eq_X retract_β_Yenc_eq_Y ⊢
          subst Xenc Yenc
          rfl
        · -- alt universality for mul
          intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
          -- Decompose B-denotation of (x *ᴮ y) under alt valuation
          have hΔ_alt_fv_mul : ∀ v ∈ B.fv (x *ᴮ y), (Δ_alt v).isSome = true := by
            intro v hv; exact Δ_fv_alt v hv
          obtain ⟨X_alt, hX_alt, den_x_alt, Y_alt, hY_alt, den_y_alt, T_alt_eq⟩ :=
            EncodeTermCorrectArith.Arith.denote_inv
              (op := .mul) (Γ := E.context) (x := x) (y := y) («Δ» := Δ_alt)
              (typ_t := B.Typing.mul typ_x typ_y) (Δ_fv := hΔ_alt_fv_mul) (T := T_alt) (hT := hT_alt)
              den_t_alt
          subst T_alt
          -- Build restricted base for x IH: zero outside σ_x.usedVars
          set Δ₀_alt_x : SMT.RenamingContext.Context :=
            fun v => if v ∈ σ_x.env.usedVars then Δ₀_alt v else none with Δ₀_alt_x_def
          -- ExtendsOnSourceFV Δ₀_alt_x Δ_alt x
          have Δ₀_alt_x_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_x Δ_alt x := by
            have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
              (hsub := by intro v hv; simpa [B.fv] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y))
              Δ₀_alt_ext
            intro v d hv
            simp only [Δ₀_alt_x_def]
            have hv_fv_x : v ∈ B.fv x := by
              by_contra hv_not
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
            have hv_used : v ∈ σ_x.env.usedVars :=
              St_used_sub_St' (vars_used v (by
                simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append]
                left; left; exact hv_fv_x))
            rw [if_pos hv_used]
            exact hsrc hv
          -- none_out for Δ₀_alt_x at σ_x
          have Δ₀_alt_x_none : ∀ v ∉ σ_x.env.usedVars, Δ₀_alt_x v = none := by
            intro v hv; simp only [Δ₀_alt_x_def]; rw [if_neg hv]
          have Δ₀_alt_x_wt : ∀ v (d : SMT.Dom), Δ₀_alt_x v = some d → ∀ τ, σ_x.types.lookup v = some τ → d.snd.fst = τ := by
            intro v d hv τ hτ
            simp only [Δ₀_alt_x_def] at hv
            split_ifs at hv with h
            exact Δ₀_alt_wt v d hv τ (AList.mem_lookup_iff.mpr (St'_eq_St'' (AList.mem_lookup_iff.mp hτ)))
          -- Call x_ih_total
          obtain ⟨Δ'_alt_x, hcov_alt_x, denT_x_alt, hext_alt_x,
            Δ'_alt_x_none_out, Δ'_alt_x_wt_out, den_x_alt_enc, hRDom_x_alt, _⟩ :=
            x_ih_total Δ_alt
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inl hv))
              Δ₀_alt_x Δ₀_alt_x_ext Δ₀_alt_x_none Δ₀_alt_x_wt X_alt hX_alt den_x_alt
          -- Build hybrid base for y IH: Δ₀_alt priority, else Δ'_alt_x (guarded by type context)
          set Δ₀_alt_y : SMT.RenamingContext.Context :=
            fun v => match Δ₀_alt v with
              | some d => some d
              | none => if v ∈ σ_x.types then Δ'_alt_x v else none
            with Δ₀_alt_y_def
          -- ExtendsOnSourceFV Δ₀_alt_y Δ_alt y
          have Δ₀_alt_y_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_y Δ_alt y := by
            have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
              (hsub := by intro v hv; simpa [B.fv] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y))
              Δ₀_alt_ext
            intro v d hv
            simp only [Δ₀_alt_y_def]
            have hΔ₀_val := hsrc hv
            simp [hΔ₀_val]
          -- none_out for Δ₀_alt_y at σ_y
          have Δ₀_alt_y_none : ∀ v ∉ σ_y.env.usedVars, Δ₀_alt_y v = none := by
            intro v hv
            simp only [Δ₀_alt_y_def]
            have h1 : Δ₀_alt v = none := Δ₀_alt_none_out v hv
            simp only [h1]
            have hv_types : v ∉ σ_x.types :=
              fun h => hv (St'_used_sub_St'' (St'_sub (AList.mem_keys.mp h)))
            simp [if_neg hv_types]
          -- wt for Δ₀_alt_y
          have Δ₀_alt_y_wt : ∀ v (d : SMT.Dom), Δ₀_alt_y v = some d → ∀ τ, σ_y.types.lookup v = some τ → d.snd.fst = τ := by
            intro v d hv τ hτ
            simp only [Δ₀_alt_y_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d' =>
              simp [hΔ] at hv
              subst hv
              exact Δ₀_alt_wt v d' hΔ τ hτ
            | none =>
              simp [hΔ] at hv
              obtain ⟨h_mem, hv⟩ := hv
              apply Δ'_alt_x_wt_out v d hv
              obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr h_mem)
              have h_lkp_y := AList.lookup_of_subset St'_eq_St'' hτ'
              rw [hτ] at h_lkp_y; cases h_lkp_y; exact hτ'
          -- Call y_ih_total
          obtain ⟨Δ'_alt_y, hcov_alt_y, denT_y_alt, hext_alt_y,
            Δ'_alt_y_none_out, Δ'_alt_y_wt_out, den_y_alt_enc, hRDom_y_alt, Δ'_alt_y_dom_out⟩ :=
            y_ih_total Δ_alt
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inr hv))
              Δ₀_alt_y Δ₀_alt_y_ext Δ₀_alt_y_none Δ₀_alt_y_wt Y_alt hY_alt den_y_alt
          -- Define final Δ'_alt: Δ₀_alt priority, else Δ'_alt_y
          set Δ'_alt : SMT.RenamingContext.Context :=
            fun v => match Δ₀_alt v with | some d => some d | none => Δ'_alt_y v
            with Δ'_alt_def
          -- Coverage for Δ'_alt on fv(x_enc.mul y_enc)
          have hcov_mul_alt : RenamingContext.CoversFV Δ'_alt (x_enc.mul y_enc) := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d => simp
            | none =>
              rw [SMT.fv, List.mem_append] at hv
              rcases hv with hv | hv
              · have hx_some : (Δ'_alt_x v).isSome = true := hcov_alt_x v hv
                have hv_types : v ∈ σ_x.types := SMT.Typing.mem_context_of_mem_fv typ_x_enc hv
                have hΔ₀_alt_y_v : Δ₀_alt_y v = Δ'_alt_x v := by
                  simp [Δ₀_alt_y_def, h, if_pos hv_types]
                obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hx_some
                have : Δ₀_alt_y v = some dx := by rw [hΔ₀_alt_y_v, hdx]
                have := hext_alt_y this
                rw [this]; simp
              · exact hcov_alt_y v hv
          -- Δ'_alt agrees with Δ'_alt_x on fv(x_enc)
          have hagree_x : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_x x_enc := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d =>
              -- v ∈ fv(x_enc) ⟹ v ∈ σ_x.usedVars ⟹ Δ₀_alt_x v = some d
              have hv_σx : v ∈ σ_x.env.usedVars := by
                by_contra hv_not
                exact absurd (Δ'_covers_x v hv) (by simp [Δ'_none_out v hv_not])
              have : Δ₀_alt_x v = some d := by simp [Δ₀_alt_x_def, if_pos hv_σx, h]
              symm; exact hext_alt_x this
            | none =>
              have hv_types : v ∈ σ_x.types := SMT.Typing.mem_context_of_mem_fv typ_x_enc hv
              have hΔ₀_alt_y_v : Δ₀_alt_y v = Δ'_alt_x v := by
                simp [Δ₀_alt_y_def, h, if_pos hv_types]
              have hx_some : (Δ'_alt_x v).isSome = true := hcov_alt_x v hv
              obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hx_some
              have h₁ : Δ₀_alt_y v = some dx := by rw [hΔ₀_alt_y_v, hdx]
              rw [hext_alt_y h₁, hdx]
          -- Δ'_alt agrees with Δ'_alt_y on fv(y_enc)
          have hagree_y : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_y y_enc := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d =>
              have : Δ₀_alt_y v = some d := by simp [Δ₀_alt_y_def, h]
              symm; exact hext_alt_y this
            | none => rfl
          -- x_enc denotes under Δ'_alt
          have hcov_x_in_alt : RenamingContext.CoversFV Δ'_alt x_enc := by
            intro v hv
            exact hcov_mul_alt v (by rw [SMT.fv, List.mem_append]; exact Or.inl hv)
          have den_x_alt_final :
              ⟦x_enc.abstract Δ'_alt hcov_x_in_alt⟧ˢ = some denT_x_alt := by
            have := RenamingContext.denote_congr_of_agreesOnFV
              (t := x_enc) (h1 := hcov_x_in_alt) (h2 := hcov_alt_x) hagree_x
            simpa [RenamingContext.denote] using this.trans den_x_alt_enc
          -- y_enc denotes under Δ'_alt
          have hcov_y_in_alt : RenamingContext.CoversFV Δ'_alt y_enc := by
            intro v hv
            exact hcov_mul_alt v (by rw [SMT.fv, List.mem_append]; exact Or.inr hv)
          have den_y_alt_final :
              ⟦y_enc.abstract Δ'_alt hcov_y_in_alt⟧ˢ = some denT_y_alt := by
            have := RenamingContext.denote_congr_of_agreesOnFV
              (t := y_enc) (h1 := hcov_y_in_alt) (h2 := hcov_alt_y) hagree_y
            simpa [RenamingContext.denote] using this.trans den_y_alt_enc
          -- Build the result
          obtain ⟨Xenc_alt, σ_x_alt, hXenc_alt⟩ := denT_x_alt
          obtain ⟨Yenc_alt, σ_y_alt, hYenc_alt⟩ := denT_y_alt
          obtain ⟨rfl, retract_x_alt⟩ := hRDom_x_alt
          obtain ⟨rfl, retract_y_alt⟩ := hRDom_y_alt
          refine ⟨Δ'_alt, hcov_mul_alt,
            ⟨Xenc_alt *ᶻ Yenc_alt, .int, overloadBinOp_mem hXenc_alt hYenc_alt⟩,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          -- Extends Δ'_alt Δ₀_alt
          · intro v d hv; simp only [Δ'_alt_def, hv]
          -- Vanishing Δ'_alt outside E'.usedVars
          · intro v hv; simp only [Δ'_alt_def, Δ₀_alt_none_out v hv, Δ'_alt_y_none_out v hv]
          -- Well-typedness: output wt
          · intro v d hv τ hτ
            simp only [Δ'_alt_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d' => simp [hΔ] at hv; subst hv; exact Δ₀_alt_wt v d' hΔ τ hτ
            | none => simp [hΔ] at hv; exact Δ'_alt_y_wt_out v d hv τ hτ
          -- Denotation of (x_enc.mul y_enc) under Δ'_alt
          · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind,
              den_x_alt_final, Option.bind_some, den_y_alt_final]
            rfl
          -- RDom
          · constructor
            · rfl
            · dsimp [retract] at retract_x_alt retract_y_alt ⊢
              rw [retract_x_alt, retract_y_alt]
              rfl
          -- dom_out
          · intro v hv
            simp only [Δ'_alt_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d =>
              exact fv_sub_typings (B.Typing.mul typ_x typ_y)
                (SMT.Typing.mul _ _ _ typ_x_in_final typ_y_enc) v
                (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext v
                  (by rw [hΔ]; simp))
            | none => simp [hΔ] at hv; exact Δ'_alt_y_dom_out v hv

theorem encodeTerm_spec.le_case.{u} (fv_sub_typings : B.FvSubTypings) (x y : B.Term)
  (x_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ x : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv x, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» x →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦x.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ x.vars, v ∈ used) →
                      (∀ v ∈ x.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm x E ⦃PostCond.mayThrow fun x_1 x_2 =>
                              match x_1 with
                              | (t', σ) =>
                                match x_2 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars x ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv x → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» x ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv x, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt x →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦x.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (y_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ y : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv y, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» y →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦y.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ y.vars, v ∈ used) →
                      (∀ v ∈ y.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm y E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars y ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv y → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» y ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv y, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt y →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦y.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (E : B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ x ≤ᴮ y : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv (x ≤ᴮ y), («Δ» v).isSome = true) {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (x ≤ᴮ y)) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(x ≤ᴮ y).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ (x ≤ᴮ y).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (x ≤ᴮ y).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (x ≤ᴮ y) E ⦃PostCond.mayThrow fun x_1 x_2 =>
      match x_1 with
      | (t', σ) =>
        match x_2 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (x ≤ᴮ y) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv (x ≤ᴮ y) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (x ≤ᴮ y) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv (x ≤ᴮ y), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (x ≤ᴮ y) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(x ≤ᴮ y).abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                    ∃ Δ'_alt,
                                                      ∃ (hcov_alt : RenamingContext.CoversFV Δ'_alt t'),
                                                        ∃ denT_alt,
                                                          RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                                                            (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                              (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                              ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                                                ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄ := by
  mstart
  mintro pre ∀σ
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  rw [encodeTerm]

  apply B.Typing.leE at typ_t
  obtain ⟨rfl, typ_x, typ_y⟩ := typ_t
  obtain ⟨X, hX, den_x, Y, hY, den_y, T_eq⟩ :=
    EncodeTermCorrectArith.Arith.denote_inv
      (op := .le) (Γ := E.context) (x := x) (y := y) («Δ» := «Δ»)
      (typ_t := B.Typing.le typ_x typ_y) (Δ_fv := Δ_fv) (T := T) (hT := hT) den_t
  subst T

  have Δ₀_ext_x : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» x := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [B.fv] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y)) Δ₀_ext
  have Δ₀_ext_y : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» y := by
    exact RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := by
        intro v hv
        simpa [B.fv] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y)) Δ₀_ext

  mspec x_ih (E := E) (Λ := σ.types) (α := .int) typ_x
    («Δ» := «Δ»)
    (EncodeTermCorrectArith.Arith.BinOp.leftFVCert (x := x) (y := y) (op := .le) Δ_fv)
    (Δ₀ := Δ₀) Δ₀_ext_x (used := used) Δ₀_none_out (T := X) (hT := hX)
    den_x (fun v hv => vars_used v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (fun v hv => Λ_inv v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inl h))
    (n := σ.env.freshvarsc)
  clear x_ih
  rename_i out_x
  obtain ⟨x_enc, σx⟩ := out_x
  mrename_i pre
  mintro ∀σ_x
  mpure pre
  dsimp at pre
  obtain ⟨St_used_sub_St', St_eq_St', St'_sub, x_cov_St', rfl, typ_x_enc, x_preserves,
    Δ', Δ'_covers_x, Δ'_extends_Δ₀, Δ'_ext_x, Δ'_none_out,
    ⟨Xenc, _, hXenc⟩, den_x_enc, ⟨rfl, retract_α_Xenc_eq_X⟩, x_ih_total⟩ := pre

  have Δ'_ext_y : RenamingContext.ExtendsOnSourceFV Δ' «Δ» y := by
    exact RenamingContext.extendsOnSourceFV_of_extends Δ'_extends_Δ₀ Δ₀_ext_y

  rw [BType.toSMTType]
  mspec y_ih (E := E) (Λ := σ_x.types) (α := .int) typ_y
    («Δ» := «Δ»)
    (EncodeTermCorrectArith.Arith.BinOp.rightFVCert (x := x) (y := y) (op := .le) Δ_fv)
    (Δ₀ := Δ') Δ'_ext_y (used := σ_x.env.usedVars) Δ'_none_out (T := Y) (hT := hY)
    den_y (fun v hv => St_used_sub_St' (vars_used v (by simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢; rcases hv with h | h <;> [left; right] <;> exact .inr h)))
    (fun v hv hΛ => by
      have hv_le : v ∈ (x ≤ᴮ y).vars := by
        simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append] at hv ⊢
        rcases hv with h | h <;> [left; right] <;> exact .inr h
      by_cases hv_St : v ∈ σ.types
      · exact Λ_inv v hv_le hv_St
      · have hv_fv_x : v ∈ B.fv x := by
          by_contra h_neg
          exact absurd hΛ (x_preserves v (vars_used v hv_le) hv_St h_neg)
        exact _root_.B.Typing.typed_by_fv typ_x hv_fv_x)
    (n := σ_x.env.freshvarsc)
  clear y_ih
  rename_i out_y
  obtain ⟨y_enc, σy⟩ := out_y
  mrename_i pre
  mintro ∀σ_y
  mpure pre
  dsimp at pre
  obtain ⟨St'_used_sub_St'', St'_eq_St'', St''_sub, y_cov_St'', rfl, typ_y_enc, y_preserves,
    Δ'', Δ''_covers_y, Δ''_extends_Δ', Δ''_ext_y, Δ''_none_out,
    ⟨Yenc, _, hYenc⟩, den_y_enc, ⟨rfl, retract_β_Yenc_eq_Y⟩, y_ih_total⟩ := pre

  have typ_x_in_final : σ_y.types ⊢ˢ x_enc : .int :=
    Typing.weakening St'_eq_St'' typ_x_enc

  have hΔ_x_final : RenamingContext.CoversFV Δ'' x_enc := by
    exact RenamingContext.coversFV_of_extends_of_coversFV Δ''_extends_Δ' Δ'_covers_x
  have den_x_enc_final : ⟦x_enc.abstract Δ'' hΔ_x_final⟧ˢ = some ⟨Xenc, ⟨SMTType.int, hXenc⟩⟩ := by
    have hag_x : RenamingContext.AgreesOnFV Δ'' Δ' x_enc := by
      exact RenamingContext.agreesOnFV_of_extends_of_coversFV Δ''_extends_Δ' Δ'_covers_x
    have hden_x_congr := RenamingContext.denote_congr_of_agreesOnFV
      (t := x_enc) (h1 := hΔ_x_final) (h2 := Δ'_covers_x) hag_x
    simpa [RenamingContext.denote] using hden_x_congr.trans den_x_enc

  mspec Std.Do.Spec.pure
  mpure_intro
  and_intros
  · intro v hv
    exact St'_used_sub_St'' (St_used_sub_St' (by simpa [St_used_eq] using hv))
  · exact fun _ h => St'_eq_St'' (St_eq_St' h)
  · exact St''_sub
  · intro v hv
    rw [B.fv, List.mem_append] at hv
    rcases hv with hv | hv
    · exact St'_used_sub_St'' (x_cov_St' v hv)
    · exact y_cov_St'' v hv
  · trivial
  · apply SMT.Typing.le
    · exact typ_x_in_final
    · exact typ_y_enc
  · -- preserves_types
    intro v hv h1 h2
    rw [B.fv, List.mem_append] at h2; push_neg at h2
    exact y_preserves v (St_used_sub_St' (by simpa [St_used_eq] using hv))
      (fun h_in => h1 (by
        by_contra h_not
        exact absurd h_in (x_preserves v (by simpa [St_used_eq] using hv) h_not h2.1)))
      h2.2
  · refine ⟨Δ'', ?_, ?_⟩
    · intro v hv
      rw [SMT.fv, List.mem_append] at hv
      rcases hv with hv | hv
      · exact hΔ_x_final v hv
      · exact Δ''_covers_y v hv
    · and_intros
      · exact RenamingContext.extends_trans Δ''_extends_Δ' Δ'_extends_Δ₀
      · exact RenamingContext.extendsOnSourceFV_of_extends
          (RenamingContext.extends_trans Δ''_extends_Δ' Δ'_extends_Δ₀) Δ₀_ext
      · exact Δ''_none_out
      · classical
        use ⟨Xenc ≤ᶻ Yenc, .bool, overloadBinOp_mem hXenc hYenc⟩
        and_intros
        · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, den_x_enc_final, Option.bind_some, den_y_enc]
          rfl
        · congr
        · dsimp [retract] at retract_α_Xenc_eq_X retract_β_Yenc_eq_Y ⊢
          subst Xenc Yenc
          rfl
        · -- alt universality for le
          intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
          -- Decompose B-denotation of (x ≤ᴮ y) under alt valuation
          have hΔ_alt_fv_le : ∀ v ∈ B.fv (x ≤ᴮ y), (Δ_alt v).isSome = true := by
            intro v hv; exact Δ_fv_alt v hv
          obtain ⟨X_alt, hX_alt, den_x_alt, Y_alt, hY_alt, den_y_alt, T_alt_eq⟩ :=
            EncodeTermCorrectArith.Arith.denote_inv
              (op := .le) (Γ := E.context) (x := x) (y := y) («Δ» := Δ_alt)
              (typ_t := B.Typing.le typ_x typ_y) (Δ_fv := hΔ_alt_fv_le) (T := T_alt) (hT := hT_alt)
              den_t_alt
          subst T_alt
          -- Build restricted base for x IH: zero outside σ_x.usedVars
          set Δ₀_alt_x : SMT.RenamingContext.Context :=
            fun v => if v ∈ σ_x.env.usedVars then Δ₀_alt v else none with Δ₀_alt_x_def
          -- ExtendsOnSourceFV Δ₀_alt_x Δ_alt x
          have Δ₀_alt_x_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_x Δ_alt x := by
            have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
              (hsub := by intro v hv; simpa [B.fv] using (Or.inl hv : v ∈ B.fv x ∨ v ∈ B.fv y))
              Δ₀_alt_ext
            intro v d hv
            simp only [Δ₀_alt_x_def]
            have hv_fv_x : v ∈ B.fv x := by
              by_contra hv_not
              simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at hv
            have hv_used : v ∈ σ_x.env.usedVars :=
              St_used_sub_St' (vars_used v (by
                simp only [B.Term.vars, List.mem_union_iff, B.fv, B.bv, List.mem_append]
                left; left; exact hv_fv_x))
            rw [if_pos hv_used]
            exact hsrc hv
          -- none_out for Δ₀_alt_x at σ_x
          have Δ₀_alt_x_none : ∀ v ∉ σ_x.env.usedVars, Δ₀_alt_x v = none := by
            intro v hv; simp only [Δ₀_alt_x_def]; rw [if_neg hv]
          have Δ₀_alt_x_wt : ∀ v (d : SMT.Dom), Δ₀_alt_x v = some d → ∀ τ, σ_x.types.lookup v = some τ → d.snd.fst = τ := by
            intro v d hv τ hτ
            simp only [Δ₀_alt_x_def] at hv
            split_ifs at hv with h
            exact Δ₀_alt_wt v d hv τ (AList.mem_lookup_iff.mpr (St'_eq_St'' (AList.mem_lookup_iff.mp hτ)))
          -- Call x_ih_total
          obtain ⟨Δ'_alt_x, hcov_alt_x, denT_x_alt, hext_alt_x,
            Δ'_alt_x_none_out, Δ'_alt_x_wt_out, den_x_alt_enc, hRDom_x_alt, _⟩ :=
            x_ih_total Δ_alt
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inl hv))
              Δ₀_alt_x Δ₀_alt_x_ext Δ₀_alt_x_none Δ₀_alt_x_wt X_alt hX_alt den_x_alt
          -- Build hybrid base for y IH: Δ₀_alt priority, else Δ'_alt_x (guarded by type context)
          set Δ₀_alt_y : SMT.RenamingContext.Context :=
            fun v => match Δ₀_alt v with
              | some d => some d
              | none => if v ∈ σ_x.types then Δ'_alt_x v else none
            with Δ₀_alt_y_def
          -- ExtendsOnSourceFV Δ₀_alt_y Δ_alt y
          have Δ₀_alt_y_ext : RenamingContext.ExtendsOnSourceFV Δ₀_alt_y Δ_alt y := by
            have hsrc := RenamingContext.extendsOnSourceFV_of_fv_subset
              (hsub := by intro v hv; simpa [B.fv] using (Or.inr hv : v ∈ B.fv x ∨ v ∈ B.fv y))
              Δ₀_alt_ext
            intro v d hv
            simp only [Δ₀_alt_y_def]
            have hΔ₀_val := hsrc hv
            simp [hΔ₀_val]
          -- none_out for Δ₀_alt_y at σ_y
          have Δ₀_alt_y_none : ∀ v ∉ σ_y.env.usedVars, Δ₀_alt_y v = none := by
            intro v hv
            simp only [Δ₀_alt_y_def]
            have h1 : Δ₀_alt v = none := Δ₀_alt_none_out v hv
            simp only [h1]
            have hv_types : v ∉ σ_x.types :=
              fun h => hv (St'_used_sub_St'' (St'_sub (AList.mem_keys.mp h)))
            simp [if_neg hv_types]
          -- wt for Δ₀_alt_y
          have Δ₀_alt_y_wt : ∀ v (d : SMT.Dom), Δ₀_alt_y v = some d → ∀ τ, σ_y.types.lookup v = some τ → d.snd.fst = τ := by
            intro v d hv τ hτ
            simp only [Δ₀_alt_y_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d' =>
              simp [hΔ] at hv
              subst hv
              exact Δ₀_alt_wt v d' hΔ τ hτ
            | none =>
              simp [hΔ] at hv
              obtain ⟨h_mem, hv⟩ := hv
              apply Δ'_alt_x_wt_out v d hv
              obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr h_mem)
              have h_lkp_y := AList.lookup_of_subset St'_eq_St'' hτ'
              rw [hτ] at h_lkp_y; cases h_lkp_y; exact hτ'
          -- Call y_ih_total
          obtain ⟨Δ'_alt_y, hcov_alt_y, denT_y_alt, hext_alt_y,
            Δ'_alt_y_none_out, Δ'_alt_y_wt_out, den_y_alt_enc, hRDom_y_alt, Δ'_alt_y_dom_out⟩ :=
            y_ih_total Δ_alt
              (fun v hv => Δ_fv_alt v (by rw [B.fv, List.mem_append]; exact Or.inr hv))
              Δ₀_alt_y Δ₀_alt_y_ext Δ₀_alt_y_none Δ₀_alt_y_wt Y_alt hY_alt den_y_alt
          -- Define final Δ'_alt: Δ₀_alt priority, else Δ'_alt_y
          set Δ'_alt : SMT.RenamingContext.Context :=
            fun v => match Δ₀_alt v with | some d => some d | none => Δ'_alt_y v
            with Δ'_alt_def
          -- Coverage for Δ'_alt on fv(x_enc.le y_enc)
          have hcov_le_alt : RenamingContext.CoversFV Δ'_alt (x_enc.le y_enc) := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d => simp
            | none =>
              rw [SMT.fv, List.mem_append] at hv
              rcases hv with hv | hv
              · have hx_some : (Δ'_alt_x v).isSome = true := hcov_alt_x v hv
                have hv_types : v ∈ σ_x.types := SMT.Typing.mem_context_of_mem_fv typ_x_enc hv
                have hΔ₀_alt_y_v : Δ₀_alt_y v = Δ'_alt_x v := by
                  simp [Δ₀_alt_y_def, h, if_pos hv_types]
                obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hx_some
                have : Δ₀_alt_y v = some dx := by rw [hΔ₀_alt_y_v, hdx]
                have := hext_alt_y this
                rw [this]; simp
              · exact hcov_alt_y v hv
          -- Δ'_alt agrees with Δ'_alt_x on fv(x_enc)
          have hagree_x : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_x x_enc := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d =>
              -- v ∈ fv(x_enc) ⟹ v ∈ σ_x.usedVars ⟹ Δ₀_alt_x v = some d
              have hv_σx : v ∈ σ_x.env.usedVars := by
                by_contra hv_not
                exact absurd (Δ'_covers_x v hv) (by simp [Δ'_none_out v hv_not])
              have : Δ₀_alt_x v = some d := by simp [Δ₀_alt_x_def, if_pos hv_σx, h]
              symm; exact hext_alt_x this
            | none =>
              have hv_types : v ∈ σ_x.types := SMT.Typing.mem_context_of_mem_fv typ_x_enc hv
              have hΔ₀_alt_y_v : Δ₀_alt_y v = Δ'_alt_x v := by
                simp [Δ₀_alt_y_def, h, if_pos hv_types]
              have hx_some : (Δ'_alt_x v).isSome = true := hcov_alt_x v hv
              obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hx_some
              have h₁ : Δ₀_alt_y v = some dx := by rw [hΔ₀_alt_y_v, hdx]
              rw [hext_alt_y h₁, hdx]
          -- Δ'_alt agrees with Δ'_alt_y on fv(y_enc)
          have hagree_y : RenamingContext.AgreesOnFV Δ'_alt Δ'_alt_y y_enc := by
            intro v hv
            simp only [Δ'_alt_def]
            cases h : Δ₀_alt v with
            | some d =>
              have : Δ₀_alt_y v = some d := by simp [Δ₀_alt_y_def, h]
              symm; exact hext_alt_y this
            | none => rfl
          -- x_enc denotes under Δ'_alt
          have hcov_x_in_alt : RenamingContext.CoversFV Δ'_alt x_enc := by
            intro v hv
            exact hcov_le_alt v (by rw [SMT.fv, List.mem_append]; exact Or.inl hv)
          have den_x_alt_final :
              ⟦x_enc.abstract Δ'_alt hcov_x_in_alt⟧ˢ = some denT_x_alt := by
            have := RenamingContext.denote_congr_of_agreesOnFV
              (t := x_enc) (h1 := hcov_x_in_alt) (h2 := hcov_alt_x) hagree_x
            simpa [RenamingContext.denote] using this.trans den_x_alt_enc
          -- y_enc denotes under Δ'_alt
          have hcov_y_in_alt : RenamingContext.CoversFV Δ'_alt y_enc := by
            intro v hv
            exact hcov_le_alt v (by rw [SMT.fv, List.mem_append]; exact Or.inr hv)
          have den_y_alt_final :
              ⟦y_enc.abstract Δ'_alt hcov_y_in_alt⟧ˢ = some denT_y_alt := by
            have := RenamingContext.denote_congr_of_agreesOnFV
              (t := y_enc) (h1 := hcov_y_in_alt) (h2 := hcov_alt_y) hagree_y
            simpa [RenamingContext.denote] using this.trans den_y_alt_enc
          -- Build the result
          obtain ⟨Xenc_alt, σ_x_alt, hXenc_alt⟩ := denT_x_alt
          obtain ⟨Yenc_alt, σ_y_alt, hYenc_alt⟩ := denT_y_alt
          obtain ⟨rfl, retract_x_alt⟩ := hRDom_x_alt
          obtain ⟨rfl, retract_y_alt⟩ := hRDom_y_alt
          classical
          refine ⟨Δ'_alt, hcov_le_alt,
            ⟨Xenc_alt ≤ᶻ Yenc_alt, .bool, overloadBinOp_mem hXenc_alt hYenc_alt⟩,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          -- Extends Δ'_alt Δ₀_alt
          · intro v d hv; simp only [Δ'_alt_def, hv]
          -- Vanishing Δ'_alt outside E'.usedVars
          · intro v hv; simp only [Δ'_alt_def, Δ₀_alt_none_out v hv, Δ'_alt_y_none_out v hv]
          -- Well-typedness: output wt
          · intro v d hv τ hτ
            simp only [Δ'_alt_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d' => simp [hΔ] at hv; subst hv; exact Δ₀_alt_wt v d' hΔ τ hτ
            | none => simp [hΔ] at hv; exact Δ'_alt_y_wt_out v d hv τ hτ
          -- Denotation of (x_enc.le y_enc) under Δ'_alt
          · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind,
              den_x_alt_final, Option.bind_some, den_y_alt_final]
            rfl
          -- RDom
          · constructor
            · rfl
            · dsimp [retract] at retract_x_alt retract_y_alt ⊢
              rw [retract_x_alt, retract_y_alt]
              rfl
          -- dom_out
          · intro v hv
            simp only [Δ'_alt_def] at hv
            cases hΔ : Δ₀_alt v with
            | some d =>
              exact fv_sub_typings (B.Typing.le typ_x typ_y)
                (SMT.Typing.le _ _ _ typ_x_in_final typ_y_enc) v
                (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext v
                  (by rw [hΔ]; simp))
            | none => simp [hΔ] at hv; exact Δ'_alt_y_dom_out v hv

theorem encodeTerm_spec.min_case.{u} (S : B.Term)
  (ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ S : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv S, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» S →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦S.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ S.vars, v ∈ used) →
                      (∀ v ∈ S.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm S E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars S ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv S → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» S ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv S, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt S →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦S.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (E : B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ S.min : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv S.min, («Δ» v).isSome = true) {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» S.min) {used : List SMT.𝒱} (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
  {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ} (den_t : ⟦S.min.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩)
  (vars_used : ∀ v ∈ S.min.vars, v ∈ used) (Λ_inv : ∀ v ∈ S.min.vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm S.min E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars S.min ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv S.min → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» S.min ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv S.min, (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt S.min →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦S.min.abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                    ∃ Δ'_alt,
                                                      ∃ (hcov_alt : RenamingContext.CoversFV Δ'_alt t'),
                                                        ∃ denT_alt,
                                                          RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                                                            (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                              (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                              ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                                                ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄ := by
  exact fun s a => trivial

theorem encodeTerm_spec.max_case.{u} (S : B.Term)
  (ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ S : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv S, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» S →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦S.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ S.vars, v ∈ used) →
                      (∀ v ∈ S.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm S E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars S ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv S → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» S ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv S, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt S →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦S.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (E : B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ S.max : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv S.max, («Δ» v).isSome = true) {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» S.max) {used : List SMT.𝒱} (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
  {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ} (den_t : ⟦S.max.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩)
  (vars_used : ∀ v ∈ S.max.vars, v ∈ used) (Λ_inv : ∀ v ∈ S.max.vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm S.max E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars S.max ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv S.max → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» S.max ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv S.max, (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt S.max →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦S.max.abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                    ∃ Δ'_alt,
                                                      ∃ (hcov_alt : RenamingContext.CoversFV Δ'_alt t'),
                                                        ∃ denT_alt,
                                                          RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                                                            (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                              (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                              ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                                                ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄ := by
  exact fun s a => trivial

theorem encodeTerm_spec.card_case.{u} (S : B.Term)
  (ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ S : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv S, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» S →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦S.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ S.vars, v ∈ used) →
                      (∀ v ∈ S.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm S E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars S ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv S → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» S ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv S, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt S →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦S.abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                                              some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                                            ∃ Δ'_alt,
                                                                              ∃ (hcov_alt :
                                                                                RenamingContext.CoversFV Δ'_alt t'),
                                                                                ∃ denT_alt,
                                                                                  RenamingContext.Extends Δ'_alt
                                                                                      Δ₀_alt ∧
                                                                                    (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                                                      (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                                                      ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ =
                                                                                          some denT_alt ∧
                                                                                        ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ
                                                                                          denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄)
  (E : B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ |S|ᴮ : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv (|S|ᴮ), («Δ» v).isSome = true) {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (|S|ᴮ)) {used : List SMT.𝒱} (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
  {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ} (den_t : ⟦|S|ᴮ.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩)
  (vars_used : ∀ v ∈ |S|ᴮ.vars, v ∈ used) (Λ_inv : ∀ v ∈ |S|ᴮ.vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (|S|ᴮ) E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (|S|ᴮ) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv (|S|ᴮ) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (|S|ᴮ) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv (|S|ᴮ), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (|S|ᴮ) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦|S|ᴮ.abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
                                                    ∃ Δ'_alt,
                                                      ∃ (hcov_alt : RenamingContext.CoversFV Δ'_alt t'),
                                                        ∃ denT_alt,
                                                          RenamingContext.Extends Δ'_alt Δ₀_alt ∧
                                                            (∀ v ∉ E'.usedVars, Δ'_alt v = none) ∧
                                                              (∀ v (d : SMT.Dom), Δ'_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) ∧
                                                              ⟦t'.abstract Δ'_alt hcov_alt⟧ˢ = some denT_alt ∧
                                                                ⟨T_alt, ⟨α, hT_alt⟩⟩ ≘ᶻ denT_alt ∧
                                                                                        (∀ v, Δ'_alt v ≠ none → v ∈ Γ')⌝⦄ := by
  exact fun s a => trivial
