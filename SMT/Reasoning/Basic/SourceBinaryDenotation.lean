import SMT.Reasoning.Defs

open B ZFSet

/-! # Source denotation inversion for binary operators -/

namespace SourceBinaryDenotation.Arith

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

theorem typingE {G : B.TypeContext} {x y : B.Term} {op : BinOp} :
    G ⊢ᴮ op.term x y : op.resultType → G ⊢ᴮ x : .int ∧ G ⊢ᴮ y : .int := by
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

theorem denote_inv.{u} (op : BinOp) {G : B.TypeContext} {x y : B.Term}
    (typ_t : G ⊢ᴮ op.term x y : op.resultType) {«Δ» : B.𝒱 → Option B.Dom}
    (Δ_fv : ∀ v ∈ B.fv (op.term x y), («Δ» v).isSome = true)
    {T : ZFSet.{u}} {hT : T ∈ ⟦op.resultType⟧ᶻ}
    (den_t : ⟦(op.term x y).abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨op.resultType, hT⟩⟩) :
    ∃ X, ∃ hX : X ∈ ⟦BType.int⟧ᶻ,
      ⟦x.abstract «Δ» (op.leftFVCert Δ_fv)⟧ᴮ =
        some ⟨X, ⟨BType.int, hX⟩⟩ ∧
      ∃ Y, ∃ hY : Y ∈ ⟦BType.int⟧ᶻ,
        ⟦y.abstract «Δ» (op.rightFVCert Δ_fv)⟧ᴮ =
          some ⟨Y, ⟨BType.int, hY⟩⟩ ∧
        op.eval X Y = T := by
  classical
  obtain ⟨typ_x, typ_y⟩ := op.typingE typ_t
  cases op <;> simp [BinOp.term, BinOp.resultType, BinOp.eval] at typ_t den_t ⊢
  all_goals
    rw [B.Term.abstract, B.denote, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at den_t
    obtain ⟨⟨X, alpha, hX⟩, den_x, eq⟩ := den_t
    cases alpha <;> simp_all only [reduceCtorEq]
    rw [Option.bind_eq_some_iff] at eq
    obtain ⟨⟨Y, beta, hY⟩, den_y, eq⟩ := eq
    cases beta <;> simp_all only [reduceCtorEq]
    rw [Option.some_inj] at eq
    injection eq with T_eq _
    exact ⟨X, ⟨hX, rfl⟩, Y, ⟨hY, rfl⟩, T_eq⟩

end SourceBinaryDenotation.Arith
