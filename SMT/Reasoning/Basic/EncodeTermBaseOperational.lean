import SMT.Reasoning.Basic.StateSpecs

set_option mvcgen.warning false

open Std.Do B SMT ZFSet

/-! # Axiom-free operational semantics for encoded base sets -/

namespace encodeTerm_base_operational

theorem intSet.{u} {Λ : SMT.TypeContext} {n : ℕ} (E : B.Env) {α : BType}
    (_typ_t : E.context ⊢ᴮ B.Term.ℤ : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv B.Term.ℤ, («Δ» v).isSome = true)
    {used : List SMT.𝒱}
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (den_t : ⟦B.Term.ℤ.abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩) :
    ⦃fun (⟨E0, Λ'⟩ : EncoderState) ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm B.Term.ℤ E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜E'.freshvarsc = n + 1 ∧ Γ' = Λ ∧
        σ = α.toSMTType ∧ Γ' ⊢ˢ t' : σ ∧
        ∃ (hΔ : RenamingContext.CoversFV
            (B.RenamingContext.toSMT «Δ») t'),
          ∃ denT',
            ⟦t'.abstract (B.RenamingContext.toSMT «Δ») hΔ⟧ˢ =
                some denT' ∧
              RDom (⟨T, ⟨α, hT⟩⟩ : B.Dom) denT'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, _St_sub, rfl⟩ := pre

  rw [encodeTerm]

  rw [B.Term.abstract, B.denote, Option.pure_def,
    Option.some_inj] at den_t
  injection den_t with T_eq heq
  subst T_eq
  injection heq with α_eq heq
  subst α_eq
  clear heq

  mspec Std.Do.Spec.get_StateT
  mspec SMT.freshVar_spec (Γ := St.types) (τ := .int)
    (n := St.env.freshvarsc) (used := St.env.usedVars)
  case post.success v =>
    mrename_i pre
    mintro ∀St'
    mpure pre
    obtain ⟨types_eq, v_notMem, freshvarsc_eq, _, _⟩ := pre
    mspec Std.Do.Spec.modifyGet_StateT
    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    · rw [freshvarsc_eq]
    · trivial
    · rfl
    · apply SMT.Typing.lambda
      · intro _ h
        rw [List.mem_singleton] at h
        obtain ⟨⟩ := h
        exact v_notMem
      · simp only [SMT.bv, List.mem_cons, List.not_mem_nil,
          or_false, not_false_eq_true, implies_true]
      · apply Nat.zero_lt_succ
      · apply SMT.Typing.bool
      · rfl
    · exists ?_
      · intro w hw
        simp only [SMT.fv, List.mem_removeAll_iff] at hw
        nomatch hw.1
      · exists ⟨
          λᶻ: Int → 𝔹
            | z ↦ zftrue,
          .fun .int .bool,
          ?_⟩
        · exact mem_funs_of_lambda fun _ ↦ ZFBool.zftrue_mem_𝔹
        · and_intros
          · rw [SMT.Term.abstract,
              dite_cond_eq_true (eq_true (by rfl))]
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
              Fin.val_eq_zero, List.getElem_cons_zero,
              SMT.Term.abstract.go, Matrix.head_fin_const,
              SMT.Term.abstract]
            simp only [Function.OfArity.uncurry,
              Function.FromTypes.uncurry, Nat.reduceAdd]
            simp only [SMT.denote, gt_iff_lt, Nat.lt_add_one,
              ↓reduceDIte, mem_union, mem_prod, mem_singleton,
              exists_eq_left, Option.pure_def, Option.isSome_some,
              implies_true, Option.get_some, Nat.add_one_sub_one,
              Fin.zero_eta, Fin.isValue, ZFSet.get, get.eq_1,
              dite_eq_ite, Nat.sub_self, Fin.foldr_zero,
              Option.some.injEq]
            congr 1
            · rw [Fin.foldr_zero]
              simp only [hasArity, mem_union, mem_prod,
                mem_singleton, exists_eq_left, forall_const,
                true_and, SMTType.toZFSet]
              rw [ZFSet.lambda_ext_iff]
              · intro z hz
                split_ifs with h
                · rfl
                · rw [forall_const, true_and] at h
                  nomatch h hz
              · intro x hx
                split_ifs with h
                · exact ZFBool.mem_ofBool_𝔹 true
                · rw [forall_const, true_and] at h
                  nomatch h hx
            · congr 1
              · funext τ
                rw [Fin.foldr_zero]
                simp only [SMTType.toZFSet, hasArity, mem_union,
                  mem_prod, mem_singleton, exists_eq_left,
                  forall_const, true_and, eq_iff_iff]
                apply (Eq.to_iff <| congrArg (· ∈ ⟦τ⟧ᶻ) ·)
                rw [ZFSet.lambda_ext_iff]
                intro z hz
                split_ifs with h
                · rfl
                · rw [forall_const, true_and] at h
                  nomatch h hz
                · intro x hx
                  split_ifs with h
                  · exact ZFBool.mem_ofBool_𝔹 true
                  · rw [forall_const, true_and] at h
                    nomatch h hx
              · apply proof_irrel_heq
          · rfl
          · rw [retract]
            dsimp
            ext1 z
            iff_intro hz hz
            · rw [ZFSet.mem_sep] at hz
              exact hz.1
            · rw [ZFSet.mem_sep]
              apply And.intro hz
              simp only [BType.toZFSet,
                dite_cond_eq_true (eq_true hz)]
              rw [dite_cond_eq_true (eq_true ?_)]
              · rw [fapply_lambda
                  (fun _ ↦ ZFBool.zftrue_mem_𝔹)
                  (fapply_mem_range _ _)]
              · exact lambda_isFunc fun _ ↦ ZFBool.zftrue_mem_𝔹

theorem boolSet.{u} {Λ : SMT.TypeContext} {n : ℕ} (E : B.Env) {α : BType}
    (_typ_t : E.context ⊢ᴮ B.Term.𝔹 : α)
    {«Δ» : B.RenamingContext.Context}
    (Δ_fv : ∀ v ∈ B.fv B.Term.𝔹, («Δ» v).isSome = true)
    {used : List SMT.𝒱}
    {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
    (den_t : ⟦B.Term.𝔹.abstract «Δ» Δ_fv⟧ᴮ =
      some ⟨T, ⟨α, hT⟩⟩) :
    ⦃fun (⟨E0, Λ'⟩ : EncoderState) ↦
      ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧
        Λ.keys ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm B.Term.𝔹 E
    ⦃⇓? (⟨t', σ⟩ : SMT.Term × SMTType) ⟨E', Γ'⟩ =>
      ⌜E'.freshvarsc = n + 1 ∧ Γ' = Λ ∧
        σ = α.toSMTType ∧ Γ' ⊢ˢ t' : σ ∧
        ∃ (hΔ : RenamingContext.CoversFV
            (B.RenamingContext.toSMT «Δ») t'),
          ∃ denT',
            ⟦t'.abstract (B.RenamingContext.toSMT «Δ») hΔ⟧ˢ =
                some denT' ∧
              RDom (⟨T, ⟨α, hT⟩⟩ : B.Dom) denT'⌝⦄ := by
  mstart
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, _St_sub, rfl⟩ := pre

  rw [encodeTerm]

  rw [B.Term.abstract, B.denote, Option.pure_def,
    Option.some_inj] at den_t
  injection den_t with T_eq heq
  subst T_eq
  injection heq with α_eq heq
  subst α_eq
  clear heq

  mspec Std.Do.Spec.get_StateT
  mspec SMT.freshVar_spec (Γ := St.types) (τ := .bool)
    (n := St.env.freshvarsc) (used := St.env.usedVars)
  case post.success v =>
    mrename_i pre
    mintro ∀St'
    mpure pre
    obtain ⟨types_eq, v_notMem, freshvarsc_eq, _, _⟩ := pre
    mspec Std.Do.Spec.modifyGet_StateT
    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    · rw [freshvarsc_eq]
    · trivial
    · rfl
    · apply SMT.Typing.lambda
      · intro _ h
        rw [List.mem_singleton] at h
        obtain ⟨⟩ := h
        exact v_notMem
      · simp only [SMT.bv, List.mem_cons, List.not_mem_nil,
          or_false, not_false_eq_true, implies_true]
      · apply Nat.zero_lt_succ
      · apply SMT.Typing.bool
      · rfl
    · exists ?_
      · intro w hw
        simp only [SMT.fv, List.mem_removeAll_iff] at hw
        nomatch hw.1
      · exists ⟨
          λᶻ: .𝔹 → .𝔹
            | z ↦ zftrue,
          .fun .bool .bool,
          ?_⟩
        · exact mem_funs_of_lambda fun _ ↦ ZFBool.zftrue_mem_𝔹
        · and_intros
          · rw [SMT.Term.abstract,
              dite_cond_eq_true (eq_true (by rfl))]
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
              Fin.val_eq_zero, List.getElem_cons_zero,
              SMT.Term.abstract.go, Matrix.head_fin_const,
              SMT.Term.abstract]
            simp only [Function.OfArity.uncurry,
              Function.FromTypes.uncurry, Nat.reduceAdd]
            simp only [SMT.denote, gt_iff_lt, Nat.lt_add_one,
              ↓reduceDIte, mem_insert_iff, subset_refl,
              subset_of_empty, mem_singleton, Option.pure_def,
              Option.isSome_some, implies_true, Option.get_some,
              Nat.add_one_sub_one, Fin.zero_eta, Fin.isValue,
              ZFSet.get, dite_eq_ite, Nat.sub_self,
              Fin.foldr_zero, Option.some.injEq]
            congr 1
            · rw [Fin.foldr_zero]
              simp only [SMTType.toZFSet, hasArity,
                forall_const, true_and]
              rw [ZFSet.lambda_ext_iff]
              · intro z hz
                split_ifs with h
                · rfl
                · rw [forall_const, true_and] at h
                  nomatch h hz
              · intro x hx
                split_ifs with h
                · exact ZFBool.mem_ofBool_𝔹 true
                · rw [forall_const, true_and] at h
                  nomatch h hx
            · congr 1
              · funext τ
                rw [Fin.foldr_zero]
                simp only [SMTType.toZFSet, hasArity,
                  forall_const, true_and, eq_iff_iff]
                apply (Eq.to_iff <| congrArg (· ∈ ⟦τ⟧ᶻ) ·)
                rw [ZFSet.lambda_ext_iff]
                intro z hz
                split_ifs with h
                · rfl
                · rw [forall_const, true_and] at h
                  nomatch h hz
                · intro x hx
                  split_ifs with h
                  · exact ZFBool.mem_ofBool_𝔹 true
                  · rw [forall_const, true_and] at h
                    nomatch h hx
              · apply proof_irrel_heq
          · rfl
          · rw [retract]
            dsimp
            ext1 z
            iff_intro hz hz
            · rw [ZFSet.mem_sep] at hz
              exact hz.1
            · rw [ZFSet.mem_sep]
              apply And.intro hz
              simp only [BType.toZFSet,
                dite_cond_eq_true (eq_true hz)]
              rw [dite_cond_eq_true (eq_true ?_)]
              · rw [fapply_lambda
                  (fun _ ↦ ZFBool.zftrue_mem_𝔹)
                  (fapply_mem_range _ _)]
              · exact lambda_isFunc fun _ ↦ ZFBool.zftrue_mem_𝔹

end encodeTerm_base_operational
