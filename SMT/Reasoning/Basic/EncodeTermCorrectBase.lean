import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Axioms

set_option mvcgen.warning false

open Std.Do B SMT ZFSet

abbrev EncPS : PostShape := PostShape.arg EncoderState (PostShape.except String PostShape.pure)

abbrev EncodeTermPre (Λ : SMT.TypeContext) (n : ℕ) : EncoderState → Prop :=
  fun ⟨E, Λ'⟩ ↦ Λ' = Λ ∧ E.freshvarsc = n

abbrev EncodeTermPost.{u_1}
  (Λ : SMT.TypeContext) (α : BType) («Δ» : B.𝒱 → _root_.Option B.Dom)
  (T : ZFSet.{u_1}) (hT : T ∈ ⟦α⟧ᶻ) :
  (SMT.Term × SMTType) → EncoderState → Prop :=
  fun ⟨t', σ⟩ ⟨E', Γ'⟩ ↦
    Λ ⊆ Γ' ∧
      σ = α.toSMTType ∧
        Γ' ⊢ˢ t' : σ ∧
          ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
            ∃ denT',
              ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧
                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'

abbrev EncodeTermIH.{u_1} (t : B.Term) : Prop :=
  ∀ (E : B.Env) {Λ0 : SMT.TypeContext} {α : BType},
    E.context ⊢ᴮ t : α →
      ∀ {«Δ» : B.𝒱 → _root_.Option B.Dom} (Δ_fv : ∀ v ∈ B.fv t, («Δ» v).isSome = true) {T : ZFSet.{u_1}}
          {hT : T ∈ ⟦α⟧ᶻ},
          ⟦t.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
            ∀ {n : ℕ},
              ⦃fun E ↦ ⌜EncodeTermPre Λ0 n E⌝⦄
              encodeTerm t E
              ⦃⇓? t'σ Env' => ⌜EncodeTermPost (Λ := Λ0) (α := α) («Δ» := «Δ») (T := T) (hT := hT) t'σ Env'⌝⦄


theorem encodeTerm_spec.ℤ.{u_1} {Λ : SMT.TypeContext} {n : ℕ} (E : B.Env) {α : BType}
  (typ_t : E.context ⊢ᴮ .ℤ : α) {«Δ» : B.𝒱 → Option B.Dom} (Δ_fv : ∀ v ∈ B.fv Term.ℤ, («Δ» v).isSome = true)
  {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ} (den_t : ⟦Term.ℤ.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, α, hT⟩) :
  ⦃fun E ↦ ⌜EncodeTermPre Λ n E⌝⦄
    encodeTerm .ℤ E
  ⦃⇓? ⟨t', σ⟩ ⟨E', Γ'⟩ =>
    ⌜E'.freshvarsc = n + 1 ∧ Γ' = Λ ∧
    σ = α.toSMTType ∧ Γ' ⊢ˢ t' : σ ∧
    ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
      ∃ denT', ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, α, hT⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl⟩ := pre

  rw [encodeTerm]

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t
  injection den_t with T_eq heq
  subst T_eq
  injection heq with α_eq heq
  subst α_eq
  clear heq

  mspec Std.Do.Spec.get_StateT
  mspec freshVar_spec (Γ := S.types) (τ := .int) (n := S.env.freshvarsc) (used := S.env.usedVars)
  case post.success 𝓋 =>
    mrename_i pre
    mintro ∀S'
    mpure pre
    obtain ⟨types_eq, 𝓋_notMem, freshvarsc_eq, _, _⟩ := pre
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
        exact 𝓋_notMem
      · simp only [List.mem_cons, List.not_mem_nil, or_false, SMT.bv, not_false_eq_true, implies_true]
      · apply Nat.zero_lt_succ
      · apply SMT.Typing.bool
      · rfl
    · exists ?_
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff] at hv
        nomatch hv.1
      · exists ⟨
          λᶻ: Int → 𝔹
            |   z ↦ zftrue,
          .fun .int .bool,
          ?_⟩
        · exact mem_funs_of_lambda fun _ ↦ ZFBool.zftrue_mem_𝔹
        · and_intros
          · rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl))]
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.val_eq_zero, List.getElem_cons_zero, SMT.Term.abstract.go, List.length_nil, List.length_cons, Nat.reduceAdd,
              Matrix.head_fin_const, SMT.Term.abstract]
            simp only [Function.OfArity.uncurry, Function.FromTypes.uncurry, Nat.reduceAdd]
            simp only [SMT.denote, gt_iff_lt, Nat.lt_add_one, ↓reduceDIte, mem_union, mem_prod, mem_singleton, exists_eq_left, Option.pure_def, Option.isSome_some, implies_true, Option.get_some, Nat.add_one_sub_one, Fin.zero_eta, Fin.isValue, ZFSet.get, get.eq_1, dite_eq_ite, Nat.sub_self, Fin.foldr_zero, Option.some.injEq]
            congr 1
            · rw [Fin.foldr_zero]
              simp only [hasArity, mem_union, mem_prod, mem_singleton,
                exists_eq_left, forall_const, true_and, SMTType.toZFSet]
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
                simp only [SMTType.toZFSet, hasArity, mem_union, mem_prod, mem_singleton, exists_eq_left, forall_const, true_and, eq_iff_iff]

                apply (Eq.to_iff <| congrArg (· ∈ ⟦τ⟧ᶻ) ·) --NOTE: engineering workaround
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
              obtain ⟨mem_int, _⟩ := hz
              exact mem_int
            · rw [ZFSet.mem_sep]
              apply And.intro hz
              simp only [BType.toZFSet, dite_cond_eq_true (eq_true hz)]
              rw [dite_cond_eq_true (eq_true ?_)]
              · rw [fapply_lambda (fun _ ↦ ZFBool.zftrue_mem_𝔹) (fapply_mem_range _ _)]
              · exact lambda_isFunc fun _ ↦ ZFBool.zftrue_mem_𝔹

theorem encodeTerm_spec.ℤ_case.{u} (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
  (typ_t : E.context ⊢ᴮ Term.ℤ : α) {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv Term.ℤ, («Δ» v).isSome = true)
  {Δ₀ : SMT.RenamingContext.Context} (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» Term.ℤ) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦Term.ℤ.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ Term.ℤ.vars, v ∈ used)
  (Λ_inv : ∀ v ∈ Term.ℤ.vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm Term.ℤ E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars Term.ℤ ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv Term.ℤ → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» Term.ℤ ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv Term.ℤ, (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt Term.ℤ →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦Term.ℤ.abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
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
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre

  rw [encodeTerm]

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t
  injection den_t with T_eq heq
  subst T_eq
  injection heq with α_eq heq
  subst α_eq
  clear heq

  mspec Std.Do.Spec.get_StateT
  mspec freshVar_spec (Γ := S.types) (τ := .int) (n := S.env.freshvarsc) (used := S.env.usedVars)
  case post.success 𝓋 =>
    mrename_i pre
    mintro ∀S'
    mpure pre
    obtain ⟨types_eq, 𝓋_notMem, freshvarsc_eq, used_eq, 𝓋_neq_used⟩ := pre
    mspec Std.Do.Spec.modifyGet_StateT
    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    · intro x hx
      rw [used_eq, St_used_eq]
      exact List.mem_cons_of_mem _ hx
    · exact fun _ => id
    · rw [used_eq]
      intro x hx
      exact List.mem_cons_of_mem _ (St_sub hx)
    · intro x hx
      rw [B.fv] at hx
      contradiction
    · rfl
    · apply SMT.Typing.lambda
      · intro _ h
        rw [List.mem_singleton] at h
        obtain ⟨⟩ := h
        exact 𝓋_notMem
      · simp only [SMT.bv, List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true, implies_true]
      · apply Nat.zero_lt_succ
      · apply SMT.Typing.bool
      · rfl
    · exact fun _ _ h _ => h
    · refine ⟨Δ₀, ?_, ?_⟩
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff] at hv
        nomatch hv.1
      · and_intros
        · exact RenamingContext.extends_refl Δ₀
        · exact Δ₀_ext
        · intro v hv_not_used
          have hv_not_init : v ∉ used := by
            intro hv_in_used
            have : v ∈ S'.env.usedVars := by
              rw [used_eq, St_used_eq]
              exact List.mem_cons_of_mem _ hv_in_used
            exact hv_not_used this
          exact Δ₀_none_out v hv_not_init
        · refine ⟨⟨
            λᶻ: Int → 𝔹
              | z ↦ zftrue,
            .fun .int .bool,
            ?_⟩, ?_, ?_⟩
          · exact mem_funs_of_lambda fun _ ↦ ZFBool.zftrue_mem_𝔹
          · rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl))]
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.val_eq_zero, List.getElem_cons_zero,
              SMT.Term.abstract.go, List.length_nil, List.length_cons, Nat.reduceAdd, Matrix.head_fin_const,
              SMT.Term.abstract]
            simp only [Function.OfArity.uncurry, Function.FromTypes.uncurry, Nat.reduceAdd]
            simp only [SMT.denote, gt_iff_lt, Nat.lt_add_one, ↓reduceDIte, mem_union, mem_prod, mem_singleton,
              exists_eq_left, Option.pure_def, Option.isSome_some, implies_true, Option.get_some,
              Nat.add_one_sub_one, Fin.zero_eta, Fin.isValue, ZFSet.get, get.eq_1, dite_eq_ite, Nat.sub_self,
              Fin.foldr_zero, Option.some.injEq]
            congr 1
            · rw [Fin.foldr_zero]
              simp only [hasArity, mem_union, mem_prod, mem_singleton, exists_eq_left, forall_const, true_and,
                SMTType.toZFSet]
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
                simp only [SMTType.toZFSet, hasArity, mem_union, mem_prod, mem_singleton, exists_eq_left,
                  forall_const, true_and, eq_iff_iff]

                apply (Eq.to_iff <| congrArg (· ∈ ⟦τ⟧ᶻ) ·) --NOTE: engineering workaround
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
          · refine ⟨⟨rfl, ?_⟩, ?_⟩
            · dsimp [retract]
              ext1 z
              iff_intro hz hz
              · rw [ZFSet.mem_sep] at hz
                obtain ⟨mem_int, _⟩ := hz
                exact mem_int
              · rw [ZFSet.mem_sep]
                apply And.intro hz
                simp only [BType.toZFSet, dite_cond_eq_true (eq_true hz)]
                rw [dite_cond_eq_true (eq_true ?_)]
                · rw [fapply_lambda (fun _ ↦ ZFBool.zftrue_mem_𝔹) (fapply_mem_range _ _)]
                · exact lambda_isFunc fun _ ↦ ZFBool.zftrue_mem_𝔹
            · -- Alt universality: ℤ is a closed term, same denotation regardless of Δ_alt
              intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
              rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t_alt
              have hT_val : ZFSet.Int = T_alt := congrArg (·.fst) den_t_alt
              subst hT_val
              -- Δ₀_alt covers the lambda (no fv)
              have hcov_alt : RenamingContext.CoversFV Δ₀_alt
                  ((λˢ [𝓋]) [SMTType.int] (SMT.Term.bool true)) :=
                fun v hv => by simp only [SMT.fv, List.mem_removeAll_iff] at hv; nomatch hv.1
              -- The lambda denotes to the same constant function
              set denT_alt : SMT.Dom := ⟨
                λᶻ: Int → 𝔹 | z ↦ zftrue, .fun .int .bool,
                mem_funs_of_lambda fun _ ↦ ZFBool.zftrue_mem_𝔹⟩
              refine ⟨Δ₀_alt, hcov_alt, denT_alt,
                RenamingContext.extends_refl Δ₀_alt, Δ₀_alt_none_out, Δ₀_alt_wt, ?_, ?_,
                fun v hv => nomatch SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext v hv⟩
              · -- Denotation: same as original case
                rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl))]
                simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.val_eq_zero,
                  List.getElem_cons_zero, SMT.Term.abstract.go, SMT.Term.abstract]
                simp only [Function.OfArity.uncurry, Function.FromTypes.uncurry, Nat.reduceAdd]
                simp only [SMT.denote, gt_iff_lt, Nat.lt_add_one, ↓reduceDIte, mem_union,
                  mem_prod, mem_singleton, exists_eq_left, Option.pure_def, Option.isSome_some,
                  implies_true, Option.get_some, Nat.add_one_sub_one, Fin.zero_eta, Fin.isValue,
                  ZFSet.get, get.eq_1, dite_eq_ite, Nat.sub_self, Fin.foldr_zero,
                  Option.some.injEq]
                congr 1
                · rw [Fin.foldr_zero]
                  simp only [hasArity, mem_union, mem_prod, mem_singleton, exists_eq_left,
                    forall_const, true_and, SMTType.toZFSet]
                  rw [ZFSet.lambda_ext_iff]
                  · intro z hz; split_ifs with h
                    · rfl
                    · rw [forall_const, true_and] at h; nomatch h hz
                  · intro x hx; split_ifs with h
                    · exact ZFBool.mem_ofBool_𝔹 true
                    · rw [forall_const, true_and] at h; nomatch h hx
                · congr 1
                  · funext τ; rw [Fin.foldr_zero]
                    simp only [SMTType.toZFSet, hasArity, mem_union, mem_prod, mem_singleton,
                      exists_eq_left, forall_const, true_and, eq_iff_iff]
                    apply (Eq.to_iff <| congrArg (· ∈ ⟦τ⟧ᶻ) ·)
                    rw [ZFSet.lambda_ext_iff]
                    intro z hz; split_ifs with h
                    · rfl
                    · rw [forall_const, true_and] at h; nomatch h hz
                    · intro x hx; split_ifs with h
                      · exact ZFBool.mem_ofBool_𝔹 true
                      · rw [forall_const, true_and] at h; nomatch h hx
                  · apply proof_irrel_heq
              · -- RDom: type component + retract component
                constructor
                · rfl
                · dsimp [retract]; ext1 z; iff_intro hz hz
                  · rw [ZFSet.mem_sep] at hz; exact hz.1
                  · rw [ZFSet.mem_sep]; apply And.intro hz
                    simp only [BType.toZFSet, dite_cond_eq_true (eq_true hz)]
                    rw [dite_cond_eq_true (eq_true ?_)]
                    · rw [fapply_lambda (fun _ ↦ ZFBool.zftrue_mem_𝔹) (fapply_mem_range _ _)]
                    · exact lambda_isFunc fun _ ↦ ZFBool.zftrue_mem_𝔹

theorem encodeTerm_spec.𝔹.{u_1} {Λ : SMT.TypeContext} {n : ℕ} (E : B.Env) {α : BType}
  (typ_t : E.context ⊢ᴮ .𝔹 : α) {«Δ» : B.𝒱 → Option B.Dom} (Δ_fv : ∀ v ∈ B.fv Term.𝔹, («Δ» v).isSome = true)
  {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ} (den_t : ⟦Term.𝔹.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩):
  ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n⌝⦄
    encodeTerm Term.𝔹 E
  ⦃⇓? ⟨t', σ⟩ ⟨E', Γ'⟩ =>
    ⌜E'.freshvarsc = n + 1 ∧ Γ' = Λ ∧
    σ = α.toSMTType ∧
    Γ' ⊢ˢ t' : σ ∧
    ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
      ∃ denT',
        ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, hlen⟩ := pre

  rw [encodeTerm]

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t
  injection den_t with T_eq heq
  subst T_eq
  injection heq with α_eq heq
  subst α_eq
  clear heq

  mspec Std.Do.Spec.get_StateT
  mspec freshVar_spec (used := S.env.usedVars)
  case post.success 𝓋 =>
    mrename_i pre
    mintro ∀S'
    mpure pre
    obtain ⟨types_eq, 𝓋_notMem, freshvarsc_eq, _, _⟩ := pre
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
        exact 𝓋_notMem
      · simp only [SMT.bv, List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true, implies_true]
      · apply Nat.zero_lt_succ
      · apply SMT.Typing.bool
      · rfl
    · exists ?_
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff] at hv
        nomatch hv.1
      · exists ⟨
          λᶻ: .𝔹 → .𝔹
            |   z ↦ zftrue,
          .fun .bool .bool,
          ?_⟩
        · exact mem_funs_of_lambda fun _ ↦ ZFBool.zftrue_mem_𝔹
        · and_intros
          · rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl))]
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.val_eq_zero, List.getElem_cons_zero, SMT.Term.abstract.go, List.length_nil, List.length_cons, Nat.reduceAdd,
              Matrix.head_fin_const, SMT.Term.abstract]
            simp only [Function.OfArity.uncurry, Function.FromTypes.uncurry, Nat.reduceAdd]
            simp only [SMT.denote, gt_iff_lt, Nat.lt_add_one, ↓reduceDIte, mem_insert_iff,
              subset_refl, subset_of_empty, mem_singleton, Option.pure_def, Option.isSome_some,
              implies_true, Option.get_some, Nat.add_one_sub_one, Fin.zero_eta, Fin.isValue,
              ZFSet.get, dite_eq_ite, Nat.sub_self, Fin.foldr_zero,
              Option.some.injEq]
            congr 1
            · rw [Fin.foldr_zero]
              simp only [SMTType.toZFSet, hasArity, forall_const, true_and]
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
                simp only [SMTType.toZFSet, hasArity, forall_const, true_and, eq_iff_iff]
                apply (Eq.to_iff <| congrArg (· ∈ ⟦τ⟧ᶻ) ·) --NOTE: engineering workaround
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
              obtain ⟨mem_int, _⟩ := hz
              exact mem_int
            · rw [ZFSet.mem_sep]
              apply And.intro hz
              simp only [BType.toZFSet, dite_cond_eq_true (eq_true hz)]
              rw [dite_cond_eq_true (eq_true ?_)]
              · rw [fapply_lambda (fun _ ↦ ZFBool.zftrue_mem_𝔹) (fapply_mem_range _ _)]
              · exact lambda_isFunc fun _ ↦ ZFBool.zftrue_mem_𝔹

theorem encodeTerm_spec.var.{u_1} {Λ : SMT.TypeContext} {n : ℕ} (v : B.𝒱) (E : B.Env) {α : BType}
  (typ_t : E.context ⊢ᴮ .var v : α) {«Δ» : B.𝒱 → Option B.Dom}
  (Δ_fv : ∀ v_1 ∈ B.fv (B.Term.var v), («Δ» v_1).isSome = true) {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(B.Term.var v).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, α, hT⟩) :
  ⦃fun ⟨E', Λ'⟩ ↦ ⌜Λ' = Λ ∧ E'.freshvarsc = n⌝⦄
    encodeTerm (.var v) E
  ⦃⇓? ⟨t', σ⟩ ⟨E', Γ'⟩ =>
    ⌜E'.freshvarsc = n ∧
      Γ' = Λ ∧ σ = α.toSMTType ∧ Γ' ⊢ˢ t' : σ ∧
      ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
      ∃ denT',
        ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, α, hT⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl⟩ := pre

  rw [encodeTerm]
  mvcgen
  case vc1 τ τ_lookup =>
    and_intros
    · trivial
    · trivial
    · rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_get] at den_t
      have hΔ : ∀ v' ∈ SMT.fv (.var v), (RenamingContext.toSMT «Δ» v').isSome = true := by
        intro _ hv
        rw [SMT.fv, List.mem_singleton, eq_comm] at hv
        subst hv
        simp only [RenamingContext.toSMT, den_t, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.isSome_some]

      set den₁ := RenamingContext.toSMT «Δ» v with den₁_def
      simp only [RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind] at den₁_def
      rw [den_t, Option.bind_some] at den₁_def

      have := @PHOAS.denote_welltyped_eq
        (t := (SMT.Term.var v).abstract (RenamingContext.toSMT «Δ») (fun v hv ↦ by apply hΔ; simpa only [B.fv, SMT.fv] using hv))
      simp [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_get] at this
      dsimp [den₁] at den₁_def
      have := @this _ _ _ ?_ den₁_def
      on_goal 2 =>
        use S.types.abstract (RenamingContext.toSMT «Δ»), PHOAS.WFTC.of_abstract, τ
        apply SMT.PHOAS.Typing.of_abstract
        exact SMT.Typing.var S.types v τ τ_lookup
      exact this
    · apply SMT.Typing.var
      exact τ_lookup
    · rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_get] at den_t
      have hΔ : ∀ v' ∈ SMT.fv (.var v), (RenamingContext.toSMT «Δ» v').isSome = true := by
        intro _ hv
        rw [SMT.fv, List.mem_singleton, eq_comm] at hv
        subst hv
        simp only [RenamingContext.toSMT, den_t, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.isSome_some]

      set den₁ := RenamingContext.toSMT «Δ» v with den₁_def
      simp only [RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind] at den₁_def
      rw [den_t, Option.bind_some] at den₁_def

      use hΔ, den₁.get (Option.isSome_of_mem den₁_def)
      · unfold den₁ at den₁_def
        conv =>
          enter [1]
          change ?den_var
          conv =>
            enter [2]
            unfold den₁
            rw [Option.some_get, den₁_def]
          rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_get, den₁_def, Option.some_inj, eq_self]
        rw [true_and]
        conv =>
          enter [2,1]
          unfold den₁
          rw [den₁_def]
        constructor
        · rfl
        · exact retract_of_canonical α hT rfl

theorem encodeTerm_spec.int.{u_1} {Λ : SMT.TypeContext} {n_1 : ℕ} (n : ℤ) (E : B.Env) {α : BType}
  (typ_t : E.context ⊢ᴮ B.Term.int n : α) {«Δ» : B.𝒱 → Option B.Dom}
  (Δ_fv : ∀ v ∈ B.fv (B.Term.int n), («Δ» v).isSome = true) {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(B.Term.int n).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) :
  ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n_1⌝⦄
    encodeTerm (B.Term.int n) E
  ⦃⇓? ⟨t', σ⟩ ⟨E', Γ'⟩ =>
    ⌜E'.freshvarsc = n_1 ∧ Γ' = Λ ∧
    σ = α.toSMTType ∧ Γ' ⊢ˢ t' : σ ∧
    ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
      ∃ denT',
        ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, hlen⟩ := pre

  rw [encodeTerm]
  mspec Std.Do.Spec.pure
  mpure_intro

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t
  injection den_t with T_eq heq
  subst T_eq
  injection heq with α_eq heq
  subst α_eq
  clear heq

  and_intros
  · trivial
  · trivial
  · trivial
  · apply SMT.Typing.int
  · use ?_, ⟨ofInt n, .int, hT⟩
    · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
      and_intros
      · congr
      · rfl
      · rfl
    · intro v hv
      rw [SMT.fv, List.mem_nil_iff] at hv
      contradiction

theorem encodeTerm_spec.bool.{u_1} {Λ : SMT.TypeContext} {n : ℕ} (b : Bool) (E : B.Env) {α : BType}
  (typ_t : E.context ⊢ᴮ .bool b : α) {«Δ» : B.𝒱 → Option B.Dom}
  (Δ_fv : ∀ v ∈ B.fv (.bool b), («Δ» v).isSome = true) {T : ZFSet.{u_1}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(B.Term.bool b).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, α, hT⟩) :
  ⦃fun ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n⌝⦄
    encodeTerm (B.Term.bool b) E
  ⦃⇓? ⟨t', σ⟩ ⟨E', Γ'⟩ =>
    ⌜E'.freshvarsc = n ∧ Γ' = Λ ∧
    σ = α.toSMTType ∧
    Γ' ⊢ˢ t' : σ ∧
    ∃ (hΔ : ∀ v ∈ SMT.fv t', (RenamingContext.toSMT «Δ» v).isSome = true),
      ∃ denT',
        ⟦t'.abstract (RenamingContext.toSMT «Δ») hΔ⟧ˢ = some denT' ∧ ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT'⌝⦄ := by
  mstart
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl⟩ := pre

  rw [encodeTerm]
  mspec Std.Do.Spec.pure
  mpure_intro

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t
  injection den_t with T_eq heq
  subst T_eq
  injection heq with α_eq heq
  subst α_eq
  clear heq

  and_intros
  · trivial
  · trivial
  · trivial
  · apply SMT.Typing.bool
  · use ?_, ⟨ZFBool.ofBool b, .bool, hT⟩
    · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
      and_intros
      · congr
      · rfl
      · rfl
    · intro v hv
      rw [SMT.fv, List.mem_nil_iff] at hv
      contradiction

theorem encodeTerm_spec.𝔹_case.{u} (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
  (typ_t : E.context ⊢ᴮ Term.𝔹 : α) {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv Term.𝔹, («Δ» v).isSome = true)
  {Δ₀ : SMT.RenamingContext.Context} (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» Term.𝔹) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦Term.𝔹.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ Term.𝔹.vars, v ∈ used)
  (Λ_inv : ∀ v ∈ Term.𝔹.vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm Term.𝔹 E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars Term.𝔹 ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv Term.𝔹 → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» Term.𝔹 ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv Term.𝔹, (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt Term.𝔹 →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦Term.𝔹.abstract Δ_alt Δ_fv_alt⟧ᴮ = some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
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
  mintro pre ∀S
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre

  rw [encodeTerm]

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t
  injection den_t with T_eq heq
  subst T_eq
  injection heq with α_eq heq
  subst α_eq
  clear heq

  mspec Std.Do.Spec.get_StateT
  mspec freshVar_spec (used := S.env.usedVars)
  case post.success 𝓋 =>
    mrename_i pre
    mintro ∀S'
    mpure pre
    obtain ⟨types_eq, 𝓋_notMem, freshvarsc_eq, used_eq, 𝓋_neq_used⟩ := pre
    mspec Std.Do.Spec.modifyGet_StateT
    mspec Std.Do.Spec.pure
    mpure_intro
    and_intros
    · intro x hx
      rw [used_eq, St_used_eq]
      exact List.mem_cons_of_mem _ hx
    · exact fun _ => id
    · rw [used_eq]
      intro x hx
      exact List.mem_cons_of_mem _ (St_sub hx)
    · intro x hx
      rw [B.fv] at hx
      contradiction
    · rfl
    · apply SMT.Typing.lambda
      · intro _ h
        rw [List.mem_singleton] at h
        obtain ⟨⟩ := h
        exact 𝓋_notMem
      · simp only [List.mem_cons, List.not_mem_nil, or_false, SMT.bv, not_false_eq_true, implies_true]
      · apply Nat.zero_lt_succ
      · apply SMT.Typing.bool
      · rfl
    · exact fun _ _ h _ => h
    · refine ⟨Δ₀, ?_, ?_⟩
      · intro v hv
        simp only [SMT.fv, List.mem_removeAll_iff] at hv
        nomatch hv.1
      · and_intros
        · exact RenamingContext.extends_refl Δ₀
        · exact Δ₀_ext
        · intro v hv_not_used
          have hv_not_init : v ∉ used := by
            intro hv_in_used
            have : v ∈ S'.env.usedVars := by
              rw [used_eq, St_used_eq]
              exact List.mem_cons_of_mem _ hv_in_used
            exact hv_not_used this
          exact Δ₀_none_out v hv_not_init
        · refine ⟨⟨
            λᶻ: .𝔹 → .𝔹
              | z ↦ zftrue,
            .fun .bool .bool,
            ?_⟩, ?_, ?_⟩
          · exact mem_funs_of_lambda fun _ ↦ ZFBool.zftrue_mem_𝔹
          · rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl))]
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.val_eq_zero, List.getElem_cons_zero,
              SMT.Term.abstract.go, List.length_nil, List.length_cons, Nat.reduceAdd, Matrix.head_fin_const,
              SMT.Term.abstract]
            simp only [Function.OfArity.uncurry, Function.FromTypes.uncurry, Nat.reduceAdd]
            simp only [SMT.denote, gt_iff_lt, Nat.lt_add_one, ↓reduceDIte, mem_insert_iff, subset_refl,
              subset_of_empty, mem_singleton, Option.pure_def, Option.isSome_some, implies_true, Option.get_some,
              Nat.add_one_sub_one, Fin.zero_eta, Fin.isValue, ZFSet.get, dite_eq_ite, Nat.sub_self,
              Fin.foldr_zero, Option.some.injEq]
            congr 1
            · rw [Fin.foldr_zero]
              simp only [SMTType.toZFSet, hasArity, forall_const, true_and]
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
                simp only [SMTType.toZFSet, hasArity, forall_const, true_and, eq_iff_iff]
                apply (Eq.to_iff <| congrArg (· ∈ ⟦τ⟧ᶻ) ·) --NOTE: engineering workaround
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
          · refine ⟨⟨rfl, ?_⟩, ?_⟩
            · dsimp [retract]
              ext1 z
              iff_intro hz hz
              · rw [ZFSet.mem_sep] at hz
                obtain ⟨mem_int, _⟩ := hz
                exact mem_int
              · rw [ZFSet.mem_sep]
                apply And.intro hz
                simp only [BType.toZFSet, dite_cond_eq_true (eq_true hz)]
                rw [dite_cond_eq_true (eq_true ?_)]
                · rw [fapply_lambda (fun _ ↦ ZFBool.zftrue_mem_𝔹) (fapply_mem_range _ _)]
                · exact lambda_isFunc fun _ ↦ ZFBool.zftrue_mem_𝔹
            · intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
              rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t_alt
              have hT_val : ZFSet.𝔹 = T_alt := congrArg (·.fst) den_t_alt
              subst hT_val
              have hcov_alt : RenamingContext.CoversFV Δ₀_alt
                  ((λˢ [𝓋]) [SMTType.bool] (SMT.Term.bool true)) :=
                fun v hv => by simp only [SMT.fv, List.mem_removeAll_iff] at hv; nomatch hv.1
              set denT_alt : SMT.Dom := ⟨
                λᶻ: .𝔹 → .𝔹 | z ↦ zftrue, .fun .bool .bool,
                mem_funs_of_lambda fun _ ↦ ZFBool.zftrue_mem_𝔹⟩
              refine ⟨Δ₀_alt, hcov_alt, denT_alt,
                RenamingContext.extends_refl Δ₀_alt, Δ₀_alt_none_out, Δ₀_alt_wt, ?_, ?_,
                fun v hv => nomatch SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext v hv⟩
              · rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl))]
                simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.val_eq_zero,
                  List.getElem_cons_zero, SMT.Term.abstract.go, SMT.Term.abstract]
                simp only [Function.OfArity.uncurry, Function.FromTypes.uncurry, Nat.reduceAdd]
                simp only [SMT.denote, gt_iff_lt, Nat.lt_add_one, ↓reduceDIte, mem_insert_iff,
                  subset_refl, subset_of_empty, mem_singleton, Option.pure_def, Option.isSome_some,
                  implies_true, Option.get_some, Nat.add_one_sub_one, Fin.zero_eta, Fin.isValue,
                  ZFSet.get, dite_eq_ite, Nat.sub_self, Fin.foldr_zero, Option.some.injEq]
                congr 1
                · rw [Fin.foldr_zero]
                  simp only [SMTType.toZFSet, hasArity, forall_const, true_and]
                  rw [ZFSet.lambda_ext_iff]
                  · intro z hz; split_ifs with h
                    · rfl
                    · rw [forall_const, true_and] at h; nomatch h hz
                  · intro x hx; split_ifs with h
                    · exact ZFBool.mem_ofBool_𝔹 true
                    · rw [forall_const, true_and] at h; nomatch h hx
                · congr 1
                  · funext τ; rw [Fin.foldr_zero]
                    simp only [SMTType.toZFSet, hasArity, forall_const, true_and, eq_iff_iff]
                    apply (Eq.to_iff <| congrArg (· ∈ ⟦τ⟧ᶻ) ·)
                    rw [ZFSet.lambda_ext_iff]
                    intro z hz; split_ifs with h
                    · rfl
                    · rw [forall_const, true_and] at h; nomatch h hz
                    · intro x hx; split_ifs with h
                      · exact ZFBool.mem_ofBool_𝔹 true
                      · rw [forall_const, true_and] at h; nomatch h hx
                  · apply proof_irrel_heq
              · constructor
                · rfl
                · dsimp [retract]; ext1 z; iff_intro hz hz
                  · rw [ZFSet.mem_sep] at hz; exact hz.1
                  · rw [ZFSet.mem_sep]; apply And.intro hz
                    simp only [BType.toZFSet, dite_cond_eq_true (eq_true hz)]
                    rw [dite_cond_eq_true (eq_true ?_)]
                    · rw [fapply_lambda (fun _ ↦ ZFBool.zftrue_mem_𝔹) (fapply_mem_range _ _)]
                    · exact lambda_isFunc fun _ ↦ ZFBool.zftrue_mem_𝔹

theorem encodeTerm_spec.var_case.{u} (v : B.𝒱) (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
  (typ_t : E.context ⊢ᴮ B.Term.var v : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v_1 ∈ B.fv (B.Term.var v), («Δ» v_1).isSome = true) {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (B.Term.var v)) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(B.Term.var v).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩)
  (vars_used : ∀ v_1 ∈ (B.Term.var v).vars, v_1 ∈ used) (Λ_inv : ∀ v_1 ∈ (B.Term.var v).vars, v_1 ∈ Λ → v_1 ∈ E.context)
  {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (B.Term.var v) E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (B.Term.var v) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v_1 ∈ used, v_1 ∉ Λ → v_1 ∉ B.fv (B.Term.var v) → v_1 ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (B.Term.var v) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v_1 ∈ B.fv (B.Term.var v), (Δ_alt v_1).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (B.Term.var v) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(B.Term.var v).abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                      some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
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
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre

  rw [encodeTerm]
  mvcgen
  case vc1 τ τ_lookup =>
    and_intros
    · intro x hx
      simpa [St_used_eq] using hx
    · intro x hx
      simpa using hx
    · intro x hx
      simpa [St_used_eq] using St_sub hx
    · intro x hx
      rw [B.fv, List.mem_singleton] at hx
      subst x
      have hv_in_types : v ∈ St.types :=
        (AList.lookup_isSome).1 (Option.isSome_of_eq_some τ_lookup)
      simpa [St_used_eq] using (St_sub hv_in_types)
    · rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_get] at den_t
      have hΔ : ∀ v' ∈ SMT.fv (.var v), (RenamingContext.toSMT «Δ» v').isSome = true := by
        intro _ hv
        rw [SMT.fv, List.mem_singleton, eq_comm] at hv
        subst hv
        simp only [RenamingContext.toSMT, den_t, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.isSome_some]

      set den₁ := RenamingContext.toSMT «Δ» v with den₁_def
      simp only [RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind] at den₁_def
      rw [den_t, Option.bind_some] at den₁_def

      have := @PHOAS.denote_welltyped_eq
        (t := (SMT.Term.var v).abstract (RenamingContext.toSMT «Δ») (fun v hv ↦ by apply hΔ; simpa only [B.fv, SMT.fv] using hv))
      simp [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_get] at this
      dsimp [den₁] at den₁_def
      have := @this _ _ _ ?_ den₁_def
      on_goal 2 =>
        use St.types.abstract (RenamingContext.toSMT «Δ»), PHOAS.WFTC.of_abstract, τ
        apply SMT.PHOAS.Typing.of_abstract
        exact SMT.Typing.var St.types v τ τ_lookup
      exact this
    · exact SMT.Typing.var St.types v τ τ_lookup
    · exact fun _ _ h _ => h
    · rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_get] at den_t
      have hΔ_smt : ∀ v' ∈ SMT.fv (.var v), (RenamingContext.toSMT «Δ» v').isSome = true := by
        intro _ hv
        rw [SMT.fv, List.mem_singleton, eq_comm] at hv
        subst hv
        simp only [RenamingContext.toSMT, den_t, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.isSome_some]

      set den₁ := RenamingContext.toSMT «Δ» v with den₁_def
      simp only [RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind] at den₁_def
      rw [den_t, Option.bind_some] at den₁_def

      have hden₁_some : den₁.isSome = true := by
        simpa [den₁] using (hΔ_smt v (by simp [SMT.fv]))
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hden₁_some

      have hbase_eq : B.RenamingContext.toSMTOnFV «Δ» (B.Term.var v) v = den₁ := by
        unfold B.RenamingContext.toSMTOnFV
        simp [B.RenamingContext.toSMT, B.RenamingContext.restrictToFV_eq_of_mem (t := B.Term.var v) (v := v) (by simp [B.fv]), den₁]
      have hbase_some : B.RenamingContext.toSMTOnFV «Δ» (B.Term.var v) v = some d := by
        simpa [hbase_eq] using hd
      have hΔ₀_v : Δ₀ v = some d := Δ₀_ext hbase_some

      refine ⟨Δ₀, ?_, ?_⟩
      · intro w hw
        rw [SMT.fv, List.mem_singleton] at hw
        subst hw
        simp [hΔ₀_v]
      · and_intros
        · exact RenamingContext.extends_refl Δ₀
        · exact Δ₀_ext
        · intro w hw
          have hw' : w ∉ used := by
            intro hwu
            exact hw (by simpa [St_used_eq] using hwu)
          exact Δ₀_none_out w hw'
        · refine ⟨d, ?_, ?_⟩
          · rwa [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_get]
          · rw [hd] at den₁_def
            injection den₁_def with hd_eq
            subst d
            refine ⟨⟨rfl, ?_⟩, ?_⟩
            · exact retract_of_canonical α hT rfl
            · intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
              -- Extract Δ_alt v = some ⟨T_alt, α, hT_alt⟩
              have hΔ_alt_v : Δ_alt v = some ⟨T_alt, ⟨α, hT_alt⟩⟩ := by
                rw [B.Term.abstract, B.denote] at den_t_alt
                simp only [Option.pure_def, Option.some.injEq] at den_t_alt
                have h_isSome := Δ_fv_alt v (by simp [B.fv])
                have h_get := den_t_alt
                exact Option.some_get h_isSome ▸ congrArg some h_get
              -- toSMT Δ_alt v = canonical(T_alt)
              have h_toSMT_alt : B.RenamingContext.toSMT Δ_alt v =
                  some ⟨(ZFSet.fapply (BType.canonicalIsoSMTType α).1
                    (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType α).2.1)
                    ⟨T_alt, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType α).2.1]⟩).1,
                  ⟨α.toSMTType, ZFSet.fapply_mem_range _ _⟩⟩ := by
                simp [B.RenamingContext.toSMT, hΔ_alt_v]
              -- Δ₀_alt v = toSMT Δ_alt v (from ExtendsOnSourceFV)
              have h_onFV : B.RenamingContext.toSMTOnFV Δ_alt (B.Term.var v) v =
                  B.RenamingContext.toSMT Δ_alt v := by
                unfold B.RenamingContext.toSMTOnFV B.RenamingContext.toSMT
                congr 1
                exact B.RenamingContext.restrictToFV_eq_of_mem (show v ∈ B.fv (B.Term.var v) by simp [B.fv])
              have hΔ₀_alt_v := Δ₀_alt_ext (h_onFV ▸ h_toSMT_alt)
              -- Use Δ₀_alt; denT_alt is the value from hΔ₀_alt_v
              obtain ⟨d_alt, hΔ₀_alt_v'⟩ : ∃ d, Δ₀_alt v = some d := ⟨_, hΔ₀_alt_v⟩
              refine ⟨Δ₀_alt,
                fun w hw => by simp [SMT.fv] at hw; subst hw; rw [hΔ₀_alt_v']; simp,
                d_alt, RenamingContext.extends_refl Δ₀_alt, ?_, ?_, ?_, ?_,
                fun w hw => by
                  have h_mem := SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext w hw
                  simp [B.fv] at h_mem
                  subst h_mem
                  exact AList.lookup_isSome.1 (Option.isSome_of_eq_some τ_lookup)⟩
              · exact St_used_eq ▸ Δ₀_alt_none_out
              · exact Δ₀_alt_wt
              · simp [SMT.Term.abstract, SMT.denote, hΔ₀_alt_v']
              · have : d_alt = ⟨(ZFSet.fapply (BType.canonicalIsoSMTType α).1
                    (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType α).2.1)
                    ⟨T_alt, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType α).2.1]⟩).1,
                  ⟨α.toSMTType, ZFSet.fapply_mem_range _ _⟩⟩ :=
                  Option.some.inj (hΔ₀_alt_v' ▸ hΔ₀_alt_v)
                rw [this]; exact ⟨rfl, retract_of_canonical α hT_alt⟩

theorem encodeTerm_spec.int_case.{u} (i : ℤ) (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
  (typ_t : E.context ⊢ᴮ B.Term.int i : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv (B.Term.int i), («Δ» v).isSome = true) {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (B.Term.int i)) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(B.Term.int i).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ (B.Term.int i).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (B.Term.int i).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (B.Term.int i) E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (B.Term.int i) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv (B.Term.int i) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (B.Term.int i) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv (B.Term.int i), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (B.Term.int i) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(B.Term.int i).abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                      some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
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
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre

  rw [encodeTerm]
  mspec Std.Do.Spec.pure
  mpure_intro

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t
  injection den_t with T_eq heq
  subst T_eq
  injection heq with α_eq heq
  subst α_eq
  clear heq

  and_intros
  · intro v hv
    simpa [St_used_eq] using hv
  · intro v hv
    simpa using hv
  · intro v hv
    simpa [St_used_eq] using St_sub hv
  · intro v hv
    simp [B.fv] at hv
  · trivial
  · apply SMT.Typing.int
  · exact fun _ _ h _ => h
  · refine ⟨Δ₀, ?_, ?_⟩
    · intro v hv
      rw [SMT.fv, List.mem_nil_iff] at hv
      contradiction
    · and_intros
      · exact RenamingContext.extends_refl Δ₀
      · exact Δ₀_ext
      · intro v hv
        have hv' : v ∉ used := by
          intro hvu
          exact hv (by simpa [St_used_eq] using hvu)
        exact Δ₀_none_out v hv'
      · refine ⟨⟨ofInt i, .int, hT⟩, ?_, ?_, ?_⟩
        · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
        · refine ⟨rfl, ?_⟩
          simp [retract]
        · intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
          rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t_alt
          have hT_val : ZFSet.ofInt i = T_alt := congrArg (·.fst) den_t_alt
          subst hT_val
          have hcov_alt : RenamingContext.CoversFV Δ₀_alt (SMT.Term.int i) :=
            fun v hv => by simp [SMT.fv] at hv
          refine ⟨Δ₀_alt, hcov_alt, ⟨ZFSet.ofInt i, ⟨.int, hT_alt⟩⟩,
            RenamingContext.extends_refl Δ₀_alt, ?_, ?_, ?_, ?_,
            fun v hv => nomatch SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext v hv⟩
          · exact St_used_eq ▸ Δ₀_alt_none_out
          · exact Δ₀_alt_wt
          · simp [SMT.Term.abstract, SMT.denote]
          · exact ⟨rfl, rfl⟩

theorem encodeTerm_spec.bool_case.{u} (b : Bool) (E : B.Env) {Λ : SMT.TypeContext} {α : BType}
  (typ_t : E.context ⊢ᴮ B.Term.bool b : α) {«Δ» : B.RenamingContext.Context}
  (Δ_fv : ∀ v ∈ B.fv (B.Term.bool b), («Δ» v).isSome = true) {Δ₀ : SMT.RenamingContext.Context}
  (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (B.Term.bool b)) {used : List SMT.𝒱}
  (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none) {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(B.Term.bool b).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩) (vars_used : ∀ v ∈ (B.Term.bool b).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (B.Term.bool b).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (B.Term.bool b) E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (B.Term.bool b) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv (B.Term.bool b) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (B.Term.bool b) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv (B.Term.bool b), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (B.Term.bool b) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(B.Term.bool b).abstract Δ_alt Δ_fv_alt⟧ᴮ =
                                                      some ⟨T_alt, ⟨α, hT_alt⟩⟩ →
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
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre

  rw [encodeTerm]
  mspec Std.Do.Spec.pure
  mpure_intro

  rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t
  injection den_t with T_eq heq
  subst T_eq
  injection heq with α_eq heq
  subst α_eq
  clear heq

  and_intros
  · intro v hv
    simpa [St_used_eq] using hv
  · intro v hv
    simpa using hv
  · intro v hv
    simpa [St_used_eq] using St_sub hv
  · intro v hv
    simp [B.fv] at hv
  · rfl
  · apply SMT.Typing.bool
  · exact fun _ _ h _ => h
  · refine ⟨Δ₀, ?_, ?_⟩
    · intro v hv
      rw [SMT.fv, List.mem_nil_iff] at hv
      contradiction
    · and_intros
      · exact RenamingContext.extends_refl Δ₀
      · exact Δ₀_ext
      · intro v hv
        have hv' : v ∉ used := by
          intro hvu
          exact hv (by simpa [St_used_eq] using hvu)
        exact Δ₀_none_out v hv'
      · refine ⟨⟨ZFBool.ofBool b, .bool, hT⟩, ?_, ?_⟩
        · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
        · refine ⟨⟨rfl, ?_⟩, ?_⟩
          · simp [retract]
          · intro Δ_alt Δ_fv_alt Δ₀_alt Δ₀_alt_ext Δ₀_alt_none_out Δ₀_alt_wt T_alt hT_alt den_t_alt
            rw [B.Term.abstract, B.denote, Option.pure_def, Option.some_inj] at den_t_alt
            have hT_val : ↑(ZFBool.ofBool b) = T_alt := congrArg (·.fst) den_t_alt
            subst hT_val
            have hcov_alt : RenamingContext.CoversFV Δ₀_alt (SMT.Term.bool b) :=
              fun v hv => by simp [SMT.fv] at hv
            refine ⟨Δ₀_alt, hcov_alt, ⟨↑(ZFBool.ofBool b), ⟨.bool, hT_alt⟩⟩,
              RenamingContext.extends_refl Δ₀_alt, ?_, ?_, ?_, ?_,
              fun v hv => nomatch SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_alt_ext v hv⟩
            · exact St_used_eq ▸ Δ₀_alt_none_out
            · exact Δ₀_alt_wt
            · simp [SMT.Term.abstract, SMT.denote]
            · exact ⟨rfl, rfl⟩
