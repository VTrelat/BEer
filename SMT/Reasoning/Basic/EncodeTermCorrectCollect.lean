import SMT.Reasoning.Basic.CollectCaseHelpers
import SMT.Reasoning.Axioms

open Std.Do B SMT ZFSet

set_option maxHeartbeats 4000000 in
theorem encodeTerm_spec.collect_case.{u} (fv_sub_typings : B.FvSubTypings) (vs : List B.𝒱) (D P : B.Term)
  (D_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ D : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv D, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» D →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦D.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ D.vars, v ∈ used) →
                      (∀ v ∈ D.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm D E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars D ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv D → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» D ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv D, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt D →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦D.abstract Δ_alt Δ_fv_alt⟧ᴮ =
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
  (P_ih :
    ∀ (E : B.Env) {Λ : SMT.TypeContext} {α : BType},
      E.context ⊢ᴮ P : α →
        ∀ {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv P, («Δ» v).isSome = true)
          {Δ₀ : SMT.RenamingContext.Context},
          RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» P →
            ∀ {used : List SMT.𝒱},
              (∀ v ∉ used, Δ₀ v = none) →
                ∀ {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ},
                  ⟦P.abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩ →
                    (∀ v ∈ P.vars, v ∈ used) →
                      (∀ v ∈ P.vars, v ∈ Λ → v ∈ E.context) →
                        ∀ {n : ℕ},
                          ⦃fun x =>
                            match x with
                            | { env := E0, types := Λ' } =>
                              ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
                            encodeTerm P E ⦃PostCond.mayThrow fun x x_1 =>
                              match x with
                              | (t', σ) =>
                                match x_1 with
                                | { env := E', types := Γ' } =>
                                  ⌜used ⊆ E'.usedVars ∧
                                      Λ ⊆ Γ' ∧
                                        AList.keys Γ' ⊆ E'.usedVars ∧
                                          CoversUsedVars E'.usedVars P ∧
                                            σ = α.toSMTType ∧
                                              Γ' ⊢ˢ t' : σ ∧
                                                (∀ v ∈ used, v ∉ Λ → v ∉ B.fv P → v ∉ Γ') ∧
                                                  ∃ Δ',
                                                    ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                                                      RenamingContext.Extends Δ' Δ₀ ∧
                                                        RenamingContext.ExtendsOnSourceFV Δ' «Δ» P ∧
                                                          (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                                            ∃ denT',
                                                              ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                                                ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                                                  ∀ (Δ_alt : B.RenamingContext.Context)
                                                                    (Δ_fv_alt : ∀ v ∈ B.fv P, (Δ_alt v).isSome = true)
                                                                    (Δ₀_alt : SMT.RenamingContext.Context),
                                                                    RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt P →
                                                                      (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                                                      (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                                        ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                                          ⟦P.abstract Δ_alt Δ_fv_alt⟧ᴮ =
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
  (E : B.Env) {Λ : SMT.TypeContext} {α : BType} (typ_t : E.context ⊢ᴮ Term.collect vs D P : α)
  {«Δ» : B.RenamingContext.Context} (Δ_fv : ∀ v ∈ B.fv (Term.collect vs D P), («Δ» v).isSome = true)
  {Δ₀ : SMT.RenamingContext.Context} (Δ₀_ext : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» (Term.collect vs D P))
  {used : List SMT.𝒱} (Δ₀_none_out : ∀ v ∉ used, Δ₀ v = none)
  {T : ZFSet.{u}} {hT : T ∈ ⟦α⟧ᶻ}
  (den_t : ⟦(Term.collect vs D P).abstract «Δ» Δ_fv⟧ᴮ = some ⟨T, ⟨α, hT⟩⟩)
  (vars_used : ∀ v ∈ (Term.collect vs D P).vars, v ∈ used)
  (Λ_inv : ∀ v ∈ (Term.collect vs D P).vars, v ∈ Λ → v ∈ E.context) {n : ℕ} :
  ⦃fun x =>
    match x with
    | { env := E0, types := Λ' } => ⌜Λ' = Λ ∧ E0.freshvarsc = n ∧ AList.keys Λ ⊆ E0.usedVars ∧ E0.usedVars = used⌝⦄
    encodeTerm (Term.collect vs D P) E ⦃PostCond.mayThrow fun x x_1 =>
      match x with
      | (t', σ) =>
        match x_1 with
        | { env := E', types := Γ' } =>
          ⌜used ⊆ E'.usedVars ∧
              Λ ⊆ Γ' ∧
                AList.keys Γ' ⊆ E'.usedVars ∧
                  CoversUsedVars E'.usedVars (Term.collect vs D P) ∧
                    σ = α.toSMTType ∧
                      Γ' ⊢ˢ t' : σ ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ B.fv (Term.collect vs D P) → v ∉ Γ') ∧
                          ∃ Δ',
                            ∃ (Δ'_covers : RenamingContext.CoversFV Δ' t'),
                              RenamingContext.Extends Δ' Δ₀ ∧
                                RenamingContext.ExtendsOnSourceFV Δ' «Δ» (Term.collect vs D P) ∧
                                  (∀ v ∉ E'.usedVars, Δ' v = none) ∧
                                    ∃ denT',
                                      ⟦t'.abstract Δ' Δ'_covers⟧ˢ = some denT' ∧
                                        ⟨T, ⟨α, hT⟩⟩ ≘ᶻ denT' ∧
                                          ∀ (Δ_alt : B.RenamingContext.Context)
                                            (Δ_fv_alt : ∀ v ∈ B.fv (Term.collect vs D P), (Δ_alt v).isSome = true)
                                            (Δ₀_alt : SMT.RenamingContext.Context),
                                            RenamingContext.ExtendsOnSourceFV Δ₀_alt Δ_alt (Term.collect vs D P) →
                                              (∀ v ∉ E'.usedVars, Δ₀_alt v = none) →
                                              (∀ v (d : SMT.Dom), Δ₀_alt v = some d → ∀ τ, Γ'.lookup v = some τ → d.snd.fst = τ) →
                                                ∀ (T_alt : ZFSet.{u}) (hT_alt : T_alt ∈ ⟦α⟧ᶻ),
                                                  ⟦(Term.collect vs D P).abstract Δ_alt Δ_fv_alt⟧ᴮ =
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
  mintro pre ∀St₀
  mpure pre
  obtain ⟨rfl, rfl, St₀_sub, St₀_used_eq⟩ := pre
  obtain ⟨αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, α_eq, vs_nodup, D_eq, typDs, typP, vs_Γ_disj⟩ :=
    Typing.collectE typ_t
  subst α_eq
  have Δ_fv_D : ∀ v ∈ B.fv D, («Δ» v).isSome := fun v hv =>
    Δ_fv v (fv.mem_collect (.inl hv))
  have Δ₀_ext_D : RenamingContext.ExtendsOnSourceFV Δ₀ «Δ» D :=
    RenamingContext.extendsOnSourceFV_of_fv_subset
      (hsub := fun v hv => fv.mem_collect (.inl hv)) Δ₀_ext
  set τ := αs.reduce (· ×ᴮ ·) (by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp) with τ_def
  have typ_D : E.context ⊢ᴮ D : .set τ := by
    rw [D_eq]
    exact typing_reduce_cprod E.context _ _ typDs
      (by simpa [vs_Ds_len, ← List.length_pos_iff] using vs_nemp)
      (by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp)
  -- Save den_t for later extraction of P denotation conditions
  have den_t_saved := den_t
  -- Extract D denotation and P default denotation from den_t
  -- We need a custom extraction since simp only [B.denote] fails after semantics change
  have denote_collect_inv := den_t
  simp only [B.Term.abstract] at denote_collect_inv
  -- Now denote_collect_inv : ⟦PHOAS.Term.collect (D.abstract ...) ((go P vs ...).uncurry)⟧ᴮ = some ...
  -- Unfold B.denote for the collect case
  unfold B.denote at denote_collect_inv
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at denote_collect_inv
  obtain ⟨⟨𝒟', τ_D', h𝒟'⟩, den_D', rest_collect⟩ := denote_collect_inv
  have den_D_eq : ⟦D.abstract «Δ» Δ_fv_D⟧ᴮ = some ⟨𝒟', ⟨τ_D', h𝒟'⟩⟩ := by
    convert den_D' using 2
  have rfl_τ' : τ_D' = .set τ := by
    have h_wt := denote_welltyped_eq
      (t := D.abstract «Δ» Δ_fv_D)
      (⟨_, WFTC.of_abstract, .set τ, by convert Typing.of_abstract Δ_fv_D typ_D⟩)
      den_D_eq
    exact h_wt.symm
  subst rfl_τ'
  have den_D_exists : ∃ (𝒟 : ZFSet) (h𝒟 : 𝒟 ∈ ⟦τ.set⟧ᶻ),
    ⟦D.abstract «Δ» Δ_fv_D⟧ᴮ = some ⟨𝒟, ⟨τ.set, h𝒟⟩⟩ :=
    ⟨𝒟', h𝒟', den_D_eq⟩
  obtain ⟨𝒟, h𝒟, den_D⟩ := den_D_exists
  have vars_used_D : ∀ v ∈ D.vars, v ∈ used := by
    intro v hv
    apply vars_used v
    simp [B.Term.vars, B.fv, B.bv, List.mem_append, List.mem_removeAll_iff] at hv ⊢
    rcases hv with hv | hv
    · left; left; exact hv
    · right; right; left; exact hv
  have vars_used_vs : ∀ v ∈ vs, v ∈ used := by
    intro v hv
    apply vars_used v
    simp [B.Term.vars, B.fv, B.bv, List.mem_append, List.mem_removeAll_iff] at hv ⊢
    right; left; exact hv
  have vars_used_P : ∀ v ∈ P.vars, v ∈ used := by
    intro v hv
    apply vars_used v
    simp only [Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc, List.mem_append,
      List.mem_removeAll_iff] at hv ⊢
    by_cases v_in_vs : v ∈ vs
    · right; left; exact v_in_vs
    · rcases hv with hv | hv
      · left; right; exact ⟨hv, v_in_vs⟩
      · right; right; right; exact hv
  rw [encodeTerm]

  have St₀_types_sub_E_ctx_on_D_vars : ∀ v ∈ D.vars, v ∈ St₀.types → v ∈ E.context := by
    intro v v_in_D_vars v_in_St₀_types
    apply Λ_inv v _ v_in_St₀_types
    simp only [Term.vars, List.mem_union_iff, B.fv, B.bv, List.append_assoc, List.mem_append,
      List.mem_removeAll_iff] at v_in_D_vars ⊢
    rcases v_in_D_vars with hv | hv
    · left; left; exact hv
    · right; right; left; exact hv

  mspec D_ih (E := E) (Λ := St₀.types) (α := .set τ) typ_D
      («Δ» := «Δ») Δ_fv_D
      (Δ₀ := Δ₀) Δ₀_ext_D (used := used) Δ₀_none_out (T := 𝒟) (hT := h𝒟)
      den_D vars_used_D (n := St₀.env.freshvarsc)
      St₀_types_sub_E_ctx_on_D_vars
  clear D_ih
  rename_i out_D
  obtain ⟨D_enc, τD⟩ := out_D
  mrename_i pre
  mintro ∀St₁
  mpure pre
  obtain ⟨used_sub_St₁, St₀_sub_St₁, St₁_keys_sub, covers_D, rfl, typ_D_enc,
    D_preserves_types,
    Δ_D, Δ_D_covers, Δ_D_extends, Δ_D_src_ext, Δ_D_none, denD', den_D_enc, D_RDom⟩ := pre
  -- Derive Δ_D_wt and Δ_D_dom via axioms (they were previously obtained from the postcondition).
  have Δ_D_wt : ∀ v (d : SMT.Dom), Δ_D v = some d →
      ∀ τ_v, St₁.types.lookup v = some τ_v → d.snd.fst = τ_v :=
    SMT.RenamingContext.ExtendsOnSourceFV.wt Δ_D_src_ext typ_D_enc
  have Δ_D_dom : ∀ v, Δ_D v ≠ none → v ∈ St₁.types := fun v hv =>
    fv_sub_typings typ_D typ_D_enc v
      (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ_D_src_ext v hv)
  simp only [BType.toSMTType] at *
  mspec addToContext_forIn_spec
      (pairs := vs.zip (τ.toSMTType.fromProdl (vs.length - 1)))
  mrename_i pre
  mintro ∀St₂
  mpure pre
  obtain ⟨St₂_types, St₂_fvc, St₂_used⟩ := pre
  set E' : B.Env := { E with context := vs.zipToAList αs ∪ E.context } with E'_def
  conv in encodeTerm P E => rw [encodeTerm_env_irrel P E E' rfl]
  have St₁_sub_St₂_used : St₁.env.usedVars ⊆ St₂.env.usedVars := by
    rw [St₂_used]; intro v hv
    have : ∀ (l : List (SMT.𝒱 × SMTType)) (acc : List SMT.𝒱),
        v ∈ acc → v ∈ l.foldl (fun used p => p.1 :: used) acc := by
      intro l
      induction l with
      | nil => intro acc hmem; exact hmem
      | cons p ps ih => intro acc hmem; exact ih _ (List.mem_cons_of_mem _ hmem)
    exact this _ _ hv
  have Δ_D_none_St₂ : ∀ v ∉ St₂.env.usedVars, Δ_D v = none :=
    fun v hv => Δ_D_none v (fun hmem => hv (St₁_sub_St₂_used hmem))
  have St₂_keys_sub : AList.keys St₂.types ⊆ St₂.env.usedVars := by
    rw [St₂_types, St₂_used]
    suffices h : ∀ (l : List (SMT.𝒱 × SMTType)) (Γ : SMT.TypeContext) (used : List SMT.𝒱),
        AList.keys Γ ⊆ used →
        AList.keys (l.foldl (fun Γ p => Γ.insert p.1 p.2) Γ) ⊆
          l.foldl (fun used p => p.1 :: used) used from
      h _ _ _ St₁_keys_sub
    intro l; induction l with
    | nil => intro Γ used h; exact h
    | cons p ps ih =>
      intro Γ used h; simp only [List.foldl_cons]
      apply ih; intro v hv
      simp only [AList.keys_insert] at hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h (List.mem_of_mem_erase hv))
  -- Derive τ.hasArity vs.length for defining default bound-variable values
  have αs_nemp : αs ≠ [] := by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp
  have τ_hasArity : τ.hasArity vs.length := by
    rw [τ_def, List.reduce]
    have h_len : αs.tail.length + 1 = vs.length := by
      rw [List.length_tail, vs_αs_len]
      have := List.length_pos_of_ne_nil αs_nemp
      omega
    convert BType.hasArity_of_foldl (α := αs.head αs_nemp) (αs := αs.tail) using 1
    exact h_len.symm
  -- Default B domain values for bound variables
  let f : Fin vs.length → B.Dom := fun i =>
    ⟨τ.defaultZFSet.get vs.length i, τ.get vs.length i,
     get_mem_type_of_isTuple (BType.hasArity_of_foldl_defaultZFSet τ_hasArity) τ_hasArity
       BType.mem_toZFSet_of_defaultZFSet⟩
  -- Extend Δ to cover bound variables vs (needed since fv P may include vs)
  set Δ_ext : B.RenamingContext.Context :=
    Function.updates «Δ» vs (List.ofFn fun i => some (f i)) with Δ_ext_def
  have Δ_fv_P : ∀ v ∈ B.fv P, (Δ_ext v).isSome := by
    intro v hv
    rw [Δ_ext_def, Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
    split_ifs with hvs
    · simp only [List.getElem_ofFn, Option.isSome_some]
    · exact Δ_fv v (fv.mem_collect (.inr ⟨hv, hvs⟩))
  -- Extend SMT renaming Δ_D at bound variables to match Δ_ext
  set Δ_D_ext : SMT.RenamingContext.Context :=
    Function.updates Δ_D vs (List.ofFn fun (i : Fin vs.length) => B.RenamingContext.toSMT Δ_ext vs[i])
    with Δ_D_ext_def
  have Δ_D_ext_none_St₂ : ∀ v ∉ St₂.env.usedVars, Δ_D_ext v = none :=
    Δ_D_ext_none_helper_shared (ΔDD := Δ_D) (ΔDDext := Δ_D_ext)
      (vs := vs) (vs_nodup := vs_nodup)
      (vs_τs_len := by rw [fromProdl_length_of_hasArity τ_hasArity])
      (used0 := St₁.env.usedVars) (used1 := St₁.env.usedVars)
      (used2 := St₂.env.usedVars)
      (St_used_def := St₂_used) (used1_eq_used0 := rfl)
      (ΔDDext_def := Δ_D_ext_def) (ΔDD_none_outside := Δ_D_none_St₂)
  have Δ₀_ext_P : RenamingContext.ExtendsOnSourceFV Δ_D_ext Δ_ext P :=
    Δ₀_ext_P_helper_shared vs_nodup Δ_ext_def Δ_D_ext_def (Term.collect vs D P) P
      (mem_binder := fun hv hvs => fv.mem_collect (.inr ⟨hv, hvs⟩))
      (lift := fun hv => Δ_D_extends (Δ₀_ext hv))
  -- Extract P denotation condition from den_t_saved:
  -- The collect semantics checks den_P_cond: ∀ x, ofFinDom x ∈ 𝒟 → ⟦P x⟧ᴮ.isSome
  -- We use this with a chosen element of 𝒟 (when nonempty) or Classical.em (when empty)
  have den_P : ∃ (TP : ZFSet) (hTP : TP ∈ ⟦BType.bool⟧ᶻ),
    ⟦P.abstract Δ_ext Δ_fv_P⟧ᴮ = some ⟨TP, ⟨.bool, hTP⟩⟩ := by
    -- rest_collect contains the hasArity + P default eval + den_P + typP_det conditions
    -- The hasArity condition is true
    have hτ_def : τ.defaultZFSet.hasArity vs.length ∧ τ.hasArity vs.length :=
      ⟨BType.hasArity_of_foldl_defaultZFSet τ_hasArity, τ_hasArity⟩
    rw [dif_pos hτ_def, Option.bind_eq_some_iff] at rest_collect
    -- Now rest_collect has the P default bind
    obtain ⟨⟨P_def_val, P_def_typ, P_def_mem⟩, den_P_def, _⟩ := rest_collect
    -- den_P_def : ⟦(go P vs «Δ» ...).uncurry def_dom⟧ᴮ = some ...
    -- Use denote_term_abstract_go_eq_term_abstract to convert
    rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp f Δ_fv_P] at den_P_def
    have P_def_bool : P_def_typ = .bool := by
      exact (denote_welltyped_eq
        (t := P.abstract Δ_ext Δ_fv_P)
        (⟨_, WFTC.of_abstract, .bool, by convert Typing.of_abstract Δ_fv_P typP⟩)
        den_P_def).symm
    subst P_def_bool
    exact ⟨P_def_val, P_def_mem, den_P_def⟩
  obtain ⟨TP, hTP, den_P⟩ := den_P
  have vars_used_P_St₂ : ∀ v ∈ P.vars, v ∈ St₂.env.usedVars :=
    fun v hv => St₁_sub_St₂_used (used_sub_St₁ (vars_used_P v hv))

  have St₂_types_sub_E_ctx_on_P_vars : ∀ v ∈ P.vars, v ∈ St₂.types → v ∈ E'.context := by
    intro v v_in_P_vars v_in_St₂_types
    simp [E']
    by_cases v_in_vs : v ∈ vs
    · left
      exact AList.mem_zipToAList_of_mem vs_nodup vs_αs_len v_in_vs
    · right
      -- v ∉ vs, v ∈ St₂.types → v ∈ St₁.types (foldl insert only adds keys from vs)
      have v_in_St₁ : v ∈ St₁.types := by
        rw [St₂_types] at v_in_St₂_types
        exact AList.mem_of_mem_foldl_insert' v_in_St₂_types (by
          intro h
          rw [List.mem_map] at h
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
          exact v_in_vs (List.of_mem_zip hab).1)
      -- v ∈ used (since v ∈ P.vars ⊆ (collect vs D P).vars ⊆ used)
      have v_used : v ∈ used := vars_used_P v v_in_P_vars
      -- By contrapositive of D_preserves_types: v ∈ St₀.types ∨ v ∈ fv D
      by_cases v_St₀ : v ∈ St₀.types
      · -- v ∈ St₀.types → v ∈ (collect vs D P).vars → v ∈ E.context
        have v_collect : v ∈ (Term.collect vs D P).vars := by
          unfold B.Term.vars at v_in_P_vars ⊢
          rw [List.mem_union_iff]
          rcases List.mem_union_iff.mp v_in_P_vars with h_fv | h_bv
          · left; simp only [B.fv, List.mem_append]
            right
            unfold List.removeAll; rw [List.mem_filter]
            exact ⟨h_fv, by simp [v_in_vs]⟩
          · right; simp only [B.bv, List.mem_append]
            right; exact h_bv
        exact Λ_inv v v_collect v_St₀
      · -- v ∉ St₀.types → v ∈ fv D (by contrapositive of D_preserves_types)
        have v_fv_D : v ∈ B.fv D := by
          by_contra h
          exact absurd v_in_St₁ (D_preserves_types v v_used v_St₀ h)
        exact AList.lookup_isSome.mp (B.Typing.mem_context_of_mem_fv typ_D v_fv_D)
  -- Helper: AList foldl-insert preserves membership and adds zipped keys
  have foldl_insert_mem : ∀ (l : List (SMT.𝒱 × SMTType)) (acc : SMT.TypeContext) (v : SMT.𝒱),
      v ∈ acc → v ∈ l.foldl (fun Γ p => AList.insert p.1 p.2 Γ) acc := by
    intro l
    induction l with
    | nil => intros _ _ hv; exact hv
    | cons p l' ih =>
      intro acc v hv_acc
      simp only [List.foldl_cons]
      apply ih _ _
      by_cases h : v = p.1
      · subst h; exact (AList.mem_insert _).mpr (Or.inl rfl)
      · exact (AList.mem_insert _).mpr (Or.inr hv_acc)
  have foldl_insert_zip_mem : ∀ (ws : List SMT.𝒱) (τs' : List SMTType)
      (acc : SMT.TypeContext) (v : SMT.𝒱),
      ws.length ≤ τs'.length → v ∈ ws →
      v ∈ (ws.zip τs').foldl (fun Γ p => AList.insert p.1 p.2 Γ) acc := by
    intro ws
    induction ws with
    | nil => intros _ _ _ _ hv; exact absurd hv List.not_mem_nil
    | cons w ws' ih =>
      intro τs' acc v hlen hv
      cases τs' with
      | nil => simp at hlen
      | cons τ' τs'' =>
        simp only [List.zip_cons_cons, List.foldl_cons]
        rcases List.mem_cons.mp hv with rfl | hv'
        · apply foldl_insert_mem
          exact (AList.mem_insert _).mpr (Or.inl rfl)
        · exact ih τs'' _ v (Nat.le_of_succ_le_succ hlen) hv'
  mspec P_ih (E := E') (Λ := St₂.types) (α := .bool) typP
    («Δ» := Δ_ext) Δ_fv_P
    (Δ₀ := Δ_D_ext) Δ₀_ext_P (used := St₂.env.usedVars) Δ_D_ext_none_St₂
    (T := TP) (hT := hTP) den_P vars_used_P_St₂ (n := St₂.env.freshvarsc)
    St₂_types_sub_E_ctx_on_P_vars
  rename_i out_P
  obtain ⟨P_enc, σP⟩ := out_P
  mrename_i pre
  mintro ∀St₃
  mpure pre
  obtain ⟨St₂_sub_St₃, St₂_sub_St₃_types, St₃_keys_sub, covers_P, rfl, typ_P_enc,
    P_preserves_types,
    Δ_P, Δ_P_covers, Δ_P_extends, Δ_P_src_ext, Δ_P_none, denP', den_P_enc, P_RDom,
    P_enc_total⟩ := pre
  -- Derive Δ_P_wt and Δ_P_dom via axioms (they were previously obtained from the postcondition).
  have Δ_P_wt : ∀ v (d : SMT.Dom), Δ_P v = some d →
      ∀ τ_v, St₃.types.lookup v = some τ_v → d.snd.fst = τ_v :=
    SMT.RenamingContext.ExtendsOnSourceFV.wt Δ_P_src_ext typ_P_enc
  have Δ_P_dom : ∀ v, Δ_P v ≠ none → v ∈ St₃.types := fun v hv =>
    fv_sub_typings typP typ_P_enc v
      (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ_P_src_ext v hv)
  simp only [BType.toSMTType] at *
  mspec freshVar_spec
  rename_i z
  mrename_i pre
  mintro ∀St₄
  mpure pre
  obtain ⟨St₄_types, z_fresh, St₄_fvc, St₄_used, z_not_used⟩ := pre
  -- Handle bound-var erasure: erase vs → erase z → return
  mspec SMT.eraseVars_forIn_spec (vars := vs)
  mrename_i pre_erase_vs
  mintro ∀St₅
  mpure pre_erase_vs
  obtain ⟨St₅_types, St₅_fvc, St₅_used⟩ := pre_erase_vs
  mspec SMT.eraseFromContext_spec
  mrename_i pre_erase_z
  mintro ∀St₆
  mpure pre_erase_z
  obtain ⟨St₆_types, St₆_fvc, St₆_used⟩ := pre_erase_z
  mspec Std.Do.Spec.pure
  mpure_intro
  -- Bridge facts: chain usedVars through erasure states
  have St₆_used_chain : St₆.env.usedVars = z :: St₃.env.usedVars := by
    rw [St₆_used, St₅_used, St₄_used]
  have z_not_St₀ : z ∉ St₀.types := by
    intro hz
    have := St₀_sub hz
    rw [St₀_used_eq] at this
    exact z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ this)))
  -- Key invariant: B binder variables vs are disjoint from the SMT type context St₁.types.
  -- Derive: bound vars vs have no free occurrence in D (from typing)
  have vs_not_D_fv : ∀ v ∈ vs, v ∉ B.fv D := by
    intro v hv hv_fv
    nomatch vs_Γ_disj v hv <| AList.lookup_isSome.mp <| B.Typing.mem_context_of_mem_fv typ_D hv_fv
  have vs_disj_St₁ : ∀ v ∈ vs, v ∉ St₁.types := by
    intro v hv
    apply D_preserves_types v (vars_used_vs v hv) _ (vs_not_D_fv v hv)
    intro hv_St₀
    have hv_collect : v ∈ (Term.collect vs D P).vars := by
      unfold B.Term.vars; rw [List.mem_union_iff]; right
      simp only [B.bv, List.mem_append]; left; left; exact hv
    exact vs_Γ_disj v hv (Λ_inv v hv_collect hv_St₀)
  have St₁_sub_St₃_types : St₁.types ⊆ St₃.types := by
    apply AList.subset_trans _ St₂_sub_St₃_types
    rw [St₂_types]
    apply AList.subset_foldl_insert'
    · intro ⟨v, ξ⟩ hv
      exact vs_disj_St₁ v (List.mem_fst_of_mem_zip hv)
    · exact List.nodup_map_fst_of_nodup_zip vs_nodup
  -- St₆.types ⊆ St₃.types because erasure only removes entries
  have St₆_sub_St₃ : St₆.types ⊆ St₃.types := by
    rw [St₆_types, St₅_types, St₄_types]
    intro ⟨k, v⟩ hkv
    have hk_ne_z : k ≠ z := AList.fst_ne_of_mem_erase_entries hkv
    have hkv_foldl := AList.erase_entries_subset z _ hkv
    have hkv_ins := AList.foldl_erase_entries_subset vs _ hkv_foldl
    rw [AList.entries_insert_of_notMem z_fresh] at hkv_ins
    exact (List.mem_cons.mp hkv_ins).elim (fun h => absurd (congrArg Sigma.fst h) hk_ne_z) id
  and_intros
  · -- 1. used ⊆ St₆.env.usedVars
    rw [St₆_used_chain]
    exact fun v hv => List.mem_cons_of_mem _ (St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ hv)))
  · -- 2. St₀.types ⊆ St₆.types
    -- Strategy: trace entries from St₀ through the chain.
    -- Each entry (k, τ) in St₀ has k ∉ vs and k ≠ z (by z_not_St₀).
    -- So erasing vs and z from St₃ preserves all St₀ entries.
    intro ⟨k, τ_k⟩ hk_St₀
    -- Now show (k, τ_k) survives the erasure steps: insert z, erase vs, erase z
    rw [St₆_types, St₅_types, St₄_types]
    have hk_not_vs : k ∉ vs := by
      intro hk_in_vs
      have hk_St₀_mem : k ∈ St₀.types :=
        AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₀, rfl⟩)
      have hk_collect : k ∈ (Term.collect vs D P).vars := by
        unfold B.Term.vars; rw [List.mem_union_iff]; right
        simp only [B.bv, List.mem_append]; left; left; exact hk_in_vs
      exact vs_Γ_disj k hk_in_vs (Λ_inv k hk_collect hk_St₀_mem)
    have hk_ne_z : k ≠ z := by
      intro rfl
      have : k ∈ St₀.types :=
        AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₀, rfl⟩)
      nomatch z_not_St₀ this

    have hk_St₃_kerase : ⟨k, τ_k⟩ ∈ (AList.insert z τ.toSMTType St₃.types).entries := by
      rw [AList.entries_insert_of_notMem z_fresh, List.mem_cons]
      right
      exact St₁_sub_St₃_types (St₀_sub_St₁ hk_St₀)
    -- Erase vs preserves (k, τ_k) since k ∉ vs, then erase z preserves since k ≠ z
    have hk_foldl := AList.mem_foldl_erase_of_not_mem_keys hk_St₃_kerase hk_not_vs
    exact List.mem_kerase_of_ne_key hk_ne_z hk_foldl
  · -- 3. AList.keys St₆.types ⊆ St₆.env.usedVars
    rw [St₆_used_chain]
    intro v hv
    apply List.mem_cons_of_mem
    -- v ∈ St₆.types.keys → v ∈ St₃.types.keys (since St₆ ⊆ St₃)
    have hv_St₃ : v ∈ St₃.types :=
      (List.map_subset _ St₆_sub_St₃) hv
    exact St₃_keys_sub hv_St₃
  · -- 4. CoversUsedVars St₆.env.usedVars (collect vs D P)
    rw [St₆_used_chain]
    intro v hv
    apply List.mem_cons_of_mem
    rw [B.fv, List.mem_append] at hv
    rcases hv with hv_D | hv_P
    · exact St₂_sub_St₃ (St₁_sub_St₂_used (covers_D v hv_D))
    · exact covers_P v (List.mem_filter.mp hv_P).1
  · rfl
  -- 6. typing of the lambda term: build in St₃.types, then strengthen to St₆.types
  · have hupdate : SMT.TypeContext.update St₃.types [z] [τ.toSMTType] rfl =
        St₃.types.insert z τ.toSMTType := by
      simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd, Fin.cast_eq_self, Fin.getElem_fin, Fin.val_eq_zero,
        List.getElem_cons_zero, Fin.foldl_succ, Fin.foldl_zero]
    have h_St₁_sub_St₃ := St₁_sub_St₃_types
    -- Build typing in St₃, then strengthen to St₆
    suffices h_typ_St₃ : St₃.types ⊢ˢ
        (SMT.Term.lambda [z] [τ.toSMTType]
          (SMT.Term.ite (SMT.Term.app D_enc (.var z))
            (SMT.substList vs (toDestPair vs (.var z)) P_enc) (.bool false))) :
        SMTType.fun τ.toSMTType .bool from
      Typing.strengthening_of_fv_subset St₆_sub_St₃ h_typ_St₃ (by
        -- ∀ v ∈ fv(lambda), v ∈ St₆.types
        -- Helper: if v ∈ St₃.types, v ∉ vs, v ≠ z, then v ∈ St₆.types
        have h_surv : ∀ v, v ∈ St₃.types → v ∉ vs → v ≠ z → v ∈ St₆.types := by
          intro v hv_St₃ hv_not_vs hv_ne_z
          rw [St₆_types, St₅_types, St₄_types]
          obtain ⟨τ_v, hτ_v⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.2 hv_St₃)
          have hentry := AList.mem_lookup_iff.1 hτ_v
          have h_ins : ⟨v, τ_v⟩ ∈ (AList.insert z τ.toSMTType St₃.types).entries := by
            rw [AList.entries_insert_of_notMem z_fresh]
            exact List.mem_cons_of_mem _ hentry
          exact AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨v, τ_v⟩,
            List.mem_kerase_of_ne_key hv_ne_z
              (AList.mem_foldl_erase_of_not_mem_keys h_ins hv_not_vs), rfl⟩)
        -- fv(lambda [z] body) = removeAll (fv body) [z]
        intro v hv_lam
        simp only [SMT.fv] at hv_lam
        -- hv_lam : v ∈ (fv_body).removeAll [z]
        unfold List.removeAll at hv_lam
        rw [List.mem_filter] at hv_lam
        obtain ⟨hv_body, hv_nz⟩ := hv_lam
        have hv_ne_z : v ≠ z := by simpa using hv_nz
        -- fv(body) = fv(app D_enc (var z)) ++ fv(substList ...) ++ fv(bool false)
        simp only [SMT.fv, List.append_nil] at hv_body
        rw [List.mem_append, List.mem_append] at hv_body
        rcases hv_body with (hv_D | hv_z) | hv_subst
        · -- v ∈ fv(D_enc)
          have hv_St₁ : v ∈ St₁.types :=
            Typing.mem_context_of_mem_fv typ_D_enc hv_D
          exact h_surv v (typeContext_mem_of_subset h_St₁_sub_St₃ hv_St₁)
            (fun hvs => vs_disj_St₁ v hvs hv_St₁) hv_ne_z
        · -- v ∈ [z], i.e. v = z, contradicts hv_ne_z
          rw [List.mem_singleton] at hv_z
          exact absurd hv_z hv_ne_z
        · -- v ∈ fv(substList ...)
          rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
          · -- v ∈ fv(P_enc)
            have hv_St₃ := Typing.mem_context_of_mem_fv typ_P_enc hv_P
            have hv_not_vs : v ∉ vs := by
              intro hvs
              suffices hlen : vs.length ≤ (toDestPair vs (.var z)).length by
                have hts : ∀ t ∈ toDestPair vs (.var z), v ∉ SMT.fv t :=
                  fun t ht hv_t => hv_ne_z (SMT_fv_toDestPair_subset ht hv_t)
                exact absurd hv_subst (SMT_not_mem_fv_substList_of_mem_vars hlen hvs hts)
              suffices ∀ (ws : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term) (d : SMT.Term),
                  ws.length + acc.length ≤ (toDestPair ws zp acc d).length by
                simpa using this vs (.var z) [] (.var z)
              intro ws
              induction ws with
              | nil => intro _ acc _; simp [toDestPair]
              | cons w ws' ih =>
                intro zp acc d
                cases ws' with
                | nil => simp [toDestPair]; omega
                | cons w' ws'' =>
                  simp only [toDestPair]
                  have := ih (.fst d) (.snd d :: acc) (.fst d)
                  simp [List.length] at this ⊢; omega
            exact h_surv v hv_St₃ hv_not_vs hv_ne_z
          · -- v ∈ fv(toDestPair term) → v = z, contradiction
            exact absurd (SMT_fv_toDestPair_subset ht hv_t) hv_ne_z)
    refine SMT.Typing.lambda St₃.types [z] [τ.toSMTType] _ .bool ?_ ?_ ?_ ?_ ?_
    · -- z ∉ St₃.types
      intro v hv; rw [List.mem_singleton] at hv; subst hv; exact z_fresh
    · -- z ∉ bv body (ite (D_enc @ var z) (substList ...) (bool false))
      intro v hv; simp only [List.mem_singleton] at hv; subst hv
      simp only [SMT.bv, List.append_nil, List.mem_append, not_or]
      constructor
      · -- z ∉ bv D_enc
        intro hbv
        have typ_D_enc_St₃ := SMT.Typing.weakening
          (SMT.TypeContext.entries_subset_insert_of_notMem (τ := τ.toSMTType) z_fresh)
          (SMT.Typing.weakening h_St₁_sub_St₃ typ_D_enc)
        exact SMT.Typing.bv_notMem_context typ_D_enc_St₃ _ hbv
          ((AList.mem_insert _).mpr (Or.inl rfl))
      · -- z ∉ bv (substList ...)
        intro hbv
        have hbv_P := SMT_bv_substList_subset (fun t ht => toDestPair_bv_nil t ht) _ hbv
        have typ_P_enc_ins := SMT.Typing.weakening
          (SMT.TypeContext.entries_subset_insert_of_notMem (τ := τ.toSMTType) z_fresh) typ_P_enc
        exact SMT.Typing.bv_notMem_context typ_P_enc_ins _ hbv_P
          ((AList.mem_insert _).mpr (Or.inl rfl))
    · exact Nat.zero_lt_succ 0
    · rfl
    · rw [hupdate]
      have h_ins := SMT.TypeContext.entries_subset_insert_of_notMem (v := z) (τ := τ.toSMTType) z_fresh
      apply SMT.Typing.ite
      · -- D_enc typing: weaken from St₁ to St₃.insert z
        exact SMT.Typing.app _ _ _ _ _
          (SMT.Typing.weakening h_ins (SMT.Typing.weakening h_St₁_sub_St₃ typ_D_enc))
          (SMT.Typing.var _ z τ.toSMTType (AList.lookup_insert St₃.types))
      · -- substList typing: directly in St₃.types.insert z (no strengthening needed)
        apply SMT_Typing_substList
        · exact SMT.Typing.weakening h_ins typ_P_enc
        · exact toDestPair_bv_nil
        · -- toDestPair pairs typing
          set Γ_z := St₃.types.insert z τ.toSMTType with Γ_z_def
          set τs := τ.toSMTType.fromProdl (vs.length - 1) with τs_def
          have τs_len : τs.length = vs.length := fromProdl_length_of_hasArity τ_hasArity
          intro i hi_x hi_t hx
          have hi_τs : i < τs.length := τs_len ▸ hi_x
          -- Establish Γ_z.lookup vs[i] = some τs[i]
          have h_St₂_lookup : St₂.types.lookup vs[i] = some τs[i] := by
            rw [St₂_types]; exact foldl_insert_lookup_zip vs_nodup hi_x hi_τs
          have h_St₃_lookup : St₃.types.lookup vs[i] = some τs[i] :=
            AList.mem_lookup_iff.2 (St₂_sub_St₃_types (AList.mem_lookup_iff.1 h_St₂_lookup))
          have hne : vs[i] ≠ z := by
            intro heq
            have hvi_used : vs[i] ∈ St₃.env.usedVars :=
              St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs vs[i] (List.getElem_mem hi_x))))
            exact z_not_used (heq ▸ hvi_used)
          have h_lookup : Γ_z.lookup vs[i] = some τs[i] := by
            rw [Γ_z_def, AList.lookup_insert_ne hne]; exact h_St₃_lookup
          -- Convert the goal type using the known lookup value
          have h_get : (Γ_z.lookup vs[i]).get hx = τs[i] := by
            simp [h_lookup]
          rw [h_get]
          -- Use toDestPair_typing_gen to get the typing
          have hz_lookup : Γ_z.lookup z = some τ.toSMTType :=
            AList.lookup_insert St₃.types
          have h_result := toDestPair_typing_gen Γ_z vs (.var z) (.var z) τ.toSMTType [] []
            vs_nemp rfl (SMT.Typing.var Γ_z z τ.toSMTType hz_lookup)
            (by rw [τs_def] at τs_len; exact τs_len) rfl
            (fun j hj => absurd hj (Nat.not_lt_zero j))
            i τs[i]
            (by simp only [List.append_nil]; rw [List.getElem?_eq_getElem hi_τs])
          obtain ⟨hj, htyp⟩ := h_result
          exact htyp
      · -- .bool false typing
        exact SMT.Typing.bool _ _
  · -- 7. preservation: ∀ v ∈ used, v ∉ Λ → v ∉ (collect vs D P).vars → v ∉ St₆.types
    intro v v_used v_notMem_St₀ v_notMem_vars v_mem_St₆
    simp only [B.fv, List.mem_append, not_or] at v_notMem_vars
    have v_notMem_fvD := v_notMem_vars.1
    -- Derive v ∈ St₃.types from v ∈ St₆.types (since St₆ ⊆ St₃)
    have v_mem_St₃ : v ∈ St₃.types :=
      typeContext_mem_of_subset St₆_sub_St₃ v_mem_St₆
    -- First establish v ∉ vs: if v ∈ vs, foldl erase would remove v, contradicting v_mem_St₆
    have hv_not_vs : v ∉ vs := by
      intro hv_vs
      have : v ∉ St₆.types := by
        rw [St₆_types]; intro h_erase_z
        have h_in_St₅ : v ∈ St₅.types := (AList.mem_erase.mp h_erase_z).2
        rw [St₅_types] at h_in_St₅
        exact absurd h_in_St₅ (AList.not_mem_foldl_erase_of_mem hv_vs vs_nodup)
      exact this v_mem_St₆
    -- Derive v ∉ B.fv P from v ∉ vs and v ∉ removeAll (fv P) vs
    have v_notMem_fvP : v ∉ B.fv P := by
      intro hv_fvP
      apply v_notMem_vars.2
      unfold List.removeAll; rw [List.mem_filter]
      exact ⟨hv_fvP, by simp [hv_not_vs]⟩
    exfalso
    have v_notMem_St₁ := D_preserves_types v v_used v_notMem_St₀ v_notMem_fvD
    have v_notMem_St₂ : v ∉ St₂.types := by
      rw [St₂_types]; intro h
      exact v_notMem_St₁ (AList.mem_of_mem_foldl_insert' h (by
        intro hmem; rw [List.mem_map] at hmem
        obtain ⟨⟨a, b⟩, hab, rfl⟩ := hmem
        exact hv_not_vs (List.of_mem_zip hab).1))
    exact P_preserves_types v (St₁_sub_St₂_used (used_sub_St₁ v_used))
      v_notMem_St₂ v_notMem_fvP v_mem_St₃
  -- 8. ∃ Δ', renaming + denotation
  · -- Define Δ' using Δ_D for vs (so coverage on D_enc is immediate)
    set Δ' : SMT.RenamingContext.Context := fun v =>
      if v ∈ vs then Δ_D v else Δ_P v with Δ'_def
    have Δ'_extends_Δ₀ : RenamingContext.Extends Δ' Δ₀ := by
      intro v d hv_eq
      rw [Δ'_def]
      by_cases hvs : v ∈ vs
      · simp [hvs]; exact Δ_D_extends hv_eq
      · simp [hvs]
        have hDD : Δ_D_ext v = Δ_D v := by
          rw [Δ_D_ext_def]; exact Function.updates_of_not_mem Δ_D vs _ v hvs
        exact Δ_P_extends (hDD ▸ Δ_D_extends hv_eq)
    have Δ'_none_out : ∀ v ∉ St₃.env.usedVars, Δ' v = none := by
      intro v hv; rw [Δ'_def]
      by_cases hvs : v ∈ vs
      · -- v ∈ vs but v ∉ St₃.env.usedVars: contradiction since addToContext adds vs to usedVars
        exfalso; apply hv
        have v_in_St₂ : v ∈ St₂.env.usedVars := by
          rw [St₂_used]
          suffices ∀ (ws : List SMT.𝒱) (τs' : List SMTType) (acc : List SMT.𝒱),
              ws.length ≤ τs'.length → v ∈ ws →
              v ∈ (ws.zip τs').foldl (fun used p => p.1 :: used) acc by
            exact this vs (τ.toSMTType.fromProdl (vs.length - 1)) St₁.env.usedVars
              (by rw [fromProdl_length_of_hasArity τ_hasArity]) hvs
          intro ws
          induction ws with
          | nil => intro _ _ _ hv; exact absurd hv List.not_mem_nil
          | cons w ws' ih =>
            intro τs' acc hlen hv
            cases τs' with
            | nil => simp at hlen
            | cons τ' τs'' =>
              simp only [List.zip_cons_cons, List.foldl_cons]
              rcases List.mem_cons.mp hv with rfl | hv'
              · suffices ∀ (l : List (SMT.𝒱 × SMTType)) (acc' : List SMT.𝒱),
                    v ∈ acc' → v ∈ l.foldl (fun used p => p.1 :: used) acc' by
                  exact this _ _ (List.mem_cons_self ..)
                intro l; induction l with
                | nil => exact fun _ h => h
                | cons _ _ ih' => intro acc' hmem; exact ih' _ (List.mem_cons_of_mem _ hmem)
              · exact ih τs'' _ (by simp at hlen; omega) hv'
        exact St₂_sub_St₃ v_in_St₂
      · simp [hvs]; exact Δ_P_none v hv
    -- Free variables of substList result that are in vs lead to contradiction
    have fv_substList_disj_vs : ∀ v ∈ SMT.fv (substList vs (toDestPair vs (.var z)) P_enc),
        v ≠ z → v ∉ vs := by
      intro v hv_subst hne hvs
      rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
      · suffices hlen : vs.length ≤ (toDestPair vs (.var z)).length by
          have hts : ∀ t ∈ toDestPair vs (.var z), v ∉ SMT.fv t :=
            fun t ht hv_t => hne (SMT_fv_toDestPair_subset ht hv_t)
          exact absurd hv_subst (SMT_not_mem_fv_substList_of_mem_vars hlen hvs hts)
        suffices ∀ (ws : List SMT.𝒱) (zp : SMT.Term) (acc : List SMT.Term) (d : SMT.Term),
            ws.length + acc.length ≤ (toDestPair ws zp acc d).length by
          simpa using this vs (.var z) [] (.var z)
        intro ws
        induction ws with
        | nil => intro _ acc _; simp [toDestPair]
        | cons w ws' ih =>
          intro zp acc d
          cases ws' with
          | nil => simp [toDestPair]; omega
          | cons w' ws'' =>
            simp only [toDestPair]
            have := ih (.fst d) (.snd d :: acc) (.fst d)
            simp [List.length] at this ⊢; omega
      · have := SMT_fv_toDestPair_subset ht hv_t
        subst this; exact hne rfl
    have hcov_lambda : RenamingContext.CoversFV Δ'
        ((λˢ [z]) [τ.toSMTType] (SMT.Term.ite ((@ˢD_enc) (.var z)) (substList vs (toDestPair vs (.var z)) P_enc) (.bool false))) := by
      intro v hv
      simp only [SMT.fv, List.mem_removeAll_iff] at hv
      obtain ⟨hv_body, hv_ne_z⟩ := hv
      have hv_ne : v ≠ z := List.mem_singleton.not.mp hv_ne_z
      simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hv_body
      rcases hv_body with (hv_D | rfl) | hv_subst
      · -- v ∈ fv D_enc: use Δ_D_covers (works for both v ∈ vs and v ∉ vs)
        rw [Δ'_def]
        by_cases hvs : v ∈ vs
        · simp [hvs]; exact Δ_D_covers v hv_D
        · simp [hvs]
          have hDD_ext : Δ_D_ext v = Δ_D v := by
            rw [Δ_D_ext_def]; exact Function.updates_of_not_mem Δ_D vs _ v hvs
          have ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Δ_D_covers v hv_D)
          exact Option.isSome_iff_exists.mpr ⟨d, Δ_P_extends (hDD_ext ▸ hd)⟩
      · exact absurd rfl hv_ne
      · -- v ∈ fv(substList ...): v ∉ vs (by fv_substList_disj_vs), so Δ' v = Δ_P v
        have hv_not_vs : v ∉ vs :=
          fv_substList_disj_vs v hv_subst hv_ne
        rcases SMT_mem_fv_substList hv_subst with hv_P | ⟨t, ht, hv_t⟩
        · rw [Δ'_def]; simp [hv_not_vs]
          exact Δ_P_covers v hv_P
        · have := SMT_fv_toDestPair_subset ht hv_t
          subst this; exact absurd rfl hv_ne
    have Δ'_wt : ∀ v (d : SMT.Dom), Δ' v = some d →
        ∀ τ_v, St₆.types.lookup v = some τ_v → d.snd.fst = τ_v := by
      intro v d hΔ'v τ_v hτ_v
      rw [Δ'_def] at hΔ'v
      by_cases hvs : v ∈ vs
      · -- v ∈ vs: v ∉ St₆.types, so lookup = some τ is impossible
        exfalso
        have hv_not_St₆ : v ∉ St₆.types := by
          rw [St₆_types]; intro h_erase_z
          have h_in_St₅ : v ∈ St₅.types := (AList.mem_erase.mp h_erase_z).2
          rw [St₅_types] at h_in_St₅
          exact absurd h_in_St₅ (AList.not_mem_foldl_erase_of_mem hvs vs_nodup)
        rw [AList.lookup_eq_none.mpr hv_not_St₆] at hτ_v
        exact absurd hτ_v nofun
      · -- v ∉ vs: Δ' v = Δ_P v, and St₆.types ⊆ St₃.types
        simp [hvs] at hΔ'v
        exact Δ_P_wt v d hΔ'v τ_v (AList.lookup_of_subset St₆_sub_St₃ hτ_v)
    have Δ'_dom : ∀ v, Δ' v ≠ none → v ∈ St₆.types := by
      intro v hv
      rw [Δ'_def] at hv
      by_cases hvs : v ∈ vs
      · -- v ∈ vs: Δ_D v ≠ none → v ∈ St₁.types (Δ_D_dom), but vs ∩ St₁.types = ∅
        simp [hvs] at hv
        exact absurd (Δ_D_dom v hv) (vs_disj_St₁ v hvs)
      · -- v ∉ vs: Δ_P v ≠ none → v ∈ St₃.types (Δ_P_dom). Need v ∈ St₆.types.
        simp [hvs] at hv
        have hv_St₃ : v ∈ St₃.types := Δ_P_dom v hv
        have hv_ne_z : v ≠ z := by
          intro hrfl; subst hrfl
          -- z ∉ St₃.usedVars, but Δ_P v ≠ none → v ∈ St₃.usedVars (via Δ_P_none)
          have hv_used : v ∈ St₃.env.usedVars := by
            by_contra h; exact hv (Δ_P_none v h)
          exact z_not_used hv_used
        -- St₆.types = erase z (foldl erase vs (insert z τ St₃.types))
        -- v ∈ St₃, v ∉ vs, v ≠ z → v ∈ erase z (foldl erase vs (insert z τ St₃))
        rw [St₆_types, St₅_types, St₄_types]
        -- Step 1: v ∈ insert z τ St₃.types (via St₃)
        have h_ins : v ∈ AList.insert z τ.toSMTType St₃.types :=
          (AList.mem_insert _).mpr (Or.inr hv_St₃)
        -- Step 2: erasing vs doesn't remove v (v ∉ vs)
        have h_after_vs : v ∈ (vs.foldl (fun Γ v => AList.erase v Γ)
            (AList.insert z τ.toSMTType St₃.types)) := by
          have : ∀ (ws : List SMT.𝒱) (acc : SMT.TypeContext),
              v ∉ ws → v ∈ acc → v ∈ ws.foldl (fun Γ v' => AList.erase v' Γ) acc := by
            intro ws
            induction ws with
            | nil => intros _ _ hv_acc; exact hv_acc
            | cons w ws' ih =>
              intro acc h_notin hv_acc
              simp only [List.foldl_cons]
              apply ih _ (fun h => h_notin (List.mem_cons.mpr (Or.inr h)))
              apply AList.mem_erase.mpr
              exact ⟨fun heq => h_notin (heq ▸ List.mem_cons_self), hv_acc⟩
          exact this vs _ hvs h_ins
        -- Step 3: erasing z doesn't remove v (v ≠ z)
        exact AList.mem_erase.mpr ⟨hv_ne_z, h_after_vs⟩
    refine ⟨Δ', hcov_lambda, ?_⟩
    and_intros
    · exact Δ'_extends_Δ₀
    · exact RenamingContext.extendsOnSourceFV_of_extends Δ'_extends_Δ₀ Δ₀_ext
    · intro v hv
      rw [St₆_used_chain, List.mem_cons, not_or] at hv
      exact Δ'_none_out v hv.2
    · -- denotation: show the lambda term denotes and its retraction gives T
      classical
      -- Extract T equation from the B.denote collect semantics
      have hτ_def : τ.defaultZFSet.hasArity vs.length ∧ τ.hasArity vs.length :=
        ⟨BType.hasArity_of_foldl_defaultZFSet τ_hasArity, τ_hasArity⟩
      rw [dif_pos hτ_def, Option.bind_eq_some_iff] at rest_collect
      obtain ⟨⟨𝒫df, τ𝒫df, h𝒫df⟩, den_goPdf, rest2⟩ := rest_collect
      -- rest2 contains the continuation after first bind
      -- It has: if den_P_cond then if typ_det then return (𝒟.sep ℙ) else failure else failure = some ⟨T, ...⟩
      split_ifs at rest2 with h_den_P h_typP_det
      · -- Both conditions hold
        simp only [Option.pure_def, Option.some.injEq, PSigma.mk.injEq] at rest2
        -- rest2 gives us the equation T = 𝒟.sep ℙ
        -- rest2 gives T = 𝒟.sep ℙ and hT types
        -- Now show the SMT lambda denotes and satisfies RDom
        -- z ∉ fv(D_enc) and z ∉ fv(P_enc) since z ∉ St₃.types
        have z_not_fv_D : z ∉ SMT.fv D_enc :=
          funNotMemFvOfNotMemContext (SMT.Typing.weakening St₁_sub_St₃_types typ_D_enc) z_fresh
        have z_not_fv_P : z ∉ SMT.fv P_enc :=
          funNotMemFvOfNotMemContext typ_P_enc z_fresh
        -- Δ' agrees with Δ_D on fv(D_enc): for v ∈ fv(D_enc), v ∉ vs (since D_enc
        -- is typed in St₁.types which is disjoint from vs), so Δ' v = Δ_P v.
        -- But Δ_P extends Δ_D on the relevant vars.
        have Δ'_agrees_D : SMT.RenamingContext.AgreesOnFV Δ_D Δ' D_enc := by
          intro v hv; rw [Δ'_def]
          -- v ∈ fv(D_enc), so v ∈ St₁.types (by typing)
          -- Since vs are disjoint from St₁.types, v ∉ vs
          have hv_ctx : v ∈ St₁.types :=
            SMT.Typing.mem_context_of_mem_fv typ_D_enc hv
          have hvs : v ∉ vs := fun hvs => vs_disj_St₁ v hvs hv_ctx
          simp [hvs]
          -- Δ_P extends Δ_D_ext, and Δ_D_ext v = Δ_D v since v ∉ vs
          have hDD_ext : Δ_D_ext v = Δ_D v := by
            rw [Δ_D_ext_def]; exact Function.updates_of_not_mem Δ_D vs _ v hvs
          -- Need: Δ_D v = Δ_P v
          -- Δ_P extends Δ_D_ext (since Δ_P_extends : Extends Δ_P Δ_D_ext)
          -- Specifically: if Δ_D_ext v = some d, then Δ_P v = some d
          cases h : Δ_D v with
          | none =>
            exfalso
            have := Δ_D_covers v hv
            rw [h] at this; exact absurd this (by simp)
          | some d =>
            symm; exact Δ_P_extends (hDD_ext ▸ h)
        have hΔ'_covers_D : RenamingContext.CoversFV Δ' D_enc := by
          intro v hv
          have hag := Δ'_agrees_D hv
          rw [← hag]; exact Δ_D_covers v hv
        have den_D_Δ' : ⟦D_enc.abstract Δ' hΔ'_covers_D⟧ˢ = some denD' := by
          have heq := SMT.RenamingContext.denote_congr_of_agreesOnFV
            (h1 := Δ_D_covers) (h2 := hΔ'_covers_D) Δ'_agrees_D
          unfold SMT.RenamingContext.denote at heq
          rw [← heq]; exact den_D_enc
        -- D_enc denotes under update Δ' z (some d) for any d (since z ∉ fv D_enc)
        have den_D_upd : ∀ d : SMT.Dom,
            SMT.RenamingContext.denote (Function.update Δ' z (some d)) D_enc
              (SMT.RenamingContext.coversFV_update_of_notMem z_not_fv_D hΔ'_covers_D) =
            some denD' := by
          intro d
          rw [← SMT.RenamingContext.denote_update_of_notMem z_not_fv_D]
          exact den_D_Δ'
        -- denD' info: D_RDom tells us denD'.2.1 = τ.set.toSMTType = τ.toSMTType.fun .bool
        -- and retract (τ.set) denD'.1 = 𝒟
        have denD'_type : denD'.2.1 = τ.toSMTType.fun .bool := D_RDom.1.1
        have denD'_retract : retract (BType.set τ) denD'.1 = 𝒟 := D_RDom.1.2
        -- denD' is a function: denD'.1 ∈ ⟦τ.toSMTType.fun .bool⟧ᶻ = ⟦τ.toSMTType⟧ᶻ.funs 𝔹
        have denD'_mem : denD'.1 ∈ ⟦τ.toSMTType.fun .bool⟧ᶻ := by
          have := denD'.2.2
          rw [denD'_type] at this
          exact this
        have denD'_func : ZFSet.IsFunc ⟦τ.toSMTType⟧ᶻ 𝔹 denD'.1 := by
          rw [SMTType.toZFSet, ZFSet.mem_funs] at denD'_mem
          exact denD'_mem
        have denP'_type : denP'.2.1 = .bool := P_RDom.1
        set ite_body : SMT.Term :=
          SMT.Term.ite ((@ˢD_enc) (.var z))
            (SMT.substList vs (toDestPair vs (.var z)) P_enc) (.bool false) with ite_body_def
        have hcov_ite_upd : ∀ d : SMT.Dom,
            RenamingContext.CoversFV (Function.update Δ' z (some d)) ite_body := by
          intro d v hv
          by_cases hvz : v = z
          · subst hvz; simp
          · rw [Function.update_of_ne hvz]
            exact hcov_lambda v (by
              simp only [SMT.fv, List.mem_removeAll_iff]
              exact ⟨ite_body_def ▸ hv, List.mem_singleton.not.mpr hvz⟩)
        have hcov_D_upd : ∀ Xarg : SMT.Dom,
            RenamingContext.CoversFV (Function.update Δ' z (some Xarg)) D_enc :=
          fun Xarg => SMT.RenamingContext.coversFV_update_of_notMem z_not_fv_D hΔ'_covers_D
        have den_D_upd_eq : ∀ Xarg : SMT.Dom,
            ⟦D_enc.abstract (Function.update Δ' z (some Xarg)) (hcov_D_upd Xarg)⟧ˢ =
            some denD' := by
          intro Xarg
          have := SMT.RenamingContext.denote_update_of_notMem (d := Xarg) z_not_fv_D (h := hΔ'_covers_D)
          unfold SMT.RenamingContext.denote at this; rw [← this]; exact den_D_Δ'
        have den_P_upd : ∀ d : SMT.Dom,
            ⟦P_enc.abstract (Function.update Δ_P z (some d))
              (SMT.RenamingContext.coversFV_update_of_notMem z_not_fv_P Δ_P_covers)⟧ˢ =
            some denP' := by
          intro d
          have := SMT.RenamingContext.denote_update_of_notMem (d := d) z_not_fv_P (h := Δ_P_covers)
          unfold SMT.RenamingContext.denote at this; rw [← this]; exact den_P_enc
        -- Step A: Δ' agrees with Δ_P on fv(P_enc) (for vars not in vs)
        have Δ'_agrees_P : ∀ v ∈ SMT.fv P_enc, v ∉ vs → Δ' v = Δ_P v := by
          intro v hv hvs; rw [Δ'_def]; simp [hvs]
        -- Step B: hgo_cov for abstract.go
        have hgo_cov : ∀ x ∈ SMT.fv ite_body, x ∉ [z] → (Δ' x).isSome = true := by
          intro x hx hxz
          have hne : x ≠ z := by simpa using hxz
          exact hcov_lambda x (by
            simp only [SMT.fv, List.mem_removeAll_iff]
            exact ⟨ite_body_def ▸ hx, List.mem_singleton.not.mpr hne⟩)
        -- Step C: substList denotes for well-typed z_val when condition is true
        -- This is the key missing piece: showing that for W ∈ ⟦τ.toSMTType⟧ᶻ with
        -- D_enc @ W = true, the substList term denotes and has type .bool.
        have hcov_substList_upd : ∀ (W : SMT.Dom),
            RenamingContext.CoversFV (Function.update Δ' z (some W))
              (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
          intro W v hv
          exact (hcov_ite_upd W) v (SMT.fv.mem_ite (Or.inr (Or.inl hv)))
        -- Step C: substList denotes for all well-typed z_val
        -- The ite body short-circuits: when D_enc @ W is false, returns false;
        -- when true, evaluates substList. We prove body totality directly.
        have hbody_total : ∀ (W : SMT.Dom), W.snd.fst = τ.toSMTType →
            ⟦ite_body.abstract (Function.update Δ' z (some W)) (hcov_ite_upd W)⟧ˢ.isSome = true := by
          intro W hW_ty
          have hW_mem : W.fst ∈ ⟦τ.toSMTType⟧ᶻ := hW_ty ▸ W.snd.snd
          -- Get condition denotation via funDenoteAppAt
          have den_D_upd_eq' : ∀ Xarg : SMT.Dom,
              ⟦D_enc.abstract (Function.update Δ' z (some Xarg)) (hcov_D_upd Xarg)⟧ˢ =
              some denD' := den_D_upd_eq
          have hcov_app_upd : ∀ Xarg : SMT.Dom,
              RenamingContext.CoversFV (Function.update Δ' z (some Xarg))
                (SMT.Term.app D_enc (.var z)) := by
            intro Xarg v hv
            simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
            rcases hv with hv | rfl
            · exact hcov_D_upd Xarg v hv
            · simp [Function.update]
          obtain ⟨hcov_app_W, Dapp, hDapp_ty, hDapp_val, hDapp_den⟩ :=
            funDenoteAppAt (Δctx := Δ') (t := D_enc) (x := z)
              (α := τ.toSMTType) (β := .bool) (Y := denD')
              hcov_D_upd den_D_upd_eq' denD'_type
              denD'_func
              W hW_ty hW_mem
          -- Show ite_body denotes by showing the abstract ite term denotes
          -- We know the condition (D_enc @ var z) denotes to Dapp with type .bool
          -- Case split on whether D_enc says z ∈ 𝒟
          by_cases hcond : ZFSet.ZFBool.toBool ⟨Dapp.fst, by
              have := Dapp.snd.snd; rw [hDapp_ty] at this; exact this⟩
          · -- Condition is true: z ∈ 𝒟, substList branch must denote
            -- Suffice to show the substList abstract denotes under Δ'[z↦W]
            suffices h_substList_isSome :
                ⟦(SMT.substList vs (toDestPair vs (.var z)) P_enc).abstract
                  (Function.update Δ' z (some W)) (hcov_substList_upd W)⟧ˢ.isSome = true by
              -- Now show ite_body.abstract isSome using the same ite unfolding as the false branch
              suffices hden : ∃ D,
                  ⟦ite_body.abstract (Function.update Δ' z (some W)) (hcov_ite_upd W)⟧ˢ = some D from
                Option.isSome_iff_exists.mpr hden
              obtain ⟨Dsub, hDsub⟩ := Option.isSome_iff_exists.mp h_substList_isSome
              refine ⟨Dsub, ?_⟩
              -- Mirror the false branch: change to expand ite_body, then simp/rw
              change ⟦(((@ˢD_enc) (SMT.Term.var z)).ite
                (SMT.substList vs (toDestPair vs (.var z)) P_enc) (.bool false)).abstract
                (Function.update Δ' z (some W)) (ite_body_def ▸ hcov_ite_upd W)⟧ˢ = _
              simp only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind]
              conv_lhs => rw [SMT.RenamingContext.denote_abstract_proof_irrel D_enc
                (Function.update Δ' z (some W)) _ (hcov_D_upd W)]
              rw [den_D_upd_eq W]
              simp only [denD'_type, Option.bind_some]
              simp only [Function.update_self, Option.get_some, Option.pure_def, Option.bind_some]
              simp only [hW_ty, dite_true]
              have hDapp_den' := hDapp_den
              simp only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind] at hDapp_den'
              conv at hDapp_den' =>
                lhs; rw [SMT.RenamingContext.denote_abstract_proof_irrel D_enc _ _ (hcov_D_upd W)]
              rw [den_D_upd_eq W] at hDapp_den'
              simp only [Function.update_self, Option.get_some, Option.pure_def,
                Option.bind_some, hW_ty, dite_true] at hDapp_den'
              rw [hDapp_den']
              simp only [Option.bind_some]
              have : Dapp = ⟨Dapp.fst, ⟨.bool, hDapp_ty ▸ Dapp.snd.snd⟩⟩ := by
                obtain ⟨_, ⟨_, _⟩⟩ := Dapp; cases hDapp_ty; rfl
              rw [this]; dsimp
              rw [show ZFSet.ZFBool.toBool ⟨Dapp.fst, _⟩ = true from by convert hcond]
              simp only [ite_true]
              -- Goal: substList abstract = some Dsub
              -- Use proof irrelevance on coverage proofs
              conv_lhs => rw [SMT.RenamingContext.denote_abstract_proof_irrel
                (SMT.substList vs (toDestPair vs (.var z)) P_enc)
                (Function.update Δ' z (some W)) _ (hcov_substList_upd W)]
              exact hDsub
            -- Now prove h_substList_isSome:
            -- Step 1: Transfer from Δ'[z↦W] to Δ_P[z↦W] by agreesOnFV
            have hΔ_agree : SMT.RenamingContext.AgreesOnFV
                (Function.update Δ' z (some W))
                (Function.update Δ_P z (some W))
                (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
              intro v hv
              by_cases hvz : v = z
              · subst hvz; simp [Function.update_self]
              · rw [Function.update_of_ne hvz, Function.update_of_ne hvz]
                have hv_not_vs := fv_substList_disj_vs v hv hvz
                exact Δ'_agrees_P v (by
                  rcases SMT_mem_fv_substList hv with h | ⟨t, ht, hv_t⟩
                  · exact h
                  · exact absurd (SMT_fv_toDestPair_subset ht hv_t ▸ rfl) hvz) hv_not_vs
            have hcov_substList_upd_ΔP : SMT.RenamingContext.CoversFV
                (Function.update Δ_P z (some W))
                (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
              intro v hv
              by_cases hvz : v = z
              · subst hvz; simp [Function.update_self]
              · rw [Function.update_of_ne hvz]
                have hv_not_vs := fv_substList_disj_vs v hv hvz
                rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
                · exact Δ_P_covers v hv_P
                · exact absurd (SMT_fv_toDestPair_subset ht hv_t ▸ rfl) hvz
            rw [show ⟦(SMT.substList vs (toDestPair vs (.var z)) P_enc).abstract
                  (Function.update Δ' z (some W)) (hcov_substList_upd W)⟧ˢ =
                ⟦(SMT.substList vs (toDestPair vs (.var z)) P_enc).abstract
                  (Function.update Δ_P z (some W)) hcov_substList_upd_ΔP⟧ˢ by
              exact SMT.RenamingContext.denote_congr_of_agreesOnFV hΔ_agree]
            -- Step 2: Now show the substList abstract denotes under Δ_P[z↦W].
            -- The substList replaces vs[i] in P_enc by projections of var z.
            -- Under Δ_P[z↦W], var z denotes to W.
            -- Since z ∉ fv(P_enc) and Δ_P covers fv(P_enc), and
            -- the substList only introduces z (which maps to W),
            -- the substList abstract is equivalent to P_enc abstract
            -- under Δ_P with vs[i] updated to proj_i(W).
            --
            -- P_enc denotes under Δ_P (by den_P_enc). We need it to denote
            -- under Δ_P with vs[i] remapped. This requires re-invoking P_ih.
            -- First, establish 𝒟 = 𝒟' (both from the same B denotation)
            have h𝒟_eq : 𝒟 = 𝒟' := by
              have := den_D_eq ▸ den_D
              simp only [Option.some.injEq, PSigma.mk.injEq] at this
              exact this.1.symm
            -- Case split: if vs ∩ fv(P_enc) = ∅ then substList is identity
            by_cases h_vs_disj : ∀ v ∈ vs, v ∉ SMT.fv P_enc
            · -- Positive: substList vs ts P_enc = P_enc, use den_P_upd directly
              have h_eq := SMT_not_mem_fv_substList (ts := toDestPair vs (.var z)) h_vs_disj
              have hcov_P_z : SMT.RenamingContext.CoversFV
                  (Function.update Δ_P z (some W)) P_enc :=
                SMT.RenamingContext.coversFV_update_of_notMem z_not_fv_P Δ_P_covers
              simp only [h_eq]
              rw [SMT.RenamingContext.denote_abstract_proof_irrel P_enc _
                (h_eq ▸ hcov_substList_upd_ΔP) hcov_P_z]
              exact Option.isSome_iff_exists.mpr ⟨denP', den_P_upd W⟩
            · -- Negative: vs intersects fv(P_enc).
              push_neg at h_vs_disj
              -- Step 1: Construct W-derived B-values from retract τ W.fst
              have retract_W_mem := retract_mem_of_canonical τ hW_mem
              have retract_W_hasArity : (retract τ W.fst).hasArity vs.length :=
                hasArity_of_mem_toZFSet τ_hasArity retract_W_mem
              let x_W : Fin vs.length → B.Dom := fun i =>
                ⟨(retract τ W.fst).get vs.length ↑i, ⟨τ.get vs.length ↑i,
                 get_mem_type_of_isTuple retract_W_hasArity τ_hasArity retract_W_mem⟩⟩
              -- Step 2: Build Δ_ext_W and Δ_D_ext_W
              set Δ_ext_W := Function.updates «Δ» vs (List.ofFn fun i => some (x_W i))
              have Δ_fv_P_W : ∀ v ∈ B.fv P, (Δ_ext_W v).isSome = true := by
                intro v hv
                show (Function.updates «Δ» vs (List.ofFn fun i => some (x_W i)) v).isSome = true
                rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
                split_ifs with hvs
                · simp [List.getElem_ofFn]
                · exact Δ_fv v (B.fv.mem_collect (.inr ⟨hv, hvs⟩))
              set Δ_D_ext_W := Function.updates Δ_D vs
                (List.ofFn fun (i : Fin vs.length) => B.RenamingContext.toSMT Δ_ext_W vs[i])
              -- Step 3: Show ofFinDom x_W ∈ 𝒟'
              have h_ofFinDom_in : ZFSet.ofFinDom x_W ∈ 𝒟' := by
                rw [ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
                  (fun i => get_mem_type_of_isTuple retract_W_hasArity τ_hasArity retract_W_mem)
                  retract_W_hasArity τ_hasArity]
                rw [← h𝒟_eq, ← denD'_retract]
                rw [retract]
                simp only [retract_W_mem, denD'_func, ZFSet.mem_sep, dif_pos]
                refine ⟨trivial, ?_⟩
                simp only [canonical_of_retract τ hW_mem]
                rw [← hDapp_val]
                have hDapp_mem_𝔹 : Dapp.fst ∈ 𝔹 := by
                  have := Dapp.snd.snd; rw [hDapp_ty] at this; exact this
                have hcond' : ZFSet.ZFBool.toBool ⟨Dapp.fst, hDapp_mem_𝔹⟩ = true := by convert hcond
                simp only [ZFSet.ZFBool.toBool] at hcond'
                split at hcond'
                · assumption
                · rename_i h_ne_true
                  split at hcond'
                  · simp at hcond'
                  · rename_i h_ne_false
                    exact absurd (ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hDapp_mem_𝔹)
                      (by push_neg; exact ⟨h_ne_false, h_ne_true⟩)
              -- Step 4: Get B-level denotation for P at x_W
              have hx_W_typ : ∀ i, (x_W i).snd.fst = τ.get vs.length i ∧
                  (x_W i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
                fun i => ⟨rfl, (x_W i).snd.snd⟩
              have h_P_W_isSome := h_den_P hx_W_typ h_ofFinDom_in
              obtain ⟨⟨T_W, ⟨τ_W, hT_W⟩⟩, h_den_P_W_eq⟩ :=
                Option.isSome_iff_exists.mp h_P_W_isSome
              have hτ_W_bool : τ_W = BType.bool := by
                rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_W Δ_fv_P_W] at h_den_P_W_eq
                exact (denote_welltyped_eq
                  (t := P.abstract Δ_ext_W Δ_fv_P_W)
                  ⟨_, WFTC.of_abstract, .bool, by convert Typing.of_abstract Δ_fv_P_W typP⟩
                  h_den_P_W_eq).symm
              subst hτ_W_bool
              have h_den_P_W : ⟦P.abstract Δ_ext_W Δ_fv_P_W⟧ᴮ = some ⟨T_W, ⟨BType.bool, hT_W⟩⟩ := by
                rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_W Δ_fv_P_W]
                exact h_den_P_W_eq
              -- Step 5: ExtendsOnSourceFV and none_out for Δ_D_ext_W
              have Δ₀_ext_P_W : RenamingContext.ExtendsOnSourceFV Δ_D_ext_W Δ_ext_W P := by
                intro v d hv_eq
                by_cases hv_fv : v ∈ B.fv P
                · have hv_smt : B.RenamingContext.toSMT Δ_ext_W v = some d := by
                    have : B.RenamingContext.toSMTOnFV Δ_ext_W P v = B.RenamingContext.toSMT Δ_ext_W v := by
                      simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                        B.RenamingContext.restrictToFV_eq_of_mem hv_fv]
                    rwa [← this]
                  by_cases hvs : v ∈ vs
                  · show Function.updates Δ_D vs _ v = some d
                    rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
                    simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                    exact hv_smt
                  · have hDD_ext_W : Δ_D_ext_W v = Δ_D v := by
                      show Function.updates Δ_D vs _ v = Δ_D v
                      exact Function.updates_of_not_mem Δ_D vs _ v hvs
                    rw [hDD_ext_W]
                    have hΔ_ext_W_eq : Δ_ext_W v = «Δ» v := by
                      show Function.updates «Δ» vs _ v = «Δ» v
                      exact Function.updates_of_not_mem «Δ» vs _ v hvs
                    have hv_collect : v ∈ B.fv (Term.collect vs D P) :=
                      fv.mem_collect (.inr ⟨hv_fv, hvs⟩)
                    have hv_smt_Δ : B.RenamingContext.toSMTOnFV «Δ» (Term.collect vs D P) v = some d := by
                      simp only [RenamingContext.toSMTOnFV, RenamingContext.toSMT,
                        B.RenamingContext.restrictToFV_eq_of_mem hv_collect, Option.pure_def,
                        Option.bind_eq_bind]
                      simpa only [RenamingContext.toSMT, hΔ_ext_W_eq, Option.pure_def,
                        Option.bind_eq_bind] using hv_smt
                    exact Δ_D_extends (Δ₀_ext hv_smt_Δ)
                · have : B.RenamingContext.toSMTOnFV Δ_ext_W P v = none := by
                    simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                      B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_fv]
                  rw [this] at hv_eq; exact absurd hv_eq (not_eq_of_beq_eq_false rfl)
              have Δ_D_ext_W_none : ∀ v ∉ St₂.env.usedVars, Δ_D_ext_W v = none := by
                intro v hv
                show Function.updates Δ_D vs _ v = none
                rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
                split_ifs with hvs
                · exfalso; exact hv (St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs _ hvs)))
                · exact Δ_D_none_St₂ v hv
              -- Use P_enc_total with a hybrid base that agrees with Δ_P on fv(P_enc)
              -- Build hybrid base: Δ_D_ext_W on vs, Δ_P on used vars outside vs, none elsewhere
              set Δ₀_hybrid_W : SMT.RenamingContext.Context := fun v =>
                if v ∈ vs then Δ_D_ext_W v
                else if v ∈ St₃.env.usedVars then Δ_P v
                else none
              have Δ₀_hybrid_ext_P_W : RenamingContext.ExtendsOnSourceFV Δ₀_hybrid_W Δ_ext_W P := by
                intro v d hv_eq
                by_cases hv_fv : v ∈ B.fv P
                · have hv_smt : B.RenamingContext.toSMT Δ_ext_W v = some d := by
                    have : B.RenamingContext.toSMTOnFV Δ_ext_W P v = B.RenamingContext.toSMT Δ_ext_W v := by
                      simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                        B.RenamingContext.restrictToFV_eq_of_mem hv_fv]
                    rwa [← this]
                  by_cases hvs : v ∈ vs
                  · show (if v ∈ vs then Δ_D_ext_W v else _) = some d
                    rw [if_pos hvs]
                    show Function.updates Δ_D vs _ v = some d
                    rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
                    simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                    exact hv_smt
                  · -- v ∉ vs, v ∈ B.fv P: Δ₀_hybrid_W v = Δ_P v
                    have hv_collect : v ∈ B.fv (Term.collect vs D P) :=
                      fv.mem_collect (.inr ⟨hv_fv, hvs⟩)
                    -- v ∈ St₃.usedVars (from fv(P) ⊆ fv(collect) ⊆ used ⊆ usedVars)
                    have hv_used : v ∈ St₃.env.usedVars := by
                      have := Δ_fv v hv_collect
                      obtain ⟨bdom, hbdom⟩ := Option.isSome_iff_exists.mp this
                      have h_toSMT : ∃ d', B.RenamingContext.toSMT «Δ» v = some d' := by
                        obtain ⟨V, τ_v, hV⟩ := bdom
                        simp only [B.RenamingContext.toSMT, hbdom, Option.pure_def]; exact ⟨_, rfl⟩
                      obtain ⟨d', hd'⟩ := h_toSMT
                      have h_onFV : B.RenamingContext.toSMTOnFV «Δ» (Term.collect vs D P) v = some d' := by
                        simp only [RenamingContext.toSMTOnFV, RenamingContext.toSMT,
                          B.RenamingContext.restrictToFV_eq_of_mem hv_collect, Option.pure_def,
                          Option.bind_eq_bind, hbdom, Option.bind_some]
                        rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind, hbdom,
                          Option.bind_some] at hd'
                        exact hd'
                      have hΔ_D_v : Δ_D v = some d' := Δ_D_extends (Δ₀_ext h_onFV)
                      by_contra hv_not_used
                      exact absurd (Δ_D_none_St₂ v (fun h => hv_not_used (St₂_sub_St₃ h)))
                        (by rw [hΔ_D_v]; simp)
                    show (if v ∈ vs then _ else if v ∈ St₃.env.usedVars then Δ_P v else none) = some d
                    rw [if_neg hvs, if_pos hv_used]
                    -- Δ_P v = toSMT Δ v = toSMT Δ_ext_W v (since v ∉ vs)
                    have hΔ_ext_W_eq : Δ_ext_W v = «Δ» v := by
                      show Function.updates «Δ» vs _ v = «Δ» v
                      exact Function.updates_of_not_mem «Δ» vs _ v hvs
                    -- toSMTOnFV Δ_ext P v = toSMT Δ v (since v ∈ fv(P) and Δ_ext v = Δ v)
                    have hΔ_ext_eq : Δ_ext v = «Δ» v := by
                      rw [Δ_ext_def]; exact Function.updates_of_not_mem «Δ» vs _ v hvs
                    -- toSMT Δ_ext_W v = toSMT Δ v (since Δ_ext_W v = Δ v)
                    -- toSMTOnFV Δ_ext P v = toSMT Δ_ext v = toSMT Δ v (since Δ_ext v = Δ v)
                    have h_toSMT_eq : B.RenamingContext.toSMT Δ_ext v = some d := by
                      rw [B.RenamingContext.toSMT, hΔ_ext_eq, ← B.RenamingContext.toSMT]
                      rw [B.RenamingContext.toSMT, hΔ_ext_W_eq, ← B.RenamingContext.toSMT] at hv_smt
                      exact hv_smt
                    have h_src : B.RenamingContext.toSMTOnFV Δ_ext P v = some d := by
                      simp only [RenamingContext.toSMTOnFV, RenamingContext.toSMT,
                        B.RenamingContext.restrictToFV_eq_of_mem hv_fv]
                      rw [B.RenamingContext.toSMT] at h_toSMT_eq; exact h_toSMT_eq
                    exact Δ_P_src_ext h_src
                · have : B.RenamingContext.toSMTOnFV Δ_ext_W P v = none := by
                    simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                      B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_fv]
                  rw [this] at hv_eq; exact absurd hv_eq (not_eq_of_beq_eq_false rfl)
              have Δ₀_hybrid_W_none_St₃ : ∀ v ∉ St₃.env.usedVars, Δ₀_hybrid_W v = none := by
                intro v hv
                show (if v ∈ vs then Δ_D_ext_W v else if v ∈ St₃.env.usedVars then Δ_P v else none) = none
                have hv_not_vs : v ∉ vs := fun hvs => hv (St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs v hvs))))
                rw [if_neg hv_not_vs, if_neg hv]
              -- none_used for hybrid: ∀ v ∉ St₂.usedVars, Δ₀_hybrid_W v = none
              -- This requires Δ_P v = none for v ∈ St₃ \ St₂, which the P-IH output
              -- does not provide (it only gives ∀ v ∉ St₃.usedVars, Δ_P v = none).
              -- The IH output postcondition needs a ∀ v ∉ used, Δ' v = none clause.
              have Δ₀_hybrid_W_dom : ∀ v, Δ₀_hybrid_W v ≠ none → v ∈ St₃.types := by
                intro v hv
                change (if v ∈ vs then Δ_D_ext_W v else if v ∈ St₃.env.usedVars then Δ_P v else none) ≠ none at hv
                split_ifs at hv with hvs hused
                · -- v ∈ vs: vs ⊆ St₂.types ⊆ St₃.types
                  apply AList.mem_of_subset St₂_sub_St₃_types
                  rw [St₂_types]
                  exact foldl_insert_zip_mem vs (τ.toSMTType.fromProdl (vs.length - 1)) St₁.types v
                    (by rw [fromProdl_length_of_hasArity τ_hasArity]) hvs
                · exact Δ_P_dom v hv
                · exact absurd rfl hv
              obtain ⟨Δ_P_W, hcov_PW, denT_W', Δ_P_W_extends, _, _, hden_PW, _, _⟩ :=
                P_enc_total Δ_ext_W Δ_fv_P_W Δ₀_hybrid_W Δ₀_hybrid_ext_P_W
                  Δ₀_hybrid_W_none_St₃ (by
                    intro v d hv τ_v hτ_v
                    change (if v ∈ vs then Δ_D_ext_W v else if v ∈ St₃.env.usedVars then Δ_P v else none) = some d at hv
                    split_ifs at hv with hvs hused
                    · -- v ∈ vs: Δ_D_ext_W v = some d, which equals toSMT Δ_ext_W v
                      have hv_idx : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hvs
                      have hΔ_ext_W_vi : Δ_ext_W v = some (x_W ⟨vs.idxOf v, hv_idx⟩) := by
                        show Function.updates «Δ» vs _ v = _
                        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
                        simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                      -- Δ_D_ext_W v = toSMT Δ_ext_W v for v ∈ vs
                      have hΔ_D_ext_eq : Δ_D_ext_W v = B.RenamingContext.toSMT Δ_ext_W v := by
                        show Function.updates Δ_D vs _ v = _
                        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
                        simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                      rw [hΔ_D_ext_eq] at hv
                      -- Unfold toSMT to extract d's type
                      rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind,
                        hΔ_ext_W_vi, Option.bind_some] at hv
                      have hd_inj := Option.some_injective _ hv
                      have hd_ty : d.snd.fst = (τ.get vs.length ⟨vs.idxOf v, hv_idx⟩).toSMTType :=
                        (congr_arg (·.snd.fst) hd_inj).symm
                      -- St₂.types.lookup v = some τs[idxOf v]
                      set τs := τ.toSMTType.fromProdl (vs.length - 1) with τs_def
                      have hτs_len := fromProdl_length_of_hasArity τ_hasArity
                      have hv_idx_τ : vs.idxOf v < τs.length := hτs_len ▸ hv_idx
                      have h_St₂ : St₂.types.lookup v = some τs[vs.idxOf v] := by
                        have h := foldl_insert_lookup_zip (Γ := St₁.types) vs_nodup hv_idx hv_idx_τ
                        rwa [← St₂_types, List.getElem_idxOf hv_idx] at h
                      have h_St₃ : St₃.types.lookup v = some τs[vs.idxOf v] :=
                        AList.lookup_of_subset St₂_sub_St₃_types h_St₂
                      rw [h_St₃] at hτ_v; cases hτ_v
                      rw [hd_ty]
                      -- (τ.get vs.length i).toSMTType = (τ.toSMTType.fromProdl (vs.length-1))[i]
                      exact toSMTType_get_eq_fromProdl_getElem τ_hasArity hv_idx
                    · -- v ∈ St₃.usedVars: Δ_P v = some d
                      exact Δ_P_wt v d hv τ_v hτ_v) T_W hT_W h_den_P_W
              -- Transfer: substList under Δ_P[z↦W] = substList under Δ_P_W[z↦W]
              -- Δ_P_W extends Δ₀_hybrid_W which agrees with Δ_P on fv(P_enc) outside vs
              -- Step 1: Show Δ_P_W[z↦W] agrees with Δ_P[z↦W] on fv(substList)
              have hΔ_PW_agree : SMT.RenamingContext.AgreesOnFV
                  (Function.update Δ_P_W z (some W))
                  (Function.update Δ_P z (some W))
                  (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
                intro v hv
                by_cases hvz : v = z
                · subst hvz; simp [Function.update_self]
                · rw [Function.update_of_ne hvz, Function.update_of_ne hvz]
                  have hv_not_vs := fv_substList_disj_vs v hv hvz
                  -- v ∈ fv(P_enc) (since v ∈ fv(substList), v ∉ vs, v ≠ z)
                  have hv_P : v ∈ SMT.fv P_enc := by
                    rcases SMT_mem_fv_substList hv with h | ⟨t, ht, hv_t⟩
                    · exact h
                    · exact absurd (SMT_fv_toDestPair_subset ht hv_t) hvz
                  -- v ∈ St₃.usedVars (from fv(P_enc) ⊆ keys(St₃.types) ⊆ St₃.usedVars)
                  have hv_used : v ∈ St₃.env.usedVars :=
                    St₃_keys_sub (AList.mem_keys.mpr (SMT.Typing.mem_context_of_mem_fv typ_P_enc hv_P))
                  -- Δ₀_hybrid_W v = Δ_P v (since v ∉ vs, v ∈ St₃.usedVars)
                  have hΔ₀_v : Δ₀_hybrid_W v = Δ_P v := by
                    show (if v ∈ vs then _ else if v ∈ St₃.env.usedVars then Δ_P v else none) = Δ_P v
                    rw [if_neg hv_not_vs, if_pos hv_used]
                  -- Δ_P v = some d (from coverage)
                  have hv_cov := Δ_P_covers v hv_P
                  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hv_cov
                  -- Δ_P_W v = some d (from Extends Δ_P_W Δ₀_hybrid_W)
                  have hΔ_PW_v : Δ_P_W v = some d := Δ_P_W_extends (hΔ₀_v ▸ hd)
                  rw [hΔ_PW_v, hd]
              -- Step 2: Coverage of substList under Δ_P_W[z↦W]
              have hcov_substList_PW : SMT.RenamingContext.CoversFV
                  (Function.update Δ_P_W z (some W))
                  (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
                intro v hv
                by_cases hvz : v = z
                · subst hvz; simp [Function.update_self]
                · rw [Function.update_of_ne hvz]
                  have hagr := hΔ_PW_agree hv
                  rw [Function.update_of_ne hvz, Function.update_of_ne hvz] at hagr
                  rw [hagr]
                  have := hcov_substList_upd_ΔP v hv
                  rwa [Function.update_of_ne hvz] at this
              -- Step 3: Transfer denotation via agreesOnFV
              rw [show ⟦(SMT.substList vs (toDestPair vs (.var z)) P_enc).abstract
                    (Function.update Δ_P z (some W)) hcov_substList_upd_ΔP⟧ˢ =
                  ⟦(SMT.substList vs (toDestPair vs (.var z)) P_enc).abstract
                    (Function.update Δ_P_W z (some W)) hcov_substList_PW⟧ˢ from
                (SMT.RenamingContext.denote_congr_of_agreesOnFV hΔ_PW_agree).symm]
              -- Step 4: Now show substList denotes under Δ_P_W[z↦W]
              -- P_enc denotes under Δ_P_W[z↦W] since z ∉ fv(P_enc)
              have hcov_PW_z : SMT.RenamingContext.CoversFV
                  (Function.update Δ_P_W z (some W)) P_enc :=
                SMT.RenamingContext.coversFV_update_of_notMem z_not_fv_P hcov_PW
              have hden_PW_z : ⟦P_enc.abstract (Function.update Δ_P_W z (some W)) hcov_PW_z⟧ˢ =
                  some denT_W' := by
                have := SMT.RenamingContext.denote_update_of_notMem (d := W) z_not_fv_P (h := hcov_PW)
                unfold SMT.RenamingContext.denote at this; rw [← this]; exact hden_PW
              -- Δ_P_W(vs[i]) is defined (via Extends from Δ_D_ext_W)
              have hΔ_PW_vs_isSome : ∀ (i : Fin vs.length), (Δ_P_W vs[i]).isSome = true := by
                intro ⟨i, hi⟩
                have hvi_mem : vs[i] ∈ vs := List.getElem_mem hi
                -- Δ_D_ext_W vs[i] = updates Δ_D vs ys vs[i] = ys[idxOf vs vs[i]]
                -- = toSMT Δ_ext_W vs[idxOf vs vs[i]] = toSMT Δ_ext_W vs[i] (by getElem_idxOf)
                -- toSMT Δ_ext_W vs[i] is some because Δ_ext_W vs[i] = some (x_W i)
                -- So Δ_D_ext_W vs[i] = some d for some d, and Extends gives Δ_P_W vs[i] = some d.
                have hΔ_ext_W_vi : (Δ_ext_W vs[i]).isSome = true := by
                  show (Function.updates «Δ» vs _ vs[i]).isSome = true
                  rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                    dif_pos hvi_mem]
                  simp only [List.getElem_ofFn, Option.isSome]
                obtain ⟨bval, hbval⟩ := Option.isSome_iff_exists.mp hΔ_ext_W_vi
                have htoSMT_some : ∃ d, B.RenamingContext.toSMT Δ_ext_W vs[i] = some d := by
                  obtain ⟨V, τ_v, hV⟩ := bval
                  simp only [B.RenamingContext.toSMT, hbval, Option.bind_some, Option.pure_def]
                  exact ⟨_, rfl⟩
                obtain ⟨d, hd⟩ := htoSMT_some
                have hΔ_D_ext_W_vi : Δ_D_ext_W vs[i] = some d := by
                  show Function.updates Δ_D vs _ vs[i] = some d
                  rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                    dif_pos hvi_mem]
                  simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                  exact hd
                have hΔ₀_hybrid_W_vi : Δ₀_hybrid_W vs[i] = some d := by
                  show (if vs[i] ∈ vs then Δ_D_ext_W vs[i] else _) = some d
                  rw [if_pos hvi_mem]; exact hΔ_D_ext_W_vi
                exact Option.isSome_iff_exists.mpr ⟨d, Δ_P_W_extends hΔ₀_hybrid_W_vi⟩
              -- Define Ds as Δ_P_W(vs[i])
              let Ds_W : List SMT.Dom := List.ofFn fun i : Fin vs.length =>
                (Δ_P_W vs[i]).get (hΔ_PW_vs_isSome i)
              -- vs[i] ∉ bv P_enc (typing: vs[i] ∈ St₃.types, bv disjoint from context)
              have hvs_not_bv : ∀ x ∈ vs, x ∉ SMT.bv P_enc := by
                intro v hv hbv
                -- v ∈ vs → v ∈ St₂.types → v ∈ St₃.types → v ∉ bv P_enc (by bv_notMem_context)
                -- First show v ∈ St₂.types via foldl_insert_lookup_zip
                have hv_used : v ∈ St₁.env.usedVars := used_sub_St₁ (vars_used_vs v hv)
                have hv_not_D : v ∉ B.fv D := by
                  intro hfv; exact vs_Γ_disj v hv (AList.lookup_isSome.mp
                    (B.Typing.mem_context_of_mem_fv typ_D hfv))
                -- v ∈ St₁.types because v is a binder variable that was inserted into St₂
                set τs := τ.toSMTType.fromProdl (vs.length - 1) with τs_def
                have hτs_len := fromProdl_length_of_hasArity τ_hasArity
                have hv_idx : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hv
                -- St₂.types has vs[i] ↦ τs[i], and v = vs[idxOf v vs]
                have hv_idx_τ : vs.idxOf v < τs.length := hτs_len ▸ hv_idx
                have h_St₂_lookup : ∃ σ, St₂.types.lookup v = some σ := by
                  have h := foldl_insert_lookup_zip (Γ := St₁.types) vs_nodup hv_idx hv_idx_τ
                  rw [← St₂_types, List.getElem_idxOf hv_idx] at h
                  exact ⟨_, h⟩
                have hv_St₃ : v ∈ St₃.types := by
                  obtain ⟨σ, hσ⟩ := h_St₂_lookup
                  have h_entry := AList.mem_lookup_iff.mp hσ
                  have h_St₃_entry := St₂_sub_St₃_types h_entry
                  have h_St₃_lookup := AList.mem_lookup_iff.mpr h_St₃_entry
                  exact AList.lookup_isSome.mp (Option.isSome_of_eq_some h_St₃_lookup)
                exact SMT.Typing.bv_notMem_context typ_P_enc v hbv hv_St₃
              -- z ∉ bv P_enc
              have z_not_bv_P : z ∉ SMT.bv P_enc := by
                intro hbv
                have typ_P_enc_ins := SMT.Typing.weakening
                  (SMT.TypeContext.entries_subset_insert_of_notMem (τ := τ.toSMTType) z_fresh) typ_P_enc
                exact SMT.Typing.bv_notMem_context typ_P_enc_ins _ hbv
                  ((AList.mem_insert _).mpr (Or.inl rfl))
              -- z ∉ vs (z is fresh, vs[i] ∈ usedVars)
              have z_not_vs : z ∉ vs := by
                intro hz; exact z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used
                  (used_sub_St₁ (vars_used_vs z hz))))
              -- CoversFV for updates context
              have h_cov_upd : SMT.RenamingContext.CoversFV
                  (Function.updates (Function.update Δ_P_W z (some W)) vs
                    (Ds_W.map Option.some)) P_enc := by
                intro v hv
                by_cases hvs : v ∈ vs
                · rw [Function.updates_eq_if (by rw [List.length_map, List.length_ofFn]) vs_nodup,
                    dif_pos hvs]
                  simp
                · rw [Function.updates_of_not_mem _ vs _ _ hvs,
                    Function.update_of_ne (by intro heq; exact z_not_fv_P (heq ▸ hv))]
                  exact hcov_PW v hv
              -- Apply abstract_substList_denote
              have hlen_xt : vs.length = (toDestPair vs (.var z)).length := by
                rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]; simp
              have hlen_xd : vs.length = Ds_W.length := by simp [Ds_W, List.length_ofFn]
              have h_eq := SMT.RenamingContext.abstract_substList_denote P_enc vs (toDestPair vs (.var z))
                Ds_W hlen_xt hlen_xd vs_nodup hvs_not_bv toDestPair_bv_nil
                (fun t ht w hw hbv => by rw [SMT_fv_toDestPair_subset ht hw] at hbv; exact z_not_bv_P hbv)
                toDestPair_ne_none
                (fun t ht w hw => by rw [SMT_fv_toDestPair_subset ht hw]; exact z_not_vs)
                (by -- hts_den: toDestPair[i] denotes to Ds_W[i] under Δ_P_W[z↦W]
                  -- Each toDestPair[i] is a nested fst/snd of (var z).
                  -- Under Δ_P_W[z↦W], (var z) denotes to W.
                  -- The i-th projection of W.fst equals
                  -- canonical(αs[i], (retract τ W.fst).get i) = (Δ_P_W vs[i]).get
                  -- by canonical_of_retract + the definition of Δ_D_ext_W + Extends.
                  -- This requires induction on the toDestPair structure
                  -- paired with the nested pair type structure of τ.toSMTType.
                  intro i hi_x hi_t hi_d
                  -- CoversFV: toDestPair[i] has fv ⊆ {z}, z is covered
                  have hcov_ti : SMT.RenamingContext.CoversFV
                      (Function.update Δ_P_W z (some W)) (toDestPair vs (.var z))[i] := by
                    intro v hv
                    have hvz := SMT_fv_toDestPair_subset (List.getElem_mem hi_t) hv
                    subst hvz; simp [Function.update_self]
                  refine ⟨hcov_ti, ?_⟩
                  -- Use toDestPair_denote_gen to get D_j
                  have hcov_z : SMT.RenamingContext.CoversFV
                      (Function.update Δ_P_W z (some W)) (.var z) := by
                    intro v hv; simp [SMT.fv] at hv; subst hv; simp [Function.update_self]
                  have hden_z : ⟦(SMT.Term.var z).abstract
                      (Function.update Δ_P_W z (some W)) hcov_z⟧ˢ = some W := by
                    simp [SMT.Term.abstract, SMT.denote, Function.update_self]
                  have hW_hasArity := hasArity_of_mem_toSMTZFSet τ_hasArity hW_mem
                  obtain ⟨hcov_j, D_j, hden_j, hfst_j, hty_j⟩ :=
                    toDestPair_denote_gen τ vs (.var z) W
                      (Function.update Δ_P_W z (some W)) [] [] vs_nemp
                      hcov_z hden_z hW_ty hW_mem τ_hasArity rfl (by simp) i hi_x hi_t
                  rw [SMT.RenamingContext.denote_abstract_proof_irrel _ _ hcov_ti hcov_j,
                    hden_j]
                  -- Goal: some D_j = some Ds_W[i]
                  have hvi_mem : vs[i] ∈ vs := List.getElem_mem hi_x
                  -- Δ_ext_W vs[i] = some (x_W ⟨i, hi_x⟩)
                  have hΔ_ext_W_vi : Δ_ext_W vs[i] = some (x_W ⟨i, hi_x⟩) := by
                    show Function.updates «Δ» vs _ vs[i] = _
                    rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                      dif_pos hvi_mem]
                    simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                    simp [List.idxOf_getElem vs_nodup]
                  -- toSMT Δ_ext_W vs[i] = some d_smt
                  obtain ⟨d_smt, hd_smt⟩ : ∃ d, B.RenamingContext.toSMT Δ_ext_W vs[i] = some d := by
                    simp only [B.RenamingContext.toSMT, hΔ_ext_W_vi, Option.pure_def]
                    exact ⟨_, rfl⟩
                  -- Unfold toSMT to extract d_smt properties
                  have htoSMT_unf : B.RenamingContext.toSMT Δ_ext_W vs[i] =
                      some d_smt := hd_smt
                  rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind,
                    hΔ_ext_W_vi, Option.bind_some] at htoSMT_unf
                  -- htoSMT_unf now equates a concrete ⟨..⟩ with some d_smt
                  have hd_inj := Option.some_injective _ htoSMT_unf
                  have hd_ty : d_smt.snd.fst = (τ.get vs.length ⟨i, hi_x⟩).toSMTType :=
                    (congr_arg (·.snd.fst) hd_inj).symm
                  have hd_retract : retract (τ.get vs.length ⟨i, hi_x⟩) d_smt.fst =
                      (retract τ W.fst).get vs.length ⟨i, hi_x⟩ := by
                    have hfst_inj := congr_arg (·.fst) hd_inj
                    dsimp at hfst_inj
                    rw [← hfst_inj]
                    exact retract_of_canonical _ (x_W ⟨i, hi_x⟩).snd.snd
                  -- Δ_D_ext_W vs[i] = some d_smt
                  have hΔ_D_ext_W_vi : Δ_D_ext_W vs[i] = some d_smt := by
                    show Function.updates Δ_D vs _ vs[i] = some d_smt
                    rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                      dif_pos hvi_mem]
                    simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                    exact hd_smt
                  -- Δ_P_W vs[i] = some d_smt (by Extends through hybrid base)
                  have hΔ₀_hybrid_W_vi' : Δ₀_hybrid_W vs[i] = some d_smt := by
                    show (if vs[i] ∈ vs then Δ_D_ext_W vs[i] else _) = some d_smt
                    rw [if_pos hvi_mem]; exact hΔ_D_ext_W_vi
                  have hΔ_PW_vi : Δ_P_W vs[i] = some d_smt :=
                    Δ_P_W_extends hΔ₀_hybrid_W_vi'
                  -- d_smt.fst = W.fst.get i via canonical_of_retract
                  have hWi_mem : W.fst.get vs.length ⟨i, hi_x⟩ ∈
                      ⟦(τ.get vs.length ⟨i, hi_x⟩).toSMTType⟧ᶻ :=
                    get_mem_toSMTZFSet (hasArity_of_mem_toSMTZFSet τ_hasArity hW_mem)
                      τ_hasArity hW_mem
                  have hd_fst : d_smt.fst = W.fst.get vs.length ⟨i, hi_x⟩ := by
                    have hd_mem : d_smt.fst ∈ ⟦(τ.get vs.length ⟨i, hi_x⟩).toSMTType⟧ᶻ :=
                      hd_ty ▸ d_smt.snd.snd
                    have h_retract_eq : retract (τ.get vs.length ⟨i, hi_x⟩) d_smt.fst =
                        retract (τ.get vs.length ⟨i, hi_x⟩) (W.fst.get vs.length ⟨i, hi_x⟩) := by
                      rw [hd_retract, retract_get_comm
                        (hasArity_of_mem_toSMTZFSet τ_hasArity hW_mem) τ_hasArity hW_mem]
                    calc d_smt.fst
                        = fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi_x⟩)).1
                            (is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                            ⟨retract (τ.get vs.length ⟨i, hi_x⟩) d_smt.fst, _⟩ :=
                          (canonical_of_retract _ hd_mem).symm
                      _ = fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi_x⟩)).1
                            (is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                            ⟨retract (τ.get vs.length ⟨i, hi_x⟩) (W.fst.get vs.length ⟨i, hi_x⟩), _⟩ := by
                          simp [h_retract_eq]
                      _ = W.fst.get vs.length ⟨i, hi_x⟩ :=
                          canonical_of_retract _ hWi_mem
                  -- D_j = d_smt (fst and snd.fst match)
                  have hD_j_eq : D_j = d_smt := by
                    rcases D_j with ⟨z1, τ1, hz1⟩
                    rcases d_smt with ⟨z2, τ2, hz2⟩
                    exact SMT.RenamingContext.Dom_ext'
                      (show z1 = z2 by simpa using hfst_j.trans hd_fst.symm)
                      (show τ1 = τ2 by simpa using hty_j.trans hd_ty.symm)
                  -- Ds_W[i] = d_smt
                  have hDs_eq : Ds_W[i] = d_smt := by
                    simp only [Ds_W, List.getElem_ofFn, Fin.getElem_fin]
                    simp only [hΔ_PW_vi, Option.get_some]
                  rw [show D_j = Ds_W[i] from hD_j_eq.trans hDs_eq.symm])
                hcov_substList_PW h_cov_upd
              rw [h_eq]
              -- RHS agrees with Δ_P_W on fv(P_enc), so equals hden_PW
              have h_upd_eq : ∀ v ∈ SMT.fv P_enc,
                  Function.updates (Function.update Δ_P_W z (some W)) vs
                    (Ds_W.map Option.some) v = Δ_P_W v := by
                intro v hv
                by_cases hvs : v ∈ vs
                · rw [Function.updates_eq_if (by rw [List.length_map, List.length_ofFn]) vs_nodup,
                    dif_pos hvs]
                  simp only [Ds_W, List.getElem_map, List.getElem_ofFn, Fin.getElem_fin,
                    List.getElem_idxOf]
                  exact Option.some_get _
                · rw [Function.updates_of_not_mem _ vs _ _ hvs,
                    Function.update_of_ne (by intro heq; exact z_not_fv_P (heq ▸ hv))]
              have h_upd_agree : SMT.RenamingContext.AgreesOnFV
                  (Function.updates (Function.update Δ_P_W z (some W)) vs
                    (Ds_W.map Option.some)) Δ_P_W P_enc :=
                h_upd_eq
              have h_eq2 := SMT.RenamingContext.denote_congr_of_agreesOnFV
                (h1 := h_cov_upd) (h2 := hcov_PW) h_upd_agree
              unfold SMT.RenamingContext.denote at h_eq2
              rw [h_eq2, hden_PW]
              rfl
          · -- Condition is false: D_enc says z ∉ 𝒟, ite returns false
            -- ite body denotes because the condition evaluates to false,
            -- short-circuiting to `bool false` which always denotes
            suffices hden : ∃ D, ⟦ite_body.abstract (Function.update Δ' z (some W)) (hcov_ite_upd W)⟧ˢ = some D from
              Option.isSome_iff_exists.mpr hden
            -- ite_body unfolds to ite (app D_enc (var z)) (substList ...) (bool false)
            -- We know condition Dapp denotes with type .bool and toBool = false
            -- So the ite evaluates to the false branch = bool false
            refine ⟨⟨ZFSet.zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩, ?_⟩
            -- The abstract of ite produces PHOAS.ite, denote evaluates cond then branches
            change ⟦(((@ˢD_enc) (SMT.Term.var z)).ite
              (SMT.substList vs (toDestPair vs (.var z)) P_enc) (.bool false)).abstract
              (Function.update Δ' z (some W)) (hcov_ite_upd W)⟧ˢ = _
            simp only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind]
            -- Rewrite D_enc denotation using proof irrelevance
            conv_lhs => rw [SMT.RenamingContext.denote_abstract_proof_irrel D_enc
              (Function.update Δ' z (some W)) _ (hcov_D_upd W)]
            rw [den_D_upd_eq W]
            -- Now denD' is the value; extract its type for the app match
            simp only [Option.bind_some]
            -- W value from context update
            simp only [Function.update_self, Option.get_some, Option.pure_def, Option.bind_some]
            -- The app should now compute: need IsPFunc and membership
            simp only [hW_ty]
            -- Use hDapp_den to establish what the match/bind chain produces
            -- hDapp_den says (app D_enc (var z)).abstract ... denotes to Dapp
            -- After simp [abstract, denote], this should match the goal's first bind
            have hDapp_den' := hDapp_den
            simp only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind] at hDapp_den'
            conv at hDapp_den' =>
              lhs; rw [SMT.RenamingContext.denote_abstract_proof_irrel D_enc _ _ (hcov_D_upd W)]
            rw [den_D_upd_eq W] at hDapp_den'
            simp only [Function.update_self, Option.get_some, Option.pure_def,
              Option.bind_some, hW_ty] at hDapp_den'
            -- hDapp_den' now matches the first bind in the goal
            rw [hDapp_den']
            simp only [Option.bind_some]
            -- Match on Dapp with type .bool; use Dapp = ⟨Dapp.fst, ⟨.bool, ...⟩⟩
            have : Dapp = ⟨Dapp.fst, ⟨.bool, hDapp_ty ▸ Dapp.snd.snd⟩⟩ := by
              obtain ⟨_, ⟨_, _⟩⟩ := Dapp; cases hDapp_ty; rfl
            rw [this]; dsimp
            have hDapp_mem_𝔹 : Dapp.fst ∈ 𝔹 := by
              have := Dapp.snd.snd; rw [hDapp_ty] at this; exact this
            have hcond' : ¬ZFSet.ZFBool.toBool ⟨Dapp.fst, hDapp_mem_𝔹⟩ = true := by
              convert hcond
            rw [show ZFSet.ZFBool.toBool ⟨Dapp.fst, _⟩ = false from eq_false_of_ne_true hcond']
            simp [ite_false, ZFSet.ZFBool.ofBool]
        have hbody_ty : ∀ (W : SMT.Dom) (hW_ty : W.snd.fst = τ.toSMTType)
            (Db : SMT.Dom),
            ⟦ite_body.abstract (Function.update Δ' z (some W)) (hcov_ite_upd W)⟧ˢ = some Db →
            Db.snd.fst = .bool := by
          intro W hW_ty Db hDb
          have typ_ite_body : St₃.types.insert z τ.toSMTType ⊢ˢ ite_body : .bool := by
            rw [ite_body_def]
            exact SMT.Typing.ite _ _ _ _ _
              (SMT.Typing.app _ _ _ _ _
                (SMT.Typing.weakening
                  (SMT.TypeContext.entries_subset_insert_of_notMem (τ := τ.toSMTType) z_fresh)
                  (SMT.Typing.weakening St₁_sub_St₃_types typ_D_enc))
                (SMT.Typing.var _ z τ.toSMTType (AList.lookup_insert St₃.types)))
              (SMT_Typing_substList vs (toDestPair vs (.var z)) P_enc
                (SMT.Typing.weakening
                  (SMT.TypeContext.entries_subset_insert_of_notMem (τ := τ.toSMTType) z_fresh)
                  typ_P_enc)
                toDestPair_bv_nil
                (by
                  set Γ_z := St₃.types.insert z τ.toSMTType
                  set τs := τ.toSMTType.fromProdl (vs.length - 1)
                  have τs_len : τs.length = vs.length := fromProdl_length_of_hasArity τ_hasArity
                  intro i hi_x hi_t hx
                  have hi_τs : i < τs.length := τs_len ▸ hi_x
                  have h_St₂_lookup : St₂.types.lookup vs[i] = some τs[i] := by
                    rw [St₂_types]; exact foldl_insert_lookup_zip vs_nodup hi_x hi_τs
                  have h_St₃_lookup : St₃.types.lookup vs[i] = some τs[i] :=
                    AList.mem_lookup_iff.2 (St₂_sub_St₃_types (AList.mem_lookup_iff.1 h_St₂_lookup))
                  have hne : vs[i] ≠ z := by
                    intro heq
                    have hvi_used : vs[i] ∈ St₃.env.usedVars :=
                      St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs vs[i] (List.getElem_mem hi_x))))
                    exact z_not_used (heq ▸ hvi_used)
                  have h_lookup : Γ_z.lookup vs[i] = some τs[i] := by
                    rw [AList.lookup_insert_ne hne]; exact h_St₃_lookup
                  have h_get : (Γ_z.lookup vs[i]).get hx = τs[i] := by simp [h_lookup]
                  rw [h_get]
                  exact (toDestPair_typing_gen Γ_z vs (.var z) (.var z) τ.toSMTType [] []
                    vs_nemp rfl (SMT.Typing.var Γ_z z τ.toSMTType (AList.lookup_insert St₃.types))
                    (by rw [show τs = τ.toSMTType.fromProdl (vs.length - 1) from rfl] at τs_len; exact τs_len) rfl
                    (fun j hj => absurd hj (Nat.not_lt_zero j))
                    i τs[i]
                    (by simp only [List.append_nil]; rw [List.getElem?_eq_getElem hi_τs])).2))
              (SMT.Typing.bool _ _)
          exact denote_type_eq_of_typing (Γ := St₃.types.insert z τ.toSMTType) typ_ite_body hDb
        -- Step E: lambda isSome
        have hcov_ite_upd' : ∀ W : SMT.Dom,
            RenamingContext.CoversFV (Function.update Δ' z (some W)) ite_body :=
          fun W => hcov_ite_upd W
        have hsome_lambda :
            ⟦((λˢ [z]) [τ.toSMTType] ite_body).abstract Δ' hcov_lambda⟧ˢ.isSome = true := by
          rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
          have hlen : [z].length > 0 := Nat.zero_lt_succ 0
          rw [dif_pos hlen]
          split_ifs with den_t_isSome den_t_typ_det
          · simp
          · exfalso; apply den_t_typ_det
            intro x y hx hy
            let Wx : SMT.Dom := x ⟨0, hlen⟩
            let Wy : SMT.Dom := y ⟨0, hlen⟩
            have hWx_ty : Wx.snd.fst = τ.toSMTType := by
              simpa [Wx] using (hx ⟨0, hlen⟩).1
            have hWy_ty : Wy.snd.fst = τ.toSMTType := by
              simpa [Wy] using (hy ⟨0, hlen⟩).1
            have hgo_x := funAbstractGoSingle (Δctx := Δ') (P := ite_body) (v := z) (τ := τ.toSMTType)
              hgo_cov hcov_ite_upd' x hx
            have hgo_y := funAbstractGoSingle (Δctx := Δ') (P := ite_body) (v := z) (τ := τ.toSMTType)
              hgo_cov hcov_ite_upd' y hy
            obtain ⟨Dx, hDx⟩ := Option.isSome_iff_exists.mp (hbody_total Wx hWx_ty)
            obtain ⟨Dy, hDy⟩ := Option.isSome_iff_exists.mp (hbody_total Wy hWy_ty)
            have hden_x : ⟦(SMT.Term.abstract.go ite_body [z] Δ' hgo_cov).uncurry x⟧ˢ = some Dx := by
              rw [hgo_x]; exact hDx
            have hden_y : ⟦(SMT.Term.abstract.go ite_body [z] Δ' hgo_cov).uncurry y⟧ˢ = some Dy := by
              rw [hgo_y]; exact hDy
            calc (⟦(SMT.Term.abstract.go ite_body [z] Δ' hgo_cov).uncurry x⟧ˢ.get
                    (den_t_isSome hx)).snd.fst
                = Dx.snd.fst := congrArg (·.snd.fst) (Option.get_of_eq_some (den_t_isSome hx) hden_x)
              _ = SMTType.bool := hbody_ty Wx hWx_ty Dx hDx
              _ = Dy.snd.fst := (hbody_ty Wy hWy_ty Dy hDy).symm
              _ = (⟦(SMT.Term.abstract.go ite_body [z] Δ' hgo_cov).uncurry y⟧ˢ.get
                    (den_t_isSome hy)).snd.fst :=
                  (congrArg (·.snd.fst) (Option.get_of_eq_some (den_t_isSome hy) hden_y)).symm
          · exfalso; apply den_t_isSome
            intro x hx
            let Wx : SMT.Dom := x ⟨0, hlen⟩
            have hWx_ty : Wx.snd.fst = τ.toSMTType := by
              simpa [Wx] using (hx ⟨0, hlen⟩).1
            rw [funAbstractGoSingle (Δctx := Δ') (P := ite_body) (v := z) (τ := τ.toSMTType)
              hgo_cov hcov_ite_upd' x hx]
            exact hbody_total Wx hWx_ty
        -- Step F: build the lambda value
        obtain ⟨lamVal, hlamVal⟩ := Option.isSome_iff_exists.mp hsome_lambda
        -- Step G: lamVal type
        have hlamVal_ty : lamVal.snd.fst = .fun τ.toSMTType .bool := by
          have hlamVal' := hlamVal
          rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
          simp only [SMT.denote] at hlamVal'
          rw [dif_pos (by exact Nat.zero_lt_succ 0)] at hlamVal'
          split_ifs at hlamVal' with h_isSome h_typ_det
          · -- Compute γ_out via default argument
            let xd : Fin 1 → SMT.Dom :=
              fun _ => ⟨τ.toSMTType.defaultZFSet, τ.toSMTType, SMTType.mem_toZFSet_of_defaultZFSet⟩
            have hxd_spec : ∀ i, (xd i).2.1 = [τ.toSMTType][↑i] ∧ (xd i).1 ∈ ⟦[τ.toSMTType][↑i]⟧ᶻ := by
              intro ⟨i, hi⟩; simp at hi; subst hi
              exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
            have hgo_d := funAbstractGoSingle (Δctx := Δ') (P := ite_body) (v := z) (τ := τ.toSMTType)
              hgo_cov hcov_ite_upd' xd hxd_spec
            obtain ⟨Dd, hDd⟩ := Option.isSome_iff_exists.mp
              (hbody_total (xd ⟨0, Nat.one_pos⟩) rfl)
            have hden_d :
                ⟦(SMT.Term.abstract.go ite_body [z] Δ' hgo_cov).uncurry xd⟧ˢ = some Dd := by
              rw [hgo_d]; exact hDd
            have hγ_out :
                (⟦(SMT.Term.abstract.go ite_body [z] Δ' hgo_cov).uncurry xd⟧ˢ.get
                  (h_isSome hxd_spec)).snd.fst = .bool := by
              rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_d)]
              exact hbody_ty (xd ⟨0, Nat.one_pos⟩) rfl Dd hDd
            simp only [Option.pure_def, Option.some.injEq] at hlamVal'
            rw [show lamVal.snd.fst = _ from congrArg (·.snd.fst) hlamVal'.symm]
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
              Fin.foldr_zero, List.getElem_cons_zero]
            exact congrArg (τ.toSMTType.fun ·) hγ_out
        -- Step H: lamVal is a function
        have hlamVal_func : ZFSet.IsFunc ⟦τ.toSMTType⟧ᶻ 𝔹 lamVal.fst := by
          have : lamVal.fst ∈ ⟦τ.toSMTType⟧ᶻ.funs 𝔹 := by
            simpa [hlamVal_ty, SMTType.toZFSet] using lamVal.snd.snd
          exact ZFSet.mem_funs.mp this
        -- Step I: provide the witness
        refine ⟨lamVal, ?_, ?_⟩
        · -- denotation: use proof irrelevance on CoversFV
          convert hlamVal using 2
        · -- RDom + totality
          constructor
          · -- RDom: ⟨T, ...⟩ ≘ᶻ lamVal
            constructor
            · rw [hlamVal_ty, τ_def, BType.toSMTType]
            · -- Goal: retract τ.set lamVal.fst = T
              -- Extract T = sep (...) 𝒟' from rest2, and 𝒟 = 𝒟'
              obtain ⟨hT_eq, _⟩ := rest2
              have h𝒟_eq : 𝒟 = 𝒟' := by
                have := den_D_eq ▸ den_D
                simp only [Option.some.injEq, PSigma.mk.injEq] at this
                exact this.1.symm
              rw [← hT_eq, τ_def]
              -- Show extensional equality via ZFSet.ext
              apply ZFSet.ext; intro x
              rw [retract, ZFSet.mem_sep, ZFSet.mem_sep]
              -- Simplify: use hlamVal_func for the IsFunc dif, τ_hasArity for arity
              -- Establish subset: 𝒟' ⊆ ⟦τ⟧ᶻ
              have h𝒟'_sub : 𝒟' ⊆ ⟦τ⟧ᶻ := by
                rwa [BType.toZFSet, ZFSet.mem_powerset] at h𝒟'
              -- Key bridge: for any W of type τ.toSMTType, the lambda
              -- fapply equals the body evaluation
              have lamVal_body_bridge : ∀ (W : SMT.Dom),
                  W.snd.fst = τ.toSMTType → W.fst ∈ ⟦τ.toSMTType⟧ᶻ →
                  ∃ (body_val : SMT.Dom),
                    ⟦ite_body.abstract (Function.update Δ' z (some W))
                      (hcov_ite_upd' W)⟧ˢ = some body_val ∧
                    body_val.snd.fst = SMTType.bool ∧
                    body_val.fst ∈ 𝔹 := by
                intro W hW_ty hW_mem
                obtain ⟨bv, hbv⟩ := Option.isSome_iff_exists.mp
                  (hbody_total W hW_ty)
                have hbv_ty := hbody_ty W hW_ty bv hbv
                have hbv_mem : bv.fst ∈ 𝔹 := by
                  have := bv.snd.snd; rw [hbv_ty, SMTType.toZFSet] at this; exact this
                exact ⟨bv, hbv, hbv_ty, hbv_mem⟩
              constructor
              · -- Forward: x ∈ retract → x ∈ T
                intro ⟨hx_mem, hx_pred⟩
                rw [dif_pos hx_mem, dif_pos hlamVal_func] at hx_pred
                -- Step 1: Build canonical witness Wx for x
                have hx_canon_mem : (ZFSet.fapply (BType.canonicalIsoSMTType τ).1
                    (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
                    ⟨x, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType τ).2.1]⟩).1 ∈
                    ⟦τ.toSMTType⟧ᶻ :=
                  ZFSet.fapply_mem_range _ _
                let Wx : SMT.Dom := ⟨_, τ.toSMTType, hx_canon_mem⟩
                have hWx_ty : Wx.snd.fst = τ.toSMTType := rfl
                have hWx_mem : Wx.fst ∈ ⟦τ.toSMTType⟧ᶻ := hx_canon_mem
                -- Step 2: Get D_enc app and body evaluation at Wx
                obtain ⟨_, Dapp_x, hDapp_x_ty, hDapp_x_val, hDapp_x_den⟩ :=
                  funDenoteAppAt (Δctx := Δ') (t := D_enc) (x := z)
                    (α := τ.toSMTType) (β := .bool) (Y := denD')
                    hcov_D_upd den_D_upd_eq denD'_type
                    denD'_func Wx hWx_ty hWx_mem
                obtain ⟨body_val, hbody_val, hbody_val_ty, hbody_val_mem⟩ :=
                  lamVal_body_bridge Wx hWx_ty hWx_mem
                have hDapp_x_mem_𝔹 : Dapp_x.fst ∈ 𝔹 := by
                  have := Dapp_x.snd.snd; rw [hDapp_x_ty] at this; exact this
                -- Step 3: body_val.fst = zftrue (from hx_pred and lambda structure)
                have hbody_val_eq_zftrue : body_val.fst = zftrue := by
                  have hlamVal' := hlamVal
                  rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
                  simp only [SMT.denote] at hlamVal'
                  rw [dif_pos (show [z].length > 0 by exact Nat.zero_lt_succ 0)] at hlamVal'
                  split_ifs at hlamVal' with h_isSome h_typ_det
                  · let xd : Fin 1 → SMT.Dom :=
                      fun _ => ⟨τ.toSMTType.defaultZFSet, τ.toSMTType, SMTType.mem_toZFSet_of_defaultZFSet⟩
                    have hxd_spec : ∀ i, (xd i).2.1 = [τ.toSMTType][↑i] ∧ (xd i).1 ∈ ⟦[τ.toSMTType][↑i]⟧ᶻ := by
                      intro ⟨i, hi⟩; simp at hi; subst hi
                      exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
                    have hgo_d := funAbstractGoSingle (Δctx := Δ') (P := ite_body) (v := z) (τ := τ.toSMTType)
                      hgo_cov hcov_ite_upd' xd hxd_spec
                    obtain ⟨Dd, hDd⟩ := Option.isSome_iff_exists.mp
                      (hbody_total (xd ⟨0, Nat.one_pos⟩) rfl)
                    have hden_d : ⟦(SMT.Term.abstract.go ite_body [z] Δ' hgo_cov).uncurry xd⟧ˢ = some Dd := by
                      rw [hgo_d]; exact hDd
                    have hγ_out : (⟦(SMT.Term.abstract.go ite_body [z] Δ' hgo_cov).uncurry xd⟧ˢ.get
                        (h_isSome hxd_spec)).snd.fst = .bool := by
                      rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_d)]
                      exact hbody_ty (xd ⟨0, Nat.one_pos⟩) rfl Dd hDd
                    simp only [Option.pure_def, Option.some.injEq] at hlamVal'
                    have hlamVal_fst_eq : lamVal.fst = _ := congrArg (·.fst) hlamVal'.symm
                    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
                      Fin.foldr_zero, List.getElem_cons_zero] at hlamVal_fst_eq
                    have h_pair_mem : Wx.fst.pair body_val.fst ∈ lamVal.fst := by
                      rw [hlamVal_fst_eq, ZFSet.mem_lambda]
                      refine ⟨Wx.fst, body_val.fst, rfl, hWx_mem, ?_, ?_⟩
                      · have := body_val.snd.snd; rw [hbody_val_ty] at this; convert this using 2
                      · split_ifs with hw'_cond
                        · let xₙ := fun i : Fin 1 => (⟨Wx.fst.get 1 i, [τ.toSMTType][↑i], hw'_cond.2 i⟩ : SMT.Dom)
                          have hgo' := funAbstractGoSingle (Δctx := Δ') (P := ite_body) (v := z) (τ := τ.toSMTType)
                            hgo_cov hcov_ite_upd' xₙ (fun i => ⟨rfl, hw'_cond.2 i⟩)
                          have hxₙ_eq : xₙ ⟨0, Nat.zero_lt_one⟩ = Wx := rfl
                          have hden' : ⟦(SMT.Term.abstract.go ite_body [z] Δ' hgo_cov).uncurry xₙ⟧ˢ = some body_val := by
                            rw [hgo', hxₙ_eq]; exact hbody_val
                          exact (congrArg (·.fst) (Option.get_of_eq_some _ hden')).symm
                        · exfalso; apply hw'_cond
                          exact ⟨trivial, fun ⟨i, hi⟩ => by
                            have : i = 0 := Nat.lt_one_iff.mp hi; subst this; exact hWx_mem⟩
                    have h_fapply := ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hlamVal_func) h_pair_mem
                    rw [Subtype.ext_iff] at h_fapply
                    exact h_fapply.symm.trans hx_pred
                -- Step 4: D_enc condition must be true (false branch gives zffalse)
                have hcond_true :
                    ZFSet.ZFBool.toBool ⟨Dapp_x.fst, hDapp_x_mem_𝔹⟩ = true := by
                  by_contra hcond_false
                  have hcond_eq_false :
                      ZFSet.ZFBool.toBool ⟨Dapp_x.fst, hDapp_x_mem_𝔹⟩ = false :=
                    eq_false_of_ne_true hcond_false
                  have hfalse_body :
                      ⟦ite_body.abstract (Function.update Δ' z (some Wx))
                        (hcov_ite_upd' Wx)⟧ˢ =
                      some ⟨ZFSet.zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                    change ⟦(((@ˢD_enc) (SMT.Term.var z)).ite
                      (SMT.substList vs (toDestPair vs (.var z)) P_enc)
                      (.bool false)).abstract
                      (Function.update Δ' z (some Wx))
                      (ite_body_def ▸ hcov_ite_upd' Wx)⟧ˢ = _
                    simp only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind]
                    conv_lhs => rw [SMT.RenamingContext.denote_abstract_proof_irrel
                      D_enc (Function.update Δ' z (some Wx)) _ (hcov_D_upd Wx)]
                    rw [den_D_upd_eq Wx]
                    simp only [Option.bind_some, Function.update_self,
                      Option.get_some, Option.pure_def, hWx_ty]
                    have hDapp_x_den' := hDapp_x_den
                    simp only [SMT.Term.abstract, SMT.denote,
                      Option.bind_eq_bind] at hDapp_x_den'
                    conv at hDapp_x_den' =>
                      lhs; rw [SMT.RenamingContext.denote_abstract_proof_irrel
                        D_enc _ _ (hcov_D_upd Wx)]
                    rw [den_D_upd_eq Wx] at hDapp_x_den'
                    simp only [Function.update_self, Option.get_some,
                      Option.pure_def, Option.bind_some, hWx_ty] at hDapp_x_den'
                    rw [hDapp_x_den']
                    simp only [Option.bind_some]
                    have : Dapp_x =
                        ⟨Dapp_x.fst, ⟨.bool, hDapp_x_ty ▸ Dapp_x.snd.snd⟩⟩ := by
                      obtain ⟨_, ⟨_, _⟩⟩ := Dapp_x; cases hDapp_x_ty; rfl
                    rw [this]; dsimp
                    rw [show ZFSet.ZFBool.toBool ⟨Dapp_x.fst, _⟩ = false
                      from hcond_eq_false]
                    simp [ZFSet.ZFBool.ofBool]
                  rw [hfalse_body] at hbody_val
                  have hfst_eq : body_val.fst = ZFSet.zffalse :=
                    congrArg (·.fst) (Option.some.inj hbody_val).symm
                  exact absurd (hfst_eq ▸ hbody_val_eq_zftrue)
                    (Ne.symm ZFSet.zftrue_ne_zffalse)
                -- Step 5: Show x ∈ 𝒟'
                -- Extract Dapp_x.fst = zftrue from hcond_true
                have hDapp_fst_true : Dapp_x.fst = zftrue := by
                  rcases ZFSet.ZFBool.mem_𝔹_iff _ |>.mp hDapp_x_mem_𝔹 with h | h
                  · exfalso
                    have : ZFSet.ZFBool.toBool ⟨Dapp_x.fst, hDapp_x_mem_𝔹⟩ = false := by
                      rw [show (⟨Dapp_x.fst, hDapp_x_mem_𝔹⟩ : ZFSet.ZFBool) =
                        ⟨ZFSet.zffalse, ZFSet.ZFBool.zffalse_mem_𝔹⟩ from Subtype.ext h]
                      exact ZFSet.ZFBool.toBool_false
                    rw [this] at hcond_true; nomatch hcond_true
                  · exact h
                have hx_in_𝒟 : x ∈ 𝒟 := by
                  rw [← denD'_retract, retract, ZFSet.mem_sep]
                  constructor
                  · exact hx_mem
                  · rw [dif_pos hx_mem, dif_pos denD'_func]
                    convert hDapp_fst_true using 1
                    exact hDapp_x_val.symm
                have hx_in_𝒟' : x ∈ 𝒟' := h𝒟_eq ▸ hx_in_𝒟
                -- Step 6: Show B-level P evaluation = zftrue
                constructor
                · exact hx_in_𝒟'
                · rw [dif_pos ⟨hasArity_of_mem_toZFSet τ_hasArity hx_mem,
                    τ_hasArity, hx_mem⟩]
                  let x_fin : Fin vs.length → B.Dom := fun i =>
                    ⟨x.get vs.length ↑i, ⟨τ.get vs.length ↑i,
                     get_mem_type_of_isTuple
                       (hasArity_of_mem_toZFSet τ_hasArity hx_mem)
                       τ_hasArity hx_mem⟩⟩
                  have h_ofFinDom_eq : ZFSet.ofFinDom x_fin = x :=
                    ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
                      (fun i => get_mem_type_of_isTuple
                        (hasArity_of_mem_toZFSet τ_hasArity hx_mem)
                        τ_hasArity hx_mem)
                      (hasArity_of_mem_toZFSet τ_hasArity hx_mem) τ_hasArity
                  have hx_fin_in_𝒟' : ZFSet.ofFinDom x_fin ∈ 𝒟' :=
                    h_ofFinDom_eq ▸ hx_in_𝒟'
                  have hx_fin_typ : ∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
                      (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
                    fun i => ⟨rfl, (x_fin i).snd.snd⟩
                  have hP_isSome := h_den_P hx_fin_typ hx_fin_in_𝒟'
                  subst 𝒟'
                  obtain ⟨⟨P_val, P_ty, hP_val⟩, hP_den⟩ := Option.isSome_iff_exists.mp hP_isSome
                  -- P_val = zftrue and the dif/match reduces to it
                  -- The full connection requires:
                  -- 1. Evaluate ite_body when cond=true to get substList result
                  -- 2. Connect substList to P_enc via abstract_substList_denote
                  -- 3. Use P_enc_total to get RDom(P_val, denT_W')
                  -- 4. retract .bool = id, so denT_W'.fst = P_val
                  -- 5. body_val.fst = denT_W'.fst, so P_val = zftrue
                  split
                  · rename_i Px τPx hPx den_P_eq_Px
                    unfold x_fin at hP_den
                    conv at den_P_eq_Px => erw [hP_den, Option.some_inj]
                    injection den_P_eq_Px with den_P_eq_Px
                    subst P_val
                    clear P_ih

                    -- Step A: Establish retract τ Wx.fst = x
                    have hretract_Wx : retract τ Wx.fst = x :=
                      retract_of_canonical τ hx_mem

                    -- Step B: Build x_fin-derived B context
                    set Δ_ext_x := Function.updates «Δ» vs
                      (List.ofFn fun i => some (x_fin i))
                    have Δ_fv_P_x : ∀ v ∈ B.fv P, (Δ_ext_x v).isSome = true := by
                      intro v hv
                      show (Function.updates «Δ» vs _ v).isSome = true
                      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
                      split_ifs with hvs
                      · simp [List.getElem_ofFn]
                      · exact Δ_fv v (B.fv.mem_collect (.inr ⟨hv, hvs⟩))
                    set Δ_D_ext_x := Function.updates Δ_D vs
                      (List.ofFn fun (i : Fin vs.length) => B.RenamingContext.toSMT Δ_ext_x vs[i])

                    -- Step C: Get B-level P denotation at x_fin
                    -- Use h_den_P to reconstruct the abstract denotation
                    -- h_den_P says P at x_fin gives isSome when ofFinDom x_fin ∈ 𝒟'
                    -- hP_den is the explicit denotation equation (with x_fin unfolded)
                    -- We need to type-determine P_ty = .bool
                    have hP_go_den : ⟦(B.Term.abstract.go P vs «Δ» (by
                          intro v hv hvs; exact Δ_fv v (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ
                        = some ⟨Px, ⟨P_ty, hP_val⟩⟩ := by
                      convert hP_den using 2
                    have hτPx_bool : P_ty = BType.bool := by
                      rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin Δ_fv_P_x] at hP_go_den
                      exact (denote_welltyped_eq
                        (t := P.abstract Δ_ext_x Δ_fv_P_x)
                        ⟨_, WFTC.of_abstract, .bool, by convert Typing.of_abstract Δ_fv_P_x typP⟩
                        hP_go_den).symm
                    subst hτPx_bool
                    have h_den_P_x : ⟦P.abstract Δ_ext_x Δ_fv_P_x⟧ᴮ = some ⟨Px, ⟨BType.bool, hP_val⟩⟩ := by
                      rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin Δ_fv_P_x]
                      exact hP_go_den

                    -- Step D: ExtendsOnSourceFV for Δ_D_ext_x
                    have Δ₀_ext_P_x : RenamingContext.ExtendsOnSourceFV Δ_D_ext_x Δ_ext_x P := by
                      intro v d hv_eq
                      by_cases hv_fv : v ∈ B.fv P
                      · have hv_smt : B.RenamingContext.toSMT Δ_ext_x v = some d := by
                          have : B.RenamingContext.toSMTOnFV Δ_ext_x P v = B.RenamingContext.toSMT Δ_ext_x v := by
                            simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                              B.RenamingContext.restrictToFV_eq_of_mem hv_fv]
                          rwa [← this]
                        by_cases hvs : v ∈ vs
                        · show Function.updates Δ_D vs _ v = some d
                          rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
                          simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                          exact hv_smt
                        · have hDD_ext_x : Δ_D_ext_x v = Δ_D v := by
                            show Function.updates Δ_D vs _ v = Δ_D v
                            exact Function.updates_of_not_mem Δ_D vs _ v hvs
                          rw [hDD_ext_x]
                          have hΔ_ext_x_eq : Δ_ext_x v = «Δ» v := by
                            show Function.updates «Δ» vs _ v = «Δ» v
                            exact Function.updates_of_not_mem «Δ» vs _ v hvs
                          have hv_collect : v ∈ B.fv (Term.collect vs D P) :=
                            fv.mem_collect (.inr ⟨hv_fv, hvs⟩)
                          have hv_smt_Δ : B.RenamingContext.toSMTOnFV «Δ» (Term.collect vs D P) v = some d := by
                            simp only [RenamingContext.toSMTOnFV, RenamingContext.toSMT,
                              B.RenamingContext.restrictToFV_eq_of_mem hv_collect, Option.pure_def,
                              Option.bind_eq_bind]
                            simpa only [RenamingContext.toSMT, hΔ_ext_x_eq, Option.pure_def,
                              Option.bind_eq_bind] using hv_smt
                          exact Δ_D_extends (Δ₀_ext hv_smt_Δ)
                      · have : B.RenamingContext.toSMTOnFV Δ_ext_x P v = none := by
                          simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                            B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_fv]
                        rw [this] at hv_eq; exact absurd hv_eq (not_eq_of_beq_eq_false rfl)

                    -- Step E: none_out for Δ_D_ext_x
                    have Δ_D_ext_x_none : ∀ v ∉ St₂.env.usedVars, Δ_D_ext_x v = none := by
                      intro v hv
                      show Function.updates Δ_D vs _ v = none
                      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
                      split_ifs with hvs
                      · exfalso; exact hv (St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs _ hvs)))
                      · exact Δ_D_none_St₂ v hv
                    -- Step F: Invoke P_enc_total with hybrid base
                    set Δ₀_hybrid_x : SMT.RenamingContext.Context := fun v =>
                      if v ∈ vs then Δ_D_ext_x v
                      else if v ∈ St₃.env.usedVars then Δ_P v
                      else none
                    have Δ₀_hybrid_ext_P_x : RenamingContext.ExtendsOnSourceFV Δ₀_hybrid_x Δ_ext_x P := by
                      intro v d hv_eq
                      by_cases hv_fv : v ∈ B.fv P
                      · have hv_smt : B.RenamingContext.toSMT Δ_ext_x v = some d := by
                          have : B.RenamingContext.toSMTOnFV Δ_ext_x P v = B.RenamingContext.toSMT Δ_ext_x v := by
                            simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                              B.RenamingContext.restrictToFV_eq_of_mem hv_fv]
                          rwa [← this]
                        by_cases hvs : v ∈ vs
                        · show (if v ∈ vs then Δ_D_ext_x v else _) = some d
                          rw [if_pos hvs]
                          show Function.updates Δ_D vs _ v = some d
                          rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
                          simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                          exact hv_smt
                        · have hv_collect : v ∈ B.fv (Term.collect vs D P) :=
                            fv.mem_collect (.inr ⟨hv_fv, hvs⟩)
                          have hv_used : v ∈ St₃.env.usedVars := by
                            have := Δ_fv v hv_collect
                            obtain ⟨bdom, hbdom⟩ := Option.isSome_iff_exists.mp this
                            have h_toSMT : ∃ d', B.RenamingContext.toSMT «Δ» v = some d' := by
                              obtain ⟨V, τ_v, hV⟩ := bdom
                              simp only [B.RenamingContext.toSMT, hbdom, Option.pure_def]; exact ⟨_, rfl⟩
                            obtain ⟨d', hd'⟩ := h_toSMT
                            have h_onFV : B.RenamingContext.toSMTOnFV «Δ» (Term.collect vs D P) v = some d' := by
                              simp only [RenamingContext.toSMTOnFV, RenamingContext.toSMT,
                                B.RenamingContext.restrictToFV_eq_of_mem hv_collect, Option.pure_def,
                                Option.bind_eq_bind, hbdom, Option.bind_some]
                              rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind, hbdom,
                                Option.bind_some] at hd'
                              exact hd'
                            have hΔ_D_v : Δ_D v = some d' := Δ_D_extends (Δ₀_ext h_onFV)
                            by_contra hv_not_used
                            exact absurd (Δ_D_none_St₂ v (fun h => hv_not_used (St₂_sub_St₃ h)))
                              (by rw [hΔ_D_v]; simp)
                          show (if v ∈ vs then _ else if v ∈ St₃.env.usedVars then Δ_P v else none) = some d
                          rw [if_neg hvs, if_pos hv_used]
                          have hΔ_ext_eq : Δ_ext v = «Δ» v := by
                            rw [Δ_ext_def]; exact Function.updates_of_not_mem «Δ» vs _ v hvs
                          have hΔ_ext_x_eq : Δ_ext_x v = «Δ» v := by
                            show Function.updates «Δ» vs _ v = «Δ» v
                            exact Function.updates_of_not_mem «Δ» vs _ v hvs
                          have h_toSMT_eq : B.RenamingContext.toSMT Δ_ext v = some d := by
                            rw [B.RenamingContext.toSMT, hΔ_ext_eq, ← B.RenamingContext.toSMT]
                            rw [B.RenamingContext.toSMT, hΔ_ext_x_eq, ← B.RenamingContext.toSMT] at hv_smt
                            exact hv_smt
                          have h_src : B.RenamingContext.toSMTOnFV Δ_ext P v = some d := by
                            simp only [RenamingContext.toSMTOnFV, RenamingContext.toSMT,
                              B.RenamingContext.restrictToFV_eq_of_mem hv_fv]
                            rw [B.RenamingContext.toSMT] at h_toSMT_eq; exact h_toSMT_eq
                          exact Δ_P_src_ext h_src
                      · have : B.RenamingContext.toSMTOnFV Δ_ext_x P v = none := by
                          simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                            B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_fv]
                        rw [this] at hv_eq; exact absurd hv_eq (not_eq_of_beq_eq_false rfl)
                    have Δ₀_hybrid_x_none_St₃ : ∀ v ∉ St₃.env.usedVars, Δ₀_hybrid_x v = none := by
                      intro v hv
                      show (if v ∈ vs then Δ_D_ext_x v else if v ∈ St₃.env.usedVars then Δ_P v else none) = none
                      have hv_not_vs : v ∉ vs := fun hvs => hv (St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs v hvs))))
                      rw [if_neg hv_not_vs, if_neg hv]
                    have Δ₀_hybrid_x_dom : ∀ v, Δ₀_hybrid_x v ≠ none → v ∈ St₃.types := by
                      intro v hv
                      change (if v ∈ vs then Δ_D_ext_x v else if v ∈ St₃.env.usedVars then Δ_P v else none) ≠ none at hv
                      split_ifs at hv with hvs hused
                      · apply AList.mem_of_subset St₂_sub_St₃_types
                        rw [St₂_types]
                        exact foldl_insert_zip_mem vs (τ.toSMTType.fromProdl (vs.length - 1)) St₁.types v
                          (by rw [fromProdl_length_of_hasArity τ_hasArity]) hvs
                      · exact Δ_P_dom v hv
                      · exact absurd rfl hv
                    obtain ⟨Δ_P_x, hcov_Px, denT_x', Δ_P_x_extends, _, _, hden_Px, hRDom_x, _⟩ :=
                      P_enc_total Δ_ext_x Δ_fv_P_x Δ₀_hybrid_x Δ₀_hybrid_ext_P_x
                        Δ₀_hybrid_x_none_St₃ (by
                          intro v d hv τ_v hτ_v
                          change (if v ∈ vs then Δ_D_ext_x v else if v ∈ St₃.env.usedVars then Δ_P v else none) = some d at hv
                          split_ifs at hv with hvs hused
                          · have hv_idx : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hvs
                            have hΔ_ext_x_vi : Δ_ext_x v = some (x_fin ⟨vs.idxOf v, hv_idx⟩) := by
                              show Function.updates «Δ» vs _ v = _
                              rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
                              simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                            have hΔ_D_ext_eq : Δ_D_ext_x v = B.RenamingContext.toSMT Δ_ext_x v := by
                              show Function.updates Δ_D vs _ v = _
                              rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
                              simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                            rw [hΔ_D_ext_eq] at hv
                            rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind,
                              hΔ_ext_x_vi, Option.bind_some] at hv
                            have hd_inj := Option.some_injective _ hv
                            have hd_ty : d.snd.fst = (τ.get vs.length ⟨vs.idxOf v, hv_idx⟩).toSMTType :=
                              (congr_arg (·.snd.fst) hd_inj).symm
                            set τs := τ.toSMTType.fromProdl (vs.length - 1) with τs_def
                            have hτs_len := fromProdl_length_of_hasArity τ_hasArity
                            have hv_idx_τ : vs.idxOf v < τs.length := hτs_len ▸ hv_idx
                            have h_St₂ : St₂.types.lookup v = some τs[vs.idxOf v] := by
                              have h := foldl_insert_lookup_zip (Γ := St₁.types) vs_nodup hv_idx hv_idx_τ
                              rwa [← St₂_types, List.getElem_idxOf hv_idx] at h
                            have h_St₃ : St₃.types.lookup v = some τs[vs.idxOf v] :=
                              AList.lookup_of_subset St₂_sub_St₃_types h_St₂
                            rw [h_St₃] at hτ_v; cases hτ_v
                            rw [hd_ty]
                            exact toSMTType_get_eq_fromProdl_getElem τ_hasArity hv_idx
                          · exact Δ_P_wt v d hv τ_v hτ_v) Px hP_val h_den_P_x

                    -- Step G: Extract Px = denT_x'.fst from RDom
                    have hdenT_x'_ty : denT_x'.snd.fst = SMTType.bool := hRDom_x.1
                    have hdenT_x'_fst_eq : denT_x'.fst = Px := hRDom_x.2

                    -- Step H: Show body_val.fst = denT_x'.fst
                    -- First: body_val is the ite_body true-branch = substList evaluation
                    -- (ite_body with cond=true gives substList result)
                    have hbody_is_substList :
                        ⟦(SMT.substList vs (toDestPair vs (.var z)) P_enc).abstract
                          (Function.update Δ' z (some Wx)) (hcov_substList_upd Wx)⟧ˢ =
                        some body_val := by
                      -- Unfold ite_body, show that when cond=true it reduces to substList
                      have hbody_val' := hbody_val
                      change ⟦(((@ˢD_enc) (SMT.Term.var z)).ite
                        (SMT.substList vs (toDestPair vs (.var z)) P_enc) (.bool false)).abstract
                        (Function.update Δ' z (some Wx)) (ite_body_def ▸ hcov_ite_upd' Wx)⟧ˢ = _ at hbody_val'
                      simp only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind] at hbody_val'
                      conv at hbody_val' =>
                        lhs; rw [SMT.RenamingContext.denote_abstract_proof_irrel D_enc
                          (Function.update Δ' z (some Wx)) _ (hcov_D_upd Wx)]
                      rw [den_D_upd_eq Wx] at hbody_val'
                      simp only [Option.bind_some, Function.update_self,
                        Option.get_some, Option.pure_def, hWx_ty] at hbody_val'
                      -- Extract Dapp_x from the app chain
                      have hDapp_x_den' := hDapp_x_den
                      simp only [SMT.Term.abstract, SMT.denote,
                        Option.bind_eq_bind] at hDapp_x_den'
                      conv at hDapp_x_den' =>
                        lhs; rw [SMT.RenamingContext.denote_abstract_proof_irrel
                          D_enc _ _ (hcov_D_upd Wx)]
                      rw [den_D_upd_eq Wx] at hDapp_x_den'
                      simp only [Function.update_self, Option.get_some,
                        Option.pure_def, Option.bind_some, hWx_ty] at hDapp_x_den'
                      rw [hDapp_x_den'] at hbody_val'
                      simp only [Option.bind_some] at hbody_val'
                      -- Rewrite Dapp_x to ⟨Dapp_x.fst, ⟨.bool, ...⟩⟩
                      have hDapp_x_struct : Dapp_x =
                          ⟨Dapp_x.fst, ⟨.bool, hDapp_x_ty ▸ Dapp_x.snd.snd⟩⟩ := by
                        obtain ⟨_, ⟨_, _⟩⟩ := Dapp_x; cases hDapp_x_ty; rfl
                      rw [hDapp_x_struct] at hbody_val'; dsimp at hbody_val'
                      rw [show ZFSet.ZFBool.toBool ⟨Dapp_x.fst, _⟩ = true from by convert hcond_true] at hbody_val'
                      simp only [ite_true] at hbody_val'
                      -- Now hbody_val' : substList.abstract ... = some body_val
                      conv at hbody_val' =>
                        lhs; rw [SMT.RenamingContext.denote_abstract_proof_irrel
                          (SMT.substList vs (toDestPair vs (.var z)) P_enc)
                          (Function.update Δ' z (some Wx)) _ (hcov_substList_upd Wx)]
                      exact hbody_val'

                    -- Step I: Transfer substList from Δ'[z↦Wx] to Δ_P[z↦Wx]
                    have hΔ_agree_substList : SMT.RenamingContext.AgreesOnFV
                        (Function.update Δ' z (some Wx))
                        (Function.update Δ_P z (some Wx))
                        (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
                      intro v hv
                      by_cases hvz : v = z
                      · subst hvz; simp [Function.update_self]
                      · rw [Function.update_of_ne hvz, Function.update_of_ne hvz]
                        have hv_not_vs := fv_substList_disj_vs v hv hvz
                        exact Δ'_agrees_P v (by
                          rcases SMT_mem_fv_substList hv with h | ⟨t, ht, hv_t⟩
                          · exact h
                          · exact absurd (SMT_fv_toDestPair_subset ht hv_t ▸ rfl) hvz) hv_not_vs

                    have hcov_substList_upd_ΔP' : SMT.RenamingContext.CoversFV
                        (Function.update Δ_P z (some Wx))
                        (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
                      intro v hv
                      by_cases hvz : v = z
                      · subst hvz; simp [Function.update_self]
                      · rw [Function.update_of_ne hvz]
                        have hv_not_vs := fv_substList_disj_vs v hv hvz
                        rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
                        · exact Δ_P_covers v hv_P
                        · exact absurd (SMT_fv_toDestPair_subset ht hv_t ▸ rfl) hvz

                    have hsubst_at_ΔP : ⟦(SMT.substList vs (toDestPair vs (.var z)) P_enc).abstract
                        (Function.update Δ_P z (some Wx)) hcov_substList_upd_ΔP'⟧ˢ =
                        some body_val := by
                      have h_transfer := SMT.RenamingContext.denote_congr_of_agreesOnFV
                        (h1 := hcov_substList_upd Wx) (h2 := hcov_substList_upd_ΔP') hΔ_agree_substList
                      unfold SMT.RenamingContext.denote at h_transfer
                      rw [← h_transfer]; exact hbody_is_substList

                    -- Step J: Transfer substList from Δ_P[z↦Wx] to Δ_P_x[z↦Wx] via hybrid base
                    have hΔ_Px_agree : SMT.RenamingContext.AgreesOnFV
                        (Function.update Δ_P_x z (some Wx))
                        (Function.update Δ_P z (some Wx))
                        (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
                      intro v hv
                      by_cases hvz : v = z
                      · subst hvz; simp [Function.update_self]
                      · rw [Function.update_of_ne hvz, Function.update_of_ne hvz]
                        have hv_not_vs := fv_substList_disj_vs v hv hvz
                        rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
                        · -- v ∈ fv(P_enc), v ∉ vs, v ∈ St₃.usedVars
                          have hv_used : v ∈ St₃.env.usedVars :=
                            St₃_keys_sub (AList.mem_keys.mpr (SMT.Typing.mem_context_of_mem_fv typ_P_enc hv_P))
                          -- Δ₀_hybrid_x v = Δ_P v (since v ∉ vs, v ∈ St₃.usedVars)
                          have hΔ₀_v : Δ₀_hybrid_x v = Δ_P v := by
                            show (if v ∈ vs then _ else if v ∈ St₃.env.usedVars then Δ_P v else none) = Δ_P v
                            rw [if_neg hv_not_vs, if_pos hv_used]
                          -- Δ_P v = some d (from coverage)
                          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Δ_P_covers v hv_P)
                          -- Δ_P_x v = some d (from Extends Δ_P_x Δ₀_hybrid_x)
                          have hΔ_Px_v : Δ_P_x v = some d := Δ_P_x_extends (hΔ₀_v ▸ hd)
                          rw [hΔ_Px_v, hd]
                        · exact absurd (SMT_fv_toDestPair_subset ht hv_t ▸ rfl) hvz

                    have hcov_substList_Px : SMT.RenamingContext.CoversFV
                        (Function.update Δ_P_x z (some Wx))
                        (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
                      intro v hv
                      by_cases hvz : v = z
                      · subst hvz; simp [Function.update_self]
                      · rw [Function.update_of_ne hvz]
                        have hagr := hΔ_Px_agree hv
                        rw [Function.update_of_ne hvz, Function.update_of_ne hvz] at hagr
                        rw [hagr]
                        have := hcov_substList_upd_ΔP' v hv
                        rwa [Function.update_of_ne hvz] at this

                    have hsubst_at_ΔPx : ⟦(SMT.substList vs (toDestPair vs (.var z)) P_enc).abstract
                        (Function.update Δ_P_x z (some Wx)) hcov_substList_Px⟧ˢ =
                        some body_val := by
                      have h_transfer2 := SMT.RenamingContext.denote_congr_of_agreesOnFV
                        (h1 := hcov_substList_Px) (h2 := hcov_substList_upd_ΔP') hΔ_Px_agree
                      unfold SMT.RenamingContext.denote at h_transfer2
                      rw [h_transfer2]; exact hsubst_at_ΔP

                    -- Step K: Apply abstract_substList_denote to show substList = P_enc at updates
                    -- Δ_P_x(vs[i]) is defined
                    have hΔ_Px_vs_isSome : ∀ (i : Fin vs.length), (Δ_P_x vs[i]).isSome = true := by
                      intro ⟨i, hi⟩
                      have hvi_mem : vs[i] ∈ vs := List.getElem_mem hi
                      have hΔ_ext_x_vi : (Δ_ext_x vs[i]).isSome = true := by
                        show (Function.updates «Δ» vs _ vs[i]).isSome = true
                        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                          dif_pos hvi_mem]
                        simp only [List.getElem_ofFn, Option.isSome]
                      obtain ⟨bval, hbval⟩ := Option.isSome_iff_exists.mp hΔ_ext_x_vi
                      have htoSMT_some : ∃ d, B.RenamingContext.toSMT Δ_ext_x vs[i] = some d := by
                        obtain ⟨V, τ_v, hV⟩ := bval
                        simp only [B.RenamingContext.toSMT, hbval, Option.bind_some, Option.pure_def]
                        exact ⟨_, rfl⟩
                      obtain ⟨d, hd⟩ := htoSMT_some
                      have hΔ_D_ext_x_vi : Δ_D_ext_x vs[i] = some d := by
                        show Function.updates Δ_D vs _ vs[i] = some d
                        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                          dif_pos hvi_mem]
                        simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                        exact hd
                      have hΔ₀_hybrid_x_vi : Δ₀_hybrid_x vs[i] = some d := by
                        show (if vs[i] ∈ vs then Δ_D_ext_x vs[i] else _) = some d
                        rw [if_pos hvi_mem]; exact hΔ_D_ext_x_vi
                      exact Option.isSome_iff_exists.mpr ⟨d, Δ_P_x_extends hΔ₀_hybrid_x_vi⟩

                    let Ds_x : List SMT.Dom := List.ofFn fun i : Fin vs.length =>
                      (Δ_P_x vs[i]).get (hΔ_Px_vs_isSome i)

                    -- Reuse: vs not in bv P_enc, z not in bv P_enc, z not in vs
                    have hvs_not_bv' : ∀ x ∈ vs, x ∉ SMT.bv P_enc := by
                      intro v hv hbv
                      set τs := τ.toSMTType.fromProdl (vs.length - 1)
                      have hτs_len := fromProdl_length_of_hasArity τ_hasArity
                      have hv_idx : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hv
                      have hv_idx_τ : vs.idxOf v < τs.length := hτs_len ▸ hv_idx
                      have h_St₂_lookup : ∃ σ, St₂.types.lookup v = some σ := by
                        have h := foldl_insert_lookup_zip (Γ := St₁.types) vs_nodup hv_idx hv_idx_τ
                        rw [← St₂_types, List.getElem_idxOf hv_idx] at h
                        exact ⟨_, h⟩
                      have hv_St₃ : v ∈ St₃.types := by
                        obtain ⟨σ, hσ⟩ := h_St₂_lookup
                        have h_entry := AList.mem_lookup_iff.mp hσ
                        have h_St₃_entry := St₂_sub_St₃_types h_entry
                        have h_St₃_lookup := AList.mem_lookup_iff.mpr h_St₃_entry
                        exact AList.lookup_isSome.mp (Option.isSome_of_eq_some h_St₃_lookup)
                      exact SMT.Typing.bv_notMem_context typ_P_enc v hbv hv_St₃
                    have z_not_bv_P' : z ∉ SMT.bv P_enc := by
                      intro hbv
                      have typ_P_enc_ins := SMT.Typing.weakening
                        (SMT.TypeContext.entries_subset_insert_of_notMem (τ := τ.toSMTType) z_fresh) typ_P_enc
                      exact SMT.Typing.bv_notMem_context typ_P_enc_ins _ hbv
                        ((AList.mem_insert _).mpr (Or.inl rfl))
                    have z_not_vs' : z ∉ vs := by
                      intro hz; exact z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used
                        (used_sub_St₁ (vars_used_vs z hz))))

                    -- CoversFV for updates context
                    have h_cov_upd_x : SMT.RenamingContext.CoversFV
                        (Function.updates (Function.update Δ_P_x z (some Wx)) vs
                          (Ds_x.map Option.some)) P_enc := by
                      intro v hv
                      by_cases hvs : v ∈ vs
                      · rw [Function.updates_eq_if (by rw [List.length_map, List.length_ofFn]) vs_nodup,
                          dif_pos hvs]
                        simp
                      · rw [Function.updates_of_not_mem _ vs _ _ hvs,
                          Function.update_of_ne (by intro heq; exact z_not_fv_P (heq ▸ hv))]
                        exact hcov_Px v hv

                    -- Apply abstract_substList_denote
                    have hlen_xt' : vs.length = (toDestPair vs (.var z)).length := by
                      rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]; simp
                    have hlen_xd' : vs.length = Ds_x.length := by simp [Ds_x, List.length_ofFn]
                    have h_eq_x := SMT.RenamingContext.abstract_substList_denote P_enc vs (toDestPair vs (.var z))
                      Ds_x hlen_xt' hlen_xd' vs_nodup hvs_not_bv' toDestPair_bv_nil
                      (fun t ht w hw hbv => by rw [SMT_fv_toDestPair_subset ht hw] at hbv; exact z_not_bv_P' hbv)
                      toDestPair_ne_none
                      (fun t ht w hw => by rw [SMT_fv_toDestPair_subset ht hw]; exact z_not_vs')
                      (by -- toDestPair[i] denotes to Ds_x[i] under Δ_P_x[z↦Wx]
                        intro i hi_x hi_t hi_d
                        have hcov_ti : SMT.RenamingContext.CoversFV
                            (Function.update Δ_P_x z (some Wx)) (toDestPair vs (.var z))[i] := by
                          intro v hv
                          have hvz := SMT_fv_toDestPair_subset (List.getElem_mem hi_t) hv
                          subst hvz; simp [Function.update_self]
                        refine ⟨hcov_ti, ?_⟩
                        have hcov_z_Px : SMT.RenamingContext.CoversFV
                            (Function.update Δ_P_x z (some Wx)) (.var z) := by
                          intro v hv; simp [SMT.fv] at hv; subst hv; simp [Function.update_self]
                        have hden_z_Px : ⟦(SMT.Term.var z).abstract
                            (Function.update Δ_P_x z (some Wx)) hcov_z_Px⟧ˢ = some Wx := by
                          simp [SMT.Term.abstract, SMT.denote, Function.update_self]
                        have hWx_hasArity := hasArity_of_mem_toSMTZFSet τ_hasArity hWx_mem
                        obtain ⟨hcov_j, D_j, hden_j, hfst_j, hty_j⟩ :=
                          toDestPair_denote_gen τ vs (.var z) Wx
                            (Function.update Δ_P_x z (some Wx)) [] [] vs_nemp
                            hcov_z_Px hden_z_Px hWx_ty hWx_mem τ_hasArity rfl (by simp) i hi_x hi_t
                        rw [SMT.RenamingContext.denote_abstract_proof_irrel _ _ hcov_ti hcov_j, hden_j]
                        have hvi_mem : vs[i] ∈ vs := List.getElem_mem hi_x
                        -- Δ_ext_x vs[i] = some (x_fin ⟨i, hi_x⟩)
                        have hΔ_ext_x_vi : Δ_ext_x vs[i] = some (x_fin ⟨i, hi_x⟩) := by
                          show Function.updates «Δ» vs _ vs[i] = _
                          rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                            dif_pos hvi_mem]
                          simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                          simp [List.idxOf_getElem vs_nodup]
                        obtain ⟨d_smt, hd_smt⟩ : ∃ d, B.RenamingContext.toSMT Δ_ext_x vs[i] = some d := by
                          simp only [B.RenamingContext.toSMT, hΔ_ext_x_vi, Option.pure_def]
                          exact ⟨_, rfl⟩
                        have htoSMT_unf : B.RenamingContext.toSMT Δ_ext_x vs[i] = some d_smt := hd_smt
                        rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind,
                          hΔ_ext_x_vi, Option.bind_some] at htoSMT_unf
                        have hd_inj := Option.some_injective _ htoSMT_unf
                        have hd_ty : d_smt.snd.fst = (τ.get vs.length ⟨i, hi_x⟩).toSMTType :=
                          (congr_arg (·.snd.fst) hd_inj).symm
                        have hd_retract : retract (τ.get vs.length ⟨i, hi_x⟩) d_smt.fst =
                            (retract τ Wx.fst).get vs.length ⟨i, hi_x⟩ := by
                          have hfst_inj := congr_arg (·.fst) hd_inj
                          dsimp at hfst_inj
                          rw [← hfst_inj]
                          rw [hretract_Wx]
                          exact retract_of_canonical (τ.get vs.length ⟨i, hi_x⟩)
                            (get_mem_type_of_isTuple
                              (hasArity_of_mem_toZFSet τ_hasArity hx_mem) τ_hasArity hx_mem)
                        have hΔ_D_ext_x_vi : Δ_D_ext_x vs[i] = some d_smt := by
                          show Function.updates Δ_D vs _ vs[i] = some d_smt
                          rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                            dif_pos hvi_mem]
                          simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                          exact hd_smt
                        have hΔ₀_hybrid_x_vi' : Δ₀_hybrid_x vs[i] = some d_smt := by
                          show (if vs[i] ∈ vs then Δ_D_ext_x vs[i] else _) = some d_smt
                          rw [if_pos hvi_mem]; exact hΔ_D_ext_x_vi
                        have hΔ_Px_vi : Δ_P_x vs[i] = some d_smt :=
                          Δ_P_x_extends hΔ₀_hybrid_x_vi'
                        have hWi_mem : Wx.fst.get vs.length ⟨i, hi_x⟩ ∈
                            ⟦(τ.get vs.length ⟨i, hi_x⟩).toSMTType⟧ᶻ :=
                          get_mem_toSMTZFSet (hasArity_of_mem_toSMTZFSet τ_hasArity hWx_mem)
                            τ_hasArity hWx_mem
                        have hd_fst : d_smt.fst = Wx.fst.get vs.length ⟨i, hi_x⟩ := by
                          have hd_mem : d_smt.fst ∈ ⟦(τ.get vs.length ⟨i, hi_x⟩).toSMTType⟧ᶻ :=
                            hd_ty ▸ d_smt.snd.snd
                          have h_retract_eq : retract (τ.get vs.length ⟨i, hi_x⟩) d_smt.fst =
                              retract (τ.get vs.length ⟨i, hi_x⟩) (Wx.fst.get vs.length ⟨i, hi_x⟩) := by
                            rw [hd_retract, retract_get_comm
                              (hasArity_of_mem_toSMTZFSet τ_hasArity hWx_mem) τ_hasArity hWx_mem]
                          calc d_smt.fst
                              = fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi_x⟩)).1
                                  (is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                                  ⟨retract (τ.get vs.length ⟨i, hi_x⟩) d_smt.fst, _⟩ :=
                                (canonical_of_retract _ hd_mem).symm
                            _ = fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi_x⟩)).1
                                  (is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                                  ⟨retract (τ.get vs.length ⟨i, hi_x⟩) (Wx.fst.get vs.length ⟨i, hi_x⟩), _⟩ := by
                                simp [h_retract_eq]
                            _ = Wx.fst.get vs.length ⟨i, hi_x⟩ :=
                                canonical_of_retract _ hWi_mem
                        have hD_j_eq : D_j = d_smt := by
                          rcases D_j with ⟨z1, τ1, hz1⟩
                          rcases d_smt with ⟨z2, τ2, hz2⟩
                          exact SMT.RenamingContext.Dom_ext'
                            (show z1 = z2 by simpa using hfst_j.trans hd_fst.symm)
                            (show τ1 = τ2 by simpa using hty_j.trans hd_ty.symm)
                        have hDs_eq : Ds_x[i] = d_smt := by
                          simp only [Ds_x, List.getElem_ofFn, Fin.getElem_fin]
                          simp only [hΔ_Px_vi, Option.get_some]
                        rw [show D_j = Ds_x[i] from hD_j_eq.trans hDs_eq.symm])
                      hcov_substList_Px h_cov_upd_x

                    -- Step L: Show updates(Δ_P_x[z↦Wx], vs, Ds_x) agrees with Δ_P_x on fv(P_enc)
                    have h_upd_eq_x : ∀ v ∈ SMT.fv P_enc,
                        Function.updates (Function.update Δ_P_x z (some Wx)) vs
                          (Ds_x.map Option.some) v = Δ_P_x v := by
                      intro v hv
                      by_cases hvs : v ∈ vs
                      · rw [Function.updates_eq_if (by rw [List.length_map, List.length_ofFn]) vs_nodup,
                          dif_pos hvs]
                        simp only [Ds_x, List.getElem_map, List.getElem_ofFn, Fin.getElem_fin,
                          List.getElem_idxOf]
                        exact Option.some_get _
                      · rw [Function.updates_of_not_mem _ vs _ _ hvs,
                          Function.update_of_ne (by intro heq; exact z_not_fv_P (heq ▸ hv))]
                    have h_upd_agree_x : SMT.RenamingContext.AgreesOnFV
                        (Function.updates (Function.update Δ_P_x z (some Wx)) vs
                          (Ds_x.map Option.some)) Δ_P_x P_enc :=
                      h_upd_eq_x
                    have h_eq2_x := SMT.RenamingContext.denote_congr_of_agreesOnFV
                      (h1 := h_cov_upd_x) (h2 := hcov_Px) h_upd_agree_x
                    unfold SMT.RenamingContext.denote at h_eq2_x

                    -- Step M: Chain everything together
                    -- h_eq_x: substList at Δ_P_x[z↦Wx] = P_enc at updates(Δ_P_x[z↦Wx], vs, Ds_x)
                    -- h_eq2_x: P_enc at updates(...) = P_enc at Δ_P_x
                    -- hden_Px: P_enc at Δ_P_x = some denT_x'
                    rw [h_eq_x, h_eq2_x, hden_Px] at hsubst_at_ΔPx
                    have hbody_eq_denT : body_val = denT_x' :=
                      Option.some.inj hsubst_at_ΔPx.symm
                    rw [← hdenT_x'_fst_eq, ← hbody_eq_denT]
                    exact hbody_val_eq_zftrue
                  · -- contradiction
                    rename_i den_P_eq_none
                    unfold x_fin at hP_den
                    conv at den_P_eq_none => erw [hP_den]
                    nomatch den_P_eq_none
              · -- Backward: x ∈ T → x ∈ retract
                intro ⟨hx_𝒟, hx_pred⟩
                have hx_mem : x ∈ ⟦τ⟧ᶻ := h𝒟'_sub hx_𝒟
                refine ⟨hx_mem, ?_⟩
                rw [dif_pos hx_mem, dif_pos hlamVal_func]
                -- Step 1: Build canonical witness Wx for x
                have hx_canon_mem : (ZFSet.fapply (BType.canonicalIsoSMTType τ).1
                    (ZFSet.is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
                    ⟨x, by rwa [ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType τ).2.1]⟩).1 ∈
                    ⟦τ.toSMTType⟧ᶻ :=
                  ZFSet.fapply_mem_range _ _
                let Wx : SMT.Dom := ⟨_, τ.toSMTType, hx_canon_mem⟩
                have hWx_ty : Wx.snd.fst = τ.toSMTType := rfl
                have hWx_mem : Wx.fst ∈ ⟦τ.toSMTType⟧ᶻ := hx_canon_mem
                -- Step 2: Get D_enc app and body evaluation at Wx
                obtain ⟨_, Dapp_x, hDapp_x_ty, hDapp_x_val, hDapp_x_den⟩ :=
                  funDenoteAppAt (Δctx := Δ') (t := D_enc) (x := z)
                    (α := τ.toSMTType) (β := .bool) (Y := denD')
                    hcov_D_upd den_D_upd_eq denD'_type
                    denD'_func Wx hWx_ty hWx_mem
                obtain ⟨body_val, hbody_val, hbody_val_ty, hbody_val_mem⟩ :=
                  lamVal_body_bridge Wx hWx_ty hWx_mem
                have hDapp_x_mem_𝔹 : Dapp_x.fst ∈ 𝔹 := by
                  have := Dapp_x.snd.snd; rw [hDapp_x_ty] at this; exact this
                -- Step 3: D_enc condition is true (from x ∈ 𝒟)
                have hx_in_𝒟 : x ∈ 𝒟 := h𝒟_eq ▸ hx_𝒟
                have hDapp_fst_true : Dapp_x.fst = zftrue := by
                  have hx_in_retract : x ∈ retract (BType.set τ) denD'.fst := by
                    rw [denD'_retract]; exact hx_in_𝒟
                  rw [retract, ZFSet.mem_sep] at hx_in_retract
                  obtain ⟨_, hx_retract_pred⟩ := hx_in_retract
                  rw [dif_pos hx_mem, dif_pos denD'_func] at hx_retract_pred
                  rw [hDapp_x_val]
                  convert hx_retract_pred using 1
                have hcond_true :
                    ZFSet.ZFBool.toBool ⟨Dapp_x.fst, hDapp_x_mem_𝔹⟩ = true := by
                  rw [show (⟨Dapp_x.fst, hDapp_x_mem_𝔹⟩ : ZFSet.ZFBool) =
                    ⟨ZFSet.zftrue, ZFSet.ZFBool.zftrue_mem_𝔹⟩ from Subtype.ext hDapp_fst_true]
                  exact ZFSet.ZFBool.toBool_true
                -- Step 4: Decompose hx_pred to get Px = zftrue
                have hx_in_𝒟' : x ∈ 𝒟' := h𝒟_eq ▸ hx_in_𝒟
                rw [dif_pos ⟨hasArity_of_mem_toZFSet τ_hasArity hx_mem,
                    τ_hasArity, hx_mem⟩] at hx_pred
                let x_fin : Fin vs.length → B.Dom := fun i =>
                  ⟨x.get vs.length ↑i, ⟨τ.get vs.length ↑i,
                   get_mem_type_of_isTuple
                     (hasArity_of_mem_toZFSet τ_hasArity hx_mem)
                     τ_hasArity hx_mem⟩⟩
                have h_ofFinDom_eq : ZFSet.ofFinDom x_fin = x :=
                  ZFSet.ofFinDom_get (List.length_pos_iff.mpr vs_nemp)
                    (fun i => get_mem_type_of_isTuple
                      (hasArity_of_mem_toZFSet τ_hasArity hx_mem)
                      τ_hasArity hx_mem)
                    (hasArity_of_mem_toZFSet τ_hasArity hx_mem) τ_hasArity
                have hx_fin_in_𝒟' : ZFSet.ofFinDom x_fin ∈ 𝒟' :=
                  h_ofFinDom_eq ▸ hx_in_𝒟'
                have hx_fin_typ : ∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
                    (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ :=
                  fun i => ⟨rfl, (x_fin i).snd.snd⟩
                have hP_isSome := h_den_P hx_fin_typ hx_fin_in_𝒟'
                subst 𝒟'
                obtain ⟨⟨P_val, P_ty, hP_val⟩, hP_den⟩ := Option.isSome_iff_exists.mp hP_isSome
                -- Extract Px = zftrue from hx_pred via split/match
                split at hx_pred
                · rename_i Px τPx hPx den_P_eq_Px
                  unfold x_fin at hP_den
                  conv at den_P_eq_Px => erw [hP_den, Option.some_inj]
                  injection den_P_eq_Px with den_P_eq_Px
                  subst P_val
                  -- Now hx_pred : Px = zftrue
                  clear P_ih
                  -- Step A: Establish retract τ Wx.fst = x
                  have hretract_Wx : retract τ Wx.fst = x :=
                    retract_of_canonical τ hx_mem
                  -- Step B: Build x_fin-derived B context
                  set Δ_ext_x := Function.updates «Δ» vs
                    (List.ofFn fun i => some (x_fin i))
                  have Δ_fv_P_x : ∀ v ∈ B.fv P, (Δ_ext_x v).isSome = true := by
                    intro v hv
                    show (Function.updates «Δ» vs _ v).isSome = true
                    rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
                    split_ifs with hvs
                    · simp [List.getElem_ofFn]
                    · exact Δ_fv v (B.fv.mem_collect (.inr ⟨hv, hvs⟩))
                  set Δ_D_ext_x := Function.updates Δ_D vs
                    (List.ofFn fun (i : Fin vs.length) => B.RenamingContext.toSMT Δ_ext_x vs[i])
                  -- Step C: Get B-level P denotation at x_fin
                  have hP_go_den : ⟦(B.Term.abstract.go P vs «Δ» (by
                        intro v hv hvs; exact Δ_fv v (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ
                      = some ⟨Px, ⟨P_ty, hP_val⟩⟩ := by
                    convert hP_den using 2
                  have hτPx_bool : P_ty = BType.bool := by
                    rw [denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin Δ_fv_P_x] at hP_go_den
                    exact (denote_welltyped_eq
                      (t := P.abstract Δ_ext_x Δ_fv_P_x)
                      ⟨_, WFTC.of_abstract, .bool, by convert Typing.of_abstract Δ_fv_P_x typP⟩
                      hP_go_den).symm
                  subst hτPx_bool
                  have h_den_P_x : ⟦P.abstract Δ_ext_x Δ_fv_P_x⟧ᴮ = some ⟨Px, ⟨BType.bool, hP_val⟩⟩ := by
                    rw [← denote_term_abstract_go_eq_term_abstract vs_nodup vs_nemp x_fin Δ_fv_P_x]
                    exact hP_go_den
                  -- Step D: ExtendsOnSourceFV for Δ_D_ext_x
                  have Δ₀_ext_P_x : RenamingContext.ExtendsOnSourceFV Δ_D_ext_x Δ_ext_x P := by
                    intro v d hv_eq
                    by_cases hv_fv : v ∈ B.fv P
                    · have hv_smt : B.RenamingContext.toSMT Δ_ext_x v = some d := by
                        have : B.RenamingContext.toSMTOnFV Δ_ext_x P v = B.RenamingContext.toSMT Δ_ext_x v := by
                          simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                            B.RenamingContext.restrictToFV_eq_of_mem hv_fv]
                        rwa [← this]
                      by_cases hvs : v ∈ vs
                      · show Function.updates Δ_D vs _ v = some d
                        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
                        simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                        exact hv_smt
                      · have hDD_ext_x : Δ_D_ext_x v = Δ_D v := by
                          show Function.updates Δ_D vs _ v = Δ_D v
                          exact Function.updates_of_not_mem Δ_D vs _ v hvs
                        rw [hDD_ext_x]
                        have hΔ_ext_x_eq : Δ_ext_x v = «Δ» v := by
                          show Function.updates «Δ» vs _ v = «Δ» v
                          exact Function.updates_of_not_mem «Δ» vs _ v hvs
                        have hv_collect : v ∈ B.fv (Term.collect vs D P) :=
                          fv.mem_collect (.inr ⟨hv_fv, hvs⟩)
                        have hv_smt_Δ : B.RenamingContext.toSMTOnFV «Δ» (Term.collect vs D P) v = some d := by
                          simp only [RenamingContext.toSMTOnFV, RenamingContext.toSMT,
                            B.RenamingContext.restrictToFV_eq_of_mem hv_collect, Option.pure_def,
                            Option.bind_eq_bind]
                          simpa only [RenamingContext.toSMT, hΔ_ext_x_eq, Option.pure_def,
                            Option.bind_eq_bind] using hv_smt
                        exact Δ_D_extends (Δ₀_ext hv_smt_Δ)
                    · have : B.RenamingContext.toSMTOnFV Δ_ext_x P v = none := by
                        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                          B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_fv]
                      rw [this] at hv_eq; exact absurd hv_eq (not_eq_of_beq_eq_false rfl)
                  -- Step E: none_out for Δ_D_ext_x
                  have Δ_D_ext_x_none : ∀ v ∉ St₂.env.usedVars, Δ_D_ext_x v = none := by
                    intro v hv
                    show Function.updates Δ_D vs _ v = none
                    rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup]
                    split_ifs with hvs
                    · exfalso; exact hv (St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs _ hvs)))
                    · exact Δ_D_none_St₂ v hv
                  -- Step F: Invoke P_enc_total with hybrid base
                  set Δ₀_hybrid_x : SMT.RenamingContext.Context := fun v =>
                    if v ∈ vs then Δ_D_ext_x v
                    else if v ∈ St₃.env.usedVars then Δ_P v
                    else none
                  have Δ₀_hybrid_ext_P_x : RenamingContext.ExtendsOnSourceFV Δ₀_hybrid_x Δ_ext_x P := by
                    intro v d hv_eq
                    by_cases hv_fv : v ∈ B.fv P
                    · have hv_smt : B.RenamingContext.toSMT Δ_ext_x v = some d := by
                        have : B.RenamingContext.toSMTOnFV Δ_ext_x P v = B.RenamingContext.toSMT Δ_ext_x v := by
                          simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                            B.RenamingContext.restrictToFV_eq_of_mem hv_fv]
                        rwa [← this]
                      by_cases hvs : v ∈ vs
                      · show (if v ∈ vs then Δ_D_ext_x v else _) = some d
                        rw [if_pos hvs]
                        show Function.updates Δ_D vs _ v = some d
                        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
                        simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                        exact hv_smt
                      · have hv_collect : v ∈ B.fv (Term.collect vs D P) :=
                          fv.mem_collect (.inr ⟨hv_fv, hvs⟩)
                        have hv_used : v ∈ St₃.env.usedVars := by
                          have := Δ_fv v hv_collect
                          obtain ⟨bdom, hbdom⟩ := Option.isSome_iff_exists.mp this
                          have h_toSMT : ∃ d', B.RenamingContext.toSMT «Δ» v = some d' := by
                            obtain ⟨V, τ_v, hV⟩ := bdom
                            simp only [B.RenamingContext.toSMT, hbdom, Option.pure_def]; exact ⟨_, rfl⟩
                          obtain ⟨d', hd'⟩ := h_toSMT
                          have h_onFV : B.RenamingContext.toSMTOnFV «Δ» (Term.collect vs D P) v = some d' := by
                            simp only [RenamingContext.toSMTOnFV, RenamingContext.toSMT,
                              B.RenamingContext.restrictToFV_eq_of_mem hv_collect, Option.pure_def,
                              Option.bind_eq_bind, hbdom, Option.bind_some]
                            rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind, hbdom,
                              Option.bind_some] at hd'
                            exact hd'
                          have hΔ_D_v : Δ_D v = some d' := Δ_D_extends (Δ₀_ext h_onFV)
                          by_contra hv_not_used
                          exact absurd (Δ_D_none_St₂ v (fun h => hv_not_used (St₂_sub_St₃ h)))
                            (by rw [hΔ_D_v]; simp)
                        show (if v ∈ vs then _ else if v ∈ St₃.env.usedVars then Δ_P v else none) = some d
                        rw [if_neg hvs, if_pos hv_used]
                        have hΔ_ext_eq : Δ_ext v = «Δ» v := by
                          rw [Δ_ext_def]; exact Function.updates_of_not_mem «Δ» vs _ v hvs
                        have hΔ_ext_x_eq : Δ_ext_x v = «Δ» v := by
                          show Function.updates «Δ» vs _ v = «Δ» v
                          exact Function.updates_of_not_mem «Δ» vs _ v hvs
                        have h_toSMT_eq : B.RenamingContext.toSMT Δ_ext v = some d := by
                          rw [B.RenamingContext.toSMT, hΔ_ext_eq, ← B.RenamingContext.toSMT]
                          rw [B.RenamingContext.toSMT, hΔ_ext_x_eq, ← B.RenamingContext.toSMT] at hv_smt
                          exact hv_smt
                        have h_src : B.RenamingContext.toSMTOnFV Δ_ext P v = some d := by
                          simp only [RenamingContext.toSMTOnFV, RenamingContext.toSMT,
                            B.RenamingContext.restrictToFV_eq_of_mem hv_fv]
                          rw [B.RenamingContext.toSMT] at h_toSMT_eq; exact h_toSMT_eq
                        exact Δ_P_src_ext h_src
                    · have : B.RenamingContext.toSMTOnFV Δ_ext_x P v = none := by
                        simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                          B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_fv]
                      rw [this] at hv_eq; exact absurd hv_eq (not_eq_of_beq_eq_false rfl)
                  have Δ₀_hybrid_x_none_St₃ : ∀ v ∉ St₃.env.usedVars, Δ₀_hybrid_x v = none := by
                    intro v hv
                    show (if v ∈ vs then Δ_D_ext_x v else if v ∈ St₃.env.usedVars then Δ_P v else none) = none
                    have hv_not_vs : v ∉ vs := fun hvs => hv (St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs v hvs))))
                    rw [if_neg hv_not_vs, if_neg hv]
                  have Δ₀_hybrid_x_dom : ∀ v, Δ₀_hybrid_x v ≠ none → v ∈ St₃.types := by
                    intro v hv
                    change (if v ∈ vs then Δ_D_ext_x v else if v ∈ St₃.env.usedVars then Δ_P v else none) ≠ none at hv
                    split_ifs at hv with hvs hused
                    · apply AList.mem_of_subset St₂_sub_St₃_types
                      rw [St₂_types]
                      exact foldl_insert_zip_mem vs (τ.toSMTType.fromProdl (vs.length - 1)) St₁.types v
                        (by rw [fromProdl_length_of_hasArity τ_hasArity]) hvs
                    · exact Δ_P_dom v hv
                    · exact absurd rfl hv
                  obtain ⟨Δ_P_x, hcov_Px, denT_x', Δ_P_x_extends, _, _, hden_Px, hRDom_x, _⟩ :=
                    P_enc_total Δ_ext_x Δ_fv_P_x Δ₀_hybrid_x Δ₀_hybrid_ext_P_x
                      Δ₀_hybrid_x_none_St₃ (by
                        intro v d hv τ_v hτ_v
                        change (if v ∈ vs then Δ_D_ext_x v else if v ∈ St₃.env.usedVars then Δ_P v else none) = some d at hv
                        split_ifs at hv with hvs hused
                        · have hv_idx : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hvs
                          have hΔ_ext_x_vi : Δ_ext_x v = some (x_fin ⟨vs.idxOf v, hv_idx⟩) := by
                            show Function.updates «Δ» vs _ v = _
                            rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
                            simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                          have hΔ_D_ext_eq : Δ_D_ext_x v = B.RenamingContext.toSMT Δ_ext_x v := by
                            show Function.updates Δ_D vs _ v = _
                            rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup, dif_pos hvs]
                            simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                          rw [hΔ_D_ext_eq] at hv
                          rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind,
                            hΔ_ext_x_vi, Option.bind_some] at hv
                          have hd_inj := Option.some_injective _ hv
                          have hd_ty : d.snd.fst = (τ.get vs.length ⟨vs.idxOf v, hv_idx⟩).toSMTType :=
                            (congr_arg (·.snd.fst) hd_inj).symm
                          set τs := τ.toSMTType.fromProdl (vs.length - 1) with τs_def
                          have hτs_len := fromProdl_length_of_hasArity τ_hasArity
                          have hv_idx_τ : vs.idxOf v < τs.length := hτs_len ▸ hv_idx
                          have h_St₂ : St₂.types.lookup v = some τs[vs.idxOf v] := by
                            have h := foldl_insert_lookup_zip (Γ := St₁.types) vs_nodup hv_idx hv_idx_τ
                            rwa [← St₂_types, List.getElem_idxOf hv_idx] at h
                          have h_St₃ : St₃.types.lookup v = some τs[vs.idxOf v] :=
                            AList.lookup_of_subset St₂_sub_St₃_types h_St₂
                          rw [h_St₃] at hτ_v; cases hτ_v
                          rw [hd_ty]
                          exact toSMTType_get_eq_fromProdl_getElem τ_hasArity hv_idx
                        · exact Δ_P_wt v d hv τ_v hτ_v) Px hP_val h_den_P_x
                  -- Step G: Extract denT_x'.fst = Px from RDom
                  have hdenT_x'_fst_eq : denT_x'.fst = Px := hRDom_x.2
                  -- Step H: Show body_val is the ite_body true-branch = substList evaluation
                  have hbody_is_substList :
                      ⟦(SMT.substList vs (toDestPair vs (.var z)) P_enc).abstract
                        (Function.update Δ' z (some Wx)) (hcov_substList_upd Wx)⟧ˢ =
                      some body_val := by
                    have hbody_val' := hbody_val
                    change ⟦(((@ˢD_enc) (SMT.Term.var z)).ite
                      (SMT.substList vs (toDestPair vs (.var z)) P_enc) (.bool false)).abstract
                      (Function.update Δ' z (some Wx)) (ite_body_def ▸ hcov_ite_upd' Wx)⟧ˢ = _ at hbody_val'
                    simp only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind] at hbody_val'
                    conv at hbody_val' =>
                      lhs; rw [SMT.RenamingContext.denote_abstract_proof_irrel D_enc
                        (Function.update Δ' z (some Wx)) _ (hcov_D_upd Wx)]
                    rw [den_D_upd_eq Wx] at hbody_val'
                    simp only [Option.bind_some, Function.update_self,
                      Option.get_some, Option.pure_def, hWx_ty] at hbody_val'
                    have hDapp_x_den' := hDapp_x_den
                    simp only [SMT.Term.abstract, SMT.denote,
                      Option.bind_eq_bind] at hDapp_x_den'
                    conv at hDapp_x_den' =>
                      lhs; rw [SMT.RenamingContext.denote_abstract_proof_irrel
                        D_enc _ _ (hcov_D_upd Wx)]
                    rw [den_D_upd_eq Wx] at hDapp_x_den'
                    simp only [Function.update_self, Option.get_some,
                      Option.pure_def, Option.bind_some, hWx_ty] at hDapp_x_den'
                    rw [hDapp_x_den'] at hbody_val'
                    simp only [Option.bind_some] at hbody_val'
                    have hDapp_x_struct : Dapp_x =
                        ⟨Dapp_x.fst, ⟨.bool, hDapp_x_ty ▸ Dapp_x.snd.snd⟩⟩ := by
                      obtain ⟨_, ⟨_, _⟩⟩ := Dapp_x; cases hDapp_x_ty; rfl
                    rw [hDapp_x_struct] at hbody_val'; dsimp at hbody_val'
                    rw [show ZFSet.ZFBool.toBool ⟨Dapp_x.fst, _⟩ = true from by convert hcond_true] at hbody_val'
                    simp only [ite_true] at hbody_val'
                    conv at hbody_val' =>
                      lhs; rw [SMT.RenamingContext.denote_abstract_proof_irrel
                        (SMT.substList vs (toDestPair vs (.var z)) P_enc)
                        (Function.update Δ' z (some Wx)) _ (hcov_substList_upd Wx)]
                    exact hbody_val'
                  -- Step I: Transfer substList from Δ'[z↦Wx] to Δ_P[z↦Wx]
                  have hΔ_agree_substList : SMT.RenamingContext.AgreesOnFV
                      (Function.update Δ' z (some Wx))
                      (Function.update Δ_P z (some Wx))
                      (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
                    intro v hv
                    by_cases hvz : v = z
                    · subst hvz; simp [Function.update_self]
                    · rw [Function.update_of_ne hvz, Function.update_of_ne hvz]
                      have hv_not_vs := fv_substList_disj_vs v hv hvz
                      exact Δ'_agrees_P v (by
                        rcases SMT_mem_fv_substList hv with h | ⟨t, ht, hv_t⟩
                        · exact h
                        · exact absurd (SMT_fv_toDestPair_subset ht hv_t ▸ rfl) hvz) hv_not_vs
                  have hcov_substList_upd_ΔP' : SMT.RenamingContext.CoversFV
                      (Function.update Δ_P z (some Wx))
                      (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
                    intro v hv
                    by_cases hvz : v = z
                    · subst hvz; simp [Function.update_self]
                    · rw [Function.update_of_ne hvz]
                      have hv_not_vs := fv_substList_disj_vs v hv hvz
                      rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
                      · exact Δ_P_covers v hv_P
                      · exact absurd (SMT_fv_toDestPair_subset ht hv_t ▸ rfl) hvz
                  have hsubst_at_ΔP : ⟦(SMT.substList vs (toDestPair vs (.var z)) P_enc).abstract
                      (Function.update Δ_P z (some Wx)) hcov_substList_upd_ΔP'⟧ˢ =
                      some body_val := by
                    have h_transfer := SMT.RenamingContext.denote_congr_of_agreesOnFV
                      (h1 := hcov_substList_upd Wx) (h2 := hcov_substList_upd_ΔP') hΔ_agree_substList
                    unfold SMT.RenamingContext.denote at h_transfer
                    rw [← h_transfer]; exact hbody_is_substList
                  -- Step J: Transfer substList from Δ_P[z↦Wx] to Δ_P_x[z↦Wx] via hybrid base
                  have hΔ_Px_agree : SMT.RenamingContext.AgreesOnFV
                      (Function.update Δ_P_x z (some Wx))
                      (Function.update Δ_P z (some Wx))
                      (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
                    intro v hv
                    by_cases hvz : v = z
                    · subst hvz; simp [Function.update_self]
                    · rw [Function.update_of_ne hvz, Function.update_of_ne hvz]
                      have hv_not_vs := fv_substList_disj_vs v hv hvz
                      rcases SMT_mem_fv_substList hv with hv_P | ⟨t, ht, hv_t⟩
                      · -- v ∈ fv(P_enc), v ∉ vs, v ∈ St₃.usedVars
                        have hv_used : v ∈ St₃.env.usedVars :=
                          St₃_keys_sub (AList.mem_keys.mpr (SMT.Typing.mem_context_of_mem_fv typ_P_enc hv_P))
                        -- Δ₀_hybrid_x v = Δ_P v (since v ∉ vs, v ∈ St₃.usedVars)
                        have hΔ₀_v : Δ₀_hybrid_x v = Δ_P v := by
                          show (if v ∈ vs then _ else if v ∈ St₃.env.usedVars then Δ_P v else none) = Δ_P v
                          rw [if_neg hv_not_vs, if_pos hv_used]
                        -- Δ_P v = some d (from coverage)
                        obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Δ_P_covers v hv_P)
                        -- Δ_P_x v = some d (from Extends Δ_P_x Δ₀_hybrid_x)
                        have hΔ_Px_v : Δ_P_x v = some d := Δ_P_x_extends (hΔ₀_v ▸ hd)
                        rw [hΔ_Px_v, hd]
                      · exact absurd (SMT_fv_toDestPair_subset ht hv_t ▸ rfl) hvz
                  have hcov_substList_Px : SMT.RenamingContext.CoversFV
                      (Function.update Δ_P_x z (some Wx))
                      (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
                    intro v hv
                    by_cases hvz : v = z
                    · subst hvz; simp [Function.update_self]
                    · rw [Function.update_of_ne hvz]
                      have hagr := hΔ_Px_agree hv
                      rw [Function.update_of_ne hvz, Function.update_of_ne hvz] at hagr
                      rw [hagr]
                      have := hcov_substList_upd_ΔP' v hv
                      rwa [Function.update_of_ne hvz] at this
                  have hsubst_at_ΔPx : ⟦(SMT.substList vs (toDestPair vs (.var z)) P_enc).abstract
                      (Function.update Δ_P_x z (some Wx)) hcov_substList_Px⟧ˢ =
                      some body_val := by
                    have h_transfer2 := SMT.RenamingContext.denote_congr_of_agreesOnFV
                      (h1 := hcov_substList_Px) (h2 := hcov_substList_upd_ΔP') hΔ_Px_agree
                    unfold SMT.RenamingContext.denote at h_transfer2
                    rw [h_transfer2]; exact hsubst_at_ΔP
                  -- Step K: Apply abstract_substList_denote
                  have hΔ_Px_vs_isSome : ∀ (i : Fin vs.length), (Δ_P_x vs[i]).isSome = true := by
                    intro ⟨i, hi⟩
                    have hvi_mem : vs[i] ∈ vs := List.getElem_mem hi
                    have hΔ_ext_x_vi : (Δ_ext_x vs[i]).isSome = true := by
                      show (Function.updates «Δ» vs _ vs[i]).isSome = true
                      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                        dif_pos hvi_mem]
                      simp only [List.getElem_ofFn, Option.isSome]
                    obtain ⟨bval, hbval⟩ := Option.isSome_iff_exists.mp hΔ_ext_x_vi
                    have htoSMT_some : ∃ d, B.RenamingContext.toSMT Δ_ext_x vs[i] = some d := by
                      obtain ⟨V, τ_v, hV⟩ := bval
                      simp only [B.RenamingContext.toSMT, hbval, Option.bind_some, Option.pure_def]
                      exact ⟨_, rfl⟩
                    obtain ⟨d, hd⟩ := htoSMT_some
                    have hΔ_D_ext_x_vi : Δ_D_ext_x vs[i] = some d := by
                      show Function.updates Δ_D vs _ vs[i] = some d
                      rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                        dif_pos hvi_mem]
                      simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                      exact hd
                    have hΔ₀_hybrid_x_vi : Δ₀_hybrid_x vs[i] = some d := by
                      show (if vs[i] ∈ vs then Δ_D_ext_x vs[i] else _) = some d
                      rw [if_pos hvi_mem]; exact hΔ_D_ext_x_vi
                    exact Option.isSome_iff_exists.mpr ⟨d, Δ_P_x_extends hΔ₀_hybrid_x_vi⟩
                  let Ds_x : List SMT.Dom := List.ofFn fun i : Fin vs.length =>
                    (Δ_P_x vs[i]).get (hΔ_Px_vs_isSome i)
                  have hvs_not_bv' : ∀ x ∈ vs, x ∉ SMT.bv P_enc := by
                    intro v hv hbv
                    set τs := τ.toSMTType.fromProdl (vs.length - 1)
                    have hτs_len := fromProdl_length_of_hasArity τ_hasArity
                    have hv_idx : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hv
                    have hv_idx_τ : vs.idxOf v < τs.length := hτs_len ▸ hv_idx
                    have h_St₂_lookup : ∃ σ, St₂.types.lookup v = some σ := by
                      have h := foldl_insert_lookup_zip (Γ := St₁.types) vs_nodup hv_idx hv_idx_τ
                      rw [← St₂_types, List.getElem_idxOf hv_idx] at h
                      exact ⟨_, h⟩
                    have hv_St₃ : v ∈ St₃.types := by
                      obtain ⟨σ, hσ⟩ := h_St₂_lookup
                      have h_entry := AList.mem_lookup_iff.mp hσ
                      have h_St₃_entry := St₂_sub_St₃_types h_entry
                      have h_St₃_lookup := AList.mem_lookup_iff.mpr h_St₃_entry
                      exact AList.lookup_isSome.mp (Option.isSome_of_eq_some h_St₃_lookup)
                    exact SMT.Typing.bv_notMem_context typ_P_enc v hbv hv_St₃
                  have z_not_bv_P' : z ∉ SMT.bv P_enc := by
                    intro hbv
                    have typ_P_enc_ins := SMT.Typing.weakening
                      (SMT.TypeContext.entries_subset_insert_of_notMem (τ := τ.toSMTType) z_fresh) typ_P_enc
                    exact SMT.Typing.bv_notMem_context typ_P_enc_ins _ hbv
                      ((AList.mem_insert _).mpr (Or.inl rfl))
                  have z_not_vs' : z ∉ vs := by
                    intro hz; exact z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used
                      (used_sub_St₁ (vars_used_vs z hz))))
                  have h_cov_upd_x : SMT.RenamingContext.CoversFV
                      (Function.updates (Function.update Δ_P_x z (some Wx)) vs
                        (Ds_x.map Option.some)) P_enc := by
                    intro v hv
                    by_cases hvs : v ∈ vs
                    · rw [Function.updates_eq_if (by rw [List.length_map, List.length_ofFn]) vs_nodup,
                        dif_pos hvs]
                      simp
                    · rw [Function.updates_of_not_mem _ vs _ _ hvs,
                        Function.update_of_ne (by intro heq; exact z_not_fv_P (heq ▸ hv))]
                      exact hcov_Px v hv
                  have hlen_xt' : vs.length = (toDestPair vs (.var z)).length := by
                    rw [toDestPair_length_gen vs (.var z) (.var z) [] vs_nemp]; simp
                  have hlen_xd' : vs.length = Ds_x.length := by simp [Ds_x, List.length_ofFn]
                  have h_eq_x := SMT.RenamingContext.abstract_substList_denote P_enc vs (toDestPair vs (.var z))
                    Ds_x hlen_xt' hlen_xd' vs_nodup hvs_not_bv' toDestPair_bv_nil
                    (fun t ht w hw hbv => by rw [SMT_fv_toDestPair_subset ht hw] at hbv; exact z_not_bv_P' hbv)
                    toDestPair_ne_none
                    (fun t ht w hw => by rw [SMT_fv_toDestPair_subset ht hw]; exact z_not_vs')
                    (by -- toDestPair[i] denotes to Ds_x[i] under Δ_P_x[z↦Wx]
                      intro i hi_x hi_t hi_d
                      have hcov_ti : SMT.RenamingContext.CoversFV
                          (Function.update Δ_P_x z (some Wx)) (toDestPair vs (.var z))[i] := by
                        intro v hv
                        have hvz := SMT_fv_toDestPair_subset (List.getElem_mem hi_t) hv
                        subst hvz; simp [Function.update_self]
                      refine ⟨hcov_ti, ?_⟩
                      have hcov_z_Px : SMT.RenamingContext.CoversFV
                          (Function.update Δ_P_x z (some Wx)) (.var z) := by
                        intro v hv; simp [SMT.fv] at hv; subst hv; simp [Function.update_self]
                      have hden_z_Px : ⟦(SMT.Term.var z).abstract
                          (Function.update Δ_P_x z (some Wx)) hcov_z_Px⟧ˢ = some Wx := by
                        simp [SMT.Term.abstract, SMT.denote, Function.update_self]
                      have hWx_hasArity := hasArity_of_mem_toSMTZFSet τ_hasArity hWx_mem
                      obtain ⟨hcov_j, D_j, hden_j, hfst_j, hty_j⟩ :=
                        toDestPair_denote_gen τ vs (.var z) Wx
                          (Function.update Δ_P_x z (some Wx)) [] [] vs_nemp
                          hcov_z_Px hden_z_Px hWx_ty hWx_mem τ_hasArity rfl (by simp) i hi_x hi_t
                      rw [SMT.RenamingContext.denote_abstract_proof_irrel _ _ hcov_ti hcov_j, hden_j]
                      have hvi_mem : vs[i] ∈ vs := List.getElem_mem hi_x
                      have hΔ_ext_x_vi : Δ_ext_x vs[i] = some (x_fin ⟨i, hi_x⟩) := by
                        show Function.updates «Δ» vs _ vs[i] = _
                        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                          dif_pos hvi_mem]
                        simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                        simp [List.idxOf_getElem vs_nodup]
                      obtain ⟨d_smt, hd_smt⟩ : ∃ d, B.RenamingContext.toSMT Δ_ext_x vs[i] = some d := by
                        simp only [B.RenamingContext.toSMT, hΔ_ext_x_vi, Option.pure_def]
                        exact ⟨_, rfl⟩
                      have htoSMT_unf : B.RenamingContext.toSMT Δ_ext_x vs[i] = some d_smt := hd_smt
                      rw [B.RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind,
                        hΔ_ext_x_vi, Option.bind_some] at htoSMT_unf
                      have hd_inj := Option.some_injective _ htoSMT_unf
                      have hd_ty : d_smt.snd.fst = (τ.get vs.length ⟨i, hi_x⟩).toSMTType :=
                        (congr_arg (·.snd.fst) hd_inj).symm
                      have hd_retract : retract (τ.get vs.length ⟨i, hi_x⟩) d_smt.fst =
                          (retract τ Wx.fst).get vs.length ⟨i, hi_x⟩ := by
                        have hfst_inj := congr_arg (·.fst) hd_inj
                        dsimp at hfst_inj
                        rw [← hfst_inj]
                        rw [hretract_Wx]
                        exact retract_of_canonical (τ.get vs.length ⟨i, hi_x⟩)
                          (get_mem_type_of_isTuple
                            (hasArity_of_mem_toZFSet τ_hasArity hx_mem) τ_hasArity hx_mem)
                      have hΔ_D_ext_x_vi : Δ_D_ext_x vs[i] = some d_smt := by
                        show Function.updates Δ_D vs _ vs[i] = some d_smt
                        rw [Function.updates_eq_if (by rw [List.length_ofFn]) vs_nodup,
                          dif_pos hvi_mem]
                        simp only [List.getElem_ofFn, Fin.getElem_fin, List.getElem_idxOf]
                        exact hd_smt
                      have hΔ₀_hybrid_x_vi' : Δ₀_hybrid_x vs[i] = some d_smt := by
                        show (if vs[i] ∈ vs then Δ_D_ext_x vs[i] else _) = some d_smt
                        rw [if_pos hvi_mem]; exact hΔ_D_ext_x_vi
                      have hΔ_Px_vi : Δ_P_x vs[i] = some d_smt :=
                        Δ_P_x_extends hΔ₀_hybrid_x_vi'
                      have hWi_mem : Wx.fst.get vs.length ⟨i, hi_x⟩ ∈
                          ⟦(τ.get vs.length ⟨i, hi_x⟩).toSMTType⟧ᶻ :=
                        get_mem_toSMTZFSet (hasArity_of_mem_toSMTZFSet τ_hasArity hWx_mem)
                          τ_hasArity hWx_mem
                      have hd_fst : d_smt.fst = Wx.fst.get vs.length ⟨i, hi_x⟩ := by
                        have hd_mem : d_smt.fst ∈ ⟦(τ.get vs.length ⟨i, hi_x⟩).toSMTType⟧ᶻ :=
                          hd_ty ▸ d_smt.snd.snd
                        have h_retract_eq : retract (τ.get vs.length ⟨i, hi_x⟩) d_smt.fst =
                            retract (τ.get vs.length ⟨i, hi_x⟩) (Wx.fst.get vs.length ⟨i, hi_x⟩) := by
                          rw [hd_retract, retract_get_comm
                            (hasArity_of_mem_toSMTZFSet τ_hasArity hWx_mem) τ_hasArity hWx_mem]
                        calc d_smt.fst
                            = fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi_x⟩)).1
                                (is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                                ⟨retract (τ.get vs.length ⟨i, hi_x⟩) d_smt.fst, _⟩ :=
                              (canonical_of_retract _ hd_mem).symm
                          _ = fapply (BType.canonicalIsoSMTType (τ.get vs.length ⟨i, hi_x⟩)).1
                                (is_func_is_pfunc (BType.canonicalIsoSMTType _).2.1)
                                ⟨retract (τ.get vs.length ⟨i, hi_x⟩) (Wx.fst.get vs.length ⟨i, hi_x⟩), _⟩ := by
                              simp [h_retract_eq]
                          _ = Wx.fst.get vs.length ⟨i, hi_x⟩ :=
                              canonical_of_retract _ hWi_mem
                      have hD_j_eq : D_j = d_smt := by
                        rcases D_j with ⟨z1, τ1, hz1⟩
                        rcases d_smt with ⟨z2, τ2, hz2⟩
                        exact SMT.RenamingContext.Dom_ext'
                          (show z1 = z2 by simpa using hfst_j.trans hd_fst.symm)
                          (show τ1 = τ2 by simpa using hty_j.trans hd_ty.symm)
                      have hDs_eq : Ds_x[i] = d_smt := by
                        simp only [Ds_x, List.getElem_ofFn, Fin.getElem_fin]
                        simp only [hΔ_Px_vi, Option.get_some]
                      rw [show D_j = Ds_x[i] from hD_j_eq.trans hDs_eq.symm])
                    hcov_substList_Px h_cov_upd_x
                  -- Step L: Show updates(Δ_P_x[z↦Wx], vs, Ds_x) agrees with Δ_P_x on fv(P_enc)
                  have h_upd_eq_x : ∀ v ∈ SMT.fv P_enc,
                      Function.updates (Function.update Δ_P_x z (some Wx)) vs
                        (Ds_x.map Option.some) v = Δ_P_x v := by
                    intro v hv
                    by_cases hvs : v ∈ vs
                    · rw [Function.updates_eq_if (by rw [List.length_map, List.length_ofFn]) vs_nodup,
                        dif_pos hvs]
                      simp only [Ds_x, List.getElem_map, List.getElem_ofFn, Fin.getElem_fin,
                        List.getElem_idxOf]
                      exact Option.some_get _
                    · rw [Function.updates_of_not_mem _ vs _ _ hvs,
                        Function.update_of_ne (by intro heq; exact z_not_fv_P (heq ▸ hv))]
                  have h_upd_agree_x : SMT.RenamingContext.AgreesOnFV
                      (Function.updates (Function.update Δ_P_x z (some Wx)) vs
                        (Ds_x.map Option.some)) Δ_P_x P_enc :=
                    h_upd_eq_x
                  have h_eq2_x := SMT.RenamingContext.denote_congr_of_agreesOnFV
                    (h1 := h_cov_upd_x) (h2 := hcov_Px) h_upd_agree_x
                  unfold SMT.RenamingContext.denote at h_eq2_x
                  -- Step M: Chain everything together to get body_val = denT_x'
                  rw [h_eq_x, h_eq2_x, hden_Px] at hsubst_at_ΔPx
                  have hbody_eq_denT : body_val = denT_x' :=
                    Option.some.inj hsubst_at_ΔPx.symm
                  -- Now body_val.fst = denT_x'.fst = Px = zftrue
                  have hbody_val_eq_zftrue : body_val.fst = zftrue := by
                    rw [← hx_pred, ← hdenT_x'_fst_eq, ← hbody_eq_denT]
                  -- Step N: Lambda bridge: fapply lamVal.fst Wx = body_val.fst
                  have hlamVal' := hlamVal
                  rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal'
                  simp only [SMT.denote] at hlamVal'
                  rw [dif_pos (show [z].length > 0 by exact Nat.zero_lt_succ 0)] at hlamVal'
                  split_ifs at hlamVal' with h_isSome h_typ_det
                  · let xd : Fin 1 → SMT.Dom :=
                      fun _ => ⟨τ.toSMTType.defaultZFSet, τ.toSMTType, SMTType.mem_toZFSet_of_defaultZFSet⟩
                    have hxd_spec : ∀ i, (xd i).2.1 = [τ.toSMTType][↑i] ∧ (xd i).1 ∈ ⟦[τ.toSMTType][↑i]⟧ᶻ := by
                      intro ⟨i, hi⟩; simp at hi; subst hi
                      exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
                    have hgo_d := funAbstractGoSingle (Δctx := Δ') (P := ite_body) (v := z) (τ := τ.toSMTType)
                      hgo_cov hcov_ite_upd' xd hxd_spec
                    obtain ⟨Dd, hDd⟩ := Option.isSome_iff_exists.mp
                      (hbody_total (xd ⟨0, Nat.one_pos⟩) rfl)
                    have hden_d : ⟦(SMT.Term.abstract.go ite_body [z] Δ' hgo_cov).uncurry xd⟧ˢ = some Dd := by
                      rw [hgo_d]; exact hDd
                    have hγ_out : (⟦(SMT.Term.abstract.go ite_body [z] Δ' hgo_cov).uncurry xd⟧ˢ.get
                        (h_isSome hxd_spec)).snd.fst = .bool := by
                      rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_d)]
                      exact hbody_ty (xd ⟨0, Nat.one_pos⟩) rfl Dd hDd
                    simp only [Option.pure_def, Option.some.injEq] at hlamVal'
                    have hlamVal_fst_eq : lamVal.fst = _ := congrArg (·.fst) hlamVal'.symm
                    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
                      Fin.foldr_zero, List.getElem_cons_zero] at hlamVal_fst_eq
                    have h_pair_mem : Wx.fst.pair body_val.fst ∈ lamVal.fst := by
                      rw [hlamVal_fst_eq, ZFSet.mem_lambda]
                      refine ⟨Wx.fst, body_val.fst, rfl, hWx_mem, ?_, ?_⟩
                      · have := body_val.snd.snd; rw [hbody_val_ty] at this; convert this using 2
                      · split_ifs with hw'_cond
                        · let xₙ := fun i : Fin 1 => (⟨Wx.fst.get 1 i, [τ.toSMTType][↑i], hw'_cond.2 i⟩ : SMT.Dom)
                          have hgo' := funAbstractGoSingle (Δctx := Δ') (P := ite_body) (v := z) (τ := τ.toSMTType)
                            hgo_cov hcov_ite_upd' xₙ (fun i => ⟨rfl, hw'_cond.2 i⟩)
                          have hxₙ_eq : xₙ ⟨0, Nat.zero_lt_one⟩ = Wx := rfl
                          have hden' : ⟦(SMT.Term.abstract.go ite_body [z] Δ' hgo_cov).uncurry xₙ⟧ˢ = some body_val := by
                            rw [hgo', hxₙ_eq]; exact hbody_val
                          exact (congrArg (·.fst) (Option.get_of_eq_some _ hden')).symm
                        · exfalso; apply hw'_cond
                          exact ⟨trivial, fun ⟨i, hi⟩ => by
                            have : i = 0 := Nat.lt_one_iff.mp hi; subst this; exact hWx_mem⟩
                    have h_fapply := ZFSet.fapply.of_pair (ZFSet.is_func_is_pfunc hlamVal_func) h_pair_mem
                    rw [Subtype.ext_iff] at h_fapply
                    exact h_fapply.trans hbody_val_eq_zftrue
                · -- contradiction
                  rename_i den_P_eq_none
                  unfold x_fin at hP_den
                  conv at den_P_eq_none => erw [hP_den]
                  nomatch den_P_eq_none
          · -- Totality: the lambda denotes under any alt B-level denotation
            intro Δ_alt Δ_fv_alt Δ₀_alt hext_alt hnone_alt hwt_alt T_alt hT_alt hden_alt
            -- Extract B-level D denotation from collect denotation
            have hden_D_alt : ∃ (𝒟_alt : ZFSet.{u}) (h𝒟_alt : 𝒟_alt ∈ ⟦τ.set⟧ᶻ),
                ⟦D.abstract Δ_alt (fun v hv => Δ_fv_alt v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
                some ⟨𝒟_alt, ⟨τ.set, h𝒟_alt⟩⟩ := by
              have h_inv := hden_alt
              simp only [B.Term.abstract] at h_inv
              unfold B.denote at h_inv
              simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
              obtain ⟨⟨d_val, d_ty, d_mem⟩, h_den_d, _⟩ := h_inv
              have h_conv : ⟦D.abstract Δ_alt
                  (fun v hv => Δ_fv_alt v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
                  some ⟨d_val, ⟨d_ty, d_mem⟩⟩ := by convert h_den_d using 2
              have : d_ty = .set τ := by
                have h_wt := denote_welltyped_eq
                  (t := D.abstract Δ_alt
                    (fun v hv => Δ_fv_alt v (B.fv.mem_collect (.inl hv))))
                  ⟨_, WFTC.of_abstract, .set τ,
                    by convert Typing.of_abstract _ typ_D⟩
                  h_conv
                exact h_wt.symm
              subst this
              exact ⟨d_val, d_mem, h_conv⟩
            obtain ⟨𝒟_alt, h𝒟_alt, hden_D_alt_eq⟩ := hden_D_alt
            -- Use D_RDom.2 to get Δ_D_alt covering D_enc
            -- Use Δ₀_alt_D that extends both toSMTOnFV Δ_alt D and Δ₀_alt on St₁.usedVars
            set Δ₀_alt_D : SMT.RenamingContext.Context :=
              fun v => match B.RenamingContext.toSMTOnFV Δ_alt D v with
                | some d => some d
                | none => if v ∈ St₁.env.usedVars then
                    match Δ₀_alt v with
                    | some d => some d
                    | none => Δ₀ v
                  else none
            have hext_alt_D : RenamingContext.ExtendsOnSourceFV Δ₀_alt_D Δ_alt D := by
              intro v d hv; simp only [Δ₀_alt_D, hv]
            have hnone_alt_D : ∀ v ∉ St₁.env.usedVars, Δ₀_alt_D v = none := by
              intro v hv
              show (match B.RenamingContext.toSMTOnFV Δ_alt D v with
                | some d => some d
                | none => if v ∈ St₁.env.usedVars then
                    match Δ₀_alt v with
                    | some d => some d
                    | none => Δ₀ v
                  else none) = none
              have hv_not_fv_D : v ∉ B.fv D := B.not_mem_fv_of_not_mem_used covers_D hv
              have h_toSMT_none : B.RenamingContext.toSMTOnFV Δ_alt D v = none := by
                simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                  B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not_fv_D]
              rw [h_toSMT_none, if_neg hv]
            have hwt_alt_D : ∀ v (d : SMT.Dom), Δ₀_alt_D v = some d → ∀ τ, St₁.types.lookup v = some τ → d.snd.fst = τ := by
              intro v d hv τ_v hτ_v
              -- Unfold Δ₀_alt_D at hv and case-split
              change (match B.RenamingContext.toSMTOnFV Δ_alt D v with
                | some d => some d
                | none => if v ∈ St₁.env.usedVars then
                    match Δ₀_alt v with
                    | some d => some d
                    | none => Δ₀ v
                  else none) = some d at hv
              cases h_toSMT : B.RenamingContext.toSMTOnFV Δ_alt D v with
              | some d' =>
                simp only [h_toSMT] at hv; cases hv
                -- v ∈ fv(D), so Δ₀_alt v = some d' via hext_alt
                have hv_fv_D : v ∈ B.fv D := by
                  by_contra hv_not
                  simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                    B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at h_toSMT
                have h_onFV : B.RenamingContext.toSMTOnFV Δ_alt (Term.collect vs D P) v = some d := by
                  simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                    B.RenamingContext.restrictToFV_eq_of_mem (B.fv.mem_collect (.inl hv_fv_D))]
                  simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                    B.RenamingContext.restrictToFV_eq_of_mem hv_fv_D] at h_toSMT
                  exact h_toSMT
                have hΔ₀_alt_v : Δ₀_alt v = some d := hext_alt h_onFV
                -- St₁.types ⊆ St₆.types (entries survive additions of vs,z and erasures)
                have St₁_sub_St₆ : St₁.types ⊆ St₆.types := by
                  rw [St₆_types, St₅_types, St₄_types]
                  intro ⟨k, τ_k⟩ hk_St₁
                  have hk_St₃ := St₁_sub_St₃_types hk_St₁
                  have hk_not_vs : k ∉ vs := fun hk_in_vs =>
                    vs_disj_St₁ k hk_in_vs (AList.mem_keys.mpr
                      (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₁, rfl⟩))
                  have hk_ne_z : k ≠ z := by
                    intro rfl
                    exact z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used (St₁_keys_sub
                      (AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₁, rfl⟩)))))
                  have hk_ins : ⟨k, τ_k⟩ ∈ (AList.insert z τ.toSMTType St₃.types).entries := by
                    rw [AList.entries_insert_of_notMem z_fresh, List.mem_cons]
                    exact Or.inr hk_St₃
                  exact List.mem_kerase_of_ne_key hk_ne_z
                    (AList.mem_foldl_erase_of_not_mem_keys hk_ins hk_not_vs)
                have hτ_v_St₆ : St₆.types.lookup v = some τ_v :=
                  AList.lookup_of_subset St₁_sub_St₆ hτ_v
                exact hwt_alt v d hΔ₀_alt_v τ_v hτ_v_St₆
              | none =>
                simp only [h_toSMT] at hv
                split_ifs at hv with h_used
                · cases hΔ₀_alt : Δ₀_alt v with
                  | some d' =>
                    simp only [hΔ₀_alt, Option.some.injEq] at hv; subst hv
                    have St₁_sub_St₆ : St₁.types ⊆ St₆.types := by
                      rw [St₆_types, St₅_types, St₄_types]
                      intro ⟨k, τ_k⟩ hk_St₁
                      have hk_St₃ := St₁_sub_St₃_types hk_St₁
                      have hk_not_vs : k ∉ vs := fun hk_in_vs =>
                        vs_disj_St₁ k hk_in_vs (AList.mem_keys.mpr
                          (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₁, rfl⟩))
                      have hk_ne_z : k ≠ z := by
                        intro rfl
                        exact z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used (St₁_keys_sub
                          (AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, τ_k⟩, hk_St₁, rfl⟩)))))
                      have hk_ins : ⟨k, τ_k⟩ ∈ (AList.insert z τ.toSMTType St₃.types).entries := by
                        rw [AList.entries_insert_of_notMem z_fresh, List.mem_cons]
                        exact Or.inr hk_St₃
                      exact List.mem_kerase_of_ne_key hk_ne_z
                        (AList.mem_foldl_erase_of_not_mem_keys hk_ins hk_not_vs)
                    have hτ_v_St₆ : St₆.types.lookup v = some τ_v :=
                      AList.lookup_of_subset St₁_sub_St₆ hτ_v
                    exact hwt_alt v d' hΔ₀_alt τ_v hτ_v_St₆
                  | none =>
                    simp only [hΔ₀_alt] at hv
                    -- hv : Δ₀ v = some d → use Δ_D_extends + Δ_D_wt
                    exact Δ_D_wt v d (Δ_D_extends hv) τ_v hτ_v
            have hdom_alt_D : ∀ v, Δ₀_alt_D v ≠ none → v ∈ St₁.types := by
              intro v hv
              change (match B.RenamingContext.toSMTOnFV Δ_alt D v with
                | some d => some d
                | none => if v ∈ St₁.env.usedVars then
                    match Δ₀_alt v with
                    | some d => some d
                    | none => Δ₀ v
                  else none) ≠ none at hv
              cases h_toSMT : B.RenamingContext.toSMTOnFV Δ_alt D v with
              | some d =>
                -- v ∈ B.fv D, so use axiom fv_sub_typings to get v ∈ St₁.types
                have hv_fv : v ∈ B.fv D := by
                  by_contra hv_not
                  simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                    B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_not] at h_toSMT
                exact fv_sub_typings typ_D typ_D_enc v hv_fv
              | none =>
                simp only [h_toSMT] at hv
                split_ifs at hv with h_used
                · cases hΔ₀_alt : Δ₀_alt v with
                  | some d' =>
                    -- Δ₀_alt v ≠ none: use outer hdom_alt (v ∈ St₆.types = Γ'), need St₁.
                    -- Use axiom via Δ₀_alt's ExtendsOnSourceFV with collect vs D P.
                    -- Δ₀_alt v ≠ none → v ∈ B.fv (collect vs D P)
                    have hv_fv_collect : v ∈ B.fv (Term.collect vs D P) :=
                      SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv
                        hext_alt v (by rw [hΔ₀_alt]; simp)
                    exact fv_sub_typings typ_t typ_D_enc v hv_fv_collect
                  | none =>
                    simp only [hΔ₀_alt] at hv
                    -- Δ₀ v ≠ none → v ∈ B.fv (collect) by axiom 1;
                    -- but we'd need v ∈ St₁.types. Use axiom 2 on D_enc typing.
                    -- This needs v ∈ B.fv D specifically. If v ∈ B.fv P only, not directly in St₁.
                    -- For now: rely on axiom that Δ₀'s dom is in B.fv D (sub-collect).
                    have hv_fv_collect : v ∈ B.fv (Term.collect vs D P) :=
                      SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv Δ₀_ext v hv
                    exact fv_sub_typings typ_t typ_D_enc v hv_fv_collect
                · exact absurd rfl hv
            obtain ⟨Δ_D_alt, hcov_D_alt, denD_alt, hext_D_alt, Δ_D_alt_none_out,
                Δ_D_alt_wt_out, hden_D_alt, hRDom_D_alt, Δ_D_alt_dom⟩ :=
              D_RDom.2
                (Δ_alt := Δ_alt)
                (fun v hv => Δ_fv_alt v (B.fv.mem_collect (.inl hv)))
                (Δ₀_alt := Δ₀_alt_D) hext_alt_D hnone_alt_D
                hwt_alt_D
                𝒟_alt h𝒟_alt hden_D_alt_eq
            -- Build Δ'_alt and show lambda denotes
            -- Δ'_alt covers fv(lambda) = fv(D_enc) ∪ (fv(substList) \ {z})
            -- Use Δ_D_alt for D_enc fv, and Δ_P for non-vs P_enc fv
            set Δ'_alt : SMT.RenamingContext.Context :=
              fun v => match Δ₀_alt v with
                | some d => some d
                | none => match Δ_D_alt v with
                  | some d => some d
                  | none => Δ' v
            -- Show Extends Δ'_alt Δ₀_alt
            have hext_Δ'_alt : RenamingContext.Extends Δ'_alt Δ₀_alt := by
              intro v d hv; simp only [Δ'_alt, hv]
            -- Show vanishing outside St₆.env.usedVars
            have Δ'_alt_none_out : ∀ v ∉ St₆.env.usedVars, Δ'_alt v = none := by
              intro v hv
              have hv_St₃ : v ∉ St₃.env.usedVars := by
                rw [St₆_used_chain, List.mem_cons, not_or] at hv; exact hv.2
              simp only [Δ'_alt]
              have h1 : Δ₀_alt v = none := hnone_alt v hv
              simp only [h1]
              have h2 : Δ_D_alt v = none :=
                Δ_D_alt_none_out v (fun hmem => hv_St₃ (St₂_sub_St₃ (St₁_sub_St₂_used hmem)))
              simp only [h2]
              exact Δ'_none_out v hv_St₃
            -- Coverage
            have hcov_lambda_alt : SMT.RenamingContext.CoversFV Δ'_alt
                ((λˢ [z]) [τ.toSMTType] ite_body) := by
              intro v hv
              simp only [Δ'_alt]
              cases h : Δ₀_alt v with
              | some d => simp
              | none =>
                cases h2 : Δ_D_alt v with
                | some d => simp
                | none =>
                  -- Fallback: Δ' covers the lambda encoding (primary coverage)
                  exact hcov_lambda v hv
            -- Lambda denotation under Δ'_alt
            -- Build hgo_cov_alt and hcov_ite_upd_alt from hcov_lambda_alt
            have hgo_cov_alt : ∀ x ∈ SMT.fv ite_body, x ∉ [z] → (Δ'_alt x).isSome = true := by
              intro x hx hxz
              have hne : x ≠ z := by simpa using hxz
              exact hcov_lambda_alt x (by
                simp only [SMT.fv, List.mem_removeAll_iff]
                exact ⟨ite_body_def ▸ hx, List.mem_singleton.not.mpr hne⟩)
            have hcov_ite_upd_alt : ∀ d : SMT.Dom,
                RenamingContext.CoversFV (Function.update Δ'_alt z (some d)) ite_body := by
              intro d v hv
              by_cases hvz : v = z
              · subst hvz; simp
              · rw [Function.update_of_ne hvz]
                exact hcov_lambda_alt v (by
                  simp only [SMT.fv, List.mem_removeAll_iff]
                  exact ⟨ite_body_def ▸ hv, List.mem_singleton.not.mpr hvz⟩)
            -- Build body typing: St₃.types.insert z τ.toSMTType ⊢ˢ ite_body : .bool
            have typ_ite_body_alt : St₃.types.insert z τ.toSMTType ⊢ˢ ite_body : .bool := by
              rw [ite_body_def]
              exact SMT.Typing.ite _ _ _ _ _
                (SMT.Typing.app _ _ _ _ _
                  (SMT.Typing.weakening
                    (SMT.TypeContext.entries_subset_insert_of_notMem (τ := τ.toSMTType) z_fresh)
                    (SMT.Typing.weakening St₁_sub_St₃_types typ_D_enc))
                  (SMT.Typing.var _ z τ.toSMTType (AList.lookup_insert St₃.types)))
                (SMT_Typing_substList vs (toDestPair vs (.var z)) P_enc
                  (SMT.Typing.weakening
                    (SMT.TypeContext.entries_subset_insert_of_notMem (τ := τ.toSMTType) z_fresh)
                    typ_P_enc)
                  toDestPair_bv_nil
                  (by
                    set Γ_z := St₃.types.insert z τ.toSMTType
                    set τs := τ.toSMTType.fromProdl (vs.length - 1)
                    have τs_len : τs.length = vs.length := fromProdl_length_of_hasArity τ_hasArity
                    intro i hi_x hi_t hx
                    have hi_τs : i < τs.length := τs_len ▸ hi_x
                    have h_St₂_lookup : St₂.types.lookup vs[i] = some τs[i] := by
                      rw [St₂_types]; exact foldl_insert_lookup_zip vs_nodup hi_x hi_τs
                    have h_St₃_lookup : St₃.types.lookup vs[i] = some τs[i] :=
                      AList.mem_lookup_iff.2 (St₂_sub_St₃_types (AList.mem_lookup_iff.1 h_St₂_lookup))
                    have hne : vs[i] ≠ z := by
                      intro heq
                      have hvi_used : vs[i] ∈ St₃.env.usedVars :=
                        St₂_sub_St₃ (St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs vs[i] (List.getElem_mem hi_x))))
                      exact z_not_used (heq ▸ hvi_used)
                    have h_lookup : Γ_z.lookup vs[i] = some τs[i] := by
                      rw [AList.lookup_insert_ne hne]; exact h_St₃_lookup
                    have h_get : (Γ_z.lookup vs[i]).get hx = τs[i] := by simp [h_lookup]
                    rw [h_get]
                    exact (toDestPair_typing_gen Γ_z vs (.var z) (.var z) τ.toSMTType [] []
                      vs_nemp rfl (SMT.Typing.var Γ_z z τ.toSMTType (AList.lookup_insert St₃.types))
                      (by rw [show τs = τ.toSMTType.fromProdl (vs.length - 1) from rfl] at τs_len; exact τs_len) rfl
                      (fun j hj => absurd hj (Nat.not_lt_zero j))
                      i τs[i]
                      (by simp only [List.append_nil]; rw [List.getElem?_eq_getElem hi_τs])).2))
                (SMT.Typing.bool _ _)
            -- Build RespectsTypeContextOnFV for body under Δ'_alt[z↦W]
            -- For body totality, use denote_exists_of_typing_fv on ite_body
            have hbody_total_alt : ∀ (W : SMT.Dom), W.snd.fst = τ.toSMTType →
                ⟦ite_body.abstract (Function.update Δ'_alt z (some W)) (hcov_ite_upd_alt W)⟧ˢ.isSome = true := by
              intro W hW_ty
              -- Build RespectsTypeContextOnFV on fv(ite_body)
              have hcompat_alt : SMT.RenamingContext.RespectsTypeContextOnFV
                  (Function.update Δ'_alt z (some W)) (St₃.types.insert z τ.toSMTType) ite_body := by
                intro v σ hv_fv hlookup
                by_cases hvz : v = z
                · subst hvz
                  rw [AList.lookup_insert] at hlookup; cases hlookup
                  exact ⟨W, by simp [Function.update], hW_ty⟩
                · rw [Function.update_of_ne hvz]
                  rw [AList.lookup_insert_ne hvz] at hlookup
                  -- v ∈ fv(ite_body) and v ≠ z
                  -- fv(ite_body) = fv(D_enc) ∪ (fv(P_enc) \ vs) ∪ {z}
                  -- Since v ≠ z, v ∈ fv(D_enc) ∪ (fv(P_enc) \ vs)
                  -- All such v are in fv(collect vs D P) (source free variables)
                  -- v ∉ vs (from fv_substList_disj_vs or vs_disj_St₁)
                  -- From hext_alt, Δ₀_alt v = toSMT Δ_alt v for v ∈ fv(collect)
                  -- So Δ'_alt v = Δ₀_alt v = toSMT Δ_alt v, with type τ_b.toSMTType
                  -- And from the encoding, St₃.types.lookup v = τ_b.toSMTType
                  -- For now, case split on Δ'_alt structure
                  simp only [Δ'_alt]
                  cases h_Δ₀ : Δ₀_alt v with
                  | some d =>
                    simp only [h_Δ₀]
                    refine ⟨d, rfl, ?_⟩
                    -- d.2.1 = σ. Use: hext_alt forces d to come from toSMT Δ_alt v.
                    -- Decompose hv_fv: v ∈ fv(ite_body), v ≠ z
                    rw [ite_body_def] at hv_fv
                    simp only [SMT.fv, List.mem_append, List.mem_singleton,
                      List.not_mem_nil, or_false] at hv_fv
                    -- v ∈ fv(D_enc @ˢ z) ∨ v ∈ fv(substList ...) (excluding v = z)
                    have hv_not_vs : v ∉ vs := by
                      rcases hv_fv with (hv_D | rfl) | hv_subst
                      · -- hv_D : v ∈ fv(D_enc) (already decomposed by outer simp)
                        intro hvs
                        exact vs_disj_St₁ v hvs (SMT.Typing.mem_context_of_mem_fv typ_D_enc hv_D)
                      · nomatch hvz
                      · exact fv_substList_disj_vs v hv_subst hvz
                    -- Δ'_extends_Δ₀ : Extends Δ' Δ₀
                    -- Δ₀_ext : ExtendsOnSourceFV Δ₀ Δ (collect vs D P)
                    -- hext_alt : ExtendsOnSourceFV Δ₀_alt Δ_alt (collect vs D P)
                    -- = Extends Δ₀_alt (toSMTOnFV Δ_alt (collect vs D P))
                    -- If v ∈ fv(collect), toSMTOnFV Δ_alt collect v = toSMT Δ_alt v = some d'
                    -- Then Extends gives Δ₀_alt v = some d', so d = d'
                    -- And d'.2.1 = (BType of v).toSMTType = σ
                    -- If v ∉ fv(collect), toSMTOnFV = none, unconstrained.
                    -- But then v is encoding-internal: v ∉ E.context,
                    -- v was added by the encoder to usedVars but NOT to types.
                    -- So v ∉ St₀.types. D encoding doesn't add v to types if v ∉ B.fv D.
                    -- P encoding similarly. So v ∉ St₃.types, contradicting hlookup.
                    -- Therefore v ∈ fv(collect).
                    --
                    -- Actually: the simplest path is to use the `none` case's
                    -- Δ' v which already has the right type. Since Δ₀ extends toSMTOnFV Δ collect,
                    -- and Δ' extends Δ₀, Δ' v has the same type structure.
                    -- But we have Δ₀_alt v = some d, not Δ' v.
                    -- Use Extends directly.
                    -- Use denote_type_eq_of_typing on (var v) under Δ'_alt
                    -- Since Δ₀_alt v = some d, Δ'_alt v = some d by definition
                    have hΔ'_alt_v : Δ'_alt v = some d := by simp [Δ'_alt, h_Δ₀]
                    have hcov_var_v : SMT.RenamingContext.CoversFV Δ'_alt (.var v) := by
                      intro w hw; simp [SMT.fv] at hw; subst hw; rw [hΔ'_alt_v]; simp
                    have hden_var : ⟦(SMT.Term.var v).abstract Δ'_alt hcov_var_v⟧ˢ =
                        some d := by
                      simp [SMT.Term.abstract, SMT.denote, hΔ'_alt_v, Option.pure_def]
                    have typ_var : St₃.types ⊢ˢ SMT.Term.var v : σ :=
                      SMT.Typing.var St₃.types v σ hlookup
                    exact denote_type_eq_of_typing typ_var hden_var
                  | none =>
                    -- Δ₀_alt v = none: Δ'_alt v = Δ_D_alt v
                    -- v ∈ fv(lambda) since v ∈ fv(ite_body) \ {z}
                    have hv_lambda : v ∈ SMT.fv ((λˢ [z]) [τ.toSMTType] ite_body) := by
                      simp only [SMT.fv, List.mem_removeAll_iff]
                      exact ⟨ite_body_def ▸ hv_fv, List.mem_singleton.not.mpr hvz⟩
                    -- Δ'_alt v is some by coverage
                    have hΔ'_alt_v_isSome := hcov_lambda_alt v hv_lambda
                    obtain ⟨dv, hdv⟩ := Option.isSome_iff_exists.mp hΔ'_alt_v_isSome
                    -- hdv : Δ'_alt v = some dv. Convert to unfolded form.
                    have hdv_unf : (match Δ_D_alt v with | some d => some d | none => Δ' v) = some dv := by
                      have : Δ'_alt v = (match Δ_D_alt v with | some d => some d | none => Δ' v) := by
                        show (match Δ₀_alt v with | some d => some d | none => match Δ_D_alt v with | some d => some d | none => Δ' v) = _
                        rw [h_Δ₀]
                      rwa [← this]
                    -- Type of dv matches St₃.types via denote_type_eq_of_typing on (var v)
                    have hcov_var_v : SMT.RenamingContext.CoversFV Δ'_alt (.var v) := by
                      intro w hw; simp [SMT.fv] at hw; subst hw; rw [hdv]; simp
                    have hden_var : ⟦(SMT.Term.var v).abstract Δ'_alt hcov_var_v⟧ˢ =
                        some dv := by
                      simp [SMT.Term.abstract, SMT.denote, hdv, Option.pure_def]
                    have typ_var : St₃.types ⊢ˢ SMT.Term.var v : σ :=
                      SMT.Typing.var St₃.types v σ hlookup
                    have hdv_ty : dv.2.1 = σ :=
                      denote_type_eq_of_typing typ_var hden_var
                    exact ⟨dv, hdv_unf, hdv_ty⟩
              obtain ⟨D_body, hD_body, _⟩ :=
                SMT.RenamingContext.denote_exists_of_typing_fv
                  typ_ite_body_alt hcompat_alt (hcov_ite_upd_alt W)
              exact Option.isSome_iff_exists.mpr ⟨D_body, hD_body⟩
            -- Body type determinacy
            have hbody_ty_alt : ∀ (W : SMT.Dom) (_ : W.snd.fst = τ.toSMTType)
                (Db : SMT.Dom),
                ⟦ite_body.abstract (Function.update Δ'_alt z (some W)) (hcov_ite_upd_alt W)⟧ˢ = some Db →
                Db.snd.fst = .bool := by
              intro W hW_ty Db hDb
              exact denote_type_eq_of_typing (Γ := St₃.types.insert z τ.toSMTType) typ_ite_body_alt hDb
            -- Now replicate hsome_lambda proof structure with Δ'_alt
            have hcov_ite_upd_alt' : ∀ W : SMT.Dom,
                RenamingContext.CoversFV (Function.update Δ'_alt z (some W)) ite_body :=
              fun W => hcov_ite_upd_alt W
            have hlamVal_alt : ∃ lamVal_alt,
                ⟦((λˢ [z]) [τ.toSMTType] ite_body).abstract Δ'_alt hcov_lambda_alt⟧ˢ =
                some lamVal_alt := by
              rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
              have hlen : [z].length > 0 := Nat.zero_lt_succ 0
              rw [dif_pos hlen]
              split_ifs with den_t_isSome den_t_typ_det
              · exact ⟨_, rfl⟩
              · exfalso; apply den_t_typ_det
                intro x y hx hy
                let Wx : SMT.Dom := x ⟨0, hlen⟩
                let Wy : SMT.Dom := y ⟨0, hlen⟩
                have hWx_ty : Wx.snd.fst = τ.toSMTType := by
                  simpa [Wx] using (hx ⟨0, hlen⟩).1
                have hWy_ty : Wy.snd.fst = τ.toSMTType := by
                  simpa [Wy] using (hy ⟨0, hlen⟩).1
                have hgo_x := funAbstractGoSingle (Δctx := Δ'_alt) (P := ite_body) (v := z) (τ := τ.toSMTType)
                  hgo_cov_alt hcov_ite_upd_alt' x hx
                have hgo_y := funAbstractGoSingle (Δctx := Δ'_alt) (P := ite_body) (v := z) (τ := τ.toSMTType)
                  hgo_cov_alt hcov_ite_upd_alt' y hy
                obtain ⟨Dx, hDx⟩ := Option.isSome_iff_exists.mp (hbody_total_alt Wx hWx_ty)
                obtain ⟨Dy, hDy⟩ := Option.isSome_iff_exists.mp (hbody_total_alt Wy hWy_ty)
                have hden_x : ⟦(SMT.Term.abstract.go ite_body [z] Δ'_alt hgo_cov_alt).uncurry x⟧ˢ = some Dx := by
                  rw [hgo_x]; exact hDx
                have hden_y : ⟦(SMT.Term.abstract.go ite_body [z] Δ'_alt hgo_cov_alt).uncurry y⟧ˢ = some Dy := by
                  rw [hgo_y]; exact hDy
                calc (⟦(SMT.Term.abstract.go ite_body [z] Δ'_alt hgo_cov_alt).uncurry x⟧ˢ.get
                        (den_t_isSome hx)).snd.fst
                    = Dx.snd.fst := congrArg (·.snd.fst) (Option.get_of_eq_some (den_t_isSome hx) hden_x)
                  _ = SMTType.bool := hbody_ty_alt Wx hWx_ty Dx hDx
                  _ = Dy.snd.fst := (hbody_ty_alt Wy hWy_ty Dy hDy).symm
                  _ = (⟦(SMT.Term.abstract.go ite_body [z] Δ'_alt hgo_cov_alt).uncurry y⟧ˢ.get
                        (den_t_isSome hy)).snd.fst :=
                      (congrArg (·.snd.fst) (Option.get_of_eq_some (den_t_isSome hy) hden_y)).symm
              · exfalso; apply den_t_isSome
                intro x hx
                let Wx : SMT.Dom := x ⟨0, hlen⟩
                have hWx_ty : Wx.snd.fst = τ.toSMTType := by
                  simpa [Wx] using (hx ⟨0, hlen⟩).1
                rw [funAbstractGoSingle (Δctx := Δ'_alt) (P := ite_body) (v := z) (τ := τ.toSMTType)
                  hgo_cov_alt hcov_ite_upd_alt' x hx]
                exact hbody_total_alt Wx hWx_ty
            obtain ⟨lamVal_alt, hlamVal_alt_eq⟩ := hlamVal_alt
            -- RDom
            -- Derive lamVal_alt type and func properties
            have hlamVal_alt_ty : lamVal_alt.snd.fst = .fun τ.toSMTType .bool := by
              have hlamVal_alt' := hlamVal_alt_eq
              rw [SMT.Term.abstract, dif_pos (by rfl)] at hlamVal_alt'
              simp only [SMT.denote] at hlamVal_alt'
              rw [dif_pos (show [z].length > 0 by exact Nat.zero_lt_succ 0)] at hlamVal_alt'
              split_ifs at hlamVal_alt' with h_isSome h_typ_det
              · let xd : Fin 1 → SMT.Dom :=
                  fun _ => ⟨τ.toSMTType.defaultZFSet, τ.toSMTType, SMTType.mem_toZFSet_of_defaultZFSet⟩
                have hxd_spec : ∀ i, (xd i).2.1 = [τ.toSMTType][↑i] ∧ (xd i).1 ∈ ⟦[τ.toSMTType][↑i]⟧ᶻ := by
                  intro ⟨i, hi⟩; simp at hi; subst hi
                  exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
                have hgo_d := funAbstractGoSingle (Δctx := Δ'_alt) (P := ite_body) (v := z) (τ := τ.toSMTType)
                  hgo_cov_alt hcov_ite_upd_alt' xd hxd_spec
                obtain ⟨Dd, hDd⟩ := Option.isSome_iff_exists.mp
                  (hbody_total_alt (xd ⟨0, Nat.one_pos⟩) rfl)
                have hden_d :
                    ⟦(SMT.Term.abstract.go ite_body [z] Δ'_alt hgo_cov_alt).uncurry xd⟧ˢ = some Dd := by
                  rw [hgo_d]; exact hDd
                have hγ_out :
                    (⟦(SMT.Term.abstract.go ite_body [z] Δ'_alt hgo_cov_alt).uncurry xd⟧ˢ.get
                      (h_isSome hxd_spec)).snd.fst = .bool := by
                  rw [congrArg (·.snd.fst) (Option.get_of_eq_some _ hden_d)]
                  exact hbody_ty_alt (xd ⟨0, Nat.one_pos⟩) rfl Dd hDd
                simp only [Option.pure_def, Option.some.injEq] at hlamVal_alt'
                rw [show lamVal_alt.snd.fst = _ from congrArg (·.snd.fst) hlamVal_alt'.symm]
                simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
                  Fin.foldr_zero, List.getElem_cons_zero]
                exact congrArg (τ.toSMTType.fun ·) hγ_out
            have hlamVal_alt_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 lamVal_alt.fst := by
              have : lamVal_alt.fst ∈ ⟦τ.toSMTType⟧ᶻ.funs 𝔹 := by
                simpa [hlamVal_alt_ty, SMTType.toZFSet] using lamVal_alt.snd.snd
              exact ZFSet.mem_funs.mp this
            have denD_alt_type : denD_alt.snd.fst = τ.toSMTType.fun SMTType.bool := hRDom_D_alt.1
            have denD_alt_retract : retract τ.set denD_alt.fst = 𝒟_alt := hRDom_D_alt.2
            have denD_alt_func : ⟦τ.toSMTType⟧ᶻ.IsFunc 𝔹 denD_alt.fst := by
              have : denD_alt.fst ∈ ⟦τ.toSMTType⟧ᶻ.funs 𝔹 := by
                simpa [denD_alt_type, SMTType.toZFSet] using denD_alt.snd.snd
              exact ZFSet.mem_funs.mp this
            -- Δ'_alt agrees with Δ_D_alt on fv(D_enc)
            have Δ'_alt_agrees_D : SMT.RenamingContext.AgreesOnFV Δ_D_alt Δ'_alt D_enc := by
              intro v hv
              show Δ_D_alt v = Δ'_alt v
              simp only [Δ'_alt]
              cases h_Δ₀_alt : Δ₀_alt v with
              | some d_alt =>
                -- Δ₀_alt v = some d_alt: need Δ_D_alt v = some d_alt
                -- Since v ∈ fv(D_enc), v ∈ St₁.types
                have hv_ctx : v ∈ St₁.types := SMT.Typing.mem_context_of_mem_fv typ_D_enc hv
                have hv_used : v ∈ St₁.env.usedVars := St₁_keys_sub (AList.mem_keys.mpr hv_ctx)
                -- Case split on toSMTOnFV Δ_alt D v
                cases h_toSMT : B.RenamingContext.toSMTOnFV Δ_alt D v with
                | some d_toSMT =>
                  have hΔ₀_D : Δ₀_alt_D v = some d_toSMT := by
                    show Δ₀_alt_D v = _; simp only [Δ₀_alt_D, h_toSMT]
                  have hv_fv_D : v ∈ B.fv D := by
                    by_contra h_not
                    simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                      B.RenamingContext.restrictToFV_eq_none_of_not_mem h_not] at h_toSMT
                  have hv_collect : v ∈ B.fv (Term.collect vs D P) :=
                    B.fv.mem_collect (.inl hv_fv_D)
                  have h_collect_eq : B.RenamingContext.toSMTOnFV Δ_alt (Term.collect vs D P) v =
                      some d_toSMT := by
                    simp only [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                      B.RenamingContext.restrictToFV_eq_of_mem hv_fv_D,
                      B.RenamingContext.restrictToFV_eq_of_mem hv_collect] at h_toSMT ⊢
                    exact h_toSMT
                  have hΔ₀_alt_v : Δ₀_alt v = some d_toSMT :=
                    hext_alt h_collect_eq
                  rw [h_Δ₀_alt] at hΔ₀_alt_v; cases hΔ₀_alt_v
                  exact hext_D_alt hΔ₀_D
                | none =>
                  have hΔ₀_D : Δ₀_alt_D v = some d_alt := by
                    show Δ₀_alt_D v = _; simp only [Δ₀_alt_D, h_toSMT, if_pos hv_used, h_Δ₀_alt]
                  exact hext_D_alt hΔ₀_D
              | none =>
                -- Δ₀_alt v = none: case split on Δ_D_alt v
                have h_some := hcov_D_alt v hv
                cases h2 : Δ_D_alt v with
                | some d => rfl
                | none => simp [h2] at h_some
            -- Δ'_alt covers D_enc
            have hΔ'_alt_covers_D : RenamingContext.CoversFV Δ'_alt D_enc := by
              intro v hv; rw [← Δ'_alt_agrees_D hv]; exact hcov_D_alt v hv
            -- D_enc denotes under Δ'_alt
            have den_D_Δ'_alt : ⟦D_enc.abstract Δ'_alt hΔ'_alt_covers_D⟧ˢ = some denD_alt := by
              have heq := SMT.RenamingContext.denote_congr_of_agreesOnFV
                (h1 := hcov_D_alt) (h2 := hΔ'_alt_covers_D) Δ'_alt_agrees_D
              unfold SMT.RenamingContext.denote at heq; rw [← heq]; exact hden_D_alt
            -- hcov_D_upd_alt
            have hcov_D_upd_alt : ∀ Xarg : SMT.Dom,
                RenamingContext.CoversFV (Function.update Δ'_alt z (some Xarg)) D_enc :=
              fun Xarg => SMT.RenamingContext.coversFV_update_of_notMem z_not_fv_D hΔ'_alt_covers_D
            -- den_D_upd_eq_alt
            have den_D_upd_eq_alt : ∀ Xarg : SMT.Dom,
                ⟦D_enc.abstract (Function.update Δ'_alt z (some Xarg))
                  (hcov_D_upd_alt Xarg)⟧ˢ = some denD_alt := by
              intro Xarg
              have := SMT.RenamingContext.denote_update_of_notMem (d := Xarg) z_not_fv_D
                (h := hΔ'_alt_covers_D)
              unfold SMT.RenamingContext.denote at this; rw [← this]; exact den_D_Δ'_alt
            -- hcov_substList_upd_alt
            have hcov_substList_upd_alt : ∀ (W : SMT.Dom),
                RenamingContext.CoversFV (Function.update Δ'_alt z (some W))
                  (SMT.substList vs (toDestPair vs (.var z)) P_enc) := by
              intro W v hv
              exact (hcov_ite_upd_alt W) v (SMT.fv.mem_ite (Or.inr (Or.inl hv)))
            -- hT_eq_alt: Extract T_alt = ZFSet.sep (...) 𝒟_alt from hden_alt
            have hT_eq_alt : ZFSet.sep (fun x =>
                if hx : x.hasArity vs.length ∧ τ.hasArity vs.length ∧ x ∈ ⟦τ⟧ᶻ then
                  match ⟦(B.Term.abstract.go P vs Δ_alt (fun v hv hvs => Δ_fv_alt v
                    (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry
                    (fun i => ⟨x.get vs.length i, ⟨τ.get vs.length i,
                      get_mem_type_of_isTuple hx.1 hx.2.1 hx.2.2⟩⟩)⟧ᴮ with
                  | some ⟨Pz, _⟩ => Pz = zftrue
                  | none => False
                else False) 𝒟_alt = T_alt := by
              have h_inv := hden_alt
              simp only [B.Term.abstract] at h_inv
              unfold B.denote at h_inv
              simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
              obtain ⟨D_dom, h_den_d, rest_alt⟩ := h_inv
              have h_conv_d : ⟦D.abstract Δ_alt
                  (fun v hv => Δ_fv_alt v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
                  some D_dom := by convert h_den_d using 2
              have hD_dom_eq : D_dom = ⟨𝒟_alt, .set τ, h𝒟_alt⟩ := by
                rw [h_conv_d] at hden_D_alt_eq
                exact Option.some.inj hden_D_alt_eq
              subst hD_dom_eq; simp only at rest_alt
              split at rest_alt
              · simp only [Option.bind_eq_some_iff] at rest_alt
                obtain ⟨_, denP_eq, rest2_alt⟩ := rest_alt
                split_ifs at rest2_alt with h_den_P_cond h_typP_det_cond
                · simp only [Option.pure_def, Option.some.injEq, PSigma.mk.injEq] at rest2_alt
                  rw [← rest2_alt.1]; congr 1; funext x; simp
                  clear * -
                  constructor
                  · rintro ⟨hx, match_eq⟩; use hx
                    split at match_eq
                    · rename_i h; erw [h]; dsimp; exact match_eq
                    · nomatch match_eq
                  · rintro ⟨hx, match_eq⟩; use hx
                    split at match_eq
                    · rename_i h; erw [h]; dsimp; exact match_eq
                    · nomatch match_eq
              · rename_i h_neg
                exact absurd ⟨BType.hasArity_of_foldl_defaultZFSet τ_hasArity, τ_hasArity⟩ h_neg
            -- h_den_P_alt: P denotability for all x ∈ 𝒟_alt
            have h_den_P_alt : ∀ {x_fin : Fin vs.length → B.Dom},
                (∀ i, (x_fin i).snd.fst = τ.get vs.length i ∧
                      (x_fin i).fst ∈ ⟦τ.get vs.length i⟧ᶻ) →
                ofFinDom x_fin ∈ 𝒟_alt →
                ⟦(B.Term.abstract.go P vs Δ_alt (fun v hv hvs => Δ_fv_alt v
                  (B.fv.mem_collect (.inr ⟨hv, hvs⟩)))).uncurry x_fin⟧ᴮ.isSome = true := by
              intro x_fin hx_typ hx_mem
              have h_inv := hden_alt
              simp only [B.Term.abstract] at h_inv
              unfold B.denote at h_inv
              simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_inv
              obtain ⟨D_dom, h_den_d, rest_alt⟩ := h_inv
              have h_conv_d : ⟦D.abstract Δ_alt
                  (fun v hv => Δ_fv_alt v (B.fv.mem_collect (.inl hv)))⟧ᴮ =
                  some D_dom := by convert h_den_d using 2
              have hD_dom_eq : D_dom = ⟨𝒟_alt, .set τ, h𝒟_alt⟩ := by
                rw [h_conv_d] at hden_D_alt_eq
                exact Option.some.inj hden_D_alt_eq
              subst hD_dom_eq; simp only at rest_alt
              split at rest_alt
              · simp only [Option.bind_eq_some_iff] at rest_alt
                obtain ⟨_, _, rest2_alt⟩ := rest_alt
                split_ifs at rest2_alt with h_den_P_cond
                exact h_den_P_cond hx_typ hx_mem
              · rename_i h_neg
                exact absurd ⟨BType.hasArity_of_foldl_defaultZFSet τ_hasArity, τ_hasArity⟩ h_neg
            -- Δ_D_alt extends toSMTOnFV Δ_alt (collect vs D P)
            have Δ_D_alt_ext_collect : SMT.RenamingContext.Extends Δ_D_alt
                (B.RenamingContext.toSMTOnFV Δ_alt (Term.collect vs D P)) := by
              intro v d hv
              have hv_fv_collect : v ∈ B.fv (Term.collect vs D P) := by
                by_contra h_neg
                simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                  B.RenamingContext.restrictToFV_eq_none_of_not_mem h_neg] at hv
              by_cases hv_fv_D : v ∈ B.fv D
              · have h_D_eq : B.RenamingContext.toSMTOnFV Δ_alt D v = some d := by
                  simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                    B.RenamingContext.restrictToFV_eq_of_mem hv_fv_D,
                    B.RenamingContext.restrictToFV_eq_of_mem hv_fv_collect] at hv ⊢; exact hv
                exact hext_D_alt (show Δ₀_alt_D v = some d by simp only [Δ₀_alt_D, h_D_eq])
              · have hΔ₀_alt_v : Δ₀_alt v = some d := hext_alt hv
                have hv_used : v ∈ St₁.env.usedVars := by
                  apply used_sub_St₁; apply vars_used
                  have : v ∈ B.fv (Term.collect vs D P) := hv_fv_collect
                  simp only [B.Term.vars, B.fv, List.mem_union_iff, List.mem_append,
                    List.mem_removeAll_iff]
                  left; right
                  constructor
                  · exact (List.mem_append.mp this).elim
                      (fun h => absurd h hv_fv_D)
                      (fun h => (List.mem_removeAll_iff.mp h).1)
                  · exact (List.mem_append.mp this).elim
                      (fun h => absurd h hv_fv_D)
                      (fun h => (List.mem_removeAll_iff.mp h).2)
                have h_D_none : B.RenamingContext.toSMTOnFV Δ_alt D v = none := by
                  simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                    B.RenamingContext.restrictToFV_eq_none_of_not_mem hv_fv_D]
                exact hext_D_alt (show Δ₀_alt_D v = some d by
                  simp only [Δ₀_alt_D, h_D_none, if_pos hv_used, hΔ₀_alt_v])
            -- Δ'_alt agrees with toSMT Δ_alt on source-level P variables not in vs
            have Δ'_alt_ctx_source : ∀ v ∈ B.fv P, v ∉ vs →
                Δ'_alt v = B.RenamingContext.toSMT Δ_alt v := by
              intro v hv hvs
              simp only [Δ'_alt]
              have hv_collect : v ∈ B.fv (Term.collect vs D P) :=
                B.fv.mem_collect (.inr ⟨hv, hvs⟩)
              obtain ⟨d, hd⟩ : ∃ d, B.RenamingContext.toSMTOnFV Δ_alt
                  (Term.collect vs D P) v = some d := by
                have := Δ_fv_alt v hv_collect
                obtain ⟨bv, hbv⟩ := Option.isSome_iff_exists.mp this
                refine ⟨?_, by
                  simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
                    B.RenamingContext.restrictToFV_eq_of_mem («Δ» := Δ_alt) hv_collect, hbv]
                  rfl⟩
              have hΔ₀_v : Δ₀_alt v = some d := hext_alt hd
              have hd_eq : some d = B.RenamingContext.toSMT Δ_alt v := by
                rw [B.RenamingContext.toSMTOnFV] at hd
                have h_restr : B.RenamingContext.restrictToFV Δ_alt (Term.collect vs D P) v =
                    Δ_alt v := B.RenamingContext.restrictToFV_eq_of_mem hv_collect
                simp only [B.RenamingContext.toSMT, h_restr] at hd
                exact hd.symm
              simp [hΔ₀_v, ← hd_eq]
            -- Δ_D_alt vanishes outside St₂.usedVars
            have Δ_D_alt_none_St₂ : ∀ v ∉ St₂.env.usedVars, Δ_D_alt v = none := by
              intro v hv_not
              have hv_not_St₁ : v ∉ St₁.env.usedVars := fun h => hv_not (St₁_sub_St₂_used h)
              exact Δ_D_alt_none_out v hv_not_St₁
            -- vars_used_vs for St₂
            have vars_used_vs_St₂ : ∀ v ∈ vs, v ∈ St₂.env.usedVars :=
              fun v hv => St₁_sub_St₂_used (used_sub_St₁ (vars_used_vs v hv))
            -- fv(P_enc) ⊆ St₃.usedVars
            have fv_P_enc_used_St₃ : ∀ v ∈ SMT.fv P_enc, v ∈ St₃.env.usedVars := by
              intro v hv
              have := SMT.Typing.mem_context_of_mem_fv typ_P_enc hv
              exact St₃_keys_sub (AList.mem_keys.mpr this)
            -- P_enc_total simplified (drop agreement clause)
            have P_enc_total_simplified :
                ∀ (Δ_alt' : B.RenamingContext.Context)
                  (Δ_fv_alt' : ∀ v ∈ B.fv P, (Δ_alt' v).isSome = true)
                  (Δ₀_alt' : SMT.RenamingContext.Context),
                  RenamingContext.ExtendsOnSourceFV Δ₀_alt' Δ_alt' P →
                  (∀ v ∉ St₃.env.usedVars, Δ₀_alt' v = none) →
                  ∀ (T_alt' : ZFSet) (hT_alt' : T_alt' ∈ ⟦BType.bool⟧ᶻ),
                    ⟦P.abstract Δ_alt' Δ_fv_alt'⟧ᴮ = some ⟨T_alt', ⟨BType.bool, hT_alt'⟩⟩ →
                    ∃ (Δ'_out : SMT.RenamingContext.Context)
                      (hcov_out : SMT.RenamingContext.CoversFV Δ'_out P_enc)
                      (denT_out : SMT.Dom),
                      SMT.RenamingContext.Extends Δ'_out Δ₀_alt' ∧
                      ⟦P_enc.abstract Δ'_out hcov_out⟧ˢ = some denT_out ∧
                      ⟨T_alt', ⟨BType.bool, hT_alt'⟩⟩ ≘ᶻ denT_out := by
              intro Δ_alt' Δ_fv_alt' Δ₀_alt' hext' hnone' T_alt' hT_alt' hden'
              -- Use axiom 3 (ExtendsOnSourceFV.wt) to supply the wt clause P_enc_total needs
              have hwt' : ∀ v (d : SMT.Dom), Δ₀_alt' v = some d →
                  ∀ τ, St₃.types.lookup v = some τ → d.snd.fst = τ :=
                SMT.RenamingContext.ExtendsOnSourceFV.wt hext' typ_P_enc
              obtain ⟨Δ'_out, hcov_out, denT_out, hext_out, _, _, hden_out, hRDom_out, _⟩ :=
                P_enc_total Δ_alt' Δ_fv_alt' Δ₀_alt' hext' hnone'
                  hwt' T_alt' hT_alt' hden'
              exact ⟨Δ'_out, hcov_out, denT_out, hext_out, hden_out, hRDom_out⟩
            -- bv constraints
            have hvs_not_bv_P_enc : ∀ v ∈ vs, v ∉ SMT.bv P_enc := by
              intro v hv hbv
              have hv_St₃ : v ∈ St₃.types := by
                set τs := τ.toSMTType.fromProdl (vs.length - 1) with τs_def
                have hτs_len := fromProdl_length_of_hasArity τ_hasArity
                have hv_idx : vs.idxOf v < vs.length := List.idxOf_lt_length_of_mem hv
                have hv_idx_τ : vs.idxOf v < τs.length := hτs_len ▸ hv_idx
                have h_St₂_lookup : ∃ σ, St₂.types.lookup v = some σ := by
                  have h := foldl_insert_lookup_zip (Γ := St₁.types) vs_nodup hv_idx hv_idx_τ
                  rw [← St₂_types, List.getElem_idxOf hv_idx] at h
                  exact ⟨_, h⟩
                obtain ⟨σ, hσ⟩ := h_St₂_lookup
                have h_entry := AList.mem_lookup_iff.mp hσ
                have h_St₃_entry := St₂_sub_St₃_types h_entry
                exact AList.lookup_isSome.mp (Option.isSome_of_eq_some (AList.mem_lookup_iff.mpr h_St₃_entry))
              exact SMT.Typing.bv_notMem_context typ_P_enc v hbv hv_St₃
            have z_not_bv_P_enc : z ∉ SMT.bv P_enc := by
              intro hbv
              have typ_P_enc_ins := SMT.Typing.weakening
                (SMT.TypeContext.entries_subset_insert_of_notMem (τ := τ.toSMTType) z_fresh) typ_P_enc
              exact SMT.Typing.bv_notMem_context typ_P_enc_ins _ hbv
                ((AList.mem_insert _).mpr (Or.inl rfl))
            have z_not_vs_proof : z ∉ vs := by
              intro hz; exact z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used
                (used_sub_St₁ (vars_used_vs z hz))))
            have hRDom_alt : ⟨T_alt, ⟨_, hT_alt⟩⟩ ≘ᶻ lamVal_alt := by
              constructor
              · rw [hlamVal_alt_ty, τ_def, BType.toSMTType]
              · exact retract_lamVal_eq_collect (denD_val := denD_alt) (𝒟_val := 𝒟_alt)
                  vs_nemp vs_nodup τ_hasArity
                  ite_body_def z_not_fv_D hcov_lambda_alt hlamVal_alt_eq
                  hlamVal_alt_func
                  hcov_D_upd_alt den_D_upd_eq_alt
                  denD_alt_type denD_alt_func h𝒟_alt denD_alt_retract
                  hcov_ite_upd_alt hbody_total_alt hbody_ty_alt
                  hcov_substList_upd_alt fv_substList_disj_vs hgo_cov_alt
                  (fun v hv => Δ_fv_alt v hv)
                  hT_eq_alt h_den_P_alt
                  (collect_hbridge vs_nemp vs_nodup τ_hasArity ite_body_def z_not_fv_D z_not_fv_P
                    z_not_vs_proof vs_not_D_fv hvs_not_bv_P_enc z_not_bv_P_enc
                    hcov_ite_upd_alt hcov_D_upd_alt den_D_upd_eq_alt
                    denD_alt_type denD_alt_func h𝒟_alt denD_alt_retract
                    hcov_substList_upd_alt fv_substList_disj_vs
                    (fun v hv => Δ_fv_alt v hv) typP Δ_D_alt_ext_collect Δ'_alt_ctx_source
                    Δ_D_alt_none_St₂ vars_used_vs_St₂
                    (fun v hv => St₂_sub_St₃ hv)
                    fv_P_enc_used_St₃ P_enc_total_simplified
                      h_den_P_alt)
            -- Output wt for Δ'_alt at St₆.types
            have Δ'_alt_wt_out : ∀ v (d : SMT.Dom), Δ'_alt v = some d →
                ∀ σ_v, St₆.types.lookup v = some σ_v → d.snd.fst = σ_v := by
              intro v d hv σ_v hσ_v
              simp only [Δ'_alt] at hv
              cases hΔ₀ : Δ₀_alt v with
              | some d' =>
                simp only [hΔ₀, Option.some.injEq] at hv; subst hv
                exact hwt_alt v d' hΔ₀ σ_v hσ_v
              | none =>
                simp only [hΔ₀] at hv
                cases hΔD : Δ_D_alt v with
                | some d' =>
                  simp only [hΔD, Option.some.injEq] at hv; subst hv
                  -- Bridge from St₆.types to St₁.types using St₁ ⊆ St₆ and case analysis
                  by_cases hv_St₁ : v ∈ St₁.types
                  · obtain ⟨σ', hσ'⟩ := Option.isSome_iff_exists.mp
                      (AList.lookup_isSome.mpr hv_St₁)
                    have St₁_sub_St₆ : St₁.types ⊆ St₆.types := by
                      rw [St₆_types, St₅_types, St₄_types]
                      intro ⟨k, σ_k⟩ hk_St₁
                      have hk_St₃ := St₁_sub_St₃_types hk_St₁
                      have hk_not_vs : k ∉ vs := fun hk_in_vs =>
                        vs_disj_St₁ k hk_in_vs (AList.mem_keys.mpr
                          (List.mem_map.mpr ⟨⟨k, σ_k⟩, hk_St₁, rfl⟩))
                      have hk_ne_z : k ≠ z := by
                        intro rfl
                        exact z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used (St₁_keys_sub
                          (AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, σ_k⟩, hk_St₁, rfl⟩)))))
                      have hk_ins : ⟨k, σ_k⟩ ∈ (AList.insert z τ.toSMTType St₃.types).entries := by
                        rw [AList.entries_insert_of_notMem z_fresh, List.mem_cons]
                        exact Or.inr hk_St₃
                      exact List.mem_kerase_of_ne_key hk_ne_z
                        (AList.mem_foldl_erase_of_not_mem_keys hk_ins hk_not_vs)
                    have h_St₆_σ' : St₆.types.lookup v = some σ' :=
                      AList.lookup_of_subset St₁_sub_St₆ hσ'
                    rw [hσ_v] at h_St₆_σ'
                    cases h_St₆_σ'
                    exact Δ_D_alt_wt_out v d' hΔD σ_v hσ'
                  · -- v ∉ St₁.types: contradiction via Δ_D_alt_dom
                    exact absurd (Δ_D_alt_dom v (by rw [hΔD]; simp)) hv_St₁
                | none =>
                  simp only [hΔD] at hv
                  exact Δ'_wt v d hv σ_v hσ_v
            -- Δ'_alt_dom: Δ'_alt's domain is in St₆.types
            have St₁_sub_St₆ : St₁.types ⊆ St₆.types := by
              rw [St₆_types, St₅_types, St₄_types]
              intro ⟨k, σ_k⟩ hk_St₁
              have hk_St₃ := St₁_sub_St₃_types hk_St₁
              have hk_not_vs : k ∉ vs := fun hk_in_vs =>
                vs_disj_St₁ k hk_in_vs (AList.mem_keys.mpr
                  (List.mem_map.mpr ⟨⟨k, σ_k⟩, hk_St₁, rfl⟩))
              have hk_ne_z : k ≠ z := by
                intro rfl
                exact z_not_used (St₂_sub_St₃ (St₁_sub_St₂_used (St₁_keys_sub
                  (AList.mem_keys.mpr (List.mem_map.mpr ⟨⟨k, σ_k⟩, hk_St₁, rfl⟩)))))
              have hk_ins : ⟨k, σ_k⟩ ∈ (AList.insert z τ.toSMTType St₃.types).entries := by
                rw [AList.entries_insert_of_notMem z_fresh, List.mem_cons]
                exact Or.inr hk_St₃
              exact List.mem_kerase_of_ne_key hk_ne_z
                (AList.mem_foldl_erase_of_not_mem_keys hk_ins hk_not_vs)
            have Δ'_alt_dom : ∀ v, Δ'_alt v ≠ none → v ∈ St₆.types := by
              intro v hv
              simp only [Δ'_alt] at hv
              cases hΔ : Δ₀_alt v with
              | some d =>
                -- axiom 1+2: v ∈ B.fv (collect vs D P) ⊆ St₆.types
                exact fv_sub_typings typ_t
                  (SMT.Typing.bool St₆.types true) v
                  (SMT.RenamingContext.ExtendsOnSourceFV.dom_sub_B_fv hext_alt v
                    (by rw [hΔ]; simp))
              | none =>
                simp only [hΔ] at hv
                cases hΔD : Δ_D_alt v with
                | some d =>
                  -- Δ_D_alt v ≠ none → v ∈ St₁.types ⊆ St₆.types
                  exact AList.mem_of_subset St₁_sub_St₆
                    (Δ_D_alt_dom v (by rw [hΔD]; simp))
                | none =>
                  simp only [hΔD] at hv
                  exact Δ'_dom v hv
            exact ⟨Δ'_alt, hcov_lambda_alt, lamVal_alt, hext_Δ'_alt, Δ'_alt_none_out,
              Δ'_alt_wt_out, hlamVal_alt_eq, hRDom_alt, Δ'_alt_dom⟩
