import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs

open Std.Do SMT ZFSet Classical

universe u

private structure ChpredTypingPack
    (Γ : TypeContext) (x : Term) (x! z z! : 𝒱) (α α' : SMTType) (z!_spec : Term) where
  typ_z!_spec_body :
    (AList.insert z α (AList.insert z! α' Γ)) ⊢ˢ z!_spec : SMTType.bool
  typ_app_body :
    (AList.insert z α (AList.insert z! α' Γ)) ⊢ˢ (@ˢx) (.var z) : SMTType.bool
  typ_exists :
    (AList.insert z! α' Γ) ⊢ˢ
      (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)) : SMTType.bool
  typ_lambda :
    Γ ⊢ˢ (λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)) :
      α'.fun SMTType.bool
  typ_eq :
    Γ ⊢ˢ
      (Term.var x! =ˢ (λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))) :
        SMTType.bool

private theorem chpredTypingPack
    {Γ : TypeContext} {x z!_spec : Term} {x! z z! : 𝒱} {α α' : SMTType}
    (typ_x : Γ ⊢ˢ x : α.fun SMTType.bool)
    (typ_x! : Γ ⊢ˢ .var x! : α'.fun SMTType.bool)
    (z_not : z ∉ Γ)
    (z!_not : z! ∉ Γ)
    (z_ne_z! : z ≠ z!)
    (typ_z!_spec_ctx :
      (AList.insert z! α' (AList.insert z α Γ)) ⊢ˢ z!_spec : SMTType.bool) :
    ChpredTypingPack Γ x x! z z! α α' z!_spec := by
  have z_not_insz!Γ : z ∉ (AList.insert z! α' Γ) := by
    rw [AList.mem_insert]
    intro hzmem
    rcases hzmem with hzmem | hzmem
    · exact z_ne_z! hzmem
    · exact z_not hzmem
  have hsub_Γ_insz! :
      Γ.entries ⊆ (AList.insert z! α' Γ).entries :=
    SMT.TypeContext.entries_subset_insert_of_notMem z!_not
  have hsub_insz!_insz_insz! :
      (AList.insert z! α' Γ).entries ⊆
        (AList.insert z α (AList.insert z! α' Γ)).entries :=
    SMT.TypeContext.entries_subset_insert_of_notMem z_not_insz!Γ
  have hsub_Γ_body :
      Γ.entries ⊆
        (AList.insert z α (AList.insert z! α' Γ)).entries := by
    intro v hv
    exact hsub_insz!_insz_insz! (hsub_Γ_insz! hv)
  have typ_x_body :
      (AList.insert z α (AList.insert z! α' Γ)) ⊢ˢ x : α.fun SMTType.bool := by
    exact SMT.Typing.weakening (h := hsub_Γ_body) typ_x
  have typ_var_z_body :
      (AList.insert z α (AList.insert z! α' Γ)) ⊢ˢ .var z : α := by
    apply SMT.Typing.var
    rw [AList.lookup_insert]
  have hperm_ctx :
      (AList.insert z! α' (AList.insert z α Γ)).entries.Perm
        ((AList.insert z α (AList.insert z! α' Γ)).entries) := by
    simpa using
      (AList.insert_insert_of_ne (s := Γ) (a := z) (a' := z!) (b := α) (b' := α') z_ne_z!)
  have typ_z!_spec_body :
      (AList.insert z α (AList.insert z! α' Γ)) ⊢ˢ z!_spec : SMTType.bool := by
    exact SMT.Typing.weakening (h := hperm_ctx.subset) typ_z!_spec_ctx
  have typ_app_body :
      (AList.insert z α (AList.insert z! α' Γ)) ⊢ˢ (@ˢx) (.var z) : SMTType.bool := by
    exact SMT.Typing.app _ _ _ _ _ typ_x_body typ_var_z_body
  have typ_and_body :
      (AList.insert z α (AList.insert z! α' Γ)) ⊢ˢ
        ((@ˢx) (.var z) ∧ˢ z!_spec) : SMTType.bool := by
    exact SMT.Typing.and _ _ _ typ_app_body typ_z!_spec_body
  have z_in_exists_ctx :
      z ∈ (AList.insert z α (AList.insert z! α' Γ)) := by
    rw [AList.mem_insert]
    exact Or.inl rfl
  have fresh_exists :
      ∀ v ∈ [z], v ∉ bv (((@ˢx) (.var z)) ∧ˢ z!_spec) := by
    intro v hv
    rw [List.mem_singleton] at hv
    subst hv
    intro hbv
    exact (SMT.Typing.bv_notMem_context typ_and_body _ hbv) z_in_exists_ctx
  have len_eq_exists : [z].length = [α].length := by
    simp
  have hupdate_exists :
      SMT.TypeContext.update (AList.insert z! α' Γ) [z] [α] len_eq_exists =
        AList.insert z α (AList.insert z! α' Γ) := by
    simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
      Fin.cast_eq_self, Fin.getElem_fin, Fin.foldl_succ_last, Fin.coe_ofNat_eq_mod,
      Nat.mod_succ, List.getElem_cons_zero, Fin.last_zero, Fin.isValue, Fin.foldl_zero]
  have typ_exists :
      (AList.insert z! α' Γ) ⊢ˢ
        (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)) : SMTType.bool := by
    apply SMT.Typing.exists (Γ := (AList.insert z! α' Γ))
      (vs := [z]) (τs := [α]) (len_eq := len_eq_exists)
    · intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      exact z_not_insz!Γ
    · exact fresh_exists
    · exact Nat.zero_lt_succ 0
    · rwa [hupdate_exists]
  have z!_in_lambda_ctx :
      z! ∈ (AList.insert z! α' Γ) := by
    rw [AList.mem_insert]
    exact Or.inl rfl
  have fresh_lambda :
      ∀ v ∈ [z!], v ∉ bv (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)) := by
    intro v hv
    rw [List.mem_singleton] at hv
    subst hv
    intro hbv
    exact (SMT.Typing.bv_notMem_context typ_exists _ hbv) z!_in_lambda_ctx
  have len_eq_lambda : [z!].length = [α'].length := by
    simp
  have hupdate_lambda :
      SMT.TypeContext.update Γ [z!] [α'] len_eq_lambda =
        AList.insert z! α' Γ := by
    simp only [SMT.TypeContext.update, List.length_cons, List.length_nil, zero_add,
      Fin.cast_eq_self, Fin.getElem_fin, Fin.foldl_succ_last, Fin.coe_ofNat_eq_mod,
      Nat.mod_succ, List.getElem_cons_zero, Fin.last_zero, Fin.isValue, Fin.foldl_zero]
  have typ_lambda :
      Γ ⊢ˢ (λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)) :
        α'.fun SMTType.bool := by
    apply SMT.Typing.lambda
      (Γ := Γ)
      (vs := [z!]) (τs := [α']) (t := (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)))
      (γ := SMTType.bool) (len_eq := len_eq_lambda)
    · intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      exact z!_not
    · exact fresh_lambda
    · exact Nat.zero_lt_succ 0
    · simpa [hupdate_lambda] using typ_exists
  exact ⟨typ_z!_spec_body, typ_app_body, typ_exists, typ_lambda,
    SMT.Typing.eq _ _ _ _ typ_x! typ_lambda⟩

private theorem chpredGoExistsCovers
    {«Δ» : RenamingContext.Context} {x z!_spec : Term} {x! z z! : 𝒱} {α : SMTType}
    (hx : RenamingContext.CoversFV «Δ» x)
    (hfv_exists_sub :
      SMT.fv (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)) ⊆ SMT.fv x ∪ {z!})
    (Yfun : SMT.Dom) :
    ∀ v ∈ SMT.fv (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)), v ∉ [z!] →
      (Function.update «Δ» x! (some Yfun) v).isSome = true := by
  intro v hv hv_not_vs
  have hv' := hfv_exists_sub hv
  rw [List.mem_union_iff] at hv'
  rcases hv' with hvx | hvz!_mem
  · by_cases hvx! : v = x!
    · subst hvx!
      simp
    · rw [Function.update_of_ne hvx!]
      exact hx v hvx
  · exact (hv_not_vs hvz!_mem).elim

private theorem chpredExistsCovers
    {«Δ» : RenamingContext.Context} {x z!_spec : Term} {x! z z! : 𝒱} {α : SMTType}
    (hx : RenamingContext.CoversFV «Δ» x)
    (hfv_exists_sub :
      SMT.fv (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)) ⊆ SMT.fv x ∪ {z!})
    (Yfun W : SMT.Dom) :
    RenamingContext.CoversFV
      (Function.update (Function.update «Δ» x! (some Yfun)) z! (some W))
      (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)) := by
  intro v hv
  by_cases hvz! : v = z!
  · subst hvz!
    simp
  · rw [Function.update_of_ne hvz!]
    have hv' := hfv_exists_sub hv
    rw [List.mem_union_iff] at hv'
    rcases hv' with hvx | hvz!_mem
    · by_cases hvx! : v = x!
      · subst hvx!
        simp only [Function.update_self, Option.isSome_some]
      · rw [Function.update_of_ne hvx!]
        exact hx v hvx
    · cases hvz!_mem <;> contradiction

private theorem chpredBodyGetTypeOf
    {«Δ» : RenamingContext.Context} {Γ : TypeContext} {x z!_spec : Term} {x! z z! : 𝒱}
    {α α' : SMTType}
    (typ_exists' :
      (AList.insert z! α' Γ) ⊢ˢ
        (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)) : SMTType.bool)
    (hgo_cov :
      ∀ (Yfun : SMT.Dom),
        ∀ v ∈ SMT.fv (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)), v ∉ [z!] →
          (Function.update «Δ» x! (some Yfun) v).isSome = true)
    (hexists_cov :
      ∀ (Yfun W : SMT.Dom),
        RenamingContext.CoversFV
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some W))
          (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)))
    (hgo_exists :
      ∀ (Yfun : SMT.Dom)
        (x_1 : Fin [z!].length → SMT.Dom)
        (hx_1 : ∀ i, (x_1 i).snd.fst = [α'][i] ∧ (x_1 i).fst ∈ ⟦[α'][i]⟧ᶻ),
        (Term.abstract.go
            (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
            [z!]
            (Function.update «Δ» x! (some Yfun))
            (hgo_cov Yfun)).uncurry x_1 =
          (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)).abstract
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some (x_1 ⟨0, by simp⟩)))
            (hexists_cov Yfun (x_1 ⟨0, by simp⟩)))
    (hbody_total :
      ∀ (Yfun : SMT.Dom)
        (x_1 : Fin [z!].length → SMT.Dom)
        (hx_1 : ∀ i, (x_1 i).snd.fst = [α'][i] ∧ (x_1 i).fst ∈ ⟦[α'][i]⟧ᶻ),
        ⟦(Term.abstract.go
            (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
            [z!]
            (Function.update «Δ» x! (some Yfun))
            (hgo_cov Yfun)).uncurry x_1⟧ˢ.isSome =
          true)
    (Yfun : SMT.Dom)
    (x_1 : Fin [z!].length → SMT.Dom)
    (hx_1 : ∀ i, (x_1 i).snd.fst = [α'][i] ∧ (x_1 i).fst ∈ ⟦[α'][i]⟧ᶻ) :
    (⟦(Term.abstract.go
        (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
        [z!]
        (Function.update «Δ» x! (some Yfun))
        (hgo_cov Yfun)).uncurry x_1⟧ˢ.get
      (hbody_total Yfun x_1 hx_1)).snd.fst =
      SMTType.bool := by
  obtain ⟨D0, hden_body⟩ := Option.isSome_iff_exists.mp (hbody_total Yfun x_1 hx_1)
  have hden_exists :
      ⟦(Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)).abstract
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some (x_1 ⟨0, by simp⟩)))
          (hexists_cov Yfun (x_1 ⟨0, by simp⟩))⟧ˢ =
        some D0 := by
    rw [←hgo_exists Yfun x_1 hx_1]
    exact hden_body
  have hD0_ty : D0.snd.fst = SMTType.bool :=
    denote_type_eq_of_typing (typ_t := typ_exists') (hden := hden_exists)
  have hget_eq :
      (⟦(Term.abstract.go
          (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
          [z!]
          (Function.update «Δ» x! (some Yfun))
          (hgo_cov Yfun)).uncurry x_1⟧ˢ.get
        (hbody_total Yfun x_1 hx_1)) = D0 := by
    apply Option.get_of_eq_some
    exact hden_body
  rw [hget_eq]
  exact hD0_ty

private theorem chpredUnaryTarget
    {α' : SMTType} {y : ZFSet}
    (hy : y ∈ ⟦α'⟧ᶻ) :
    y.hasArity 1 ∧ ∀ i : Fin 1, y ∈ ⟦[α'][i]⟧ᶻ := by
  constructor
  · simp [ZFSet.hasArity]
  · rintro ⟨i, hi⟩
    simp at hi
    subst hi
    simpa using hy

private theorem chpredDenAppAt
    {«Δ» : RenamingContext.Context} {x : Term} {x! z z! : 𝒱}
    {α : SMTType} {X Yfun wy0 : SMT.Dom}
    (hcov_x_upd : ∀ Y : SMT.Dom,
      RenamingContext.CoversFV (Function.update «Δ» x! (some Y)) x)
    (denx_upd : ∀ Y : SMT.Dom,
      ⟦x.abstract (Function.update «Δ» x! (some Y)) (hcov_x_upd Y)⟧ˢ = some X)
    (hX_ty : X.snd.fst = α.fun SMTType.bool)
    (hX_func : IsFunc ⟦α⟧ᶻ 𝔹 X.fst)
    (z!_not_mem_fv_x : z! ∉ SMT.fv x)
    (z_not_mem_fv_x : z ∉ SMT.fv x)
    (x₀ : SMT.Dom)
    (hx₀_ty : x₀.snd.fst = α)
    (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ) :
    ∃ hcov_app_goal :
        SMT.RenamingContext.CoversFV
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some x₀))
          ((@ˢx) (.var z)),
      ⟦((@ˢx) (.var z)).abstract
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some x₀))
          hcov_app_goal⟧ˢ =
        some ⟨(@ᶻX.fst
                  ⟨x₀.fst, by
                    simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩).1,
          SMTType.bool,
          (@ᶻX.fst
            ⟨x₀.fst, by
              simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩).2⟩ := by
  let Δgoal : SMT.RenamingContext.Context :=
    Function.update
      (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
      z (some x₀)
  have hcov_x_z! :
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0)) x :=
    SMT.RenamingContext.coversFV_update_of_notMem
      (x := z!) (d := wy0) z!_not_mem_fv_x (hcov_x_upd Yfun)
  have hcov_x_goal : SMT.RenamingContext.CoversFV Δgoal x :=
    SMT.RenamingContext.coversFV_update_of_notMem
      (x := z) (d := x₀) z_not_mem_fv_x hcov_x_z!
  have hdenx_goal :
      ⟦x.abstract Δgoal hcov_x_goal⟧ˢ = some X := by
    have hdenx_z! :
        ⟦x.abstract
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            hcov_x_z!⟧ˢ = some X := by
      rw [←SMT.RenamingContext.denote]
      rw [←SMT.RenamingContext.denote_update_of_notMem
        («Δ» := Function.update «Δ» x! (some Yfun))
        (t := x) (x := z!) (d := wy0) (h := hcov_x_upd Yfun) z!_not_mem_fv_x]
      rw [SMT.RenamingContext.denote]
      exact denx_upd Yfun
    rw [←SMT.RenamingContext.denote]
    rw [←SMT.RenamingContext.denote_update_of_notMem
      («Δ» := Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
      (t := x) (x := z) (d := x₀) (h := hcov_x_z!) z_not_mem_fv_x]
    simpa [SMT.RenamingContext.denote] using hdenx_z!
  have hcov_var_z_goal : SMT.RenamingContext.CoversFV Δgoal (.var z) := by
    intro v hv
    rw [fv, List.mem_singleton] at hv
    subst hv
    simp [Δgoal]
  have hden_var_z_goal :
      ⟦(Term.var z).abstract Δgoal hcov_var_z_goal⟧ˢ = some x₀ := by
    rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some.injEq]
    apply Option.get_of_eq_some
    simp [Δgoal]
  have hcov_app_goal : SMT.RenamingContext.CoversFV Δgoal ((@ˢx) (.var z)) := by
    intro v hv
    simp only [SMT.fv, List.mem_append] at hv
    rcases hv with hvx | hvz
    · exact hcov_x_goal v hvx
    · exact hcov_var_z_goal v (by simpa [fv] using hvz)
  let Xfun : SMT.Dom := ⟨X.fst, α.fun SMTType.bool, by simpa [hX_ty] using X.snd.snd⟩
  have hdenx_goal_fun :
      ⟦x.abstract Δgoal hcov_x_goal⟧ˢ = some Xfun := by
    rcases X with ⟨Xv, Xτ, hXv⟩
    dsimp [Xfun] at hdenx_goal hX_ty ⊢
    cases hX_ty
    simpa using hdenx_goal
  refine ⟨hcov_app_goal, ?_⟩
  rw [SMT.Term.abstract, SMT.denote, hdenx_goal_fun, hden_var_z_goal]
  have hmem_bool :
      x₀.fst.pair zffalse ∈ X.fst ∨ x₀.fst.pair zftrue ∈ X.fst := by
    obtain ⟨w, hw, _⟩ := hX_func.2 x₀.fst hx₀_mem
    have hwB : w ∈ 𝔹 := by
      have hwprod := hX_func.1 hw
      rw [ZFSet.pair_mem_prod] at hwprod
      exact hwprod.2
    rw [ZFSet.ZFBool.mem_𝔹_iff] at hwB
    rcases hwB with hwB | hwB
    · left
      rwa [hwB] at hw
    · right
      rwa [hwB] at hw
  have hmem_bool' : ∃ y ∈ 𝔹, x₀.fst.pair y ∈ X.fst := by
    rcases hmem_bool with hfalse | htrue
    · exact ⟨zffalse, ZFSet.ZFBool.zffalse_mem_𝔹, hfalse⟩
    · exact ⟨zftrue, ZFSet.ZFBool.zftrue_mem_𝔹, htrue⟩
  simpa [Xfun, hX_ty, hx₀_ty, ZFSet.is_func_is_pfunc hX_func, hx₀_mem, hmem_bool']

private theorem chpredDenSpecSomeAt
    {Γ : TypeContext} {«Δ» : RenamingContext.Context} {z!_spec : Term}
    {x! z z! : 𝒱} {α α' : SMTType} {p : α ⇝ α'} {Yfun wy0 : SMT.Dom}
    (den_z_at :
      ∀ (x₀ : SMT.Dom) (hx₀_ty : x₀.snd.fst = α) (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ),
        ∃ Φ X₀!,
          ∃ (_ :
            ⟦(Term.var z!).abstract
              (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!))
              (by
                intro v hv
                rw [fv, List.mem_singleton] at hv
                subst hv
                simp [Function.update])⟧ˢ = some X₀!)
            (hφ :
              RenamingContext.CoversFV
                (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!)) z!_spec)
            (_ :
              ⟦z!_spec.abstract
                (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!)) hφ⟧ˢ =
                some Φ),
            Φ.snd.fst = SMTType.bool ∧
              (Φ.fst = zftrue ∧ x₀.fst.pair X₀!.fst ∈ (castZF_of_path p).1) ∧
                ∀ (Y : SMT.Dom), Y.snd.fst = α' →
                  ∀ (hφY :
                    RenamingContext.CoversFV
                      (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                      z!_spec),
                    ⟦z!_spec.abstract
                      (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                        hφY⟧ˢ.isSome = true ∧
                      ∀ {ΦY : SMT.Dom},
                        ⟦z!_spec.abstract
                          (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                            hφY⟧ˢ =
                          some ΦY →
                        ΦY.fst = zftrue →
                          x₀.fst.pair Y.fst ∈ (castZF_of_path p).1)
    (fv_z!_spec : SMT.fv z!_spec ⊆ SMT.fv (.var z) ∪ {z!})
    (z_ne_z! : z ≠ z!)
    (x_ne_z : x! ≠ z)
    (x_ne_z! : x! ≠ z!)
    (typ_z!_spec_body :
      (AList.insert z α (AList.insert z! α' Γ)) ⊢ˢ z!_spec : SMTType.bool)
    (hwy0_ty : wy0.snd.fst = α')
    (x₀ : SMT.Dom)
    (hx₀_ty : x₀.snd.fst = α)
    (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ) :
    ∃ hφY :
        RenamingContext.CoversFV
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some x₀))
          z!_spec,
      ∃ Φ,
        ⟦z!_spec.abstract
            (Function.update
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
              z (some x₀))
            hφY⟧ˢ =
          some Φ ∧
        Φ.snd.fst = SMTType.bool := by
  obtain ⟨_, _, _, _, _, _, _, htot0⟩ := den_z_at x₀ hx₀_ty hx₀_mem
  let Δbase : SMT.RenamingContext.Context :=
    Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some wy0)
  have hφ_base : SMT.RenamingContext.CoversFV Δbase z!_spec := by
    intro u hu
    have hu' := fv_z!_spec hu
    rw [List.mem_union_iff] at hu'
    rcases hu' with huz | huz!
    · have huz' : u = z := by
        simpa [fv] using huz
      subst u
      simp [Δbase, z_ne_z!]
    · have huz!' : u = z! := List.mem_singleton.mp huz!
      subst u
      simp [Δbase]
  have hspec_some_base :
      (SMT.RenamingContext.denote Δbase z!_spec hφ_base).isSome = true := by
    simp only [SMT.RenamingContext.denote, Δbase]
    exact (htot0 wy0 hwy0_ty hφ_base).1
  let Δgoal : SMT.RenamingContext.Context :=
    Function.update
      (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
      z (some x₀)
  have hφ_goal : SMT.RenamingContext.CoversFV Δgoal z!_spec := by
    intro u hu
    have hu' := fv_z!_spec hu
    rw [List.mem_union_iff] at hu'
    rcases hu' with huz | huz!
    · have huz' : u = z := by
        simpa [fv] using huz
      subst u
      simp only [Function.update_self, Option.isSome_some, Δgoal]
    · have huz!' : u = z! := List.mem_singleton.mp huz!
      subst u
      rw [show Δgoal z! =
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some x₀) z!) by rfl]
      rw [Function.update_of_ne z_ne_z!.symm, Function.update_self]
      rfl
  have hag_spec : SMT.RenamingContext.AgreesOnFV Δgoal Δbase z!_spec := by
    intro u hu
    have hu' := fv_z!_spec hu
    rw [List.mem_union_iff] at hu'
    rcases hu' with huz | huz!
    · have huz' : u = z := by
        simpa [fv] using huz
      subst u
      simp only [Function.update_self, ne_eq, z_ne_z!, not_false_eq_true, Function.update_of_ne,
        ↓reduceIte, Δgoal, Δbase]
    · have huz!' : u = z! := List.mem_singleton.mp huz!
      subst u
      rw [show Δgoal z! =
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some x₀) z!) by rfl]
      rw [show Δbase z! =
        (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some wy0) z!) by rfl]
      rw [Function.update_of_ne z_ne_z!.symm, Function.update_self, Function.update_self]
  have hspec_eq :
      SMT.RenamingContext.denote Δgoal z!_spec hφ_goal =
        SMT.RenamingContext.denote Δbase z!_spec hφ_base :=
    SMT.RenamingContext.denote_congr_of_agreesOnFV (h1 := hφ_goal) (h2 := hφ_base) hag_spec
  have hspec_some_goal :
      ⟦z!_spec.abstract Δgoal hφ_goal⟧ˢ.isSome = true := by
    have hspec_isSome := congrArg Option.isSome hspec_eq
    rw [hspec_some_base] at hspec_isSome
    simpa [SMT.RenamingContext.denote] using hspec_isSome
  obtain ⟨Φ, hdenΦ⟩ := Option.isSome_iff_exists.mp hspec_some_goal
  refine ⟨hφ_goal, Φ, hdenΦ, ?_⟩
  exact denote_type_eq_of_typing (typ_t := typ_z!_spec_body) (hden := hdenΦ)

private theorem chpredDenSpecTrueAtCast
    {Γ : TypeContext} {«Δ» : RenamingContext.Context} {z!_spec : Term}
    {x! z z! : 𝒱} {α α' : SMTType} {p : α ⇝ α'} {cast y : ZFSet} {Yfun wy0 : SMT.Dom}
    (den_z_at :
      ∀ (x₀ : SMT.Dom) (hx₀_ty : x₀.snd.fst = α) (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ),
        ∃ Φ X₀!,
          ∃ (_ :
            ⟦(Term.var z!).abstract
              (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!))
              (by
                intro v hv
                rw [fv, List.mem_singleton] at hv
                subst hv
                simp [Function.update])⟧ˢ = some X₀!)
            (hφ :
              RenamingContext.CoversFV
                (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!)) z!_spec)
            (_ :
              ⟦z!_spec.abstract
                (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!)) hφ⟧ˢ =
                some Φ),
            Φ.snd.fst = SMTType.bool ∧
              (Φ.fst = zftrue ∧ x₀.fst.pair X₀!.fst ∈ cast) ∧
                ∀ (Y : SMT.Dom), Y.snd.fst = α' →
                  ∀ (hφY :
                    RenamingContext.CoversFV
                      (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                      z!_spec),
                    ⟦z!_spec.abstract
                      (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                        hφY⟧ˢ.isSome = true ∧
                      ∀ {ΦY : SMT.Dom},
                        ⟦z!_spec.abstract
                          (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                            hφY⟧ˢ =
                          some ΦY →
                        ΦY.fst = zftrue →
                          x₀.fst.pair Y.fst ∈ cast)
    (fv_z!_spec : SMT.fv z!_spec ⊆ SMT.fv (.var z) ∪ {z!})
    (z_ne_z! : z ≠ z!)
    (x_ne_z : x! ≠ z)
    (x_ne_z! : x! ≠ z!)
    (typ_z! :
      Γ ⊢ˢ Term.var z! : α')
    (hcast : IsFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ cast)
    (hwy0_ty : wy0.snd.fst = α')
    (hwy0_val : wy0.fst = y)
    (x₀ : SMT.Dom)
    (hx₀_ty : x₀.snd.fst = α)
    (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ)
    (hcast_xy : x₀.fst.pair y ∈ cast) :
    ∃ hφY :
        RenamingContext.CoversFV
          (Function.update
            (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
            z (some x₀))
          z!_spec,
      ∃ Φ,
        ⟦z!_spec.abstract
            (Function.update
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
              z (some x₀))
            hφY⟧ˢ =
          some Φ ∧
        Φ.fst = zftrue := by
  obtain ⟨Φ0, X₀!, hden_var_z!, hφ0, hden0, _, hΦ0_true_cast, _⟩ := den_z_at x₀ hx₀_ty hx₀_mem
  obtain ⟨hΦ0_true, hcast0⟩ := hΦ0_true_cast
  have hcast_pfunc :
      cast.IsPFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ :=
    ZFSet.is_func_is_pfunc hcast
  have hx₀_cast_dom : x₀.fst ∈ cast.Dom := by
    simpa [ZFSet.is_func_dom_eq hcast] using hx₀_mem
  have hX₀_ty : X₀!.snd.fst = α' :=
    denote_type_eq_of_typing (typ_t := typ_z!) (hden := hden_var_z!)
  have hX₀_val :
      X₀!.fst = (@ᶻcast ⟨x₀.fst, hx₀_cast_dom⟩) := by
    symm
    exact congrArg Subtype.val (ZFSet.fapply.of_pair (hf := hcast_pfunc) hcast0)
  have hy_val :
      y = (@ᶻcast ⟨x₀.fst, hx₀_cast_dom⟩) := by
    symm
    exact congrArg Subtype.val (ZFSet.fapply.of_pair (hf := hcast_pfunc) hcast_xy)
  have hX₀_eq_wy0 : X₀! = wy0 := by
    rcases X₀! with ⟨X₀v, X₀τ, hX₀mem⟩
    rcases wy0 with ⟨wyv, wyτ, hwy0mem⟩
    dsimp at hX₀_ty hwy0_ty hwy0_val hX₀_val hy_val ⊢
    cases hX₀_ty
    cases hwy0_ty
    have hval : X₀v = wyv := by
      calc
        X₀v = (@ᶻcast ⟨x₀.fst, hx₀_cast_dom⟩) := hX₀_val
        _ = y := hy_val.symm
        _ = wyv := hwy0_val.symm
    cases hval
    congr
  let Δbase : SMT.RenamingContext.Context :=
    Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some wy0)
  let Δgoal : SMT.RenamingContext.Context :=
    Function.update
      (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
      z (some x₀)
  have hφ_goal : SMT.RenamingContext.CoversFV Δgoal z!_spec := by
    intro u hu
    have hu' := fv_z!_spec hu
    rw [List.mem_union_iff] at hu'
    rcases hu' with huz | huz!
    · have huz' : u = z := by
        simpa [fv] using huz
      subst u
      simp [Δgoal, z_ne_z!, x_ne_z, x_ne_z!]
    · have huz!' : u = z! := List.mem_singleton.mp huz!
      subst u
      rw [show Δgoal z! =
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some x₀) z!) by rfl]
      rw [Function.update_of_ne z_ne_z!.symm, Function.update_self]
      rfl
  have hag_spec : SMT.RenamingContext.AgreesOnFV Δgoal Δbase z!_spec := by
    intro u hu
    have hu' := fv_z!_spec hu
    rw [List.mem_union_iff] at hu'
    rcases hu' with huz | huz!
    · have huz' : u = z := by
        simpa [fv] using huz
      subst u
      simp [Δgoal, Δbase, z_ne_z!, x_ne_z, x_ne_z!]
    · have huz!' : u = z! := List.mem_singleton.mp huz!
      subst u
      rw [show Δgoal z! =
        (Function.update
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
          z (some x₀) z!) by rfl]
      rw [show Δbase z! =
        (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some wy0) z!) by rfl]
      rw [Function.update_of_ne z_ne_z!.symm, Function.update_self, Function.update_self]
  have hden0_goal :
      SMT.RenamingContext.denote Δgoal z!_spec hφ_goal = some Φ0 := by
    rw [SMT.RenamingContext.denote_congr_of_agreesOnFV (h1 := hφ_goal) (h2 := by
      simpa [Δbase, hX₀_eq_wy0] using hφ0) hag_spec]
    simpa [SMT.RenamingContext.denote, hX₀_eq_wy0] using hden0
  refine ⟨hφ_goal, Φ0, ?_, hΦ0_true⟩
  simpa [SMT.RenamingContext.denote] using hden0_goal

private theorem chpredBodyTotal
    {Γ : TypeContext} {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α α' : SMTType} {p : α ⇝ α'}
    {X : SMT.Dom}
    (hgo_cov :
      ∀ Yfun : SMT.Dom,
        ∀ v ∈ SMT.fv (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)),
          v ∉ [z!] → (Function.update «Δ» x! (some Yfun) v).isSome = true)
    (hexists_cov :
      ∀ (Yfun W : SMT.Dom),
        RenamingContext.CoversFV
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some W))
          (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)))
    (hgo_exists :
      ∀ (Yfun : SMT.Dom)
        (w : Fin [z!].length → SMT.Dom)
        (hw : ∀ i, (w i).snd.fst = [α'][i] ∧ (w i).fst ∈ ⟦[α'][i]⟧ᶻ),
          (Term.abstract.go
              (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)).uncurry w =
            (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)).abstract
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some (w ⟨0, by simp⟩)))
              (hexists_cov Yfun (w ⟨0, by simp⟩)))
    (hcov_x_upd :
      ∀ Y : SMT.Dom, RenamingContext.CoversFV (Function.update «Δ» x! (some Y)) x)
    (denx_upd :
      ∀ Y : SMT.Dom, ⟦x.abstract (Function.update «Δ» x! (some Y)) (hcov_x_upd Y)⟧ˢ = some X)
    (hX_ty : X.snd.fst = α.fun SMTType.bool)
    (hX_func : IsFunc ⟦α⟧ᶻ 𝔹 X.fst)
    (den_z_at :
      ∀ (x₀ : SMT.Dom) (hx₀_ty : x₀.snd.fst = α) (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ),
        ∃ Φ X₀!,
          ∃ (_ :
            ⟦(Term.var z!).abstract
              (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!))
              (by
                intro v hv
                rw [fv, List.mem_singleton] at hv
                subst hv
                simp [Function.update])⟧ˢ = some X₀!)
            (hφ :
              RenamingContext.CoversFV
                (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!)) z!_spec)
            (_ :
              ⟦z!_spec.abstract
                (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!)) hφ⟧ˢ =
                some Φ),
            Φ.snd.fst = SMTType.bool ∧
              (Φ.fst = zftrue ∧ x₀.fst.pair X₀!.fst ∈ (castZF_of_path p).1) ∧
                ∀ (Y : SMT.Dom), Y.snd.fst = α' →
                  ∀ (hφY :
                    RenamingContext.CoversFV
                      (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                      z!_spec),
                    ⟦z!_spec.abstract
                      (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                        hφY⟧ˢ.isSome = true ∧
                      ∀ {ΦY : SMT.Dom},
                        ⟦z!_spec.abstract
                          (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
                            hφY⟧ˢ =
                          some ΦY →
                        ΦY.fst = zftrue →
                          x₀.fst.pair Y.fst ∈ (castZF_of_path p).1)
    (fv_z!_spec : SMT.fv z!_spec ⊆ SMT.fv (.var z) ∪ {z!})
    (z_ne_z! : z ≠ z!)
    (x_ne_z : x! ≠ z)
    (x_ne_z! : x! ≠ z!)
    (z_not_mem_fv_x : z ∉ SMT.fv x)
    (z!_not_mem_fv_x : z! ∉ SMT.fv x)
    (typ_app_body :
      (AList.insert z α (AList.insert z! α' Γ)) ⊢ˢ (@ˢx) (.var z) : SMTType.bool)
    (typ_z!_spec_body :
      (AList.insert z α (AList.insert z! α' Γ)) ⊢ˢ z!_spec : SMTType.bool)
    (Yfun : SMT.Dom)
    (x_1 : Fin [z!].length → SMT.Dom)
    (hx_1 : ∀ i, (x_1 i).snd.fst = [α'][i] ∧ (x_1 i).fst ∈ ⟦[α'][i]⟧ᶻ) :
    ⟦(Term.abstract.go
        (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
        [z!]
        (Function.update «Δ» x! (some Yfun))
        (hgo_cov Yfun)).uncurry x_1⟧ˢ.isSome =
      true := by
  let i0 : Fin [z!].length := ⟨0, by simp⟩
  have hx0 : (x_1 i0).snd.fst = α' ∧ (x_1 i0).fst ∈ ⟦α'⟧ᶻ := by
    simpa [i0] using hx_1 i0
  rw [hgo_exists Yfun x_1 hx_1]
  rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists, SMT.denote]
  simp only [Option.bind_eq_bind, Option.pure_def]
  have hlen_exists : [z].length > 0 := by
    simp
  rw [SMT.denote, dite_cond_eq_true (eq_true hlen_exists)]
  split_ifs with den_exists_isSome
  · simp
  · exfalso
    apply den_exists_isSome
    intro z_1 hz_1
    let j0 : Fin [z].length := ⟨0, by simp⟩
    have hz0 : (z_1 j0).snd.fst = α ∧ (z_1 j0).fst ∈ ⟦α⟧ᶻ := by
      simpa [j0] using hz_1 j0
    obtain ⟨hcov_app_goal, hden_app⟩ :=
      chpredDenAppAt
        (hcov_x_upd := hcov_x_upd) (denx_upd := denx_upd)
        (hX_ty := hX_ty) (hX_func := hX_func)
        (z!_not_mem_fv_x := z!_not_mem_fv_x)
        (z_not_mem_fv_x := z_not_mem_fv_x)
        (Yfun := Yfun) (wy0 := x_1 i0)
        (z_1 j0) hz0.1 hz0.2
    obtain ⟨hφY, Dspec, hden_spec, hDspec_ty⟩ :=
      chpredDenSpecSomeAt
        (den_z_at := den_z_at) (fv_z!_spec := fv_z!_spec)
        (z_ne_z! := z_ne_z!) (x_ne_z := x_ne_z) (x_ne_z! := x_ne_z!)
        (typ_z!_spec_body := typ_z!_spec_body)
        (wy0 := x_1 i0) (hwy0_ty := hx0.1)
        (z_1 j0) hz0.1 hz0.2
    obtain ⟨Dbody, hDbody, hDbody_ty⟩ :=
      denote_and_some_bool_of_some_bool hden_app rfl hden_spec hDspec_ty
    have hnot_some :=
      denote_not_isSome_of_some_bool (hden := hDbody) (hTy := hDbody_ty)
    rw [denote, Term.abstract.go]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Matrix.head_fin_const,
      Fin.zero_eta, Fin.isValue, Option.pure_def, Option.failure_eq_none, Option.bind_eq_bind,
      Function.OfArity.uncurry, Function.FromTypes.uncurry, Term.abstract.go]
    simpa only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def,
      SMT.Term.abstract.go, Function.OfArity.uncurry, Function.FromTypes.uncurry,
      i0, j0, proof_irrel_heq] using hnot_some

private theorem chpredBodyTyOf
    {Γ : TypeContext} {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α α' : SMTType}
    (hgo_cov :
      ∀ Yfun : SMT.Dom,
        ∀ v ∈ SMT.fv (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)),
          v ∉ [z!] → (Function.update «Δ» x! (some Yfun) v).isSome = true)
    (hexists_cov :
      ∀ (Yfun W : SMT.Dom),
        RenamingContext.CoversFV
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some W))
          (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)))
    (hgo_exists :
      ∀ (Yfun : SMT.Dom)
        (w : Fin [z!].length → SMT.Dom)
        (hw : ∀ i, (w i).snd.fst = [α'][i] ∧ (w i).fst ∈ ⟦[α'][i]⟧ᶻ),
          (Term.abstract.go
              (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)).uncurry w =
            (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)).abstract
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some (w ⟨0, by simp⟩)))
              (hexists_cov Yfun (w ⟨0, by simp⟩)))
    (typ_exists :
      (AList.insert z! α' Γ) ⊢ˢ
        (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)) : SMTType.bool)
    (hbody_total :
      ∀ (Yfun : SMT.Dom)
        (x_1 : Fin [z!].length → SMT.Dom)
        (hx_1 : ∀ i, (x_1 i).snd.fst = [α'][i] ∧ (x_1 i).fst ∈ ⟦[α'][i]⟧ᶻ),
          ⟦(Term.abstract.go
              (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)).uncurry x_1⟧ˢ.isSome =
            true)
    (Yfun : SMT.Dom)
    (x_1 : Fin [z!].length → SMT.Dom)
    (hx_1 : ∀ i, (x_1 i).snd.fst = [α'][i] ∧ (x_1 i).fst ∈ ⟦[α'][i]⟧ᶻ) :
    (⟦(Term.abstract.go
        (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
        [z!]
        (Function.update «Δ» x! (some Yfun))
        (hgo_cov Yfun)).uncurry x_1⟧ˢ.get
        (hbody_total Yfun x_1 hx_1)).snd.fst =
      SMTType.bool := by
  exact chpredBodyGetTypeOf
    (Γ := Γ) (typ_exists' := typ_exists) hgo_cov hexists_cov hgo_exists hbody_total
    Yfun x_1 hx_1

set_option maxHeartbeats 1500000 in
private theorem chpredDenoteLambdaAt
    {Γ : TypeContext} {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α α' : SMTType} {p : α ⇝ α'}
    (X : SMT.Dom)
    (hX_mem : X.fst ∈ ⟦α.fun SMTType.bool⟧ᶻ)
    (hX_func : IsFunc ⟦α⟧ᶻ 𝔹 X.fst)
    (hcov_lambda_upd :
      ∀ Y : SMT.Dom,
        RenamingContext.CoversFV
          (Function.update «Δ» x! (some Y))
          ((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))))
    (hgo_cov :
      ∀ Yfun : SMT.Dom,
        ∀ v ∈ SMT.fv (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)),
          v ∉ [z!] → (Function.update «Δ» x! (some Yfun) v).isSome = true)
    (hexists_cov :
      ∀ (Yfun W : SMT.Dom),
        RenamingContext.CoversFV
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some W))
          (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)))
    (hgo_exists :
      ∀ (Yfun : SMT.Dom)
        (w : Fin [z!].length → SMT.Dom)
        (hw : ∀ i, (w i).snd.fst = [α'][i] ∧ (w i).fst ∈ ⟦[α'][i]⟧ᶻ),
          (Term.abstract.go
              (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)
            ).uncurry w =
            (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)).abstract
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some (w ⟨0, by simp⟩)))
              (hexists_cov Yfun (w ⟨0, by simp⟩)))
    (hbody_total :
      ∀ (Yfun : SMT.Dom)
        (x_1 : Fin [z!].length → SMT.Dom)
        (hx_1 : ∀ i, (x_1 i).snd.fst = [α'][i] ∧ (x_1 i).fst ∈ ⟦[α'][i]⟧ᶻ),
          ⟦(Term.abstract.go
              (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)).uncurry x_1⟧ˢ.isSome =
            true)
    (hbody_ty_of :
      ∀ (Yfun : SMT.Dom)
        (x_1 : Fin [z!].length → SMT.Dom)
        (hx_1 : ∀ i, (x_1 i).snd.fst = [α'][i] ∧ (x_1 i).fst ∈ ⟦[α'][i]⟧ᶻ),
          (⟦(Term.abstract.go
              (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)).uncurry x_1⟧ˢ.get
              (hbody_total Yfun x_1 hx_1)).snd.fst =
            SMTType.bool)
    (den_app_at :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hx₀_ty : x₀.snd.fst = α)
        (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ),
        ∃ hcov_app_goal :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              ((@ˢx) (.var z)),
          ⟦((@ˢx) (.var z)).abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              hcov_app_goal⟧ˢ =
            some ⟨(@ᶻX.fst
                    ⟨x₀.fst, by
                      simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩).1,
              SMTType.bool,
              (@ᶻX.fst
                ⟨x₀.fst, by
                  simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩).2⟩)
    (den_spec_some_at :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α')
        (hx₀_ty : x₀.snd.fst = α)
        (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ),
        ∃ hφY :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              z!_spec,
          ∃ Φ,
            ⟦z!_spec.abstract
                (Function.update
                  (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                  z (some x₀))
                hφY⟧ˢ =
              some Φ ∧
            Φ.snd.fst = SMTType.bool)
    (den_spec_true_at_cast :
      ∀ (y Yfun wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α')
        (hwy0_val : wy0.fst = y.fst)
        (hx₀_ty : x₀.snd.fst = α)
        (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ)
        (hcast_xy : x₀.fst.pair y.fst ∈ (castZF_of_path p).1),
        ∃ hφY :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              z!_spec,
          ∃ Φ,
            ⟦z!_spec.abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              hφY⟧ˢ =
            some Φ ∧
          Φ.fst = zftrue)
    (den_spec_true_implies_cast :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α')
        (hx₀_ty : x₀.snd.fst = α)
        (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ)
        {Φ : SMT.Dom}
        (hφY :
          RenamingContext.CoversFV
            (Function.update
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
              z (some x₀))
            z!_spec)
        (hdenY :
          ⟦z!_spec.abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              hφY⟧ˢ =
            some Φ)
        (htrue : Φ.fst = zftrue),
        x₀.fst.pair wy0.fst ∈ (castZF_of_path p).1)
    (den_z_exact_at :
      ∀ (x₀ : SMT.Dom)
        (hx₀_ty : x₀.snd.fst = α)
        (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ)
        {Y Φ : SMT.Dom}
        (hY_ty : Y.snd.fst = α')
        (hφY :
          RenamingContext.CoversFV
            (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
            z!_spec)
        (hdenY :
          ⟦z!_spec.abstract
              (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
              hφY⟧ˢ =
            some Φ)
        (htrue : Φ.fst = zftrue),
        x₀.fst.pair Y.fst ∈ (castZF_of_path p).1) :
    let cast : ZFSet := (castZF_of_path p).1
    let castRange : ZFSet := ZFSet.sep (fun y => ∃ x ∈ cast.Dom (castZF_of_path p).2.1, x.pair y ∈ cast) ⟦α'⟧ᶻ
    let X!zf : ZFSet :=
      λᶻ: ⟦α'⟧ᶻ → .𝔹
        | y ↦ if hy_ran : y ∈ castRange then
                 let x₀ := Classical.choose (ZFSet.mem_sep.mp hy_ran).2
                 have hx₀ : x₀ ∈ ⟦α⟧ᶻ := by
                   have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hy_ran).2
                   exact (ZFSet.mem_sep.mp dom).1
                 let hx₀_dom : x₀ ∈ X.fst.Dom := by
                   simpa [ZFSet.is_func_dom_eq hX_func] using hx₀
                 let b : {u // u ∈ 𝔹} :=
                   ZFSet.fapply X.fst (hf := ZFSet.is_func_is_pfunc hX_func) ⟨x₀, hx₀_dom⟩
                 b.1
               else zffalse
    let X! : SMT.Dom := ⟨X!zf, α'.fun SMTType.bool, by
      rw [ZFSet.mem_funs]
      apply ZFSet.lambda_isFunc
      intro y hy
      split_ifs with hy_ran
      · have hx₀ : Classical.choose (ZFSet.mem_sep.mp hy_ran).2 ∈ ⟦α⟧ᶻ := by
          have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hy_ran).2
          exact (ZFSet.mem_sep.mp dom).1
        exact ZFSet.fapply_mem_range (ZFSet.is_func_is_pfunc hX_func) (by
          rwa [ZFSet.is_func_dom_eq hX_func])
      · exact ZFSet.ZFBool.zffalse_mem_𝔹⟩
    ⟦((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))).abstract
        (Function.update «Δ» x! (some X!)) (hcov_lambda_upd X!)⟧ˢ =
      some X! := by
  let cast : ZFSet := (castZF_of_path p).1
  have hcast : IsFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ cast := (castZF_of_path p).2
  let castRange : ZFSet := ZFSet.sep (fun y => ∃ x ∈ cast.Dom hcast.1, x.pair y ∈ cast) ⟦α'⟧ᶻ
  let X!zf : ZFSet :=
    λᶻ: ⟦α'⟧ᶻ → .𝔹
      | y ↦ if hy_ran : y ∈ castRange then
               let x₀ := Classical.choose (ZFSet.mem_sep.mp hy_ran).2
               have hx₀ : x₀ ∈ ⟦α⟧ᶻ := by
                 have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hy_ran).2
                 exact (ZFSet.mem_sep.mp dom).1
               let hx₀_dom : x₀ ∈ X.fst.Dom := by
                 simpa [ZFSet.is_func_dom_eq hX_func] using hx₀
               let b : {u // u ∈ 𝔹} :=
                 ZFSet.fapply X.fst (hf := ZFSet.is_func_is_pfunc hX_func) ⟨x₀, hx₀_dom⟩
               b.1
             else zffalse
  have hX!zf_mem : X!zf ∈ ⟦α'.fun SMTType.bool⟧ᶻ := by
    rw [ZFSet.mem_funs]
    apply ZFSet.lambda_isFunc
    intro y hy
    split_ifs with hy_ran
    · have hx₀ : Classical.choose (ZFSet.mem_sep.mp hy_ran).2 ∈ ⟦α⟧ᶻ := by
        have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hy_ran).2
        exact (ZFSet.mem_sep.mp dom).1
      exact ZFSet.fapply_mem_range (ZFSet.is_func_is_pfunc hX_func) (by
        rwa [ZFSet.is_func_dom_eq hX_func])
    · exact ZFSet.ZFBool.zffalse_mem_𝔹
  let X! : SMT.Dom := ⟨X!zf, α'.fun SMTType.bool, hX!zf_mem⟩
  change
    ⟦((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))).abstract
        (Function.update «Δ» x! (some X!)) (hcov_lambda_upd X!)⟧ˢ =
      some X!
  rw [show X! = ⟨X!zf, α'.fun SMTType.bool, hX!zf_mem⟩ by rfl]
  have hcast_mem :
      X.fst.pair X!.fst ∈ (castZF_of_path p.chpred).1 := by
    rw [castZF_of_path, castZF_chpred, ZFSet.lambda_spec]
    refine ⟨hX_mem, hX!zf_mem, ?_⟩
    rw [dif_pos hX_func]
  unfold X! at hcast_mem
  rw [castZF_of_path, castZF_chpred, lambda_spec] at hcast_mem
  obtain ⟨hX, hX!zf, X!zf_eq⟩ := hcast_mem
  dsimp at X!zf_eq
  rw [mem_funs] at hX
  rw [dif_pos hX] at X!zf_eq
  let evalBody
      (Yfun : SMT.Dom)
      (x_1 : Fin [z!].length → SMT.Dom)
      (hx_1 : ∀ i, (x_1 i).snd.fst = [α'][i] ∧ (x_1 i).fst ∈ ⟦[α'][i]⟧ᶻ) :
      SMT.Dom :=
    (⟦(Term.abstract.go
        (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
        [z!]
        (Function.update «Δ» x! (some Yfun))
        (hgo_cov Yfun)).uncurry x_1⟧ˢ.get
      (hbody_total Yfun x_1 hx_1))
  have hden_lambda_X! :
      ⟦((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))).abstract
          (Function.update «Δ» x! (some X!)) (hcov_lambda_upd X!)⟧ˢ =
        some X! := by
    rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.denote]
    split_ifs with hlen_pos den_t_isSome den_t_typ_det
    · simp only [Option.pure_def, Option.some.injEq]
      dsimp [X!]
      have hbody_ty :
          (⟦(Term.abstract.go
              (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some X!))
              (hgo_cov X!)).uncurry
              (fun i => ⟨[α'][i].defaultZFSet, [α'][i], SMTType.mem_toZFSet_of_defaultZFSet⟩)⟧ˢ.get
              (den_t_isSome (fun i => ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩))).snd.fst =
            SMTType.bool := by
        let w0 : Fin [z!].length → SMT.Dom :=
          fun i => ⟨[α'][i].defaultZFSet, [α'][i], SMTType.mem_toZFSet_of_defaultZFSet⟩
        have hw0 : ∀ i, (w0 i).snd.fst = [α'][i] ∧ (w0 i).fst ∈ ⟦[α'][i]⟧ᶻ := by
          intro i
          exact ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩
        obtain ⟨D0, hden_body⟩ := Option.isSome_iff_exists.mp (den_t_isSome hw0)
        have hD0_ty : D0.snd.fst = SMTType.bool := by
          have hget_eq_body :
              (⟦(Term.abstract.go
                  (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                  [z!]
                  (Function.update «Δ» x! (some X!))
                  (hgo_cov X!)).uncurry w0⟧ˢ.get
                (hbody_total X! w0 hw0)) = D0 := by
            apply Option.get_of_eq_some
            exact hden_body
          rw [←hget_eq_body]
          exact hbody_ty_of X! w0 hw0
        have hget_eq :
            (⟦(Term.abstract.go
                (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                [z!]
                (Function.update «Δ» x! (some X!))
                (hgo_cov X!)).uncurry w0⟧ˢ.get
              (den_t_isSome hw0)) =
              (⟦(Term.abstract.go
                  (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                  [z!]
                (Function.update «Δ» x! (some X!))
                (hgo_cov X!)).uncurry w0⟧ˢ.get
                (hbody_total X! w0 hw0)) := by
          apply Eq.trans
          · apply Option.get_of_eq_some
            exact hden_body
          · symm
            apply Option.get_of_eq_some
            exact hden_body
        rw [hget_eq]
        exact hbody_ty_of X! w0 hw0
      let bodyL : ZFSet → ZFSet := fun y =>
        if hy : y.hasArity 1 ∧ ∀ i : Fin 1, y ∈ ⟦[α'][i]⟧ᶻ then
          (⟦(Term.abstract.go
              (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some X!))
              (hgo_cov X!)).uncurry
              (fun i => ⟨y, [α'][i], hy.2 i⟩)⟧ˢ.get
            (den_t_isSome (fun i => ⟨rfl, hy.2 i⟩))).fst
        else
          (⟦(Term.abstract.go
              (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some X!))
              (hgo_cov X!)).uncurry
              (fun i => ⟨[α'][i].defaultZFSet, [α'][i], SMTType.mem_toZFSet_of_defaultZFSet⟩)⟧ˢ.get
            (den_t_isSome (fun i => ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩))).snd.fst.defaultZFSet
      let bodyR : ZFSet → ZFSet := fun y =>
        if hy_ran : y ∈ castRange then
          let x₀ := Classical.choose (ZFSet.mem_sep.mp hy_ran).2
          have hx₀ : x₀ ∈ ⟦α⟧ᶻ := by
            have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hy_ran).2
            exact (ZFSet.mem_sep.mp dom).1
          let hx₀_dom : x₀ ∈ X.fst.Dom := by
            simpa [ZFSet.is_func_dom_eq hX_func] using hx₀
          let b : {u // u ∈ 𝔹} :=
            ZFSet.fapply X.fst (hf := ZFSet.is_func_is_pfunc hX_func) ⟨x₀, hx₀_dom⟩
          b.1
        else zffalse
      have hX!zf_eq :
          (⟦α'⟧ᶻ.lambda
            ⟦(⟦(Term.abstract.go
                (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                [z!]
                (Function.update «Δ» x! (some X!))
                (hgo_cov X!)).uncurry
                (fun i => ⟨[α'][i].defaultZFSet, [α'][i], SMTType.mem_toZFSet_of_defaultZFSet⟩)⟧ˢ.get
              (den_t_isSome (fun i => ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩))).snd.fst⟧ᶻ
            bodyL) = X!zf := by
        dsimp [X!zf]
        change
          (⟦α'⟧ᶻ.lambda
            ⟦(⟦(Term.abstract.go
                (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                [z!]
                (Function.update «Δ» x! (some X!))
                (hgo_cov X!)).uncurry
                (fun i => ⟨[α'][i].defaultZFSet, [α'][i], SMTType.mem_toZFSet_of_defaultZFSet⟩)⟧ˢ.get
              (den_t_isSome (fun i => ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩))).snd.fst⟧ᶻ
            bodyL) =
          (⟦α'⟧ᶻ.lambda 𝔹 bodyR)
        rw [hbody_ty]
        have hbodyL_mem : ∀ {y}, y ∈ ⟦α'⟧ᶻ → bodyL y ∈ 𝔹 := by
          intro y hy
          have hy1 := chpredUnaryTarget (α' := α') hy
          let wy : Fin [z!].length → SMT.Dom := fun i => ⟨y, [α'][i], hy1.2 i⟩
          let hwy :
              ∀ i : Fin [z!].length, (wy i).snd.fst = [α'][i] ∧ (wy i).fst ∈ ⟦[α'][i]⟧ᶻ :=
            fun i => ⟨rfl, hy1.2 i⟩
          have hbodyL_y :
              bodyL y =
                (⟦(Term.abstract.go
                    (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                    [z!]
                    (Function.update «Δ» x! (some X!))
                    (hgo_cov X!)).uncurry wy⟧ˢ.get
                  (den_t_isSome hwy)).fst := by
            dsimp [bodyL, wy, hwy]
            split_ifs with h
            · have hh : h = hy1 := Subsingleton.elim _ _
              cases hh
              rfl
            · exfalso
              exact h hy1
          rw [hbodyL_y]
          simpa [hbody_ty_of X! wy hwy] using
            ((⟦(Term.abstract.go
                (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                [z!]
                (Function.update «Δ» x! (some X!))
                (hgo_cov X!)).uncurry wy⟧ˢ.get
              (den_t_isSome hwy)).snd.snd)
        apply (ZFSet.lambda_ext_iff hbodyL_mem).2
        intro y hy
        have hy1 := chpredUnaryTarget (α' := α') hy
        let wy : Fin [z!].length → SMT.Dom := fun i => ⟨y, [α'][i], hy1.2 i⟩
        let hwy :
            ∀ i : Fin [z!].length, (wy i).snd.fst = [α'][i] ∧ (wy i).fst ∈ ⟦[α'][i]⟧ᶻ :=
          fun i => ⟨rfl, hy1.2 i⟩
        let wy0 : SMT.Dom := wy ⟨0, by simp⟩
        have hwy0_ty : wy0.snd.fst = α' := by
          simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
            Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero, wy0, wy]
        have hbodyL_y :
            bodyL y =
              (⟦(Term.abstract.go
                  (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                  [z!]
                  (Function.update «Δ» x! (some X!))
                  (hgo_cov X!)).uncurry wy⟧ˢ.get
                (den_t_isSome hwy)).fst := by
          dsimp [bodyL, wy, hwy]
          split_ifs with h
          · have hh : h = hy1 := Subsingleton.elim _ _
            cases hh
            rfl
          · exfalso
            exact h hy1
        rw [hbodyL_y]
        dsimp [bodyR]
        by_cases hy_ran : y ∈ castRange
        · simp [hy_ran]
          let x₀ := Classical.choose (ZFSet.mem_sep.mp hy_ran).2
          have hx₀ : x₀ ∈ ⟦α⟧ᶻ := by
            have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hy_ran).2
            exact (ZFSet.mem_sep.mp dom).1
          let hx₀_dom : x₀ ∈ X.fst.Dom := by
            simpa [ZFSet.is_func_dom_eq hX_func] using hx₀
          have hcast_xy : x₀.pair wy0.fst ∈ (castZF_of_path p).1 := by
            simpa [x₀, wy0, wy, cast] using (Classical.choose_spec (ZFSet.mem_sep.mp hy_ran).2).2
          have hgo_body_cov :
              ∀ v ∈ SMT.fv (((@ˢx) (.var z)) ∧ˢ z!_spec), v ∉ [z] →
                (Function.update
                  (Function.update «Δ» x! (some X!))
                  z! (some wy0) v).isSome = true := by
            intro v hv hv_not_z
            have hv' : v ∈ SMT.fv (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)) := by
              exact SMT.fv.mem_exists ⟨hv, hv_not_z⟩
            by_cases hvz! : v = z!
            · subst hvz!
              simp
            · rw [Function.update_of_ne hvz!]
              exact hgo_cov X! v hv' (by simpa [List.mem_singleton] using hvz!)
          by_cases hXx₀_true : (@ᶻX.fst ⟨x₀, hx₀_dom⟩).1 = zftrue
          · have hden_body_true :
                ⟦(Term.abstract.go
                    (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                    [z!]
                    (Function.update «Δ» x! (some X!))
                    (hgo_cov X!)).uncurry wy⟧ˢ =
                  some ⟨zftrue, SMTType.bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
              rw [hgo_exists X! wy hwy]
              rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists,
                SMT.denote]
              simp only [Option.bind_eq_bind, Option.pure_def]
              have hlen_exists : [z].length > 0 := by
                simp
              rw [SMT.denote, dite_cond_eq_true (eq_true hlen_exists)]
              split_ifs with den_exists_isSome
              · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
                  List.getElem_cons_succ, Fin.zero_eta, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
                  List.getElem_cons_zero, Fin.val_eq_zero, get.eq_1, forall_const, Option.pure_def,
                  overloadUnaryOp, id_eq, Option.failure_eq_none, Option.bind_some, Fin.foldl_zero,
                  Option.some.injEq, PSigma.mk.injEq]
                obtain ⟨hcov_app_goal, hden_app⟩ :=
                  den_app_at X! wy0 ⟨x₀, α, hx₀⟩ rfl hx₀
                obtain ⟨hφY, Dspec, hden_spec, hDspec_ty⟩ :=
                  den_spec_some_at X! wy0 ⟨x₀, α, hx₀⟩ hwy0_ty rfl hx₀
                obtain ⟨_, Φtrue, hden_spec_true, hΦtrue⟩ :=
                  den_spec_true_at_cast wy0 X! wy0 ⟨x₀, α, hx₀⟩ hwy0_ty rfl rfl hx₀ hcast_xy
                have hDspec_true : Dspec.fst = zftrue := by
                  have hEq : Dspec = Φtrue := by
                    rwa [hden_spec, Option.some_inj] at hden_spec_true
                  simpa [hEq] using hΦtrue
                have hcov_body_goal :
                    RenamingContext.CoversFV
                      (Function.update
                        (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                        z (some ⟨x₀, α, hx₀⟩))
                      (((@ˢx) (.var z)) ∧ˢ z!_spec) := by
                  intro v hv
                  simp only [fv, List.mem_append] at hv
                  rcases hv with hvapp | hvspec
                  · have hvapp' : v ∈ SMT.fv x ∨ v ∈ SMT.fv (.var z) := by
                      simpa [fv] using hvapp
                    exact hcov_app_goal v (SMT.fv.mem_app hvapp')
                  · exact hφY v hvspec
                have hden_and_true :
                    ⟦(((@ˢx) (.var z)) ∧ˢ z!_spec).abstract
                        (Function.update
                          (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                          z (some ⟨x₀, α, hx₀⟩))
                        hcov_body_goal⟧ˢ =
                      some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                  rw [Term.abstract, denote_and_eq_zftrue_of_some_zftrue hden_app rfl hXx₀_true hden_spec hDspec_ty hDspec_true]
                have hden_not_false :
                    ⟦¬ˢ'
                        (((@ˢx) (.var z)) ∧ˢ z!_spec).abstract
                          (Function.update
                            (Function.update (Function.update «Δ» x! (some X!)) z! (some wy0))
                            z (some ⟨x₀, α, hx₀⟩))
                          hcov_body_goal⟧ˢ =
                      some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                  exact denote_not_eq_zffalse_of_some_zftrue hden_and_true rfl rfl
                let w : Fin [z].length → SMT.Dom := fun _ => ⟨x₀, α, hx₀⟩
                have hw :
                    ∀ i : Fin [z].length, (w i).snd.fst = [α][i] ∧ (w i).fst ∈ ⟦[α][i]⟧ᶻ := by
                  intro i
                  have hi0 : i = ⟨0, by simp⟩ := by
                    apply Fin.ext
                    simp
                  cases hi0
                  exact ⟨rfl, hx₀⟩
                have hget_not_false :
                    (⟦¬ˢ'
                        (Term.abstract.go
                            (((@ˢx) (.var z)) ∧ˢ z!_spec)
                            [z]
                            (Function.update
                              (Function.update «Δ» x! (some X!))
                              z! (some wy0))
                            hgo_body_cov).uncurry
                        w⟧ˢ.get
                      (den_exists_isSome hw)) =
                      ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                  apply Option.get_of_eq_some
                  simpa only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind,
                    Option.pure_def, SMT.Term.abstract.go, Function.OfArity.uncurry,
                    Function.FromTypes.uncurry, proof_irrel_heq, w] using hden_not_false
                have hsInter_false :
                    (⋂₀
                      ZFSet.sep
                        (fun y =>
                          ∃ x_1 ∈ ⟦α⟧ᶻ,
                            y =
                              if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ then
                                let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α, h.2⟩
                                (⟦¬ˢ'
                                      (Term.abstract.go
                                          (((@ˢx) (.var z)) ∧ˢ z!_spec)
                                          [z]
                                          (Function.update
                                            (Function.update «Δ» x! (some X!))
                                            z! (some (wy ⟨0, by simp⟩)))
                                          hgo_body_cov).uncurry
                                      w⟧ˢ.get
                                  (den_exists_isSome (by
                                    intro i
                                    have hi0 : i = ⟨0, by simp⟩ := by
                                      apply Fin.ext
                                      simp
                                    cases hi0
                                    exact ⟨rfl, h.2⟩))).fst
                              else zffalse)
                        𝔹 : ZFSet) = zffalse := by
                  apply sInter_sep_eq_empty_of_exists_eq_empty
                  refine ⟨x₀, hx₀, ?_⟩
                  have hx₀_cast : x₀.hasArity 1 ∧ x₀ ∈ ⟦α⟧ᶻ := by
                    constructor
                    · exact (chpredUnaryTarget (α' := α) hx₀).1
                    · exact hx₀
                  rw [dif_pos hx₀_cast]
                  exact congrArg (fun D => D.1) hget_not_false
                have hbool :
                    (⟨⋂₀
                        ZFSet.sep
                          (fun y =>
                            ∃ x_1 ∈ ⟦α⟧ᶻ,
                              y =
                                if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ then
                                  let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α, h.2⟩
                                  (⟦¬ˢ'
                                        (Term.abstract.go
                                            (((@ˢx) (.var z)) ∧ˢ z!_spec)
                                            [z]
                                            (Function.update
                                              (Function.update «Δ» x! (some X!))
                                              z! (some (wy ⟨0, by simp⟩)))
                                            hgo_body_cov).uncurry
                                        w⟧ˢ.get
                                    (den_exists_isSome (by
                                      intro i
                                      have hi0 : i = ⟨0, by simp⟩ := by
                                        apply Fin.ext
                                        simp
                                      cases hi0
                                      exact ⟨rfl, h.2⟩))).fst
                                else zffalse)
                          𝔹,
                      ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩ : ZFSet.ZFBool) = ⊥ := by
                  rw [Subtype.mk.injEq]
                  exact hsInter_false
                have hnot_bool := congrArg ZFSet.ZFBool.not hbool
                and_intros
                · rw [dif_pos (ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id))]
                  rw [ZFSet.ZFBool.not_false_eq_true] at hnot_bool
                  exact congrArg (fun b : ZFSet.ZFBool => (b : ZFSet)) hnot_bool
                · congr
                  · funext τ
                    apply congrArg (fun z => z ∈ ⟦τ⟧ᶻ)
                    rw [dif_pos (ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id))]
                    rw [ZFSet.ZFBool.not_false_eq_true] at hnot_bool
                    simpa using congrArg (fun b : ZFSet.ZFBool => (b : ZFSet)) hnot_bool
                  · apply proof_irrel_heq
              · exfalso
                apply den_exists_isSome
                intro z_1 hz_1
                let j0 : Fin [z].length := ⟨0, by simp⟩
                have hz0 : (z_1 j0).snd.fst = α ∧ (z_1 j0).fst ∈ ⟦α⟧ᶻ := by
                  simpa [j0] using hz_1 j0
                obtain ⟨hcov_app_goal, hden_app⟩ :=
                  den_app_at X! wy0 (z_1 j0) hz0.1 hz0.2
                obtain ⟨hφY, Dspec, hden_spec, hDspec_ty⟩ :=
                  den_spec_some_at X! wy0 (z_1 j0) hwy0_ty hz0.1 hz0.2
                obtain ⟨Dbody, hDbody, hDbody_ty⟩ :=
                  denote_and_some_bool_of_some_bool hden_app rfl hden_spec hDspec_ty
                have hnot_some :=
                  denote_not_isSome_of_some_bool (hden := hDbody) (hTy := hDbody_ty)
                rw [denote, Term.abstract.go]
                simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Matrix.head_fin_const,
                  Fin.zero_eta, Fin.isValue, Option.pure_def, Option.failure_eq_none,
                  Option.bind_eq_bind, Function.OfArity.uncurry, Function.FromTypes.uncurry,
                  Term.abstract.go]
                simpa only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def,
                  SMT.Term.abstract.go, Function.OfArity.uncurry, Function.FromTypes.uncurry,
                  j0, proof_irrel_heq] using hnot_some
            conv =>
              enter [1, 1, 1]
              erw [hden_body_true]
            -- have hget_body := Option.get_of_eq_some hden_body_true
            symm
            dsimp
            unfold x₀ hx₀_dom at hXx₀_true
            rw [←hXx₀_true]
            congr
            simp only [mem_sep]
          · have hXx₀_false : (@ᶻX.fst ⟨x₀, hx₀_dom⟩).1 = zffalse := by
              have hXx₀_bool : (@ᶻX.fst ⟨x₀, hx₀_dom⟩).1 ∈ 𝔹 := (@ᶻX.fst ⟨x₀, hx₀_dom⟩).2
              rw [ZFSet.ZFBool.mem_𝔹_iff] at hXx₀_bool
              rcases hXx₀_bool with hfalse | htrue
              · exact hfalse
              · exfalso
                exact hXx₀_true htrue
            have hden_body_false :
                ⟦(Term.abstract.go
                    (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                    [z!]
                    (Function.update «Δ» x! (some X!))
                    (hgo_cov X!)).uncurry wy⟧ˢ =
                  some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
              rw [hgo_exists X! wy hwy]
              rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists,
                SMT.denote]
              simp only [Option.bind_eq_bind, Option.pure_def]
              have hlen_exists : [z].length > 0 := hlen_pos
              rw [SMT.denote, dite_cond_eq_true (eq_true hlen_exists)]
              split_ifs with den_exists_isSome
              · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
                  List.getElem_cons_succ, Fin.zero_eta, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
                  List.getElem_cons_zero, Fin.val_eq_zero, get.eq_1, forall_const, Option.pure_def,
                  overloadUnaryOp, id_eq, Option.failure_eq_none, Option.bind_some, Fin.foldl_zero,
                  Option.some.injEq, PSigma.mk.injEq]
                have hsInter_true :
                    (⋂₀
                      ZFSet.sep
                        (fun y =>
                          ∃ x_1 ∈ ⟦α⟧ᶻ,
                            y =
                              if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ then
                                let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α, h.2⟩
                                (⟦¬ˢ'
                                      (Term.abstract.go
                                          (((@ˢx) (.var z)) ∧ˢ z!_spec)
                                          [z]
                                          (Function.update
                                            (Function.update «Δ» x! (some X!))
                                            z! (some (wy ⟨0, by simp⟩)))
                                          hgo_body_cov).uncurry
                                      w⟧ˢ.get
                                  (den_exists_isSome (by
                                    intro i
                                    have hi0 : i = ⟨0, by simp⟩ := by
                                      apply Fin.ext
                                      simp
                                    cases hi0
                                    exact ⟨rfl, h.2⟩))).fst
                              else zffalse)
                        𝔹 : ZFSet) = zftrue := by
                  apply sInter_sep_eq_zftrue_of_forall_eq_zftrue
                  · exact ⟨α.defaultZFSet, SMTType.mem_toZFSet_of_defaultZFSet⟩
                  · intro x_1 hx_1
                    have hx1 := chpredUnaryTarget (α' := α) hx_1
                    have hx_cast : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ := by
                      constructor
                      · exact hx1.1
                      · exact hx_1
                    split_ifs
                    · obtain ⟨hcov_app_goal, hden_app⟩ :=
                        den_app_at X! wy0 ⟨x_1, α, hx_1⟩ rfl hx_1
                      obtain ⟨hφY, Dspec, hden_spec, hDspec_ty⟩ :=
                        den_spec_some_at X! wy0 ⟨x_1, α, hx_1⟩ hwy0_ty rfl hx_1
                      have hDspec_bool : Dspec.fst ∈ 𝔹 := by
                        simpa [hDspec_ty] using Dspec.snd.snd
                      rw [ZFSet.ZFBool.mem_𝔹_iff] at hDspec_bool
                      have hcov_body_goal :
                          RenamingContext.CoversFV
                            (Function.update
                              (Function.update
                                (Function.update «Δ» x! (some X!))
                                z! (some wy0))
                              z (some ⟨x_1, α, hx_1⟩))
                            (((@ˢx) (.var z)) ∧ˢ z!_spec) := by
                        intro v hv
                        simp only [fv, List.mem_append] at hv
                        rcases hv with hvapp | hvspec
                        · have hvapp' : v ∈ SMT.fv x ∨ v ∈ SMT.fv (.var z) := by
                            simpa [fv] using hvapp
                          exact hcov_app_goal v (SMT.fv.mem_app hvapp')
                        · exact hφY v hvspec
                      rcases hDspec_bool with hDspec_false | hDspec_true
                      · have hden_and_false :
                          ⟦(((@ˢx) (.var z)) ∧ˢ z!_spec).abstract
                              (Function.update
                                (Function.update
                                  (Function.update «Δ» x! (some X!))
                                  z! (some wy0))
                                z (some ⟨x_1, α, hx_1⟩))
                              hcov_body_goal⟧ˢ =
                            some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                          simpa only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind,
                            Option.pure_def, SMT.Term.abstract.go, Function.OfArity.uncurry,
                            Function.FromTypes.uncurry, proof_irrel_heq] using
                            (denote_and_eq_zffalse_of_some_zffalse_right
                              hden_app rfl hden_spec hDspec_ty hDspec_false)
                        have hden_not_true :
                            ⟦¬ˢ'
                                (((@ˢx) (.var z)) ∧ˢ z!_spec).abstract
                                  (Function.update
                                    (Function.update
                                      (Function.update «Δ» x! (some X!))
                                      z! (some wy0))
                                    z (some ⟨x_1, α, hx_1⟩))
                                  hcov_body_goal⟧ˢ =
                              some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                          exact denote_not_eq_zftrue_of_some_zffalse hden_and_false rfl rfl
                        let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α, hx_1⟩
                        have hw :
                            ∀ i : Fin [z].length, (w i).snd.fst = [α][i] ∧ (w i).fst ∈ ⟦[α][i]⟧ᶻ := by
                          intro i
                          have hi0 : i = ⟨0, by simp⟩ := by
                            apply Fin.ext
                            simp
                          cases hi0
                          exact ⟨rfl, hx_1⟩
                        have hget_not :
                            (⟦¬ˢ'
                                (Term.abstract.go
                                    (((@ˢx) (.var z)) ∧ˢ z!_spec)
                                    [z]
                                    (Function.update
                                      (Function.update «Δ» x! (some X!))
                                      z! (some wy0))
                                    hgo_body_cov).uncurry
                                w⟧ˢ.get
                              (den_exists_isSome hw)) =
                              ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                          apply Option.get_of_eq_some
                          simpa only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind,
                            Option.pure_def, SMT.Term.abstract.go, Function.OfArity.uncurry,
                            Function.FromTypes.uncurry, proof_irrel_heq, w] using hden_not_true
                        exact congrArg (fun D => D.1) hget_not
                      · have hx1_dom_cast : x_1 ∈ cast.Dom hcast.1 := by
                          simpa [ZFSet.is_func_dom_eq hcast] using hx_1
                        have hx₀_dom_cast : x₀ ∈ cast.Dom hcast.1 := by
                          simpa [ZFSet.is_func_dom_eq hcast] using hx₀
                        have hcast_x1y : @ᶻcast ⟨x_1, hx1_dom_cast⟩ = wy0.fst := by
                          have := fapply.of_pair (is_func_is_pfunc hcast) <| den_spec_true_implies_cast X! wy0 ⟨x_1, α, hx_1⟩ hwy0_ty rfl hx_1 hφY hden_spec hDspec_true
                          simpa only [Subtype.ext_iff] using this
                        have hcast_x₀y : @ᶻcast ⟨x₀, hx₀_dom_cast⟩ = wy0.fst := by
                          have := fapply.of_pair (is_func_is_pfunc hcast) hcast_xy
                          simpa only [Subtype.ext_iff] using this
                        have hx1_eq_x₀ : x_1 = x₀ := by
                          rw [←hcast_x1y, ←Subtype.ext_iff] at hcast_x₀y
                          have := IsInjective.apply_inj hcast (castZF_of_path_injective p) hcast_x₀y
                          symm
                          simpa only [Subtype.mk.injEq] using this
                        have hden_and_false :
                            ⟦(((@ˢx) (.var z)) ∧ˢ z!_spec).abstract
                                (Function.update
                                  (Function.update
                                    (Function.update «Δ» x! (some X!))
                                    z! (some wy0))
                                  z (some ⟨x_1, α, hx_1⟩))
                                hcov_body_goal⟧ˢ =
                              some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                          have := denote_and_eq_zffalse_of_some_zffalse_left hden_app rfl (by simpa only [hx1_eq_x₀] using hXx₀_false) hden_spec hDspec_ty
                          rw [Term.abstract, this]
                        have hden_not_true :
                            ⟦¬ˢ'
                                (((@ˢx) (.var z)) ∧ˢ z!_spec).abstract
                                  (Function.update
                                    (Function.update
                                      (Function.update «Δ» x! (some X!))
                                      z! (some wy0))
                                    z (some ⟨x_1, α, hx_1⟩))
                                  hcov_body_goal⟧ˢ =
                              some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                          exact denote_not_eq_zftrue_of_some_zffalse hden_and_false rfl rfl
                        let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α, hx_1⟩
                        have hw :
                            ∀ i : Fin [z].length, (w i).snd.fst = [α][i] ∧ (w i).fst ∈ ⟦[α][i]⟧ᶻ := by
                          intro i
                          have hi0 : i = ⟨0, by simp⟩ := by
                            apply Fin.ext
                            simp
                          cases hi0
                          exact ⟨rfl, hx_1⟩
                        have hget_not :
                            (⟦¬ˢ'
                                (Term.abstract.go
                                    (((@ˢx) (.var z)) ∧ˢ z!_spec)
                                    [z]
                                    (Function.update
                                      (Function.update «Δ» x! (some X!))
                                      z! (some wy0))
                                    hgo_body_cov).uncurry
                                w⟧ˢ.get
                              (den_exists_isSome hw)) =
                              ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                          apply Option.get_of_eq_some
                          simpa only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind,
                            Option.pure_def, SMT.Term.abstract.go, Function.OfArity.uncurry,
                            Function.FromTypes.uncurry, proof_irrel_heq, w] using hden_not_true
                        exact congrArg (fun D => D.1) hget_not
                have hbool :
                    (⟨⋂₀
                        ZFSet.sep
                          (fun y =>
                            ∃ x_1 ∈ ⟦α⟧ᶻ,
                              y =
                                if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ then
                                  let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α, h.2⟩
                                  (⟦¬ˢ'
                                        (Term.abstract.go
                                            (((@ˢx) (.var z)) ∧ˢ z!_spec)
                                            [z]
                                            (Function.update
                                              (Function.update «Δ» x! (some X!))
                                              z! (some (wy ⟨0, by simp⟩)))
                                            hgo_body_cov).uncurry
                                        w⟧ˢ.get
                                    (den_exists_isSome (by
                                      intro i
                                      have hi0 : i = ⟨0, by simp⟩ := by
                                        apply Fin.ext
                                        simp
                                      cases hi0
                                      exact ⟨rfl, h.2⟩))).fst
                                else zffalse)
                          𝔹,
                      ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩ : ZFSet.ZFBool) = ⊤ := by
                  rw [Subtype.mk.injEq]
                  exact hsInter_true
                have hnot_bool := congrArg ZFSet.ZFBool.not hbool
                and_intros
                · rw [dif_pos (ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id))]
                  rw [ZFSet.ZFBool.not_true_eq_false] at hnot_bool
                  exact congrArg (fun b : ZFSet.ZFBool => (b : ZFSet)) hnot_bool
                · congr
                  · funext τ
                    apply congrArg (fun z => z ∈ ⟦τ⟧ᶻ)
                    rw [dif_pos (ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id))]
                    rw [ZFSet.ZFBool.not_true_eq_false] at hnot_bool
                    simpa using congrArg (fun b : ZFSet.ZFBool => (b : ZFSet)) hnot_bool
                  · apply proof_irrel_heq
              · exfalso
                apply den_exists_isSome
                intro z_1 hz_1
                let j0 : Fin [z].length := ⟨0, by simp⟩
                have hz0 : (z_1 j0).snd.fst = α ∧ (z_1 j0).fst ∈ ⟦α⟧ᶻ := by
                  simpa [j0] using hz_1 j0
                obtain ⟨hcov_app_goal, hden_app⟩ :=
                  den_app_at X! wy0 (z_1 j0) hz0.1 hz0.2
                obtain ⟨hφY, Dspec, hden_spec, hDspec_ty⟩ :=
                  den_spec_some_at X! wy0 (z_1 j0) hwy0_ty hz0.1 hz0.2
                obtain ⟨Dbody, hDbody, hDbody_ty⟩ :=
                  denote_and_some_bool_of_some_bool hden_app rfl hden_spec hDspec_ty
                have hnot_some :=
                  denote_not_isSome_of_some_bool (hden := hDbody) (hTy := hDbody_ty)
                rw [denote, Term.abstract.go]
                simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Matrix.head_fin_const,
                  Fin.zero_eta, Fin.isValue, Option.pure_def, Option.failure_eq_none,
                  Option.bind_eq_bind, Function.OfArity.uncurry, Function.FromTypes.uncurry,
                  Term.abstract.go]
                simpa [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def,
                  SMT.Term.abstract.go, Function.OfArity.uncurry, Function.FromTypes.uncurry,
                  j0, proof_irrel_heq] using hnot_some
            -- have hget_body := Option.get_of_eq_some hden_body_false
            conv =>
              enter [1, 1, 1]
              erw [hden_body_false]
            dsimp
            symm
            simp only [x₀] at hXx₀_false
            rw [←hXx₀_false]
            congr
            simp only [mem_sep]
        · simp only [hy_ran, ↓reduceDIte]
          have hden_body_false :
              ⟦(Term.abstract.go
                  (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                  [z!]
                  (Function.update «Δ» x! (some X!))
                  (hgo_cov X!)).uncurry wy⟧ˢ =
                some ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
            rw [hgo_exists X! wy hwy]
            rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.PHOAS.Term.exists,
              SMT.denote]
            simp only [Option.bind_eq_bind, Option.pure_def]
            have hlen_exists : [z].length > 0 := by
              simp
            rw [SMT.denote, dite_cond_eq_true (eq_true hlen_exists)]
            split_ifs with den_exists_isSome
            · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one,
              List.getElem_cons_succ, Fin.zero_eta, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
              List.getElem_cons_zero, Fin.val_eq_zero, get.eq_1, forall_const, Option.pure_def,
              overloadUnaryOp, id_eq, Option.failure_eq_none, Option.bind_some, Fin.foldl_zero,
              Option.some.injEq, PSigma.mk.injEq]
              have hgo_body_cov :
                  ∀ v ∈ SMT.fv (((@ˢx) (.var z)) ∧ˢ z!_spec), v ∉ [z] →
                    (Function.update
                      (Function.update «Δ» x! (some X!))
                      z! (some wy0) v).isSome = true := by
                intro v hv hv_not_z
                have hv' : v ∈ SMT.fv (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)) := by
                  exact SMT.fv.mem_exists ⟨hv, hv_not_z⟩
                by_cases hvz! : v = z!
                · subst hvz!
                  simp
                · rw [Function.update_of_ne hvz!]
                  exact hgo_cov X! v hv' (by simpa [List.mem_singleton] using hvz!)
              have hsInter_true :
                  (⋂₀
                    ZFSet.sep
                      (fun y =>
                        ∃ x_1 ∈ ⟦α⟧ᶻ,
                          y =
                            if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ then
                              let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α, h.2⟩
                              (⟦¬ˢ'
                                    (Term.abstract.go
                                        (((@ˢx) (.var z)) ∧ˢ z!_spec)
                                        [z]
                                        (Function.update
                                          (Function.update «Δ» x! (some X!))
                                          z! (some (wy ⟨0, by simp⟩)))
                                        hgo_body_cov).uncurry
                                    w⟧ˢ.get
                                (den_exists_isSome (by
                                  intro i
                                  have hi0 : i = ⟨0, by simp⟩ := by
                                    apply Fin.ext
                                    simp
                                  cases hi0
                                  exact ⟨rfl, h.2⟩))).fst
                            else zffalse)
                      𝔹 : ZFSet) = zftrue := by
                apply sInter_sep_eq_zftrue_of_forall_eq_zftrue
                · exact ⟨α.defaultZFSet, SMTType.mem_toZFSet_of_defaultZFSet⟩
                · intro x_1 hx_1
                  have hx1 := chpredUnaryTarget (α' := α) hx_1
                  have hx_cast : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ := by
                    constructor
                    · exact hx1.1
                    · exact hx_1
                  split_ifs
                  · obtain ⟨hcov_app_goal, hden_app⟩ :=
                      den_app_at X! wy0 ⟨x_1, α, hx_1⟩ rfl hx_1
                    obtain ⟨hφY, Dspec, hden_spec, hDspec_ty⟩ :=
                      den_spec_some_at X! wy0 ⟨x_1, α, hx_1⟩ hwy0_ty rfl hx_1
                    have hDspec_bool : Dspec.fst ∈ 𝔹 := by
                      simpa [hDspec_ty] using Dspec.snd.snd
                    rw [ZFSet.ZFBool.mem_𝔹_iff] at hDspec_bool
                    have hDspec_false : Dspec.fst = zffalse := by
                      rcases hDspec_bool with hDspec_false | hDspec_true
                      · exact hDspec_false
                      · exfalso
                        have hy_ran' : y ∈ castRange := by
                          apply ZFSet.mem_sep.mpr
                          constructor
                          · exact hy
                          · refine ⟨x_1, ?_, ?_⟩
                            · simpa [ZFSet.is_func_dom_eq hcast] using hx_1
                            · simpa [wy0, wy] using
                                (den_spec_true_implies_cast X! wy0 ⟨x_1, α, hx_1⟩
                                  hwy0_ty rfl hx_1 hφY hden_spec hDspec_true)
                        exact hy_ran hy_ran'
                    have hcov_body_goal :
                        RenamingContext.CoversFV
                          (Function.update
                            (Function.update
                              (Function.update «Δ» x! (some X!))
                              z! (some wy0))
                            z (some ⟨x_1, α, hx_1⟩))
                          (((@ˢx) (.var z)) ∧ˢ z!_spec) := by
                      intro v hv
                      simp only [fv, List.mem_append] at hv
                      rcases hv with hvapp | hvspec
                      · have hvapp' : v ∈ SMT.fv x ∨ v ∈ SMT.fv (.var z) := by
                          simpa [fv] using hvapp
                        exact hcov_app_goal v (SMT.fv.mem_app hvapp')
                      · exact hφY v hvspec
                    have hden_and_false :
                        ⟦(((@ˢx) (.var z)) ∧ˢ z!_spec).abstract
                            (Function.update
                              (Function.update
                                (Function.update «Δ» x! (some X!))
                                z! (some wy0))
                              z (some ⟨x_1, α, hx_1⟩))
                            hcov_body_goal⟧ˢ =
                          some ⟨zffalse, .bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
                      simpa [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind,
                        Option.pure_def, SMT.Term.abstract.go, Function.OfArity.uncurry,
                        Function.FromTypes.uncurry, proof_irrel_heq] using
                        (denote_and_eq_zffalse_of_some_zffalse_right
                          hden_app rfl hden_spec hDspec_ty hDspec_false)
                    have hden_not_true :
                        ⟦¬ˢ'
                            (((@ˢx) (.var z)) ∧ˢ z!_spec).abstract
                              (Function.update
                                (Function.update
                                  (Function.update «Δ» x! (some X!))
                                  z! (some wy0))
                                z (some ⟨x_1, α, hx_1⟩))
                              hcov_body_goal⟧ˢ =
                          some ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                      exact denote_not_eq_zftrue_of_some_zffalse hden_and_false rfl rfl
                    let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α, hx_1⟩
                    have hw :
                        ∀ i : Fin [z].length, (w i).snd.fst = [α][i] ∧ (w i).fst ∈ ⟦[α][i]⟧ᶻ := by
                      intro i
                      have hi0 : i = ⟨0, by simp⟩ := by
                        apply Fin.ext
                        simp
                      cases hi0
                      exact ⟨rfl, hx_1⟩
                    have hget_not :
                        (⟦¬ˢ'
                            (Term.abstract.go
                                (((@ˢx) (.var z)) ∧ˢ z!_spec)
                                [z]
                                (Function.update
                                  (Function.update «Δ» x! (some X!))
                                  z! (some wy0))
                                hgo_body_cov).uncurry
                            w⟧ˢ.get
                          (den_exists_isSome hw)) =
                          ⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ := by
                      apply Option.get_of_eq_some
                      simp only [Term.abstract.go, Function.OfArity.uncurry, Function.FromTypes.uncurry]
                      erw [hden_not_true]
                    dsimp
                    erw [hget_not]
              have hbool :
                  (⟨⋂₀
                      ZFSet.sep
                        (fun y =>
                          ∃ x_1 ∈ ⟦α⟧ᶻ,
                            y =
                              if h : x_1.hasArity 1 ∧ x_1 ∈ ⟦α⟧ᶻ then
                                let w : Fin [z].length → SMT.Dom := fun _ => ⟨x_1, α, h.2⟩
                                (⟦¬ˢ'
                                      (Term.abstract.go
                                          (((@ˢx) (.var z)) ∧ˢ z!_spec)
                                          [z]
                                          (Function.update
                                            (Function.update «Δ» x! (some X!))
                                            z! (some (wy ⟨0, by simp⟩)))
                                          hgo_body_cov).uncurry
                                      w⟧ˢ.get
                                  (den_exists_isSome (by
                                    intro i
                                    have hi0 : i = ⟨0, by simp⟩ := by
                                      apply Fin.ext
                                      simp
                                    cases hi0
                                    exact ⟨rfl, h.2⟩))).fst
                              else zffalse)
                        𝔹,
                    ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id)⟩ : ZFSet.ZFBool) = ⊤ := by
                rw [Subtype.mk.injEq]
                exact hsInter_true
              have hnot_bool := congrArg ZFSet.ZFBool.not hbool
              and_intros
              · rw [dif_pos (ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id))]
                rw [ZFSet.ZFBool.not_true_eq_false] at hnot_bool
                exact congrArg (fun b : ZFSet.ZFBool => (b : ZFSet)) hnot_bool
              · congr
                · funext τ
                  apply congrArg (fun z => z ∈ ⟦τ⟧ᶻ)
                  rw [dif_pos (ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 (fun _ ↦ id))]
                  rw [ZFSet.ZFBool.not_true_eq_false] at hnot_bool
                  simpa using congrArg (fun b : ZFSet.ZFBool => (b : ZFSet)) hnot_bool
                · apply proof_irrel_heq
            · exfalso
              apply den_exists_isSome
              intro z_1 hz_1
              let j0 : Fin [z].length := ⟨0, by simp⟩
              have hz0 : (z_1 j0).snd.fst = α ∧ (z_1 j0).fst ∈ ⟦α⟧ᶻ := by
                simpa [j0] using hz_1 j0
              obtain ⟨hcov_app_goal, hden_app⟩ :=
                den_app_at X! wy0 (z_1 j0) hz0.1 hz0.2
              obtain ⟨hφY, Dspec, hden_spec, hDspec_ty⟩ :=
                den_spec_some_at X! wy0 (z_1 j0) hwy0_ty hz0.1 hz0.2
              obtain ⟨Dbody, hDbody, hDbody_ty⟩ :=
                denote_and_some_bool_of_some_bool hden_app rfl hden_spec hDspec_ty
              have hnot_some :=
                denote_not_isSome_of_some_bool (hden := hDbody) (hTy := hDbody_ty)
              rw [denote, Term.abstract.go]
              simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Matrix.head_fin_const,
                Fin.zero_eta, Fin.isValue, Option.pure_def, Option.failure_eq_none,
                Option.bind_eq_bind, Function.OfArity.uncurry, Function.FromTypes.uncurry,
                Term.abstract.go]
              obtain ⟨Dbody, τDbody, hDbody⟩ := Dbody
              obtain rfl := hDbody_ty
              conv =>
                enter [1, 1, 1]
                erw [Term.abstract, hDbody]
              rw [Option.bind_some]
              rfl
          have hget_body :
              (⟦(Term.abstract.go
                  (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                  [z!]
                  (Function.update «Δ» x! (some X!))
                  (hgo_cov X!)).uncurry wy⟧ˢ.get
                (den_t_isSome hwy)) =
                ⟨zffalse, SMTType.bool, ZFSet.ZFBool.zffalse_mem_𝔹⟩ := by
            apply Option.get_of_eq_some
            exact hden_body_false
          exact congrArg (fun D => D.1) hget_body
      apply PSigma.ext
      · exact hX!zf_eq
      · simp only [List.getElem_singleton, Fin.foldr_zero]
        generalize hγ :
            (⟦(Term.abstract.go
                (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                [z!]
                (Function.update «Δ» x! (some X!))
                (hgo_cov X!)).uncurry
                (fun i => ⟨[α'][i].defaultZFSet, [α'][i], SMTType.mem_toZFSet_of_defaultZFSet⟩)⟧ˢ.get
              (den_t_isSome (fun i => ⟨rfl, SMTType.mem_toZFSet_of_defaultZFSet⟩))).snd.fst = γ at *
        cases hbody_ty
        conv =>
          enter [1, 1, 2]
          erw [hγ]
        congr
        · funext τ
          simp only [List.getElem_singleton, Fin.foldr_zero, Fin.val_eq_zero,
            List.getElem_cons_zero, forall_const, eq_iff_iff]
          conv =>
            enter [1, 2, 2, 1]
            erw [hγ]
          rw [←propext_iff]
          apply congrArg (fun z => z ∈ ⟦τ⟧ᶻ)
          conv_rhs => erw [←hX!zf_eq]
          congr
          unfold bodyL
          simp only [Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero, forall_const,
            List.length_cons, List.length_nil, Nat.reduceAdd]
          congr
        · apply proof_irrel_heq
    · exfalso
      apply den_t_typ_det
      intro x_1 y_1 hx_1 hy_1
      rw [hbody_ty_of X! x_1 hx_1, hbody_ty_of X! y_1 hy_1]
    · exfalso
      exact den_t_isSome (fun {x_1} hx_1 => hbody_total X! x_1 hx_1)
    · exfalso
      exact hlen_pos (Nat.zero_lt_succ 0)
  exact hden_lambda_X!

private theorem chpredLambdaWitness
    {Γ : TypeContext} {«Δ» : RenamingContext.Context} {x z!_spec : Term}
    {x! z z! : 𝒱} {α α' : SMTType} {p : α ⇝ α'}
    (X : SMT.Dom)
    (hX_mem : X.fst ∈ ⟦α.fun SMTType.bool⟧ᶻ)
    (hX_func : IsFunc ⟦α⟧ᶻ 𝔹 X.fst)
    (hcov_lambda_upd :
      ∀ Y : SMT.Dom,
        RenamingContext.CoversFV
          (Function.update «Δ» x! (some Y))
          ((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))))
    (hgo_cov :
      ∀ Yfun : SMT.Dom,
        ∀ v ∈ SMT.fv (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)),
          v ∉ [z!] → (Function.update «Δ» x! (some Yfun) v).isSome = true)
    (hexists_cov :
      ∀ (Yfun W : SMT.Dom),
        RenamingContext.CoversFV
          (Function.update (Function.update «Δ» x! (some Yfun)) z! (some W))
          (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)))
    (hgo_exists :
      ∀ (Yfun : SMT.Dom)
        (w : Fin [z!].length → SMT.Dom)
        (hw : ∀ i, (w i).snd.fst = [α'][i] ∧ (w i).fst ∈ ⟦[α'][i]⟧ᶻ),
          (Term.abstract.go
              (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)
            ).uncurry w =
            (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)).abstract
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some (w ⟨0, by simp⟩)))
              (hexists_cov Yfun (w ⟨0, by simp⟩)))
    (hbody_total :
      ∀ (Yfun : SMT.Dom)
        (x_1 : Fin [z!].length → SMT.Dom)
        (hx_1 : ∀ i, (x_1 i).snd.fst = [α'][i] ∧ (x_1 i).fst ∈ ⟦[α'][i]⟧ᶻ),
          ⟦(Term.abstract.go
              (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)).uncurry x_1⟧ˢ.isSome =
            true)
    (hbody_ty_of :
      ∀ (Yfun : SMT.Dom)
        (x_1 : Fin [z!].length → SMT.Dom)
        (hx_1 : ∀ i, (x_1 i).snd.fst = [α'][i] ∧ (x_1 i).fst ∈ ⟦[α'][i]⟧ᶻ),
          (⟦(Term.abstract.go
              (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
              [z!]
              (Function.update «Δ» x! (some Yfun))
              (hgo_cov Yfun)).uncurry x_1⟧ˢ.get
              (hbody_total Yfun x_1 hx_1)).snd.fst =
            SMTType.bool)
    (den_app_at :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hx₀_ty : x₀.snd.fst = α)
        (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ),
        ∃ hcov_app_goal :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              ((@ˢx) (.var z)),
          ⟦((@ˢx) (.var z)).abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              hcov_app_goal⟧ˢ =
            some ⟨(@ᶻX.fst
                    ⟨x₀.fst, by
                      simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩).1,
              SMTType.bool,
              (@ᶻX.fst
                ⟨x₀.fst, by
                  simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩).2⟩)
    (den_spec_some_at :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α')
        (hx₀_ty : x₀.snd.fst = α)
        (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ),
        ∃ hφY :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              z!_spec,
          ∃ Φ,
            ⟦z!_spec.abstract
                (Function.update
                  (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                  z (some x₀))
                hφY⟧ˢ =
              some Φ ∧
            Φ.snd.fst = SMTType.bool)
    (den_spec_true_at_cast :
      ∀ (y Yfun wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α')
        (hwy0_val : wy0.fst = y.fst)
        (hx₀_ty : x₀.snd.fst = α)
        (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ)
        (hcast_xy : x₀.fst.pair y.fst ∈ (castZF_of_path p).1),
        ∃ hφY :
            RenamingContext.CoversFV
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              z!_spec,
          ∃ Φ,
            ⟦z!_spec.abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              hφY⟧ˢ =
            some Φ ∧
          Φ.fst = zftrue)
    (den_spec_true_implies_cast :
      ∀ (Yfun wy0 x₀ : SMT.Dom)
        (hwy0_ty : wy0.snd.fst = α')
        (hx₀_ty : x₀.snd.fst = α)
        (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ)
        {Φ : SMT.Dom}
        (hφY :
          RenamingContext.CoversFV
            (Function.update
              (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
              z (some x₀))
            z!_spec)
        (hdenY :
          ⟦z!_spec.abstract
              (Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀))
              hφY⟧ˢ =
            some Φ)
        (htrue : Φ.fst = zftrue),
        x₀.fst.pair wy0.fst ∈ (castZF_of_path p).1)
    (den_z_exact_at :
      ∀ (x₀ : SMT.Dom)
        (hx₀_ty : x₀.snd.fst = α)
        (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ)
        {Y Φ : SMT.Dom}
        (hY_ty : Y.snd.fst = α')
        (hφY :
          RenamingContext.CoversFV
            (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
            z!_spec)
        (hdenY :
          ⟦z!_spec.abstract
              (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y))
              hφY⟧ˢ =
            some Φ)
        (htrue : Φ.fst = zftrue),
        x₀.fst.pair Y.fst ∈ (castZF_of_path p).1) :
    ∃ X! : SMT.Dom,
      X.fst.pair X!.fst ∈ (castZF_of_path p.chpred).1 ∧
      ⟦((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))).abstract
          (Function.update «Δ» x! (some X!)) (hcov_lambda_upd X!)⟧ˢ =
        some X! := by
  let cast : ZFSet := (castZF_of_path p).1
  let castRange : ZFSet := ZFSet.sep (fun y => ∃ x ∈ cast.Dom (castZF_of_path p).2.1, x.pair y ∈ cast) ⟦α'⟧ᶻ
  let X!zf : ZFSet :=
    λᶻ: ⟦α'⟧ᶻ → .𝔹
      | y ↦ if hy_ran : y ∈ castRange then
               let x₀ := Classical.choose (ZFSet.mem_sep.mp hy_ran).2
               have hx₀ : x₀ ∈ ⟦α⟧ᶻ := by
                 have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hy_ran).2
                 exact (ZFSet.mem_sep.mp dom).1
               let hx₀_dom : x₀ ∈ X.fst.Dom := by
                 simpa [ZFSet.is_func_dom_eq hX_func] using hx₀
               let b : {u // u ∈ 𝔹} :=
                 ZFSet.fapply X.fst (hf := ZFSet.is_func_is_pfunc hX_func) ⟨x₀, hx₀_dom⟩
               b.1
             else zffalse
  have hX!zf_mem : X!zf ∈ ⟦α'.fun SMTType.bool⟧ᶻ := by
    rw [ZFSet.mem_funs]
    apply ZFSet.lambda_isFunc
    intro y hy
    split_ifs with hy_ran
    · have hx₀ : Classical.choose (ZFSet.mem_sep.mp hy_ran).2 ∈ ⟦α⟧ᶻ := by
        have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hy_ran).2
        exact (ZFSet.mem_sep.mp dom).1
      exact ZFSet.fapply_mem_range (ZFSet.is_func_is_pfunc hX_func) (by
        rwa [ZFSet.is_func_dom_eq hX_func])
    · exact ZFSet.ZFBool.zffalse_mem_𝔹
  let X! : SMT.Dom := ⟨X!zf, α'.fun SMTType.bool, hX!zf_mem⟩
  have hden_lambda_X! :
      ⟦((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))).abstract
          (Function.update «Δ» x! (some X!)) (hcov_lambda_upd X!)⟧ˢ =
        some X! := by
    simpa only [cast, castRange, X!zf, X!] using
      (chpredDenoteLambdaAt
        (Γ := Γ) («Δ» := «Δ») (x := x) (z!_spec := z!_spec)
        (x! := x!) (z := z) (z! := z!) (α := α) (α' := α') (p := p)
        X hX_mem hX_func hcov_lambda_upd hgo_cov hexists_cov hgo_exists
        hbody_total hbody_ty_of den_app_at den_spec_some_at den_spec_true_at_cast
        den_spec_true_implies_cast den_z_exact_at)
  refine ⟨X!, ?_, hden_lambda_X!⟩
  rw [castZF_of_path, castZF_chpred, ZFSet.lambda_spec]
  refine ⟨hX_mem, hX!zf_mem, ?_⟩
  rw [dif_pos hX_func]

set_option maxHeartbeats 4000000
theorem loosenAux_prf_exact.chpred («Δ» : RenamingContext.Context.{u})
  (pf : ∀ (x! : 𝒱) (X! : SMT.Dom), ∀ v ∈ fv (Term.var x!), (Function.update «Δ» x! (some X!) v).isSome = true)
  {α α' : SMTType} (p : α ⇝ α')
  (ih :
    ∀ {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term},
      Λ ⊢ˢ x : α →
        ∀ («Δ₀» : RenamingContext.Context.{u}) (hx : RenamingContext.CoversFV «Δ₀» x)
          (pf₀ : ∀ (x! : 𝒱) (X! : SMT.Dom), ∀ v ∈ fv (Term.var x!), (Function.update «Δ₀» x! (some X!) v).isSome = true),
          ⦃fun x =>
            match x with
            | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
            loosenAux_prf name p x ⦃PostCond.mayThrow fun x_1 x_2 =>
              match x_1 with
              | (x!, x!_spec) =>
                match x_2 with
                | { env := E', types := Γ' } =>
                  ⌜n ≤ E'.freshvarsc ∧
                      AList.insert x! α' Λ ⊆ Γ' ∧
                        x! ∉ Λ ∧
                          x! ∉ used ∧
                            used ⊆ E'.usedVars ∧
                              AList.keys Γ' ⊆ E'.usedVars ∧
                                (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
                                AList.insert x! α' Λ ⊢ˢ Term.var x! : α' ∧
                                  AList.insert x! α' Λ ⊢ˢ x!_spec : SMTType.bool ∧
                                    Γ' ⊢ˢ Term.var x! : α' ∧
                                      Γ' ⊢ˢ x!_spec : SMTType.bool ∧
                                        fv x!_spec ⊆ fv x ∪ {x!} ∧
                                          ∀ (X : SMT.Dom),
                                            ⟦x.abstract «Δ₀» hx⟧ˢ = some X →
                                              ∃ Φ X!,
                                                ∃ (denx! :
                                                  ⟦(Term.var x!).abstract (Function.update «Δ₀» x! (some X!)) (pf₀ x! X!)⟧ˢ =
                                                    some X!)
                                                  (hφ :
                                                  RenamingContext.CoversFV (Function.update «Δ₀» x! (some X!)) x!_spec)
                                                  (denφ :
                                                  ⟦x!_spec.abstract (Function.update «Δ₀» x! (some X!)) hφ⟧ˢ = some Φ),
                                                  Φ.snd.fst = SMTType.bool ∧
                                                    (Φ.fst = zftrue ∧ X.fst.pair X!.fst ∈ (castZF_of_path p).1) ∧
                                                      ∀ (Y : SMT.Dom),
                                                        Y.snd.fst = α' →
                                                          ∀
                                                            (hφY :
                                                              RenamingContext.CoversFV (Function.update «Δ₀» x! (some Y))
                                                                x!_spec),
                                                            ⟦x!_spec.abstract (Function.update «Δ₀» x! (some Y))
                                                                    hφY⟧ˢ.isSome =
                                                              true ∧
                                                              ∀ {ΦY : SMT.Dom},
                                                                ⟦x!_spec.abstract
                                                                    (Function.update «Δ₀» x! (some Y)) hφY⟧ˢ =
                                                                  some ΦY →
                                                                ΦY.fst = zftrue →
                                                                  X.fst.pair Y.fst ∈
                                                                    (castZF_of_path p).1⌝⦄)
  {Λ : TypeContext} {n : ℕ} {used : List 𝒱} {name : String} {x : Term} (typ_x : Λ ⊢ˢ x : α.fun SMTType.bool)
  (hx : RenamingContext.CoversFV «Δ» x) :
  ⦃fun x =>
    match x with
    | { env := E, types := Λ' } => ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ' ⊆ E.usedVars ∧ E.usedVars = used⌝⦄
    loosenAux_prf name p.chpred x ⦃PostCond.mayThrow fun x_1 x_2 =>
      match x_1 with
      | (x!, x!_spec) =>
        match x_2 with
        | { env := E', types := Γ' } =>
          ⌜n ≤ E'.freshvarsc ∧
              AList.insert x! (α'.fun SMTType.bool) Λ ⊆ Γ' ∧
                x! ∉ Λ ∧
                  x! ∉ used ∧
                    used ⊆ E'.usedVars ∧
                      AList.keys Γ' ⊆ E'.usedVars ∧
                        (∀ v ∈ used, v ∉ Λ → v ∉ Γ') ∧
                        AList.insert x! (α'.fun SMTType.bool) Λ ⊢ˢ Term.var x! : α'.fun SMTType.bool ∧
                          AList.insert x! (α'.fun SMTType.bool) Λ ⊢ˢ x!_spec : SMTType.bool ∧
                            Γ' ⊢ˢ Term.var x! : α'.fun SMTType.bool ∧
                              Γ' ⊢ˢ x!_spec : SMTType.bool ∧
                                fv x!_spec ⊆ fv x ∪ {x!} ∧
                                  ∀ (X : SMT.Dom),
                                    ⟦x.abstract «Δ» hx⟧ˢ = some X →
                                      ∃ Φ X!,
                                        ∃ (_ : ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!)) (pf x! X!)⟧ˢ = some X!)
                                          (hφ : RenamingContext.CoversFV (Function.update «Δ» x! (some X!)) x!_spec) (_
                                          : ⟦x!_spec.abstract (Function.update «Δ» x! (some X!)) hφ⟧ˢ = some Φ),
                                          Φ.snd.fst = SMTType.bool ∧
                                            (Φ.fst = zftrue ∧ X.fst.pair X!.fst ∈ (castZF_of_path p.chpred).1) ∧
                                              ∀ (Y : SMT.Dom),
                                                Y.snd.fst = α'.fun SMTType.bool →
                                                  ∀
                                                    (hφY :
                                                      RenamingContext.CoversFV (Function.update «Δ» x! (some Y))
                                                        x!_spec),
                                                    ⟦x!_spec.abstract (Function.update «Δ» x! (some Y)) hφY⟧ˢ.isSome =
                                                      true ∧
                                                      ∀ {ΦY : SMT.Dom},
                                                        ⟦x!_spec.abstract
                                                            (Function.update «Δ» x! (some Y)) hφY⟧ˢ =
                                                          some ΦY →
                                                        ΦY.fst = zftrue →
                                                          X.fst.pair Y.fst ∈
                                                            (castZF_of_path p.chpred).1⌝⦄ := by
  mintro pre ∀St₁
  mpure pre
  obtain ⟨rfl, rfl, sub, rfl⟩ := pre
  unfold loosenAux_prf
  mspec SMT.freshVar_spec (Γ := St₁.types) (n := St₁.env.freshvarsc) (used := St₁.env.usedVars)
  next x! =>
    mrename_i pre
    mintro ∀St₂
    mcases pre with ⟨St₂_types_eq, x!_fresh, St₂_fvc, St₂_used_eq, x!_not_used⟩
    mspec SMT.freshVar_spec (Γ := St₂.types) (n := St₂.env.freshvarsc) (used := St₂.env.usedVars)
    next z =>
      mrename_i pre
      mintro ∀St₃
      mcases pre with ⟨St₃_types_eq, z_fresh, St₃_fvc, St₃_used_eq, z_not_used⟩
      have typ_var_z_St₃ : St₃.types ⊢ˢ .var z : α := by
        apply SMT.Typing.var
        rw [St₃_types_eq]
        exact AList.lookup_insert St₂.types
      let Δz : RenamingContext.Context := fun v =>
        if v = z then some ⟨α.defaultZFSet, α, SMTType.mem_toZFSet_of_defaultZFSet⟩ else «Δ» v
      have hcov_var_z : RenamingContext.CoversFV Δz (.var z) := by
        intro v hv
        rw [fv, List.mem_singleton] at hv
        subst hv
        simp [Δz]
      have pf_var_z :
          ∀ (xz! : 𝒱) (Xz! : SMT.Dom), ∀ v ∈ fv (Term.var xz!),
            (Function.update Δz xz! (some Xz!) v).isSome = true := by
        intro xz! Xz! v hv
        rw [fv, List.mem_singleton] at hv
        subst hv
        simp [Function.update]
      have ih_var_z := ih (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars)
        (name := s!"{name}_char_pred") (x := .var z) typ_var_z_St₃ Δz hcov_var_z pf_var_z
      have run_var_z_spec :
          ⦃fun st => ⌜st = St₃⌝⦄
            loosenAux_prf s!"{name}_char_pred" p (.var z)
          ⦃PostCond.mayThrow fun out st =>
            ⌜StateT.run (loosenAux_prf s!"{name}_char_pred" p (.var z)) St₃ = Except.ok (out, st)⌝⦄ := by
        unfold Std.Do.Triple
        intro st hst
        subst st
        simp only [wp, PredTrans.pushArg_apply, PredTrans.pushExcept_apply, PredTrans.pure_apply]
        cases hrun : Id.run ((loosenAux_prf s!"{name}_char_pred" p (.var z)) St₃) with
        | error e =>
            trivial
        | ok a =>
            simpa using hrun
      mspec (Std.Do.Triple.and _ run_var_z_spec ih_var_z)
      · mpure_intro
        and_intros
        · rfl
        · trivial
        · trivial
        · have keys_sub₂ : AList.keys St₂.types ⊆ St₂.env.usedVars := by
            rw [St₂_types_eq, St₂_used_eq, AList.keys_insert]
            intro v hv
            rw [List.mem_cons] at hv ⊢
            rcases hv with rfl | hv
            · exact Or.inl rfl
            · exact Or.inr (sub (List.mem_of_mem_erase hv))
          rw [St₃_types_eq, St₃_used_eq, AList.keys_insert]
          intro v hv
          rw [List.mem_cons] at hv ⊢
          rcases hv with rfl | hv
          · exact Or.inl rfl
          · exact Or.inr (keys_sub₂ (List.mem_of_mem_erase hv))
        · trivial
      · rename_i out_z
        obtain ⟨z!, z!_spec⟩ := out_z
        mrename_i pre
        mintro ∀St₄
        mpure pre
        obtain ⟨hrun, hn₄, St₄_types_eq, z!_fresh, z!_not_used, used_sub₄, keys_sub₄, preserves_z!,
          typ_z!, typ_z!_spec, typ_z!_St₄, typ_z!_spec_St₄, fv_z!_spec, den_z⟩ := pre
        mspec Std.Do.Spec.pure
        have z!_not_St₂ : z! ∉ St₂.types := by
          intro hz!
          apply z!_fresh
          rw [St₃_types_eq, AList.mem_insert]
          exact Or.inr hz!
        have z_ne_z! : z ≠ z! := by
          intro hz
          apply z!_fresh
          rw [St₃_types_eq, hz, AList.mem_insert]
          exact Or.inl rfl
        have typ_x_St₂ : St₂.types ⊢ˢ x : α.fun SMTType.bool := by
          rw [St₂_types_eq]
          exact SMT.Typing.weakening
            (h := SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh)
            typ_x
        have typ_var_x!_St₂ : St₂.types ⊢ˢ .var x! : α'.fun SMTType.bool := by
          rw [St₂_types_eq]
          apply SMT.Typing.var
          exact AList.lookup_insert St₁.types
        have typ_z!_spec_ctx :
            (AList.insert z! α' (AList.insert z α St₂.types)) ⊢ˢ z!_spec : SMTType.bool := by
          simpa [St₃_types_eq] using typ_z!_spec
        have typing_pack := chpredTypingPack
          (Γ := St₂.types) (x := x) (x! := x!) (z := z) (z! := z!)
          (α := α) (α' := α')
          typ_x_St₂ typ_var_x!_St₂ z_fresh z!_not_St₂ z_ne_z! typ_z!_spec_ctx
        have typ_z!_spec_body := typing_pack.typ_z!_spec_body
        have typ_app_body := typing_pack.typ_app_body
        have typ_exists' := typing_pack.typ_exists
        have typ_lambda := typing_pack.typ_lambda
        have typ_x!_spec_base := typing_pack.typ_eq
        mpure_intro
        and_intros
        · calc
            St₁.env.freshvarsc ≤ St₂.env.freshvarsc := by rw [St₂_fvc]; exact Nat.le_succ _
            _ ≤ St₃.env.freshvarsc := by rw [St₃_fvc]; exact Nat.le_succ _
            _ ≤ St₄.env.freshvarsc := hn₄
        · intro v hv
          have hv₂ : v ∈ St₂.types.entries := by
            rw [St₂_types_eq]
            exact hv
          have hv₃ : v ∈ St₃.types.entries := by
            rw [St₃_types_eq]
            exact SMT.TypeContext.entries_subset_insert_of_notMem z_fresh hv₂
          exact St₄_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem z!_fresh hv₃)
        · exact x!_fresh
        · exact x!_not_used
        · intro v hv
          have hv₂ : v ∈ St₂.env.usedVars := by
            rw [St₂_used_eq]
            exact List.mem_cons_of_mem _ hv
          exact used_sub₄ (by
            rw [St₃_used_eq]
            exact List.mem_cons_of_mem _ hv₂)
        · exact keys_sub₄
        · -- preserves_types
          intro v hv hv_not_Λ
          have hv_ne_x : v ≠ x! := fun h => absurd (h ▸ hv) x!_not_used
          have z_not_used_base : z ∉ St₁.env.usedVars := by
            intro hmem; apply z_not_used; rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hmem
          have hv_ne_z : v ≠ z := fun h => absurd (h ▸ hv) z_not_used_base
          have hv_not_St₂ : v ∉ St₂.types := by
            rw [St₂_types_eq, AList.mem_insert]; push_neg
            exact ⟨hv_ne_x, hv_not_Λ⟩
          have hv_not_St₃ : v ∉ St₃.types := by
            rw [St₃_types_eq, AList.mem_insert]; push_neg
            exact ⟨hv_ne_z, hv_not_St₂⟩
          have hv_in_St₃_used : v ∈ St₃.env.usedVars := by
            rw [St₃_used_eq]; exact List.mem_cons_of_mem _ (by rw [St₂_used_eq]; exact List.mem_cons_of_mem _ hv)
          exact preserves_z! v hv_in_St₃_used hv_not_St₃
        · apply SMT.Typing.var
          exact AList.lookup_insert St₁.types
        · simpa [St₂_types_eq] using typ_x!_spec_base
        · have typ_x!_base : (AList.insert x! (α'.fun SMTType.bool) St₁.types) ⊢ˢ .var x! : α'.fun SMTType.bool := by
            apply SMT.Typing.var
            exact AList.lookup_insert St₁.types
          apply SMT.Typing.weakening _ typ_x!_base
          intro v hv
          have hv₂ : v ∈ St₂.types.entries := by
            rwa [St₂_types_eq]
          have hv₃ : v ∈ St₃.types.entries := by
            rw [St₃_types_eq]
            exact SMT.TypeContext.entries_subset_insert_of_notMem z_fresh hv₂
          exact St₄_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem z!_fresh hv₃)
        · have typ_x!_spec_base₁ :
            (AList.insert x! (α'.fun SMTType.bool) St₁.types) ⊢ˢ
              (Term.var x! =ˢ (λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))) : SMTType.bool := by
            simpa [St₂_types_eq] using typ_x!_spec_base
          apply SMT.Typing.weakening _ typ_x!_spec_base₁
          intro v hv
          have hv₂ : v ∈ St₂.types.entries := by
            rwa [St₂_types_eq]
          have hv₃ : v ∈ St₃.types.entries := by
            rw [St₃_types_eq]
            exact SMT.TypeContext.entries_subset_insert_of_notMem z_fresh hv₂
          exact St₄_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem z!_fresh hv₃)
        · intro v hv
          simp only [fv, List.cons_append, List.nil_append, List.mem_removeAll_iff, List.mem_cons,
            List.mem_append, List.not_mem_nil, or_false] at hv
          rcases hv with hv | hv
          · rw [List.mem_union_iff]
            exact Or.inr (List.mem_singleton.mpr hv)
          · rcases hv with ⟨hv_main, hv_ne_z!⟩
            rcases hv_main with ⟨hv_main, hv_ne_z⟩
            rcases hv_main with hvx_or_z | hvspec
            · rcases hvx_or_z with hvx | hvz
              · rw [List.mem_union_iff]
                exact Or.inl hvx
              · exact (hv_ne_z hvz).elim
            · have hv' := fv_z!_spec hvspec
              rw [List.mem_union_iff] at hv'
              rcases hv' with hvz | hvz!
              · exact (hv_ne_z (by simpa [fv] using hvz)).elim
              · exact (hv_ne_z! (List.mem_singleton.mp hvz!)).elim
        · intro X denx
          have hX_ty : X.snd.fst = α.fun SMTType.bool := denote_type_eq_of_typing typ_x denx
          have hX_mem : X.fst ∈ ⟦α.fun SMTType.bool⟧ᶻ := by
            simpa [hX_ty] using X.snd.snd
          have x!_not_mem_fv_x : x! ∉ SMT.fv x := by
            intro hx_mem
            exact x!_fresh (SMT.Typing.mem_context_of_mem_fv typ_x hx_mem)
          have hcov_x_upd (Y : SMT.Dom) :
              SMT.RenamingContext.CoversFV (Function.update «Δ» x! (some Y)) x := by
            intro v hv
            by_cases hvx : v = x!
            · subst hvx
              exfalso
              exact x!_not_mem_fv_x hv
            · rw [Function.update_of_ne hvx]
              exact hx v hv
          have denx_upd (Y : SMT.Dom) :
              ⟦x.abstract (Function.update «Δ» x! (some Y)) (hcov_x_upd Y)⟧ˢ = some X := by
            rw [←SMT.RenamingContext.denote]
            rw [←SMT.RenamingContext.denote_update_of_notMem
              («Δ» := «Δ») (t := x) (x := x!) (d := Y) (h := hx) x!_not_mem_fv_x]
            rw [SMT.RenamingContext.denote]
            exact denx
          have den_z_at
              (x₀ : SMT.Dom)
              (hx₀_ty : x₀.snd.fst = α)
              (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ) :
              ∃ Φ X₀!,
                ∃ (_ :
                    ⟦(Term.var z!).abstract (Function.update
                      (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!))
                      (by
                        intro v hv
                        rw [fv, List.mem_singleton] at hv
                        subst hv
                        simp [Function.update])⟧ˢ = some X₀!)
                  (hφ :
                    RenamingContext.CoversFV (Function.update
                      (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!)) z!_spec)
                  (_ :
                    ⟦z!_spec.abstract
                      (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some X₀!)) hφ⟧ˢ =
                      some Φ),
                  Φ.snd.fst = SMTType.bool ∧
                    (Φ.fst = zftrue ∧ x₀.fst.pair X₀!.fst ∈ (castZF_of_path p).1) ∧
                      ∀ (Y : SMT.Dom),
                        Y.snd.fst = α' →
                          ∀ (hφY :
                            RenamingContext.CoversFV (Function.update
                              (fun v => if v = z then some x₀ else «Δ» v) z! (some Y)) z!_spec),
                            ⟦z!_spec.abstract
                              (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y)) hφY⟧ˢ.isSome =
                              true ∧
                              ∀ {ΦY : SMT.Dom},
                                ⟦z!_spec.abstract
                                    (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y)) hφY⟧ˢ =
                                  some ΦY →
                                  ΦY.fst = zftrue →
                                    x₀.fst.pair Y.fst ∈ (castZF_of_path p).1 := by
            let Δx₀ : RenamingContext.Context := fun v => if v = z then some x₀ else «Δ» v
            have hcov_var_z_x₀ : RenamingContext.CoversFV Δx₀ (.var z) := by
              intro v hv
              rw [fv, List.mem_singleton] at hv
              subst hv
              simp [Δx₀]
            have pf_var_z_x₀ :
                ∀ (xz! : 𝒱) (Xz! : SMT.Dom), ∀ v ∈ fv (Term.var xz!),
                  (Function.update Δx₀ xz! (some Xz!) v).isSome = true := by
              intro xz! Xz! v hv
              rw [fv, List.mem_singleton] at hv
              subst hv
              simp [Function.update]
            have ih_var_z_x₀ := ih (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars)
              (name := s!"{name}_char_pred") (x := .var z) typ_var_z_St₃ Δx₀ hcov_var_z_x₀ pf_var_z_x₀
            have post_x₀ := ih_var_z_x₀ St₃ (by
              dsimp
              refine ⟨rfl, rfl, ?_, rfl⟩
              have keys_sub₂ : AList.keys St₂.types ⊆ St₂.env.usedVars := by
                rw [St₂_types_eq, St₂_used_eq, AList.keys_insert]
                intro v hv
                rw [List.mem_cons] at hv ⊢
                rcases hv with rfl | hv
                · exact Or.inl rfl
                · exact Or.inr (sub (List.mem_of_mem_erase hv))
              rw [St₃_types_eq, St₃_used_eq, AList.keys_insert]
              intro v hv
              rw [List.mem_cons] at hv ⊢
              rcases hv with rfl | hv
              · exact Or.inl rfl
              · exact Or.inr (keys_sub₂ (List.mem_of_mem_erase hv)))
            simp only [wp, PredTrans.pushArg_apply, PredTrans.pushExcept_apply, PredTrans.pure_apply] at post_x₀
            have hrun' :
                Id.run ((loosenAux_prf s!"{name}_char_pred" p (.var z)) St₃) =
                  Except.ok ((z!, z!_spec), St₄) := by
              simpa using hrun
            rw [hrun'] at post_x₀
            have hden_var_z_x₀ :
                ⟦(Term.var z).abstract Δx₀ hcov_var_z_x₀⟧ˢ = some x₀ := by
              rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
              apply Option.get_of_eq_some
              simp [Δx₀]
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hden_z_x₀⟩ := post_x₀
            exact hden_z_x₀ x₀ hden_var_z_x₀
          have den_z_exact_at
              (x₀ : SMT.Dom)
              (hx₀_ty : x₀.snd.fst = α)
              (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ)
              {Y Φ : SMT.Dom}
              (hY_ty : Y.snd.fst = α')
              (hφY : RenamingContext.CoversFV
                (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y)) z!_spec)
              (hdenY :
                ⟦z!_spec.abstract
                    (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some Y)) hφY⟧ˢ =
                  some Φ)
              (htrue : Φ.fst = zftrue) :
              x₀.fst.pair Y.fst ∈ (castZF_of_path p).1 := by
            let Δx₀ : RenamingContext.Context := fun v => if v = z then some x₀ else «Δ» v
            have hcov_var_z_x₀ : RenamingContext.CoversFV Δx₀ (.var z) := by
              intro v hv
              rw [fv, List.mem_singleton] at hv
              subst hv
              simp [Δx₀]
            have pf_var_z_x₀ :
                ∀ (xz! : 𝒱) (Xz! : SMT.Dom), ∀ v ∈ fv (Term.var xz!),
                  (Function.update Δx₀ xz! (some Xz!) v).isSome = true := by
              intro xz! Xz! v hv
              rw [fv, List.mem_singleton] at hv
              subst hv
              simp [Function.update]
            have exact_var_z_x₀ := ih
              (Λ := St₃.types) (n := St₃.env.freshvarsc) (used := St₃.env.usedVars)
              (name := s!"{name}_char_pred") (x := .var z) typ_var_z_St₃ Δx₀ hcov_var_z_x₀ pf_var_z_x₀
            have post_x₀ := exact_var_z_x₀ St₃ (by
              dsimp
              refine ⟨rfl, rfl, ?_, rfl⟩
              have keys_sub₂ : AList.keys St₂.types ⊆ St₂.env.usedVars := by
                rw [St₂_types_eq, St₂_used_eq, AList.keys_insert]
                intro v hv
                rw [List.mem_cons] at hv ⊢
                rcases hv with rfl | hv
                · exact Or.inl rfl
                · exact Or.inr (sub (List.mem_of_mem_erase hv))
              rw [St₃_types_eq, St₃_used_eq, AList.keys_insert]
              intro v hv
              rw [List.mem_cons] at hv ⊢
              rcases hv with rfl | hv
              · exact Or.inl rfl
              · exact Or.inr (keys_sub₂ (List.mem_of_mem_erase hv)))
            simp only [wp, PredTrans.pushArg_apply, PredTrans.pushExcept_apply, PredTrans.pure_apply] at post_x₀
            have hrun' :
                Id.run ((loosenAux_prf s!"{name}_char_pred" p (.var z)) St₃) =
                  Except.ok ((z!, z!_spec), St₄) := by
              simpa using hrun
            rw [hrun'] at post_x₀
            have hden_var_z_x₀ :
                ⟦(Term.var z).abstract Δx₀ hcov_var_z_x₀⟧ˢ = some x₀ := by
              rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
              apply Option.get_of_eq_some
              simp [Δx₀]
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hden_z_x₀⟩ := post_x₀
            obtain ⟨_, _, _, _, _, _, _, htot_x₀⟩ := hden_z_x₀ x₀ hden_var_z_x₀
            exact (htot_x₀ Y hY_ty hφY).2 hdenY htrue
          have hfv_spec_sub :
              SMT.fv
                (Term.var x! =ˢ
                  (λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))) ⊆
                SMT.fv x ∪ {x!} := by
            intro v hv
            simp only [fv, List.cons_append, List.nil_append, List.mem_removeAll_iff, List.mem_cons,
              List.mem_append, List.not_mem_nil, or_false] at hv
            rcases hv with hv | hv
            · rw [List.mem_union_iff]
              exact Or.inr (List.mem_singleton.mpr hv)
            · rcases hv with ⟨hv_main, hv_ne_z!⟩
              rcases hv_main with ⟨hv_main, hv_ne_z⟩
              rcases hv_main with hvx_or_z | hvspec
              · rcases hvx_or_z with hvx | hvz
                · rw [List.mem_union_iff]
                  exact Or.inl hvx
                · exact (hv_ne_z hvz).elim
              · have hv' := fv_z!_spec hvspec
                rw [List.mem_union_iff] at hv'
                rcases hv' with hvz | hvz!
                · exact (hv_ne_z (by simpa [fv] using hvz)).elim
                · exact (hv_ne_z! (List.mem_singleton.mp hvz!)).elim
          have hX_func : IsFunc ⟦α⟧ᶻ 𝔹 X.fst := by
            rw [ZFSet.mem_funs] at hX_mem
            exact hX_mem
          let cast : ZFSet := (castZF_of_path p).1
          have hcast : IsFunc ⟦α⟧ᶻ ⟦α'⟧ᶻ cast := (castZF_of_path p).2
          let castRange : ZFSet := ZFSet.sep (fun y => ∃ x ∈ cast.Dom hcast.1, x.pair y ∈ cast) ⟦α'⟧ᶻ
          let X!zf : ZFSet :=
            λᶻ: ⟦α'⟧ᶻ → .𝔹
              | y ↦ if hy_ran : y ∈ castRange then
                       let x₀ := Classical.choose (ZFSet.mem_sep.mp hy_ran).2
                       have hx₀ : x₀ ∈ ⟦α⟧ᶻ := by
                         have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hy_ran).2
                         exact (ZFSet.mem_sep.mp dom).1
                       let hx₀_dom : x₀ ∈ X.fst.Dom := by
                         simpa [ZFSet.is_func_dom_eq hX_func] using hx₀
                       let b : {u // u ∈ 𝔹} :=
                         ZFSet.fapply X.fst (hf := ZFSet.is_func_is_pfunc hX_func) ⟨x₀, hx₀_dom⟩
                       b.1
                     else zffalse
          have hX!zf_mem : X!zf ∈ ⟦α'.fun SMTType.bool⟧ᶻ := by
            rw [ZFSet.mem_funs]
            apply ZFSet.lambda_isFunc
            intro y hy
            split_ifs with hy_ran
            · have hx₀ : Classical.choose (ZFSet.mem_sep.mp hy_ran).2 ∈ ⟦α⟧ᶻ := by
                have ⟨dom, _⟩ := Classical.choose_spec (ZFSet.mem_sep.mp hy_ran).2
                exact (ZFSet.mem_sep.mp dom).1
              exact ZFSet.fapply_mem_range (ZFSet.is_func_is_pfunc hX_func) (by
                rwa [ZFSet.is_func_dom_eq hX_func])
            · exact ZFSet.ZFBool.zffalse_mem_𝔹
          let X! : SMT.Dom := ⟨X!zf, α'.fun SMTType.bool, hX!zf_mem⟩
          have hcast_mem : X.fst.pair X!.fst ∈ (castZF_of_path p.chpred).1 := by
            rw [castZF_of_path, castZF_chpred, ZFSet.lambda_spec]
            refine ⟨hX_mem, hX!zf_mem, ?_⟩
            rw [dite_cond_eq_true (eq_true hX_func)]
          have hfv_lambda_sub :
              SMT.fv ((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))) ⊆
                SMT.fv x := by
            intro v hv
            simp only [fv, List.append_assoc, List.cons_append, List.nil_append,
              List.mem_removeAll_iff, List.mem_append, List.mem_cons, List.not_mem_nil,
              or_false] at hv
            rcases hv with ⟨⟨hvx | rfl | hvz, hv_ne_z⟩, hv_ne_z!⟩
            · exact hvx
            · nomatch hv_ne_z rfl
            · have hv' := fv_z!_spec hvz
              rw [List.mem_union_iff] at hv'
              rcases hv' with hvz | hvz!
              · nomatch hv_ne_z (by rwa [fv, List.mem_singleton] at hvz)
              · nomatch hv_ne_z! (List.mem_singleton.mp hvz!)
          have hfv_exists_sub :
              SMT.fv (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)) ⊆
                SMT.fv x ∪ {z!} := by
            intro v hv
            simp only [fv, List.mem_removeAll_iff, List.mem_cons, List.mem_append,
              List.not_mem_nil, or_false] at hv
            rcases hv with ⟨hv_main, hv_ne_z⟩
            rcases hv_main with hvx_or_z | hvspec
            · rcases hvx_or_z with hvx | hvz
              · rw [List.mem_union_iff]
                exact Or.inl hvx
              · exact (hv_ne_z hvz).elim
            · have hv' := fv_z!_spec hvspec
              rw [List.mem_union_iff] at hv'
              rcases hv' with hvz | hvz!
              · exact (hv_ne_z (by simpa [fv] using hvz)).elim
              · rw [List.mem_union_iff]
                exact Or.inr hvz!
          have x!_not_mem_fv_lambda :
              x! ∉ SMT.fv ((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))) := by
            intro hx_lambda
            exact x!_not_mem_fv_x (hfv_lambda_sub hx_lambda)
          have hcov_lambda_upd (Y : SMT.Dom) :
              RenamingContext.CoversFV (Function.update «Δ» x! (some Y))
                ((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))) := by
            intro v hv
            by_cases hvx : v = x!
            · subst hvx
              exfalso
              exact x!_not_mem_fv_lambda hv
            · rw [Function.update_of_ne hvx]
              exact hx v (hfv_lambda_sub hv)
          have hgo_cov (Yfun : SMT.Dom) :
              ∀ v ∈ SMT.fv (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)), v ∉ [z!] →
                (Function.update «Δ» x! (some Yfun) v).isSome = true :=
            chpredGoExistsCovers (x := x) (z!_spec := z!_spec) (x! := x!) (z := z) (z! := z!)
              (α := α) hx hfv_exists_sub Yfun
          have hexists_cov (Yfun W : SMT.Dom) :
              RenamingContext.CoversFV
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some W))
                (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)) :=
            chpredExistsCovers (x := x) (z!_spec := z!_spec) (x! := x!) (z := z) (z! := z!)
              (α := α) hx hfv_exists_sub Yfun W
          have z_not_mem_fv_x : z ∉ SMT.fv x := by
            intro hz_mem
            exact z_fresh (SMT.Typing.mem_context_of_mem_fv typ_x_St₂ hz_mem)
          have z!_not_mem_fv_x : z! ∉ SMT.fv x := by
            intro hz!_mem
            exact z!_not_St₂ (SMT.Typing.mem_context_of_mem_fv typ_x_St₂ hz!_mem)
          have hgo_exists
              (Yfun : SMT.Dom)
              (w : Fin [z!].length → SMT.Dom)
              (hw : ∀ i, (w i).snd.fst = [α'][i] ∧ (w i).fst ∈ ⟦[α'][i]⟧ᶻ) :
              (Term.abstract.go
                  (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                  [z!]
                  (Function.update «Δ» x! (some Yfun))
                  (hgo_cov Yfun)).uncurry w =
                (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec)).abstract
                  (Function.update (Function.update «Δ» x! (some Yfun)) z! (some (w ⟨0, by simp⟩)))
                  (hexists_cov Yfun (w ⟨0, by simp⟩)) := by
            have hgo := SMT.Term.abstract.go.alt_def₂
              (vs := [z!]) (P := Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
              (Δctx := Function.update «Δ» x! (some Yfun))
              (αs := List.ofFn w) (vs_αs_len := by simp)
              (Δ_isSome := hgo_cov Yfun)
              (tmp₁ := by
                intro v hv
                have hv' := hfv_exists_sub hv
                rw [List.mem_union_iff] at hv'
                rcases hv' with hvx | hvz!_mem
                · by_cases hvz! : v = z!
                  · subst hvz!
                    exfalso
                    exact z!_not_mem_fv_x hvx
                  · rw [Function.updates_of_not_mem
                      (f := Function.update «Δ» x! (some Yfun))
                      (xs := [z!]) (ys := (List.ofFn w).map Option.some) (k := v)
                      (by simp [hvz!])]
                    by_cases hvx! : v = x!
                    · subst hvx!
                      simp
                    · rw [Function.update_of_ne hvx!]
                      exact hx v hvx
                · exact Function.updates_isSome_of_mem_map_some
                    (Function.update «Δ» x! (some Yfun)) [z!] (List.ofFn w) v
                    hvz!_mem (by simp))
            have h_ofFn_list : List.ofFn w = [w ⟨0, by simp⟩] := rfl
            have h_ofFn : (fun ⟨i, hi⟩ ↦ (List.ofFn w)[i]) = w := by
              funext ⟨i, hi⟩
              simp at hi
              subst hi
              rfl
            simpa only [
              List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
              List.ofFn_succ, List.ofFn_zero, Fin.val_eq_zero, List.getElem_cons_zero,
              List.map_cons, List.map_nil, Function.updates] using hgo
          have x_ne_z : x! ≠ z := by
            intro hxz
            apply z_fresh
            rw [St₂_types_eq, hxz, AList.mem_insert]
            left
            rfl
          have x_ne_z! : x! ≠ z! := by
            rintro rfl
            apply z!_not_St₂
            rw [St₂_types_eq, AList.mem_insert]
            left
            rfl
          have hbody_total
              (Yfun : SMT.Dom)
              (x_1 : Fin [z!].length → SMT.Dom)
              (hx_1 : ∀ i, (x_1 i).snd.fst = [α'][i] ∧ (x_1 i).fst ∈ ⟦[α'][i]⟧ᶻ) :
              ⟦(Term.abstract.go
                  (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                  [z!]
                  (Function.update «Δ» x! (some Yfun))
                  (hgo_cov Yfun)).uncurry x_1⟧ˢ.isSome =
                true := by
            exact chpredBodyTotal
              (Γ := St₂.types) (p := p)
              (hgo_cov := hgo_cov) (hexists_cov := hexists_cov) (hgo_exists := hgo_exists)
              (hcov_x_upd := hcov_x_upd) (denx_upd := denx_upd)
              (hX_ty := hX_ty) (hX_func := hX_func)
              (den_z_at := den_z_at) (fv_z!_spec := fv_z!_spec)
              (z_ne_z! := z_ne_z!) (x_ne_z := x_ne_z) (x_ne_z! := x_ne_z!)
              (z_not_mem_fv_x := z_not_mem_fv_x) (z!_not_mem_fv_x := z!_not_mem_fv_x)
              (typ_app_body := typ_app_body) (typ_z!_spec_body := typ_z!_spec_body)
              Yfun x_1 hx_1
          have hbody_ty_of
              (Yfun : SMT.Dom)
              (x_1 : Fin [z!].length → SMT.Dom)
              (hx_1 : ∀ i, (x_1 i).snd.fst = [α'][i] ∧ (x_1 i).fst ∈ ⟦[α'][i]⟧ᶻ) :
              (⟦(Term.abstract.go
                  (Term.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))
                  [z!]
                  (Function.update «Δ» x! (some Yfun))
                  (hgo_cov Yfun)).uncurry x_1⟧ˢ.get
                  (hbody_total Yfun x_1 hx_1)).snd.fst =
                SMTType.bool := by
            exact chpredBodyTyOf
              (Γ := St₂.types)
              (hgo_cov := hgo_cov) (hexists_cov := hexists_cov) (hgo_exists := hgo_exists)
              (typ_exists := typ_exists') (hbody_total := hbody_total)
              Yfun x_1 hx_1
          have den_app_at
              (Yfun wy0 x₀ : SMT.Dom)
              (hx₀_ty : x₀.snd.fst = α)
              (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ) :
              ∃ hcov_app_goal :
                  SMT.RenamingContext.CoversFV
                    (Function.update
                      (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                      z (some x₀))
                    ((@ˢx) (.var z)),
                ⟦((@ˢx) (.var z)).abstract
                    (Function.update
                      (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                      z (some x₀))
                    hcov_app_goal⟧ˢ =
                    some ⟨(@ᶻX.fst
                            ⟨x₀.fst, by
                              simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩).1,
                    SMTType.bool,
                    (@ᶻX.fst
                      ⟨x₀.fst, by
                        simpa [ZFSet.is_func_dom_eq hX_func] using hx₀_mem⟩).2⟩ := by
            exact chpredDenAppAt
              (hcov_x_upd := hcov_x_upd) (denx_upd := denx_upd)
              (hX_ty := hX_ty) (hX_func := hX_func)
              (z!_not_mem_fv_x := z!_not_mem_fv_x)
              (z_not_mem_fv_x := z_not_mem_fv_x)
              (Yfun := Yfun) (wy0 := wy0)
              x₀ hx₀_ty hx₀_mem
          have den_spec_some_at
              (Yfun wy0 x₀ : SMT.Dom)
              (hwy0_ty : wy0.snd.fst = α')
              (hx₀_ty : x₀.snd.fst = α)
              (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ) :
              ∃ hφY : RenamingContext.CoversFV
                  (Function.update
                    (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                    z (some x₀))
                  z!_spec,
                ∃ Φ,
                  ⟦z!_spec.abstract
                      (Function.update
                        (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                        z (some x₀))
                      hφY⟧ˢ =
                    some Φ ∧
                  Φ.snd.fst = SMTType.bool := by
            exact chpredDenSpecSomeAt
              (p := p) (Yfun := Yfun) (wy0 := wy0)
              (den_z_at := den_z_at) (fv_z!_spec := fv_z!_spec)
              (z_ne_z! := z_ne_z!) (x_ne_z := x_ne_z) (x_ne_z! := x_ne_z!)
              (typ_z!_spec_body := typ_z!_spec_body)
              (hwy0_ty := hwy0_ty)
              x₀ hx₀_ty hx₀_mem
          have den_spec_true_at_cast
              (y Yfun wy0 x₀ : SMT.Dom)
              (hwy0_ty : wy0.snd.fst = α')
              (hwy0_val : wy0.fst = y.fst)
              (hx₀_ty : x₀.snd.fst = α)
              (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ)
              (hcast_xy : x₀.fst.pair y.fst ∈ (castZF_of_path p).1) :
              ∃ hφY : RenamingContext.CoversFV
                  (Function.update
                    (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                    z (some x₀))
                  z!_spec,
                ∃ Φ,
                  ⟦z!_spec.abstract
                      (Function.update
                        (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                        z (some x₀))
                      hφY⟧ˢ =
                    some Φ ∧
                  Φ.fst = zftrue := by
            exact chpredDenSpecTrueAtCast
              (p := p) (cast := (castZF_of_path p).1) (y := y.fst) (Yfun := Yfun) (wy0 := wy0)
              (den_z_at := den_z_at) (fv_z!_spec := fv_z!_spec)
              (z_ne_z! := z_ne_z!) (x_ne_z := x_ne_z) (x_ne_z! := x_ne_z!)
              (typ_z! := typ_z!_St₄)
              (hcast := (castZF_of_path p).2) (hwy0_ty := hwy0_ty)
              (hwy0_val := hwy0_val)
              x₀ hx₀_ty hx₀_mem hcast_xy
          have den_spec_true_implies_cast
              (Yfun wy0 x₀ : SMT.Dom)
              (hwy0_ty : wy0.snd.fst = α')
              (hx₀_ty : x₀.snd.fst = α)
              (hx₀_mem : x₀.fst ∈ ⟦α⟧ᶻ)
              {Φ : SMT.Dom}
              (hφY :
                RenamingContext.CoversFV
                  (Function.update
                    (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                    z (some x₀))
                  z!_spec)
              (hdenY :
                ⟦z!_spec.abstract
                    (Function.update
                      (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                      z (some x₀))
                    hφY⟧ˢ =
                  some Φ)
              (htrue : Φ.fst = zftrue) :
              x₀.fst.pair wy0.fst ∈ (castZF_of_path p).1 := by
            let Δbase : SMT.RenamingContext.Context :=
              Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some wy0)
            let Δgoal : SMT.RenamingContext.Context :=
              Function.update
                (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                z (some x₀)
            have hφ_base : RenamingContext.CoversFV Δbase z!_spec := by
              intro u hu
              have hu' := fv_z!_spec hu
              rw [List.mem_union_iff] at hu'
              rcases hu' with huz | huz!
              · have huz' : u = z := by
                  simpa [fv] using huz
                subst u
                simp [Δbase, z_ne_z!]
              · have huz!' : u = z! := List.mem_singleton.mp huz!
                subst u
                simp [Δbase]
            have hag_spec : SMT.RenamingContext.AgreesOnFV Δgoal Δbase z!_spec := by
              intro u hu
              have hu' := fv_z!_spec hu
              rw [List.mem_union_iff] at hu'
              rcases hu' with huz | huz!
              · have huz' : u = z := by
                  simpa [fv] using huz
                subst u
                simp only [Function.update_self, ne_eq, z_ne_z!, not_false_eq_true,
                  Function.update_of_ne, ↓reduceIte, Δgoal, Δbase]
              · have huz!' : u = z! := List.mem_singleton.mp huz!
                subst u
                rw [show Δgoal z! =
                  (Function.update
                    (Function.update (Function.update «Δ» x! (some Yfun)) z! (some wy0))
                    z (some x₀) z!) by rfl]
                rw [show Δbase z! =
                  (Function.update (fun v => if v = z then some x₀ else «Δ» v) z! (some wy0) z!) by rfl]
                rw [Function.update_of_ne z_ne_z!.symm, Function.update_self, Function.update_self]
            have hden_base :
                ⟦z!_spec.abstract Δbase hφ_base⟧ˢ = some Φ := by
              have hden_eq :
                  SMT.RenamingContext.denote Δgoal z!_spec hφY =
                    SMT.RenamingContext.denote Δbase z!_spec hφ_base :=
                SMT.RenamingContext.denote_congr_of_agreesOnFV
                  (h1 := hφY) (h2 := hφ_base) hag_spec
              simpa [SMT.RenamingContext.denote] using hden_eq.symm.trans hdenY
            exact den_z_exact_at x₀ hx₀_ty hx₀_mem hwy0_ty hφ_base hden_base htrue
          have hden_lambda_X! :
              ⟦((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))).abstract
                  (Function.update «Δ» x! (some X!)) (hcov_lambda_upd X!)⟧ˢ =
                some X! := by
            simpa only [cast, castRange, X!zf, X!] using
              (chpredDenoteLambdaAt
                (Γ := St₂.types) («Δ» := «Δ») (x := x) (z!_spec := z!_spec)
                (x! := x!) (z := z) (z! := z!) (α := α) (α' := α') (p := p)
                X hX_mem hX_func hcov_lambda_upd hgo_cov hexists_cov hgo_exists
                hbody_total hbody_ty_of den_app_at den_spec_some_at den_spec_true_at_cast
                den_spec_true_implies_cast den_z_exact_at)
          have hvar_X! :
              ⟦(Term.var x!).abstract (Function.update «Δ» x! (some X!)) (pf x! X!)⟧ˢ =
                some X! := by
            rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
            apply Option.get_of_eq_some
            exact Function.update_self _ _ _
          refine ⟨⟨zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩, X!, ?_, ?_, ?_, rfl, ?_⟩
          · exact hvar_X!
          · intro v hv
            by_cases hvx : v = x!
            · subst hvx
              rw [Function.update_self, Option.isSome_some]
            · rw [Function.update_of_ne hvx]
              have hv' := hfv_spec_sub hv
              rw [List.mem_union_iff] at hv'
              rcases hv' with hvx_in | hvx_single
              · exact hx v hvx_in
              · exfalso
                exact hvx (List.mem_singleton.mp hvx_single)
          · rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.bind_eq_bind, hvar_X!, hden_lambda_X!]
            simp only [Option.bind_some, overloadBinOp, Function.onFun, dite_eq_ite, dite_true, Option.some_inj]
            congr
            · rw [if_pos (by rw [if_pos (by rw [and_self]; exact X!.2.2)])]
            · funext τ
              conv =>
                enter [1,2]
                rw [if_pos (by rw [if_pos (by rw [and_self]; exact X!.2.2)])]
            · apply proof_irrel_heq
          · constructor
            · exact ⟨rfl, hcast_mem⟩
            · intro Y hY hφY
              have hvar :
                  ⟦(Term.var x!).abstract (Function.update «Δ» x! (some Y)) (pf x! Y)⟧ˢ = some Y := by
                rw [SMT.Term.abstract, SMT.denote, Option.pure_def, Option.some_inj]
                apply Option.get_of_eq_some
                exact Function.update_self _ _ _
              have hlam_some :
                  ⟦((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))).abstract
                      (Function.update «Δ» x! (some Y)) (hcov_lambda_upd Y)⟧ˢ.isSome =
                    true := by
                rw [SMT.Term.abstract, dite_cond_eq_true (eq_true (by rfl)), SMT.denote]
                split_ifs with hlen_pos den_t_isSome den_t_typ_det
                · simp
                · exfalso
                  apply den_t_typ_det
                  intro x_1 y_1 hx_1 hy_1
                  rw [hbody_ty_of Y x_1 hx_1, hbody_ty_of Y y_1 hy_1]
                · exfalso
                  exact den_t_isSome (fun {x_1} hx_1 => hbody_total Y x_1 hx_1)
                · exfalso
                  exact hlen_pos (by simp)
              obtain ⟨Dlam, hDlam_raw⟩ := Option.isSome_iff_exists.mp hlam_some
              have hDlam_ty : Dlam.snd.fst = α'.fun SMTType.bool :=
                denote_type_eq_of_typing (typ_t := typ_lambda) (hden := hDlam_raw)
              have hEq_ty : Y.snd.fst = Dlam.snd.fst := by
                rw [hY, hDlam_ty]
              obtain ⟨Deq, hDeq_raw, hDeq_ty⟩ :=
                denote_eq_some_of_some
                  (h₁ := hvar)
                  (h₂ := hDlam_raw)
                  (hτ := hEq_ty)
              constructor
              · simpa only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def,
                  proof_irrel_heq] using congrArg Option.isSome hDeq_raw
              · intro ΦY hdenY htrue
                have hDeq_eq_ΦY : Deq = ΦY := by
                  apply Option.some.inj
                  rw [← hDeq_raw]
                  simpa only [SMT.Term.abstract, SMT.denote, Option.bind_eq_bind, Option.pure_def,
                    proof_irrel_heq] using hdenY
                have hDeq_true : Deq.fst = zftrue := by
                  rw [hDeq_eq_ΦY]
                  exact htrue
                have hY_eq_Dlam : Y.fst = Dlam.fst :=
                  denote_eq_true_implies_fst_eq hvar hDlam_raw hEq_ty hDeq_raw hDeq_true
                have hden_lam_congr :
                    ⟦((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))).abstract
                        (Function.update «Δ» x! (some Y)) (hcov_lambda_upd Y)⟧ˢ =
                      ⟦((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))).abstract
                        (Function.update «Δ» x! (some X!)) (hcov_lambda_upd X!)⟧ˢ := by
                  apply SMT.RenamingContext.denote_congr_of_agreesOnFV
                    (h1 := hcov_lambda_upd Y) (h2 := hcov_lambda_upd X!)
                  intro v hv
                  by_cases hvx : v = x!
                  · exfalso
                    exact x!_not_mem_fv_lambda (hvx ▸ hv)
                  · rw [Function.update_of_ne hvx, Function.update_of_ne hvx]
                have hDlam_eq_X! : Dlam = X! := by
                  apply Option.some.inj
                  calc
                    some Dlam =
                        ⟦((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))).abstract
                            (Function.update «Δ» x! (some Y)) (hcov_lambda_upd Y)⟧ˢ := by
                      symm
                      exact hDlam_raw
                    _ =
                        ⟦((λˢ [z!]) [α'] (.exists [z] [α] (((@ˢx) (.var z)) ∧ˢ z!_spec))).abstract
                            (Function.update «Δ» x! (some X!)) (hcov_lambda_upd X!)⟧ˢ := hden_lam_congr
                    _ = some X! := hden_lambda_X!
                have hY_eq_X! : Y.fst = X!.fst := by
                  rw [hDlam_eq_X!] at hY_eq_Dlam
                  exact hY_eq_Dlam
                rw [hY_eq_X!]
                exact hcast_mem
