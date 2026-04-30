import SMT.Reasoning.Defs
import SMT.Reasoning.LooseningDefs
import SMT.Reasoning.Basic.StateSpecs
import SMT.Reasoning.Basic.LoosenAuxSpec
import SMT.Reasoning.Basic.DenotationTotality

set_option mvcgen.warning false

open Std.Do

set_option maxHeartbeats 3000000 in
@[spec]
theorem castMembership_spec.{u} {α β : SMT.SMTType} {x S : SMT.Term} {Λ : SMT.TypeContext} {n : ℕ}
  (typ_x : Λ ⊢ˢ x : α) (typ_S : Λ ⊢ˢ S : β) {used : List SMT.𝒱} :
  ⦃ λ ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used⌝ ⦄
    castMembership ⟨x, α⟩ ⟨S, β⟩
  ⦃ ⇓? ⟨t, τ⟩ ⟨E', Λ'⟩ =>
    ⌜n ≤ E'.freshvarsc ∧ Λ ⊆ Λ' ∧ AList.keys Λ' ⊆ E'.usedVars ∧ used ⊆ E'.usedVars ∧
      τ = .bool ∧ Λ' ⊢ˢ t : .bool ∧
      (∀ v ∈ SMT.fv t, v ∈ SMT.fv x ∨ v ∈ SMT.fv S ∨ v ∉ Λ) ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ Λ') ∧
      (∀ (Δctx : SMT.RenamingContext.Context.{u}) (hcov_t : SMT.RenamingContext.CoversFV Δctx t)
          (_hcompat : SMT.RenamingContext.RespectsTypeContext Δctx Λ'),
         ∃ denCM : SMT.Dom.{u},
           ⟦t.abstract Δctx hcov_t⟧ˢ = some denCM ∧ denCM.snd.fst = .bool)⌝ ⦄ := by
  let Δdummy : SMT.RenamingContext.Context.{0} :=
    (fun _ => (some (⟨ZFSet.zftrue, .bool, ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom.{0})))
  have hcov_dummy : ∀ t : SMT.Term, SMT.RenamingContext.CoversFV.{0} Δdummy t := by
    intro t v hv
    simp [Δdummy]
  induction β generalizing α x S Λ n used with
  | bool | int | unit | option | pair =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, _, _⟩ := pre
    unfold castMembership
    conv =>
      enter [2,1,1]
      dsimp
    mspec Std.Do.Spec.throw_StateT
  | «fun» τ σ τ_ih σ_ih =>
    mintro pre ∀St
    mpure pre
    obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
    cases hσ : σ with
    | bool =>
      have typ_S_bool : St.types ⊢ˢ S : .fun τ .bool := by
        subst hσ
        exact typ_S
      unfold castMembership
      conv =>
        enter [2,1,1]
        simp only [bind_pure_comp]
      split_ifs with α_le_τ τ_le_α
      · -- Branch 1: α = τ. Encoder returns pure (.app S x, .bool).
        subst α_le_τ
        mspec Std.Do.Spec.pure
        mpure_intro
        and_intros
        · exact Nat.le_refl _
        · intro v hv; exact hv
        · exact St_sub
        · rw [St_used_eq]; exact fun _ h => h
        · trivial
        · exact SMT.Typing.app _ _ _ _ _ typ_S_bool typ_x
        · -- fv tracking: fv (.app S x) = fv S ∪ fv x
          intro v hv
          unfold SMT.fv at hv
          rw [List.mem_append] at hv
          rcases hv with hS | hx
          · exact Or.inr (Or.inl hS)
          · exact Or.inl hx
        · -- preservation: Λ' = Λ here, so Λ ⊆ Λ' and (v ∉ Λ → v ∉ Λ') trivially
          intro v _ hv_notΛ
          exact hv_notΛ
        · -- totality: typing of `.app S x : .bool` plus `denote_exists_of_typing`.
          intro Δctx hcov_t hcompat
          exact SMT.RenamingContext.denote_exists_of_typing
            (SMT.Typing.app _ _ _ _ _ typ_S_bool typ_x) hcompat hcov_t
      · -- Branch 2: α ⊑ τ. Encoder does loosenAux on x then declareConst x! τ.
        mspec loosenAux_prf_spec (Λ := St.types) (n := St.env.freshvarsc) (used := St.env.usedVars)
          typ_x τ_le_α.toCastPath (Δdummy) (hcov_dummy x)
        next out =>
        obtain ⟨x!, x!_spec⟩ := out
        mrename_i pre
        mintro ∀St1
        mpure pre
        obtain ⟨hn1, St1_types_eq, x!_fresh, x!_not_used, used_sub1, keys_sub1, preserves1, typ_x!, typ_x!_spec, typ_x!_St1, typ_x!_spec_St1, fv_x!_spec, _⟩ := pre
        mspec Std.Do.Spec.map
        mspec SMT.declareConst_spec (v := x!) (τ := τ) (decl := St1.env.declarations)
          (as := St1.env.asserts) (n := St1.env.freshvarsc) (Γ := St1.types) (used := St1.env.usedVars)
        mrename_i pre
        mintro ∀St2
        mpure pre
        obtain ⟨_, _, St2_fvc_eq, St2_used_eq, St2_types_eq⟩ := pre
        have typ_full : St2.types ⊢ˢ x!_spec ∧ˢ .app S (.var x!) : .bool := by
          rw [St2_types_eq]
          apply SMT.Typing.and
          · exact typ_x!_spec_St1
          · apply SMT.Typing.app
            · exact SMT.Typing.weakening
                (h := fun v hv => St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh hv))
                typ_S_bool
            · exact typ_x!_St1
        mpure_intro
        and_intros
        · rw [St2_fvc_eq]
          exact hn1
        · intro v hv
          rw [St2_types_eq]
          exact St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh hv)
        · rw [St2_types_eq, St2_used_eq]
          exact keys_sub1
        · rw [←St_used_eq, St2_used_eq]
          exact used_sub1
        · trivial
        · exact typ_full
        · -- fv tracking: fv (x!_spec ∧ˢ .app S (.var x!)) ⊆ fv x ∪ fv S ∪ {x!}
          intro v hv
          simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
          rcases hv with h_spec | h_S | rfl
          · -- v ∈ fv x!_spec ⊆ fv x ∪ {x!}
            have hmem := fv_x!_spec h_spec
            -- {x!} is literally [x!] but display obscures this
            rcases List.mem_union_iff.mp hmem with hx | hx_in
            · exact Or.inl hx
            · -- hx_in : v ∈ [x!]
              have heq : v = x! := List.mem_singleton.mp hx_in
              subst heq
              exact Or.inr (Or.inr (fun hΛ => x!_fresh hΛ))
          · exact Or.inr (Or.inl h_S)
          · exact Or.inr (Or.inr (fun hΛ => x!_fresh hΛ))
        · -- preservation: v ∈ used ∧ v ∉ Λ → v ∉ Λ'
          -- St2.types = St1.types, and preserves1 gives v ∉ St1.types directly.
          intro v hv_used hv_notΛ
          rw [St2_types_eq]
          rw [St_used_eq] at preserves1
          exact preserves1 v hv_used hv_notΛ
        · -- totality: typing of full term plus `denote_exists_of_typing`.
          intro Δctx hcov_t hcompat
          exact SMT.RenamingContext.denote_exists_of_typing typ_full hcompat hcov_t
      · -- Branch 3: τ ⊑ α. Encoder does loosenAux on S with chpred then declareConst S! (α.fun .bool).
        rename_i h
        mspec loosenAux_prf_spec (Λ := St.types) (n := St.env.freshvarsc) (used := St.env.usedVars)
          typ_S_bool (castPath.chpred h.toCastPath) (Δdummy) (hcov_dummy S)
        next out =>
        obtain ⟨S!, S!_spec⟩ := out
        mrename_i pre
        mintro ∀St1
        mpure pre
        obtain ⟨hn1, St1_types_eq, S!_fresh, S!_not_used, used_sub1, keys_sub1, preserves1, typ_S!, typ_S!_spec, typ_S!_St1, typ_S!_spec_St1, fv_S!_spec, _⟩ := pre
        mspec Std.Do.Spec.map
        mspec SMT.declareConst_spec (v := S!) (τ := .fun α .bool) (decl := St1.env.declarations)
          (as := St1.env.asserts) (n := St1.env.freshvarsc) (Γ := St1.types) (used := St1.env.usedVars)
        mrename_i pre
        mintro ∀St2
        mpure pre
        obtain ⟨_, _, St2_fvc_eq, St2_used_eq, St2_types_eq⟩ := pre
        have typ_full : St2.types ⊢ˢ S!_spec ∧ˢ .app (.var S!) x : .bool := by
          rw [St2_types_eq]
          apply SMT.Typing.and
          · exact typ_S!_spec_St1
          · apply SMT.Typing.app
            · exact typ_S!_St1
            · exact SMT.Typing.weakening
                (h := fun v hv => St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv))
                typ_x
        mpure_intro
        and_intros
        · rw [St2_fvc_eq]
          exact hn1
        · intro v hv
          rw [St2_types_eq]
          exact St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv)
        · rw [St2_types_eq, St2_used_eq]
          exact keys_sub1
        · rw [←St_used_eq, St2_used_eq]
          exact used_sub1
        · trivial
        · exact typ_full
        · -- fv tracking: fv (S!_spec ∧ˢ .app (.var S!) x) ⊆ fv x ∪ fv S ∪ {S!}
          intro v hv
          simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
          rcases hv with h_spec | rfl | h_x
          · -- v ∈ fv S!_spec ⊆ fv S ∪ {S!}
            have hmem := fv_S!_spec h_spec
            rcases List.mem_union_iff.mp hmem with hS | hS_in
            · exact Or.inr (Or.inl hS)
            · have heq : v = S! := List.mem_singleton.mp hS_in
              subst heq
              exact Or.inr (Or.inr (fun hΛ => S!_fresh hΛ))
          · -- v = S!
            exact Or.inr (Or.inr (fun hΛ => S!_fresh hΛ))
          · exact Or.inl h_x
        · -- preservation: St2.types = St1.types, use preserves1.
          intro v hv_used hv_notΛ
          rw [St2_types_eq]
          rw [St_used_eq] at preserves1
          exact preserves1 v hv_used hv_notΛ
        · -- totality: typing of full term plus `denote_exists_of_typing`.
          intro Δctx hcov_t hcompat
          exact SMT.RenamingContext.denote_exists_of_typing typ_full hcompat hcov_t
      · mspec Std.Do.Spec.throw_StateT
    | option β' =>
      have typ_S_opt : St.types ⊢ˢ S : .fun τ (.option β') := by
        subst hσ
        exact typ_S
      cases hα : α with
      | pair α0 β0 =>
        have typ_x_pair : St.types ⊢ˢ x : .pair α0 β0 := by
          subst hα
          exact typ_x
        unfold castMembership
        conv =>
          enter [2,1,1]
          simp [hσ, hα]
        split_ifs with hαL hβL hβR hαR hβL2 hβR2
        · mspec loosenAux_prf_spec (Λ := St.types) (n := St.env.freshvarsc) (used := St.env.usedVars)
            typ_x_pair (.pair hαL.toCastPath hβL.toCastPath) (Δdummy) (hcov_dummy x)
          next out =>
          obtain ⟨x!, x!_spec⟩ := out
          mrename_i pre
          mintro ∀St1
          mpure pre
          obtain ⟨hn1, St1_types_eq, x!_fresh, _, used_sub1, keys_sub1, preserves1, typ_x!, typ_x!_spec, typ_x!_St1, typ_x!_spec_St1, fv_x!_spec, _⟩ := pre
          mspec Std.Do.Spec.map
          mspec SMT.declareConst_spec (v := x!) (τ := .pair τ β') (decl := St1.env.declarations)
            (as := St1.env.asserts) (n := St1.env.freshvarsc) (Γ := St1.types) (used := St1.env.usedVars)
          mrename_i pre
          mintro ∀St2
          mpure pre
          obtain ⟨_, _, St2_fvc_eq, St2_used_eq, St2_types_eq⟩ := pre
          have typ_full : St2.types ⊢ˢ
              x!_spec ∧ˢ ((SMT.Term.app S (.fst (.var x!))) =ˢ (SMT.Term.snd (.var x!)).some) :
              .bool := by
            rw [St2_types_eq]
            apply SMT.Typing.and
            · exact typ_x!_spec_St1
            · apply SMT.Typing.eq
              · apply SMT.Typing.app
                · exact SMT.Typing.weakening
                    (h := fun v hv => St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh hv))
                    typ_S_opt
                · apply SMT.Typing.fst
                  exact typ_x!_St1
              · apply SMT.Typing.some
                apply SMT.Typing.snd
                exact typ_x!_St1
          mpure_intro
          and_intros
          · rw [St2_fvc_eq]
            exact hn1
          · intro v hv
            rw [St2_types_eq]
            exact St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh hv)
          · rw [St2_types_eq, St2_used_eq]
            exact keys_sub1
          · rw [←St_used_eq, St2_used_eq]
            exact used_sub1
          · trivial
          · exact typ_full
          · -- fv tracking
            intro v hv
            simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
            -- hv : v ∈ fv x!_spec ∨ (v ∈ fv S ∨ v = x!) ∨ v = x!
            rcases hv with h_spec | (h_S | rfl) | rfl
            · have hmem := fv_x!_spec h_spec
              rcases List.mem_union_iff.mp hmem with hx | hx_in
              · exact Or.inl hx
              · have heq : v = x! := List.mem_singleton.mp hx_in
                subst heq
                exact Or.inr (Or.inr (fun hΛ => x!_fresh hΛ))
            · exact Or.inr (Or.inl h_S)
            · exact Or.inr (Or.inr (fun hΛ => x!_fresh hΛ))
            · exact Or.inr (Or.inr (fun hΛ => x!_fresh hΛ))
          · -- preservation: St2.types = St1.types, use preserves1.
            intro v hv_used hv_notΛ
            rw [St2_types_eq]
            rw [St_used_eq] at preserves1
            exact preserves1 v hv_used hv_notΛ
          · -- totality: typing of full term plus `denote_exists_of_typing`.
            intro Δctx hcov_t hcompat
            exact SMT.RenamingContext.denote_exists_of_typing typ_full hcompat hcov_t
        · have typ_fst_x : St.types ⊢ˢ .fst x : α0 := by
            apply SMT.Typing.fst
            exact typ_x_pair
          mspec loosenAux_prf_spec (Λ := St.types) (n := St.env.freshvarsc) (used := St.env.usedVars)
            typ_fst_x hαL.toCastPath (Δdummy) (hcov_dummy (.fst x))
          next out =>
          obtain ⟨x!, x!_spec⟩ := out
          mrename_i pre
          mintro ∀St1
          mpure pre
          obtain ⟨hn1, St1_types_eq, x!_fresh, x!_not_used, used_sub1, keys_sub1, preserves1, typ_x!, typ_x!_spec, typ_x!_St1, typ_x!_spec_St1, fv_x!_spec, _⟩ := pre
          mspec SMT.declareConst_spec (v := x!) (τ := τ) (decl := St1.env.declarations)
            (as := St1.env.asserts) (n := St1.env.freshvarsc) (Γ := St1.types) (used := St1.env.usedVars)
          mrename_i pre
          mintro ∀St2
          mpure pre
          obtain ⟨_, _, St2_fvc_eq, St2_used_eq, St2_types_eq⟩ := pre
          have typ_S_opt_St2 : St2.types ⊢ˢ S : .fun τ (.option β') := by
            rw [St2_types_eq]
            exact SMT.Typing.weakening
              (h := fun v hv => St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh hv))
              typ_S_opt
          mspec loosenAux_prf_spec (Λ := St2.types) (n := St2.env.freshvarsc) (used := St2.env.usedVars)
            typ_S_opt_St2
            (.fun (not_eq_of_beq_eq_false rfl) (castPath.reflexive τ) (.opt hβR.toCastPath))
            (Δdummy) (hcov_dummy S)
          · mpure_intro
            and_intros
            · trivial
            · trivial
            · rw [St2_types_eq, St2_used_eq]
              exact keys_sub1
            · trivial
          · rename_i out
            mrename_i pre
            mintro ∀St3
            mpure pre
            set S! : SMT.𝒱 := out.1
            set S!_spec : SMT.Term := out.2
            dsimp [S!, S!_spec] at pre
            obtain ⟨hn2, St3_types_eq, S!_fresh, S!_not_used, used_sub2, keys_sub2, preserves2, typ_S!, typ_S!_spec, typ_S!_St3, typ_S!_spec_St3, fv_S!_spec, _⟩ := pre
            mspec Std.Do.Spec.map
            mspec SMT.declareConst_spec (v := S!) (τ := .fun τ (.option β0)) (decl := St3.env.declarations)
              (as := St3.env.asserts) (n := St3.env.freshvarsc) (Γ := St3.types) (used := St3.env.usedVars)
            mrename_i pre
            mintro ∀St4
            mpure pre
            obtain ⟨_, _, St4_fvc_eq, St4_used_eq, St4_types_eq⟩ := pre
            have typ_full :
                St4.types ⊢ˢ
                  (x!_spec ∧ˢ S!_spec) ∧ˢ
                    ((SMT.Term.app (.var out.1) (.var x!)) =ˢ (SMT.Term.snd x).some) :
                  .bool := by
              rw [St4_types_eq]
              dsimp [S!, S!_spec] at *
              have typ_x!_spec_St2 : St2.types ⊢ˢ x!_spec : .bool := by
                rw [St2_types_eq]
                exact typ_x!_spec_St1
              have typ_x!_spec_St3 : St3.types ⊢ˢ x!_spec : .bool := by
                exact SMT.Typing.weakening
                  (h := fun v hv => St3_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv))
                  typ_x!_spec_St2
              have typ_x!_St2 : St2.types ⊢ˢ .var x! : τ := by
                rw [St2_types_eq]
                exact typ_x!_St1
              have typ_x!_St3 : St3.types ⊢ˢ .var x! : τ := by
                exact SMT.Typing.weakening
                  (h := fun v hv => St3_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv))
                  typ_x!_St2
              have typ_snd_x : St.types ⊢ˢ .snd x : β0 := by
                apply SMT.Typing.snd
                exact typ_x_pair
              have typ_snd_x_St2 : St2.types ⊢ˢ .snd x : β0 := by
                rw [St2_types_eq]
                exact SMT.Typing.weakening
                  (h := fun v hv => St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh hv))
                  typ_snd_x
              have typ_snd_x_St3 : St3.types ⊢ˢ .snd x : β0 := by
                exact SMT.Typing.weakening
                  (h := fun v hv => St3_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv))
                  typ_snd_x_St2
              apply SMT.Typing.and
              · apply SMT.Typing.and
                · exact typ_x!_spec_St3
                · exact typ_S!_spec_St3
              · refine SMT.Typing.eq
                  (Γ := St3.types)
                  (t₁ := .app (.var out.1) (.var x!))
                  (t₂ := .some (.snd x))
                  (τ := .option β0) ?_ ?_
                · apply SMT.Typing.app
                  · exact typ_S!_St3
                  · exact typ_x!_St3
                · apply SMT.Typing.some
                  exact typ_snd_x_St3
            mpure_intro
            and_intros
            · rw [St4_fvc_eq]
              calc
                St.env.freshvarsc ≤ St1.env.freshvarsc := hn1
                _ = St2.env.freshvarsc := by symm; exact St2_fvc_eq
                _ ≤ St3.env.freshvarsc := hn2
            · have hsub12 : St.types ⊆ St2.types := by
                intro v hv
                rw [St2_types_eq]
                exact St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh hv)
              have hsub24 : St2.types ⊆ St4.types := by
                intro v hv
                rw [St4_types_eq]
                exact St3_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv)
              intro v hv
              exact hsub24 (hsub12 hv)
            · rw [St4_types_eq, St4_used_eq]
              exact keys_sub2
            · rw [←St_used_eq, St4_used_eq]
              intro v hv
              exact used_sub2 (by rw [St2_used_eq]; exact used_sub1 hv)
            · trivial
            · exact typ_full
            · -- fv tracking
              -- hv : (v ∈ fv x!_spec ∨ v ∈ fv out.2) ∨ (v = out.1 ∨ v = x!) ∨ v ∈ fv x
              -- St.types ⊆ St2.types (via insert and rewrite)
              have hsub_St_St2 : St.types ⊆ St2.types := by
                intro ⟨k, t⟩ hk
                rw [St2_types_eq]
                exact St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh hk)
              intro v hv
              simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
              rcases hv with (h_xspec | h_Sspec) | (h_S! | h_x!) | h_x
              · -- v ∈ fv x!_spec ⊆ fv x.fst ∪ {x!}
                have hmem := fv_x!_spec h_xspec
                rcases List.mem_union_iff.mp hmem with hxfst | hx_in
                · -- hxfst : v ∈ fv x.fst, want: v ∈ fv x.
                  simp only [SMT.fv] at hxfst
                  exact Or.inl hxfst
                · have heq : v = x! := List.mem_singleton.mp hx_in
                  subst heq
                  exact Or.inr (Or.inr (fun hΛ => x!_fresh hΛ))
              · -- v ∈ fv out.2 = fv S!_spec ⊆ fv S ∪ {out.1}
                have hmem := fv_S!_spec h_Sspec
                rcases List.mem_union_iff.mp hmem with hS | hS_in
                · exact Or.inr (Or.inl hS)
                · have heq : v = S! := List.mem_singleton.mp hS_in
                  subst heq
                  refine Or.inr (Or.inr (fun hΛ => ?_))
                  exact S!_fresh (AList.mem_of_subset hsub_St_St2 hΛ)
              · -- v = out.1 = S!
                subst h_S!
                refine Or.inr (Or.inr (fun hΛ => ?_))
                exact S!_fresh (AList.mem_of_subset hsub_St_St2 hΛ)
              · -- v = x!
                subst h_x!
                exact Or.inr (Or.inr (fun hΛ => x!_fresh hΛ))
              · -- h_x : v ∈ fv x (after simp unfolds .some and .snd)
                exact Or.inl h_x
            · -- preservation: chain preserves1 (St → St1 = St2) and preserves2 (St2 → St3 = St4).
              intro v hv_used hv_notΛ
              rw [St_used_eq] at preserves1
              have hv_not_St1 : v ∉ St1.types := preserves1 v hv_used hv_notΛ
              have hv_not_St2 : v ∉ St2.types := by
                rw [St2_types_eq]; exact hv_not_St1
              have hv_St2_used : v ∈ St2.env.usedVars := by
                rw [St2_used_eq]; exact used_sub1 (St_used_eq ▸ hv_used)
              have hv_not_St3 : v ∉ St3.types := preserves2 v hv_St2_used hv_not_St2
              rw [St4_types_eq]
              exact hv_not_St3
            · -- totality: typing of full term plus `denote_exists_of_typing`.
              intro Δctx hcov_t hcompat
              exact SMT.RenamingContext.denote_exists_of_typing typ_full hcompat hcov_t
        · mspec Std.Do.Spec.throw_StateT
        · have typ_snd_x : St.types ⊢ˢ .snd x : β0 := by
            apply SMT.Typing.snd
            exact typ_x_pair
          mspec loosenAux_prf_spec (Λ := St.types) (n := St.env.freshvarsc) (used := St.env.usedVars)
            typ_snd_x hβL2.toCastPath (Δdummy) (hcov_dummy (.snd x))
          next out =>
          obtain ⟨y!, y!_spec⟩ := out
          mrename_i pre
          mintro ∀St1
          mpure pre
          obtain ⟨hn1, St1_types_eq, y!_fresh, y!_not_used, used_sub1, keys_sub1, preserves1, typ_y!, typ_y!_spec, typ_y!_St1, typ_y!_spec_St1, fv_y!_spec, _⟩ := pre
          mspec SMT.declareConst_spec (v := y!) (τ := β') (decl := St1.env.declarations)
            (as := St1.env.asserts) (n := St1.env.freshvarsc) (Γ := St1.types) (used := St1.env.usedVars)
          mrename_i pre
          mintro ∀St2
          mpure pre
          obtain ⟨_, _, St2_fvc_eq, St2_used_eq, St2_types_eq⟩ := pre
          have typ_S_opt_St2 : St2.types ⊢ˢ S : .fun τ (.option β') := by
            rw [St2_types_eq]
            exact SMT.Typing.weakening
              (h := fun v hv => St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem y!_fresh hv))
              typ_S_opt
          mspec loosenAux_prf_spec (Λ := St2.types) (n := St2.env.freshvarsc) (used := St2.env.usedVars)
            typ_S_opt_St2
            (.fun (not_eq_of_beq_eq_false rfl) hαR.toCastPath (castPath.reflexive (.option β')))
            (Δdummy) (hcov_dummy S)
          · mpure_intro
            and_intros
            · trivial
            · trivial
            · rw [St2_types_eq, St2_used_eq]
              exact keys_sub1
            · trivial
          · rename_i out
            mrename_i pre
            mintro ∀St3
            mpure pre
            set S! : SMT.𝒱 := out.1
            set S!_spec : SMT.Term := out.2
            dsimp [S!, S!_spec] at pre
            obtain ⟨hn2, St3_types_eq, S!_fresh, S!_not_used, used_sub2, keys_sub2, preserves2, typ_S!, typ_S!_spec, typ_S!_St3, typ_S!_spec_St3, fv_S!_spec, _⟩ := pre
            mspec Std.Do.Spec.map
            mspec SMT.declareConst_spec (v := S!) (τ := .fun α0 (.option β')) (decl := St3.env.declarations)
              (as := St3.env.asserts) (n := St3.env.freshvarsc) (Γ := St3.types) (used := St3.env.usedVars)
            mrename_i pre
            mintro ∀St4
            mpure pre
            obtain ⟨_, _, St4_fvc_eq, St4_used_eq, St4_types_eq⟩ := pre
            have typ_full :
                St4.types ⊢ˢ
                  (y!_spec ∧ˢ S!_spec) ∧ˢ
                    ((SMT.Term.app (.var out.1) (.fst x)) =ˢ (SMT.Term.var y!).some) :
                  .bool := by
              rw [St4_types_eq]
              dsimp [S!, S!_spec] at *
              have typ_y!_spec_St2 : St2.types ⊢ˢ y!_spec : .bool := by
                rw [St2_types_eq]
                exact typ_y!_spec_St1
              have typ_y!_spec_St3 : St3.types ⊢ˢ y!_spec : .bool := by
                exact SMT.Typing.weakening
                  (h := fun v hv => St3_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv))
                  typ_y!_spec_St2
              have typ_y!_St2 : St2.types ⊢ˢ .var y! : β' := by
                rw [St2_types_eq]
                exact typ_y!_St1
              have typ_y!_St3 : St3.types ⊢ˢ .var y! : β' := by
                exact SMT.Typing.weakening
                  (h := fun v hv => St3_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv))
                  typ_y!_St2
              have typ_fst_x : St.types ⊢ˢ .fst x : α0 := by
                apply SMT.Typing.fst
                exact typ_x_pair
              have typ_fst_x_St2 : St2.types ⊢ˢ .fst x : α0 := by
                rw [St2_types_eq]
                exact SMT.Typing.weakening
                  (h := fun v hv => St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem y!_fresh hv))
                  typ_fst_x
              have typ_fst_x_St3 : St3.types ⊢ˢ .fst x : α0 := by
                exact SMT.Typing.weakening
                  (h := fun v hv => St3_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv))
                  typ_fst_x_St2
              apply SMT.Typing.and
              · apply SMT.Typing.and
                · exact typ_y!_spec_St3
                · exact typ_S!_spec_St3
              · refine SMT.Typing.eq
                  (Γ := St3.types)
                  (t₁ := .app (.var out.1) (.fst x))
                  (t₂ := .some (.var y!))
                  (τ := .option β') ?_ ?_
                · apply SMT.Typing.app
                  · exact typ_S!_St3
                  · exact typ_fst_x_St3
                · apply SMT.Typing.some
                  exact typ_y!_St3
            mpure_intro
            and_intros
            · rw [St4_fvc_eq]
              calc
                St.env.freshvarsc ≤ St1.env.freshvarsc := hn1
                _ = St2.env.freshvarsc := by symm; exact St2_fvc_eq
                _ ≤ St3.env.freshvarsc := hn2
            · have hsub12 : St.types ⊆ St2.types := by
                intro v hv
                rw [St2_types_eq]
                exact St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem y!_fresh hv)
              have hsub24 : St2.types ⊆ St4.types := by
                intro v hv
                rw [St4_types_eq]
                exact St3_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv)
              intro v hv
              exact hsub24 (hsub12 hv)
            · rw [St4_types_eq, St4_used_eq]
              exact keys_sub2
            · rw [←St_used_eq, St4_used_eq]
              intro v hv
              exact used_sub2 (by rw [St2_used_eq]; exact used_sub1 hv)
            · trivial
            · exact typ_full
            · -- fv tracking
              have hsub_St_St2 : St.types ⊆ St2.types := by
                intro ⟨k, t⟩ hk
                rw [St2_types_eq]
                exact St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem y!_fresh hk)
              intro v hv
              simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
              -- term: y!_spec ∧ˢ S!_spec ∧ˢ ((@ˢ.var S!) x.fst =ˢ (.var y!).some)
              -- hv : (v ∈ fv y!_spec ∨ v ∈ fv out.2) ∨ ((v = out.1 ∨ v ∈ fv x.fst) ∨ v = y!)
              rcases hv with (h_yspec | h_Sspec) | (h_S! | h_fst_x) | h_y!
              · -- v ∈ fv y!_spec ⊆ fv x.snd ∪ {y!}
                have hmem := fv_y!_spec h_yspec
                rcases List.mem_union_iff.mp hmem with hxsnd | hy_in
                · -- fv x.snd = fv x
                  simp only [SMT.fv] at hxsnd
                  exact Or.inl hxsnd
                · have heq : v = y! := List.mem_singleton.mp hy_in
                  subst heq
                  exact Or.inr (Or.inr (fun hΛ => y!_fresh hΛ))
              · -- v ∈ fv out.2 = fv S!_spec ⊆ fv S ∪ {out.1}
                have hmem := fv_S!_spec h_Sspec
                rcases List.mem_union_iff.mp hmem with hS | hS_in
                · exact Or.inr (Or.inl hS)
                · have heq : v = S! := List.mem_singleton.mp hS_in
                  subst heq
                  refine Or.inr (Or.inr (fun hΛ => ?_))
                  exact S!_fresh (AList.mem_of_subset hsub_St_St2 hΛ)
              · -- v = out.1 = S!
                subst h_S!
                refine Or.inr (Or.inr (fun hΛ => ?_))
                exact S!_fresh (AList.mem_of_subset hsub_St_St2 hΛ)
              · -- h_fst_x : v ∈ fv x (after simp; fv x.fst = fv x)
                exact Or.inl h_fst_x
              · -- v = y!
                subst h_y!
                exact Or.inr (Or.inr (fun hΛ => y!_fresh hΛ))
            · -- preservation: chain preserves1 (St → St1 = St2) and preserves2 (St2 → St3 = St4).
              intro v hv_used hv_notΛ
              rw [St_used_eq] at preserves1
              have hv_not_St1 : v ∉ St1.types := preserves1 v hv_used hv_notΛ
              have hv_not_St2 : v ∉ St2.types := by
                rw [St2_types_eq]; exact hv_not_St1
              have hv_St2_used : v ∈ St2.env.usedVars := by
                rw [St2_used_eq]; exact used_sub1 (St_used_eq ▸ hv_used)
              have hv_not_St3 : v ∉ St3.types := preserves2 v hv_St2_used hv_not_St2
              rw [St4_types_eq]
              exact hv_not_St3
            · -- totality: typing of full term plus `denote_exists_of_typing`.
              intro Δctx hcov_t hcompat
              exact SMT.RenamingContext.denote_exists_of_typing typ_full hcompat hcov_t
        · mspec loosenAux_prf_spec (Λ := St.types) (n := St.env.freshvarsc) (used := St.env.usedVars)
            typ_S_opt
            (.fun (not_eq_of_beq_eq_false rfl) hαR.toCastPath (.opt hβR2.toCastPath))
            (Δdummy) (hcov_dummy S)
          rename_i out
          mrename_i pre
          mintro ∀St1
          mpure pre
          set S! : SMT.𝒱 := out.1
          set S!_spec : SMT.Term := out.2
          dsimp [S!, S!_spec] at pre
          obtain ⟨hn1, St1_types_eq, S!_fresh, S!_not_used, used_sub1, keys_sub1, preserves1, typ_S!, typ_S!_spec, typ_S!_St1, typ_S!_spec_St1, fv_S!_spec, _⟩ := pre
          mspec Std.Do.Spec.map
          mspec SMT.declareConst_spec (v := S!) (τ := .fun α0 (.option β0)) (decl := St1.env.declarations)
            (as := St1.env.asserts) (n := St1.env.freshvarsc) (Γ := St1.types) (used := St1.env.usedVars)
          mrename_i pre
          mintro ∀St2
          mpure pre
          obtain ⟨_, _, St2_fvc_eq, St2_used_eq, St2_types_eq⟩ := pre
          have typ_full :
              St2.types ⊢ˢ
                S!_spec ∧ˢ
                  ((SMT.Term.app (.var out.1) (.fst x)) =ˢ (SMT.Term.snd x).some) :
                .bool := by
            rw [St2_types_eq]
            dsimp [S!, S!_spec] at *
            have typ_fst_x : St.types ⊢ˢ .fst x : α0 := by
              apply SMT.Typing.fst
              exact typ_x_pair
            have typ_fst_x_St1 : St1.types ⊢ˢ .fst x : α0 := by
              exact SMT.Typing.weakening
                (h := fun v hv => St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv))
                typ_fst_x
            have typ_snd_x : St.types ⊢ˢ .snd x : β0 := by
              apply SMT.Typing.snd
              exact typ_x_pair
            have typ_snd_x_St1 : St1.types ⊢ˢ .snd x : β0 := by
              exact SMT.Typing.weakening
                (h := fun v hv => St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv))
                typ_snd_x
            apply SMT.Typing.and
            · exact typ_S!_spec_St1
            · refine SMT.Typing.eq
                (Γ := St1.types)
                (t₁ := .app (.var out.1) (.fst x))
                (t₂ := .some (.snd x))
                (τ := .option β0) ?_ ?_
              · apply SMT.Typing.app
                · exact typ_S!_St1
                · exact typ_fst_x_St1
              · apply SMT.Typing.some
                exact typ_snd_x_St1
          mpure_intro
          and_intros
          · rw [St2_fvc_eq]
            exact hn1
          · intro v hv
            rw [St2_types_eq]
            exact St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem S!_fresh hv)
          · rw [St2_types_eq, St2_used_eq]
            exact keys_sub1
          · rw [←St_used_eq, St2_used_eq]
            exact used_sub1
          · trivial
          · exact typ_full
          · -- fv tracking
            -- term: S!_spec ∧ˢ ((@ˢ.var S!) x.fst =ˢ x.snd.some)
            intro v hv
            simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
            -- hv : v ∈ fv S!_spec ∨ ((v = out.1 ∨ v ∈ fv x.fst) ∨ v ∈ fv x.snd.some)
            rcases hv with h_Sspec | (h_S! | h_fst_x) | h_snd_x
            · -- v ∈ fv S!_spec ⊆ fv S ∪ {S!}
              have hmem := fv_S!_spec h_Sspec
              rcases List.mem_union_iff.mp hmem with hS | hS_in
              · exact Or.inr (Or.inl hS)
              · have heq : v = S! := List.mem_singleton.mp hS_in
                subst heq
                exact Or.inr (Or.inr (fun hΛ => S!_fresh hΛ))
            · -- v = out.1 = S!
              subst h_S!
              exact Or.inr (Or.inr (fun hΛ => S!_fresh hΛ))
            · -- v ∈ fv x.fst = fv x
              exact Or.inl h_fst_x
            · -- v ∈ fv x.snd.some = fv x
              exact Or.inl h_snd_x
          · -- preservation: St2.types = St1.types, use preserves1.
            intro v hv_used hv_notΛ
            rw [St2_types_eq]
            rw [St_used_eq] at preserves1
            exact preserves1 v hv_used hv_notΛ
          · -- totality: typing of full term plus `denote_exists_of_typing`.
            intro Δctx hcov_t hcompat
            exact SMT.RenamingContext.denote_exists_of_typing typ_full hcompat hcov_t
        · mspec Std.Do.Spec.throw_StateT
        · mspec Std.Do.Spec.throw_StateT
      | int | bool | unit | option | «fun» _ _ =>
        unfold castMembership
        conv =>
          enter [2,1,1]
          simp [hσ, hα]
        mspec Std.Do.Spec.throw_StateT
    | int | unit | pair | «fun» _ _ =>
      unfold castMembership
      conv =>
        enter [2,1,1]
        simp [hσ]
      mspec Std.Do.Spec.throw_StateT

set_option maxHeartbeats 3000000 in
/--
Branch-2 specialization of `castMembership_spec` exposing Δ-universal adequacy.
Specifically for the case `castMembership ⟨x, α⟩ ⟨S, .fun τ .bool⟩` with `α ⊑ τ`
and `α ≠ τ` (so the encoder takes the "loosen x up to τ" branch).

Adds a Δ-universal adequacy clause derived from `loosenAux_prf_spec_univ`,
exposing the cast denotation in the post-condition.
-/
theorem castMembership_branch2_spec.{u}
  {α τ : SMT.SMTType} {x S : SMT.Term} {Λ : SMT.TypeContext} {n : ℕ}
  (typ_x : Λ ⊢ˢ x : α) (typ_S : Λ ⊢ˢ S : .fun τ .bool)
  (α_ne_τ : α ≠ τ) (α_le_τ : α ⊑ τ)
  {used : List SMT.𝒱} :
  ⦃ λ ⟨E, Λ'⟩ ↦ ⌜Λ' = Λ ∧ E.freshvarsc = n ∧ AList.keys Λ ⊆ E.usedVars ∧ E.usedVars = used⌝ ⦄
    castMembership ⟨x, α⟩ ⟨S, .fun τ .bool⟩
  ⦃ ⇓? ⟨t, σ⟩ ⟨E', Λ'⟩ =>
    ⌜n ≤ E'.freshvarsc ∧ Λ ⊆ Λ' ∧ AList.keys Λ' ⊆ E'.usedVars ∧ used ⊆ E'.usedVars ∧
      σ = .bool ∧ Λ' ⊢ˢ t : .bool ∧
      (∀ v ∈ SMT.fv t, v ∈ SMT.fv x ∨ v ∈ SMT.fv S ∨ v ∉ Λ) ∧
      (∀ v ∈ used, v ∉ Λ → v ∉ Λ') ∧
      (∀ (Δctx : SMT.RenamingContext.Context.{u}) (hcov_t : SMT.RenamingContext.CoversFV Δctx t)
          (_hcompat : SMT.RenamingContext.RespectsTypeContext Δctx Λ'),
         ∃ denCM : SMT.Dom.{u},
           ⟦t.abstract Δctx hcov_t⟧ˢ = some denCM ∧ denCM.snd.fst = .bool) ∧
      -- Δ-universal adequacy clause: for any Δctx where x and S denote, the
      -- output term `t` denotes to a boolean which is `zftrue` iff the
      -- denotation of `x` (cast up to τ) lies in the relation `S`.
      (∃ (x! : SMT.𝒱) (x!_spec : SMT.Term),
         t = x!_spec ∧ˢ .app S (.var x!) ∧
         x! ∉ Λ ∧
         x! ∉ used ∧
         (∀ («Δctx» : SMT.RenamingContext.Context.{u})
            (hx : SMT.RenamingContext.CoversFV «Δctx» x)
            (pf : ∀ (x_! : SMT.𝒱) (X! : SMT.Dom),
              ∀ v ∈ SMT.fv (SMT.Term.var x_!),
                (Function.update «Δctx» x_! (some X!) v).isSome = true),
          ∀ (X : SMT.Dom), ⟦x.abstract «Δctx» hx⟧ˢ = some X →
            ∃ (Φ X! : SMT.Dom)
              (_ : ⟦(SMT.Term.var x!).abstract (Function.update «Δctx» x! (some X!))
                (pf x! X!)⟧ˢ = some X!)
              (hφ : SMT.RenamingContext.CoversFV
                (Function.update «Δctx» x! (some X!)) x!_spec)
              (_ : ⟦x!_spec.abstract (Function.update «Δctx» x! (some X!)) hφ⟧ˢ = some Φ),
              (Φ.2.1 = SMT.SMTType.bool) ∧
              (Φ.1 = ZFSet.zftrue ∧ (X.1.pair X!.1) ∈ (castZF_of_path α_le_τ.toCastPath).1) ∧
              (∀ (Y : SMT.Dom) (_ : Y.2.1 = τ)
                (hφY : SMT.RenamingContext.CoversFV
                  (Function.update «Δctx» x! (some Y)) x!_spec),
                (⟦x!_spec.abstract (Function.update «Δctx» x! (some Y)) hφY⟧ˢ).isSome = true)))⌝ ⦄ := by
  mintro pre ∀St
  mpure pre
  obtain ⟨rfl, rfl, St_sub, St_used_eq⟩ := pre
  unfold castMembership
  conv =>
    enter [2,1,1]
    simp only [bind_pure_comp]
  -- Branch 2 condition: α ≠ τ, α ⊑ τ.
  rw [dif_neg α_ne_τ, dif_pos α_le_τ]
  -- Use loosenAux_prf_spec_univ to get the Δ-universal adequacy.
  mspec loosenAux_prf_spec_univ (Λ := St.types) (n := St.env.freshvarsc)
    (used := St.env.usedVars) typ_x α_le_τ.toCastPath
  next out =>
  obtain ⟨x!, x!_spec⟩ := out
  mrename_i pre
  mintro ∀St1
  mpure pre
  obtain ⟨hn1, St1_types_eq, x!_fresh, x!_not_used, used_sub1, keys_sub1, preserves1,
    typ_x!, typ_x!_spec, typ_x!_St1, typ_x!_spec_St1, fv_x!_spec, hadq_univ⟩ := pre
  mspec Std.Do.Spec.map
  mspec SMT.declareConst_spec (v := x!) (τ := τ) (decl := St1.env.declarations)
    (as := St1.env.asserts) (n := St1.env.freshvarsc) (Γ := St1.types)
    (used := St1.env.usedVars)
  mrename_i pre
  mintro ∀St2
  mpure pre
  obtain ⟨_, _, St2_fvc_eq, St2_used_eq, St2_types_eq⟩ := pre
  have typ_full : St2.types ⊢ˢ x!_spec ∧ˢ .app S (.var x!) : .bool := by
    rw [St2_types_eq]
    apply SMT.Typing.and
    · exact typ_x!_spec_St1
    · apply SMT.Typing.app
      · exact SMT.Typing.weakening
          (h := fun v hv => St1_types_eq
            (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh hv))
          typ_S
      · exact typ_x!_St1
  mpure_intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [St2_fvc_eq]; exact hn1
  · intro v hv
    rw [St2_types_eq]
    exact St1_types_eq (SMT.TypeContext.entries_subset_insert_of_notMem x!_fresh hv)
  · rw [St2_types_eq, St2_used_eq]; exact keys_sub1
  · rw [←St_used_eq, St2_used_eq]; exact used_sub1
  · trivial
  · exact typ_full
  · -- fv tracking
    intro v hv
    simp only [SMT.fv, List.mem_append, List.mem_singleton] at hv
    rcases hv with h_spec | h_S | rfl
    · have hmem := fv_x!_spec h_spec
      rcases List.mem_union_iff.mp hmem with hx | hx_in
      · exact Or.inl hx
      · have heq : v = x! := List.mem_singleton.mp hx_in
        subst heq
        exact Or.inr (Or.inr (fun hΛ => x!_fresh hΛ))
    · exact Or.inr (Or.inl h_S)
    · exact Or.inr (Or.inr (fun hΛ => x!_fresh hΛ))
  · intro v hv_used hv_notΛ
    rw [St2_types_eq]
    rw [St_used_eq] at preserves1
    exact preserves1 v hv_used hv_notΛ
  · intro Δctx hcov_t hcompat
    exact SMT.RenamingContext.denote_exists_of_typing typ_full hcompat hcov_t
  · -- Δ-universal adequacy clause.
    refine ⟨x!, x!_spec, rfl, x!_fresh, ?_, hadq_univ⟩
    -- x! ∉ used: we have x!_not_used : x! ∉ St.env.usedVars = used.
    rw [St_used_eq] at x!_not_used
    exact x!_not_used
