import B.Reasoning.Lemmas
import SMT.PHOAS.SMTPHOAS
import SMT.Reasoning.Lemmas
import Encoder.Encoder

open B SMT ZFSet Classical

/--
Translation from B types to SMT types is correct in the sense that the sets
`they represent are isomorphic.
-/
theorem BType_iso_SMTType (α : BType) : ⟦α⟧ᶻ ≅ᶻ ⟦α.toSMTType⟧ᶻ := by
  induction α with
  | int | bool => exact ZFSet.isIso_refl _
  | set α ih =>
    exact ZFSet.isIso_trans ZFSet.isIso_powerset_char_pred
      (ZFSet.isIso_of_funs ih (ZFSet.isIso_refl _))
  | prod _ _ ih ih' => exact ZFSet.isIso_of_prod ih ih'

/--
Canonical isomorphism between `⟦τ⟧ᶻ` and `⟦τ.toSMTType⟧ᶻ`. Bases cases are identities, and
the inductive cases are built using the canonical isomorphisms of the subcomponents inductively.
-/
noncomputable def BType.canonicalIsoSMTType.{u} : (τ : BType) → {ζ : ZFSet.{u} // ∃ (ζ_isfunc : ⟦τ⟧ᶻ.IsFunc ⟦τ.toSMTType⟧ᶻ ζ), ZFSet.IsBijective ζ}
  | .int =>
    ⟨ZFSet.Id Int, Id.IsFunc, Id.IsBijective⟩
  | .bool =>
    ⟨ZFSet.Id 𝔹, Id.IsFunc, Id.IsBijective⟩
  | .set α =>
    let ⟨ζ, ζ_def⟩ := canonicalIsoSMTType α
    let ζ_isfunc := ζ_def.1
    let ζ_bij := ζ_def.2
    let ξ : ZFSet :=
      λᶻ: ⟦α⟧ᶻ.powerset → (⟦(α.toSMTType)⟧ᶻ.funs 𝔹)
        |             X ↦ if hX : X ∈ ⟦α⟧ᶻ.powerset then
                            λᶻ: ⟦(α.toSMTType)⟧ᶻ → 𝔹
                              |               x  ↦ if hx : x ∈ ⟦α.toSMTType⟧ᶻ then
                                                    let ζinvx : ZFSet := @ᶻζ⁻¹ ⟨x, by
                                                      rwa [is_func_dom_eq (inv_is_func_of_bijective ζ_bij)]⟩ -- ζ⁻¹(x) ∈ ⟦α⟧ᶻ
                                                    ZFBool.ofBool <| ζinvx ∈ X
                                                  else ∅
                          else ∅
    have hξ : ⟦α⟧ᶻ.powerset.IsFunc (⟦(α.toSMTType)⟧ᶻ.funs 𝔹) ξ := by
      apply lambda_isFunc
      intro x hx
      rw [mem_funs, dite_cond_eq_true (eq_true hx)]
      and_intros
      · intro z hz
        rw [mem_lambda] at hz
        obtain ⟨a, b, rfl, ha, hb, rfl⟩ := hz
        rw [dite_cond_eq_true (eq_true ha)] at hb ⊢
        rw [pair_mem_prod]
        exact ⟨ha, hb⟩
      · intro z hz
        let ζinvz : ZFSet := @ᶻζ⁻¹ ⟨z, by rwa [is_func_dom_eq (inv_is_func_of_bijective ζ_bij)]⟩
        simp_rw [lambda_spec, dite_cond_eq_true (eq_true hz)]
        use ZFBool.ofBool <| ζinvz ∈ x
        beta_reduce
        and_intros
        · exact hz
        · apply ZFBool.mem_ofBool_𝔹
        · rfl
        · rintro y ⟨-, hy, rfl⟩
          rfl
    have ξ_bij : ξ.IsBijective := by
      and_intros
      · intro x y f hx hy hf xf yf
        simp only [mem_powerset, mem_lambda, pair_inj, mem_funs, existsAndEq, and_true, exists_eq_left', ξ] at hx hy hf xf yf
        obtain ⟨-, f_isfunc, rfl⟩ := xf
        obtain ⟨-, _, eq⟩ := yf
        rw [dite_cond_eq_true (eq_true hx)] at f_isfunc eq
        rw [dite_cond_eq_true (eq_true hy), lambda_ext_iff (fun h ↦ by rw [dite_cond_eq_true (eq_true h)]; apply ZFBool.mem_ofBool_𝔹)] at eq

        ext1 z
        constructor <;> intro hz
        · let ζz : ZFSet := @ᶻζ ⟨z, by rw [is_func_dom_eq ζ_isfunc]; exact hx hz⟩
          specialize eq ζz (fapply_mem_range _ _)
          iterate 2 rw [dite_cond_eq_true (eq_true (fapply_mem_range _ _))] at eq
          rw [←Subtype.ext_iff] at eq
          conv at eq =>
            enter [1,1]
            rw [←fapply_composition (inv_is_func_of_bijective ζ_bij) ζ_isfunc (hx hz),
              fapply_eq_Image_singleton (IsFunc_of_composition_IsFunc (inv_is_func_of_bijective ζ_bij) ζ_isfunc) (hx hz)]
            conv =>
              enter [1,2,1,1]
              change ζ⁻¹ ∘ᶻ ζ
              rw [composition_self_inv_of_bijective ζ_bij]
            rw [←fapply_eq_Image_singleton Id.IsFunc (hx hz),
              fapply_Id (hx hz)]
            dsimp
            rw [eq_true hz, decide_true]
          conv at eq =>
            enter [2,1]
            rw [←fapply_composition (inv_is_func_of_bijective ζ_bij) ζ_isfunc (hx hz),
              fapply_eq_Image_singleton (IsFunc_of_composition_IsFunc (inv_is_func_of_bijective ζ_bij) ζ_isfunc) (hx hz)]
            conv =>
              enter [1,2,1,1]
              change ζ⁻¹ ∘ᶻ ζ
              rw [composition_self_inv_of_bijective ζ_bij]
            rw [←fapply_eq_Image_singleton Id.IsFunc (hx hz),
              fapply_Id (hx hz)]
            dsimp
          symm at eq
          rwa [ZFBool.ofBool, ←ZFBool.true, ←ZFBool.top_eq_true, ZFBool.ofBool_decide_eq_true_iff] at eq
        · let ζz : ZFSet := @ᶻζ ⟨z, by rw [is_func_dom_eq ζ_isfunc]; exact hy hz⟩
          specialize eq ζz (fapply_mem_range _ _)
          iterate 2 rw [dite_cond_eq_true (eq_true (fapply_mem_range _ _))] at eq
          rw [←Subtype.ext_iff] at eq
          conv at eq =>
            enter [1,1]
            rw [←fapply_composition (inv_is_func_of_bijective ζ_bij) ζ_isfunc (hy hz),
              fapply_eq_Image_singleton (IsFunc_of_composition_IsFunc (inv_is_func_of_bijective ζ_bij) ζ_isfunc) (hy hz)]
            conv =>
              enter [1,2,1,1]
              change ζ⁻¹ ∘ᶻ ζ
              rw [composition_self_inv_of_bijective ζ_bij]
            rw [←fapply_eq_Image_singleton Id.IsFunc (hy hz),
              fapply_Id (hy hz)]
            dsimp
          conv at eq =>
            enter [2,1]
            rw [←fapply_composition (inv_is_func_of_bijective ζ_bij) ζ_isfunc (hy hz),
              fapply_eq_Image_singleton (IsFunc_of_composition_IsFunc (inv_is_func_of_bijective ζ_bij) ζ_isfunc) (hy hz)]
            conv =>
              enter [1,2,1,1]
              change ζ⁻¹ ∘ᶻ ζ
              rw [composition_self_inv_of_bijective ζ_bij]
            rw [←fapply_eq_Image_singleton Id.IsFunc (hy hz),
              fapply_Id (hy hz)]
            dsimp
            rw [eq_true hz, decide_true]
          rwa [ZFBool.ofBool, ←ZFBool.true, ←ZFBool.top_eq_true, ZFBool.ofBool_decide_eq_true_iff] at eq
      · intro f hf
        rw [mem_funs] at hf
        let X : ZFSet := (⟦α⟧ᶻ).sep fun x ↦
          if hx : x ∈ ⟦α⟧ᶻ then
            let ζx : ZFSet := @ᶻζ ⟨x, by rwa [is_func_dom_eq ζ_isfunc]⟩
            -- fapply f ⟨x, hx'⟩ = ⊤
            let fζx := @ᶻf ⟨ζx, by
              rw [is_func_dom_eq hf]
              apply fapply_mem_range⟩
            fζx = zftrue
          else False
        use X
        and_intros
        · rw [mem_powerset]
          exact sep_subset_self
        · rw [lambda_spec]
          and_intros
          · rw [mem_powerset]
            exact sep_subset_self
          · rwa [mem_funs]
          · rw [dite_cond_eq_true (eq_true (by rw [mem_powerset]; exact sep_subset_self)),
              lambda_eta hf,
              lambda_ext_iff (fun h ↦ by rw [dite_cond_eq_true (eq_true h)]; apply fapply_mem_range)]
            intro w hw
            iterate 2 rw [dite_cond_eq_true (eq_true hw)]
            dsimp
            set fw : ZFBool := @ᶻf ⟨w, by rwa [is_func_dom_eq hf]⟩
            cases hfw : fw with
            | false =>
              symm
              rw [←Subtype.ext_iff, ZFBool.ofBool_decide_eq_false_iff]
              intro contr
              rw [mem_sep, dite_cond_eq_true (eq_true (fapply_mem_range _ _))] at contr
              dsimp at contr
              obtain ⟨-, contr⟩ := contr
              conv at contr =>
                enter [1,1]
                unfold fapply
                dsimp
              dsimp at contr
              generalize_proofs ζrel wa_ζinv aa'ζ a'bf at contr
              have ⟨a_mem, a_def⟩ := Classical.choose_spec wa_ζinv
              have ⟨a'_mem, a'_def⟩ := Classical.choose_spec aa'ζ
              have ⟨b_mem, b_def⟩ := Classical.choose_spec a'bf
              set! a := Classical.choose wa_ζinv with a_eq
              set! a' := Classical.choose aa'ζ with a'_eq
              set! b := Classical.choose a'bf with b_eq
              rw [←a_eq, mem_inv] at a_def
              have w_eq := fapply.of_pair (is_func_is_pfunc ζ_isfunc) a_def
              simp only [Subtype.ext_iff] at w_eq

              conv at a'_def =>
                rw [←a'_eq, ←a_eq, ←mem_inv ζrel]
              have ζinva'_eq_a := fapply.of_pair (is_func_is_pfunc (inv_is_func_of_bijective ζ_bij)) a'_def
              simp only [Subtype.ext_iff] at ζinva'_eq_a
              conv at b_def =>
                enter [2]
                conv =>
                  lhs
                  rw [←a'_eq]
                conv =>
                  rhs
                  rw [←b_eq]
              conv at w_eq =>
                simp only [←ζinva'_eq_a]
                rw [←fapply_composition ζ_isfunc (inv_is_func_of_bijective ζ_bij) a'_mem]
                unfold fapply
                dsimp
              generalize_proofs _ ha at w_eq
              have ⟨a_mem, ha⟩ := Classical.choose_spec ha
              conv at ha =>
                conv =>
                  enter [1]
                  rw [composition_inv_self_of_bijective ζ_bij]
                rw [pair_mem_Id_iff a'_mem, w_eq, ←a'_eq]
              rw [←b_eq] at contr
              rw [ha, contr] at b_def
              have := fapply.of_pair (is_func_is_pfunc hf) b_def
              unfold fw at hfw
              rw [this, ZFBool.bot_eq_false, ZFBool.false, Subtype.ext_iff] at hfw
              nomatch zftrue_ne_zffalse hfw
            | true =>
              symm
              rw [←Subtype.ext_iff, ZFBool.ofBool_decide_eq_true_iff]
              rw [mem_sep, dite_cond_eq_true (eq_true (fapply_mem_range _ _))]
              dsimp
              and_intros
              · apply fapply_mem_range
              · conv =>
                  enter [1,1]
                  unfold fapply
                  dsimp
                dsimp
                generalize_proofs ζrel wa_ζinv aa'ζ a'bf
                have ⟨a_mem, a_def⟩ := Classical.choose_spec wa_ζinv
                have ⟨a'_mem, a'_def⟩ := Classical.choose_spec aa'ζ
                have ⟨b_mem, b_def⟩ := Classical.choose_spec a'bf
                set b := Classical.choose a'bf
                set! a' := Classical.choose aa'ζ with a'_eq
                set! a := Classical.choose wa_ζinv with a_eq
                rw [←a_eq] at a_def
                rw [←a'_eq] at b_def
                conv at a'_def =>
                  enter [2]
                  conv => lhs; rw [←a_eq]
                  conv => rhs; rw [←a'_eq]
                have w_eq_a' : w = a' := by
                  rw [mem_inv] at a_def
                  apply ζ_isfunc.2 a a_mem |>.unique a_def a'_def
                have := fapply.of_pair (is_func_is_pfunc hf) b_def
                unfold fw at hfw
                simp only [←w_eq_a', Subtype.ext_iff, hfw] at this
                exact this.symm
    ⟨ξ, hξ, ξ_bij⟩
  | .prod α β =>
    let ⟨ζ, ζ_def⟩ := canonicalIsoSMTType α
    let ζ_isfunc := ζ_def.1
    let ζ_bij := ζ_def.2
    let ⟨ξ, ξ_def⟩ := canonicalIsoSMTType β
    let ξ_isfunc := ξ_def.1
    let ξ_bij := ξ_def.2

    let ζ_ξ := fprod ζ ξ
    have ζ_ξ_isfunc := fprod_is_func ζ_isfunc ξ_isfunc
    have ζ_ξ_bij := fprod_bijective_of_bijective ζ_bij ξ_bij
    ⟨ζ_ξ, ζ_ξ_isfunc, ζ_ξ_bij⟩

/--
Retraction from `⟦τ.toSMTType⟧ᶻ` to `⟦τ⟧ᶻ`. Bases cases are identities, and the inductive cases are
built using the retractions of the subcomponents inductively.

**NOTE:** nothing is enforced on the set passed as argument to reduce the complexity of the definition.
-/
noncomputable def retract : (τ : BType) → ZFSet → ZFSet
| .int | .bool => id
| .prod α β => fun u ↦
  let u₁ := u.π₁
  let u₂ := u.π₂
  (retract α u₁).pair (retract β u₂)
| .set α => fun f ↦
  let ⟨ζ, hζ⟩ := BType.canonicalIsoSMTType α
  let ζ_isfunc := hζ.1
  let ζ_bij := hζ.2

  (⟦α⟧ᶻ).sep fun x ↦
    if hx : x ∈ ⟦α⟧ᶻ then
      let ζx : ZFSet := @ᶻζ ⟨x, by rwa [ZFSet.is_func_dom_eq ζ_isfunc]⟩
      if hf : ⟦α.toSMTType⟧ᶻ.IsFunc 𝔹 f then
        -- fapply f ⟨x, hx'⟩ = ⊤
        let fx := @ᶻf ⟨ζx, by
          rw [is_func_dom_eq hf]
          apply fapply_mem_range⟩
        fx = zftrue
      else False
    else False

/--
`retract` is a left inverse for the corresponding canonical isomorphism, i.e.
`η_τ ∘ ζ_τ = id` where `ζ_τ` is the canonical isomorphism between `⟦τ⟧ᶻ` and `⟦τ.toSMTType⟧ᶻ`,
and `η` is the retraction from `⟦τ.toSMTType⟧ᶻ` to `⟦τ⟧ᶻ`.
-/
@[simp]
theorem retract_of_canonical.{u} {x : ZFSet.{u}} (τ : BType) (hx : x ∈ ⟦τ⟧ᶻ) {ζ}
  (hζ : ζ = BType.canonicalIsoSMTType τ := by rfl) :
    retract τ (fapply ζ (is_func_is_pfunc ζ.2.1) ⟨x, by rwa [ZFSet.is_func_dom_eq ζ.2.1]⟩) = x := by
  -- preprocess proof
  obtain ⟨ζ, ζ_isfunc, ζ_bij⟩ := ζ
  rw [Subtype.ext_iff] at hζ
  dsimp at hζ

  induction τ generalizing ζ x with
  | int | bool =>
    rw [BType.canonicalIsoSMTType] at hζ
    subst ζ
    rw [retract, fapply_Id (by exact hx)]
    rfl
  | set α =>
    rename' x => X -- readability

    rw [BType.canonicalIsoSMTType] at hζ
    dsimp at hζ
    -- subst ζ

    rw [retract]
    dsimp
    generalize_proofs ζ_ispfunc _ X_mem_dom ζX_is_pfunc_of_is_func ζ_α_is_pfunc ζ_α_dom app_ζ_α_dom
    let ζ_α : ZFSet := (BType.canonicalIsoSMTType α).1
    have ζ_α_is_func := (BType.canonicalIsoSMTType α).2.1
    have ζ_α_bij := (BType.canonicalIsoSMTType α).2.2
    have ζ_α_inv := ZFSet.subset_prod_inv ζ_α_is_func.1
    refold_let ζ_α at *

    have ζ_restr : (@ᶻζ ⟨X, X_mem_dom⟩).val =
        λᶻ: ⟦α.toSMTType⟧ᶻ → 𝔹
          |             z  ↦ if hx : z ∈ ⟦α.toSMTType⟧ᶻ then
                              ZFBool.ofBool (decide (↑(@ᶻζ_α⁻¹ ⟨z, by rwa [is_func_dom_eq (inv_is_func_of_bijective ζ_α_bij)]⟩) ∈ X))
                            else ∅
        := by
      subst ζ
      rw [BType.toZFSet] at hx
      rw [fapply_lambda (B := ⟦α.toSMTType⟧ᶻ.funs 𝔹) ?_ hx, ite_cond_eq_true _ _ (eq_true hx)]

      intro _ h
      rw [ite_cond_eq_true _ _ (eq_true h)]
      apply mem_funs_of_lambda
      intro x hx
      rw [dite_cond_eq_true (eq_true hx)]
      apply ZFBool.mem_ofBool_𝔹

    ext1 z
    constructor <;> intro hz
    · rw [mem_sep] at hz
      obtain ⟨hz, eq⟩ := hz
      rw [dite_cond_eq_true (eq_true hz), dite_cond_eq_true (eq_true (by rw [←mem_funs]; apply fapply_mem_range))] at eq
      generalize_proofs ζX_is_pfunc z_mem_dom app_z_mem_dom at eq

      let ζ_α_z : ZFSet := @ᶻζ_α ⟨z, by rwa [is_func_dom_eq ζ_α_is_func]⟩
      have := @fapply_lambda ⟦α.toSMTType⟧ᶻ 𝔹
        (fun z ↦ if hx : z ∈ ⟦α.toSMTType⟧ᶻ then
                  ZFBool.ofBool (decide (↑(@ᶻζ_α⁻¹ ⟨z, by rwa [is_func_dom_eq (inv_is_func_of_bijective ζ_α_bij)]⟩) ∈ X))
                else ∅)
        ?_ ζ_α_z (fapply_mem_range _ _)

      · rw [dite_cond_eq_true (eq_true (fapply_mem_range _ _))] at this
        rw [fapply_eq_Image_singleton
          (lambda_isFunc fun hx ↦ by rw [dite_cond_eq_true (eq_true hx)]; apply ZFBool.mem_ofBool_𝔹)
          (fapply_mem_range _ _)] at this
        · conv at this =>
            enter [1,1,1]
            rw [←ζ_restr]
          rw [←fapply_eq_Image_singleton (by rw [←mem_funs]; apply fapply_mem_range) (fapply_mem_range _ _),
            eq, eq_comm, (by rfl : zftrue = ↑(⊤ : ZFBool)), ←Subtype.ext_iff, ZFBool.ofBool_decide_eq_true_iff,
            ←fapply_composition (inv_is_func_of_bijective ζ_α_bij) ζ_α_is_func hz,
            fapply_eq_Image_singleton (IsFunc_of_composition_IsFunc (inv_is_func_of_bijective ζ_α_bij) ζ_α_is_func) hz] at this
          conv at this =>
            enter [2,1,1]
            change ζ_α⁻¹ ∘ᶻ ζ_α
            rw [composition_self_inv_of_bijective ζ_α_bij]
          rwa [←fapply_eq_Image_singleton Id.IsFunc hz, fapply_Id hz] at this
      · intro x hx
        beta_reduce
        rw [dite_cond_eq_true (eq_true hx)]
        apply ZFBool.mem_ofBool_𝔹
    · rw [mem_sep]
      rw [BType.toZFSet, mem_powerset] at hx
      and_intros
      · exact hx hz
      · rw [dite_cond_eq_true (eq_true <| hx hz), dite_cond_eq_true (eq_true (by rw [←mem_funs]; apply fapply_mem_range))]
        generalize_proofs ζX_is_pfunc z_mem_dom app_z_mem_dom
        subst ζ
        conv =>
          enter [1]
          rw [fapply_eq_Image_singleton (by rw [←mem_funs]; apply fapply_mem_range) (fapply_mem_range _ _)]
          conv =>
            enter [1,1]
            rw [fapply_lambda (B := (⟦α.toSMTType⟧ᶻ.funs 𝔹)) (by
              intro x hx
              rw [ite_cond_eq_true _ _ (eq_true hx)]
              apply mem_funs_of_lambda
              intro x hx
              rw [dite_cond_eq_true (eq_true hx)]
              apply ZFBool.mem_ofBool_𝔹
            ) (by rwa [mem_powerset]), mem_powerset, ite_cond_eq_true _ _ (eq_true hx)]
          rw [←fapply_eq_Image_singleton
            (lambda_isFunc fun hx ↦ by rw [dite_cond_eq_true (eq_true hx)]; apply ZFBool.mem_ofBool_𝔹)
            (fapply_mem_range _ _),
            fapply_lambda (fun hx ↦ by rw [dite_cond_eq_true (eq_true hx)]; apply ZFBool.mem_ofBool_𝔹) (fapply_mem_range _ _),
            dite_cond_eq_true (eq_true (fapply_mem_range _ _))]
        rw [(by rfl : zftrue = ↑(⊤ : ZFBool)), ←Subtype.ext_iff, ZFBool.ofBool_decide_eq_true_iff,
          ←fapply_composition (inv_is_func_of_bijective ζ_α_bij) ζ_α_is_func (hx hz),
          fapply_eq_Image_singleton (IsFunc_of_composition_IsFunc (inv_is_func_of_bijective ζ_α_bij) ζ_α_is_func) (hx hz)]
        conv =>
          enter [2,1,1]
          change ζ_α⁻¹ ∘ᶻ ζ_α
          rw [composition_self_inv_of_bijective ζ_α_bij]
        rwa [←fapply_eq_Image_singleton Id.IsFunc (hx hz), fapply_Id (hx hz)]
  | prod α β α_ih β_ih =>
    rw [BType.toZFSet, mem_prod] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx

    rw [BType.canonicalIsoSMTType] at hζ
    dsimp at hζ
    subst ζ

    let ζ_α : ZFSet.{u} := (BType.canonicalIsoSMTType α).1
    let ζ_β : ZFSet.{u} := (BType.canonicalIsoSMTType β).1
    let ζ_α_isfunc := (BType.canonicalIsoSMTType α).2.1
    let ζ_β_isfunc := (BType.canonicalIsoSMTType β).2.1
    let ζ_α_bij := (BType.canonicalIsoSMTType α).2.2
    let ζ_β_bij := (BType.canonicalIsoSMTType β).2.2

    rw [retract, pair_inj]
    and_intros
    · conv =>
        enter [1,2,1]
        rw [fapply_fprod ζ_α_isfunc ζ_β_isfunc ha hb]
      rw [π₁_pair, α_ih ha _ ζ_α_isfunc ζ_α_bij]
      rfl
    · conv =>
        enter [1,2,1]
        rw [fapply_fprod ζ_α_isfunc ζ_β_isfunc ha hb]
      rw [π₂_pair, β_ih hb _ ζ_β_isfunc ζ_β_bij]
      rfl

/--
Another version of `retract_of_canonical` but stated as composition explicitly.
-/
theorem retract_composition_canonicalIso (τ : BType) :
  composition
    (λᶻ : ⟦τ.toSMTType⟧ᶻ → ⟦τ⟧ᶻ | z ↦ retract τ z)
    (BType.canonicalIsoSMTType τ).1 ⟦τ⟧ᶻ ⟦τ.toSMTType⟧ᶻ ⟦τ⟧ᶻ = ZFSet.Id ⟦τ⟧ᶻ := by
  ext1 x
  constructor <;> intro hx
  · rw [ZFSet.mem_Id_iff]
    rw [mem_composition] at hx
    obtain ⟨x, z, y, rfl, hx, hy, hz, xz, zy⟩ := hx
    rw [lambda_spec] at zy
    obtain ⟨-, -, y_eq⟩ := zy

    set ζ_τ := (BType.canonicalIsoSMTType τ).1
    have ζ_τ_isfunc := (BType.canonicalIsoSMTType τ).2.1

    have ζx_eq := fapply.of_pair (is_func_is_pfunc ζ_τ_isfunc) xz
    rw [Subtype.ext_iff] at ζx_eq
    dsimp at ζx_eq
    rw [←ζx_eq, retract_of_canonical τ hx] at y_eq
    subst y
    use x, hx
  · rw [ZFSet.mem_Id_iff] at hx
    obtain ⟨x, hx, rfl⟩ := hx

    rw [mem_composition]
    simp only [pair_inj, existsAndEq, and_true, exists_and_left, exists_eq_left', and_self_left]
    apply And.intro hx

    set ζ_τ := (BType.canonicalIsoSMTType τ).1
    have ζ_τ_isfunc := (BType.canonicalIsoSMTType τ).2.1

    use @ᶻζ_τ ⟨x, by rwa [is_func_dom_eq ζ_τ_isfunc]⟩
    and_intros
    · apply fapply_mem_range
    · apply fapply.def
    · rw [lambda_spec]
      and_intros
      · apply fapply_mem_range
      · exact hx
      · rw [retract_of_canonical τ hx]

/--
Relation RDom via retraction :
`⟨X, τ, _⟩` and `⟨X', τ', _⟩` are related in `RDom` iff `τ' = τ.toSMTType` and `η_τ X' = X`.
-/
def RDom : B.Dom → SMT.Dom → Prop :=
  fun ⟨X, τ, _⟩ ⟨X', τ', _⟩ ↦ τ' = τ.toSMTType ∧ retract τ X' = X

infix:50 " ≘ᶻ " => RDom

def RValuation (Ξ : B.𝒱 → Option B.Dom) (Θ : SMT.𝒱 → Option SMT.Dom) : Prop := ∀ v,
  match Ξ v, Θ v with
  | none, none => True
  | some d, some d' => d ≘ᶻ d'
  | _, _ => False


-- theorem BType_iso_prod_of_iso {α β : BType} : ⟦α⟧ᶻ.funs ⟦β⟧ᶻ ≅ᶻ ⟦α.toSMTType⟧ᶻ.funs ⟦β.toSMTType⟧ᶻ := by
--   have ⟨ζ, ζ_isfunc, ζ_bij⟩ := BType_iso_SMTType α
--   have ⟨ξ, ξ_isfunc, ξ_bij⟩ := BType_iso_SMTType β
--   obtain ⟨Φ_isfunc, Φ_bij⟩ := ZFSet.composition_fprod_Image_bijective (A := ⟦α⟧ᶻ) (B := ⟦β⟧ᶻ) (φ_bij := ζ_bij) (ψ_bij := ξ_bij)
--   exists ?_
--   admit

/--
Given a renaming context for B variables `Δ : B.𝒱 → Option B.Dom`, a renaming context for SMT
variables can be constructed isomorphically, so that variables themselves are mapped to isomorphic
sets. Such a functor is said to be *fully faithful*.

`Δ.toSMT` is therefore constructed as bijection up to isomorphism, first proving that
`(B.𝒱 → Option B.Dom) ≅ (SMT.𝒱 → Option SMT.Dom)` and second that for any variable
`∀ v : 𝒱, (Δ v) ≅ (Δ.toSMT v)`.
-/
noncomputable def B.RenamingContext.toSMT.{u} («Δ» : B.𝒱 → Option B.Dom.{u}) (v : SMT.𝒱) : Option SMT.Dom.{u} := do
  let ⟨V, τ, pf⟩ ← «Δ» v
  let ζ_τ : ZFSet.{u} := (BType.canonicalIsoSMTType τ).1
  let ζ_τ_isfunc : (⟦τ⟧ᶻ).IsFunc (⟦τ.toSMTType⟧ᶻ) ζ_τ := (BType.canonicalIsoSMTType τ).2.1
  let ζ_τ_bij : IsBijective ζ_τ ζ_τ_isfunc := (BType.canonicalIsoSMTType τ).2.2

  let V' : ZFSet := @ᶻζ_τ ⟨V, by rwa [ZFSet.is_func_dom_eq ζ_τ_isfunc]⟩
  return ⟨V', τ.toSMTType, fapply_mem_range _ _⟩

/-- `RenamingContext.toSMT` preserves `RValuation` pointwise. -/
theorem RValuation_toSMT (Ξ : B.𝒱 → Option B.Dom) :
    RValuation Ξ (B.RenamingContext.toSMT Ξ) := by
  intro v
  cases hΞv : Ξ v with
  | none =>
    rw [RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind, hΞv, Option.bind_none]
    trivial
  | some d =>
    let ⟨V, τ, hV⟩ := d
    rw [RenamingContext.toSMT, Option.pure_def, Option.bind_eq_bind, hΞv, Option.bind_some]
    dsimp
    rw [RDom]
    apply And.intro rfl
    rw [retract_of_canonical τ hV]
