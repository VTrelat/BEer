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

theorem canonical_pair_of_retract.{u} {x : ZFSet.{u}} (τ : BType)
  (hx : x ∈ ⟦τ.toSMTType⟧ᶻ) :
    (retract τ x).pair x ∈ (BType.canonicalIsoSMTType τ).1 := by
  have ζ_τ_isfunc : ⟦τ⟧ᶻ.IsFunc ⟦τ.toSMTType⟧ᶻ (BType.canonicalIsoSMTType τ).1 :=
    (BType.canonicalIsoSMTType τ).2.1
  have ζ_τ_bij : IsBijective (BType.canonicalIsoSMTType τ).1 ζ_τ_isfunc :=
    (BType.canonicalIsoSMTType τ).2.2

  obtain ⟨y, hy, hyx⟩ := ζ_τ_bij.2 x hx
  have x_eq := fapply.of_pair (is_func_is_pfunc ζ_τ_isfunc) hyx
  rw [Subtype.ext_iff] at x_eq
  dsimp at x_eq
  have retract_eq : retract τ x = y := by
    rw [←x_eq, retract_of_canonical τ hy]
  rwa [←retract_eq] at hyx

theorem retract_mem_of_canonical.{u} {x : ZFSet.{u}} (τ : BType)
  (hx : x ∈ ⟦τ.toSMTType⟧ᶻ) : retract τ x ∈ ⟦τ⟧ᶻ := by
  rw [←ZFSet.is_func_dom_eq (BType.canonicalIsoSMTType τ).2.1]
  exact mem_dom (is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
    (canonical_pair_of_retract τ hx)

@[simp]
theorem canonical_of_retract.{u} {x : ZFSet.{u}} (τ : BType)
  (hx : x ∈ ⟦τ.toSMTType⟧ᶻ) :
    fapply (BType.canonicalIsoSMTType τ).1 (is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
      ⟨retract τ x, mem_dom (is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
        (canonical_pair_of_retract τ hx)⟩ = x := by
  exact Subtype.ext_iff.mp <|
    fapply.of_pair (is_func_is_pfunc (BType.canonicalIsoSMTType τ).2.1)
      (canonical_pair_of_retract τ hx)

theorem canonicalIso_composition_retract (τ : BType) :
  composition
    (BType.canonicalIsoSMTType τ).1
    (λᶻ : ⟦τ.toSMTType⟧ᶻ → ⟦τ⟧ᶻ | z ↦ retract τ z)
    ⟦τ.toSMTType⟧ᶻ ⟦τ⟧ᶻ ⟦τ.toSMTType⟧ᶻ = ZFSet.Id ⟦τ.toSMTType⟧ᶻ := by
  ext1 x
  constructor <;> intro hx
  · rw [ZFSet.mem_Id_iff]
    rw [mem_composition] at hx
    obtain ⟨x, z, y, rfl, hx, hy, hz, xz, zy⟩ := hx
    rw [lambda_spec] at xz
    obtain ⟨-, -, z_eq⟩ := xz

    have retract_x_mem : retract τ x ∈ ⟦τ⟧ᶻ := retract_mem_of_canonical τ hx
    have retract_pair : (retract τ x).pair x ∈ (BType.canonicalIsoSMTType τ).1 :=
      canonical_pair_of_retract τ hx

    have zy' : (retract τ x).pair y ∈ (BType.canonicalIsoSMTType τ).1 := by
      rwa [z_eq] at zy

    have y_eq_x : y = x := by
      exact ((BType.canonicalIsoSMTType τ).2.1).2 (retract τ x) retract_x_mem |>.unique zy' retract_pair
    subst y
    use x, hx
  · rw [ZFSet.mem_Id_iff] at hx
    obtain ⟨x, hx, rfl⟩ := hx

    rw [mem_composition]
    simp only [pair_inj, existsAndEq, and_true, exists_and_left, exists_eq_left', and_self_left]
    apply And.intro hx

    use retract τ x
    and_intros
    · exact retract_mem_of_canonical τ hx
    · rw [lambda_spec]
      and_intros
      · exact hx
      · exact retract_mem_of_canonical τ hx
      · rfl
    · exact canonical_pair_of_retract τ hx

/-! ### Canonical image of a B-side domain under the canonical iso

Lift `retract τ` and the canonical iso from pointwise to set-level. For a
`𝒟 ⊆ ⟦τ⟧ᶻ` on the B side, `canonicalImage τ 𝒟` is the corresponding subset of
`⟦τ.toSMTType⟧ᶻ` on the SMT side. Defined via `sep` for convenience: the set of
SMT-level values whose retract lies in `𝒟`.
-/

/-- The image of a B-side set `𝒟` under the canonical iso `⟦τ⟧ᶻ → ⟦τ.toSMTType⟧ᶻ`. -/
noncomputable def BType.canonicalImage (τ : BType) (𝒟 : ZFSet) : ZFSet :=
  ZFSet.sep (fun y => retract τ y ∈ 𝒟) ⟦τ.toSMTType⟧ᶻ

/-- Membership in `canonicalImage` unfolds to the `sep` characterization. -/
theorem mem_canonicalImage_iff (τ : BType) (𝒟 : ZFSet) (y : ZFSet) :
    y ∈ BType.canonicalImage τ 𝒟 ↔ y ∈ ⟦τ.toSMTType⟧ᶻ ∧ retract τ y ∈ 𝒟 := by
  unfold BType.canonicalImage
  rw [ZFSet.mem_sep]

/-- Nonempty B-side domain (subset of `⟦τ⟧ᶻ`) has a nonempty canonical image. -/
theorem canonicalImage_nonempty {τ : BType} {𝒟 : ZFSet} (h_sub : 𝒟 ⊆ ⟦τ⟧ᶻ)
    (h_ne : 𝒟.Nonempty) : (BType.canonicalImage τ 𝒟).Nonempty := by
  obtain ⟨x, hx⟩ := h_ne
  have hx_τ : x ∈ ⟦τ⟧ᶻ := h_sub hx
  -- Witness: canonical iso applied to x.
  set ζ := (BType.canonicalIsoSMTType τ).1
  have ζ_isfunc : ⟦τ⟧ᶻ.IsFunc ⟦τ.toSMTType⟧ᶻ ζ := (BType.canonicalIsoSMTType τ).2.1
  set y : ZFSet :=
    (ZFSet.fapply ζ (ZFSet.is_func_is_pfunc ζ_isfunc)
      ⟨x, by rwa [ZFSet.is_func_dom_eq ζ_isfunc]⟩).1 with y_def
  refine ⟨y, ?_⟩
  show y ∈ BType.canonicalImage τ 𝒟
  rw [mem_canonicalImage_iff]
  refine ⟨?_, ?_⟩
  · -- y ∈ ⟦τ.toSMTType⟧ᶻ via the fapply's subtype proof.
    exact (ZFSet.fapply ζ (ZFSet.is_func_is_pfunc ζ_isfunc)
      ⟨x, by rwa [ZFSet.is_func_dom_eq ζ_isfunc]⟩).2
  · -- retract τ y = x ∈ 𝒟 via retract_of_canonical
    rw [y_def, retract_of_canonical τ hx_τ]
    exact hx

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

namespace B.RenamingContext

abbrev Context := B.𝒱 → Option B.Dom

/-- Keep only bindings for variables listed in `xs`. -/
def restrictToVars («Δ» : Context) (xs : List B.𝒱) : Context :=
  fun v ↦ if v ∈ xs then «Δ» v else none

/-- Keep only bindings for free variables of `t`. -/
def restrictToFV («Δ» : Context) (t : B.Term) : Context :=
  restrictToVars «Δ» (B.fv t)

@[simp]
theorem restrictToVars_eq_of_mem {«Δ» : Context} {xs : List B.𝒱} {v : B.𝒱}
  (hv : v ∈ xs) : restrictToVars «Δ» xs v = «Δ» v := by
  simp [restrictToVars, hv]

@[simp]
theorem restrictToVars_eq_none_of_not_mem {«Δ» : Context} {xs : List B.𝒱} {v : B.𝒱}
  (hv : v ∉ xs) : restrictToVars «Δ» xs v = none := by
  simp [restrictToVars, hv]

@[simp]
theorem restrictToFV_eq_of_mem {«Δ» : Context} {t : B.Term} {v : B.𝒱}
  (hv : v ∈ B.fv t) : restrictToFV «Δ» t v = «Δ» v := by
  simp [restrictToFV, restrictToVars, hv]

@[simp]
theorem restrictToFV_eq_none_of_not_mem {«Δ» : Context} {t : B.Term} {v : B.𝒱}
  (hv : v ∉ B.fv t) : restrictToFV «Δ» t v = none := by
  simp [restrictToFV, restrictToVars, hv]

/-- SMT context corresponding to the source-FV restriction of `Δ` for term `t`. -/
noncomputable def toSMTOnFV («Δ» : Context) (t : B.Term) : SMT.𝒱 → Option SMT.Dom :=
  B.RenamingContext.toSMT (restrictToFV «Δ» t)

end B.RenamingContext

namespace B

/-- Source free variables of `t` are all present in the SMT `usedVars` list. -/
abbrev CoversUsedVars (used : List SMT.𝒱) (t : B.Term) : Prop :=
  ∀ v ∈ B.fv t, v ∈ used

theorem CoversUsedVars.mono {used₁ used₂ : List SMT.𝒱} {t : B.Term}
  (hsub : used₁ ⊆ used₂) (hcov : CoversUsedVars used₁ t) :
  CoversUsedVars used₂ t := by
  intro v hv
  exact hsub (hcov v hv)

theorem CoversUsedVars.mem {used : List SMT.𝒱} {x S : B.Term}
  (hx : CoversUsedVars used x) (hS : CoversUsedVars used S) :
  CoversUsedVars used (x ∈ᴮ S) := by
  intro v hv
  rw [B.fv, List.mem_append] at hv
  rcases hv with hv | hv
  · exact hx v hv
  · exact hS v hv

theorem not_mem_fv_of_not_mem_used {used : List SMT.𝒱} {t : B.Term} {v : SMT.𝒱}
  (hcov : CoversUsedVars used t) (hv : v ∉ used) :
  v ∉ B.fv t := by
  intro hv_fv
  exact hv (hcov v hv_fv)

theorem fv_subset_mem_left (x S : B.Term) : B.fv x ⊆ B.fv (x ∈ᴮ S) := by
  intro v hv
  simp [B.fv, hv]

theorem fv_subset_mem_right (x S : B.Term) : B.fv S ⊆ B.fv (x ∈ᴮ S) := by
  intro v hv
  simp [B.fv, hv]

end B

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

namespace Function

theorem updates_of_not_mem {α β} [DecidableEq α]
  (f : α → β) (xs : List α) (ys : List β) (k : α)
  (hk : k ∉ xs) : (Function.updates f xs ys) k = f k := by
  induction xs generalizing f ys with
  | nil => simp [Function.updates]
  | cons x xs ih =>
    cases ys with
    | nil => simp [Function.updates]
    | cons y ys =>
      simp at hk
      simp [Function.updates]
      rw [ih (Function.update f x y) ys hk.2]
      simp [Function.update, hk.1]

theorem updates_eq_of_mem_map_some {α β} [DecidableEq α]
  (f g : α → _root_.Option β) (xs : List α) (ys : List β) (k : α)
  (hmem : k ∈ xs) (hlen : xs.length = ys.length) :
  (Function.updates f xs (ys.map _root_.Option.some)) k =
  (Function.updates g xs (ys.map _root_.Option.some)) k := by
  induction xs generalizing f g ys with
  | nil => cases hmem
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp at hlen
      simp [Function.updates] at hmem ⊢
      rcases hmem with rfl | hmem
      · by_cases hkxs : k ∈ xs
        · exact ih (Function.update f k (_root_.Option.some y)) (Function.update g k (_root_.Option.some y)) ys hkxs hlen
        · rw [Function.updates_of_not_mem (f := Function.update f k (_root_.Option.some y)) (xs := xs) (ys := ys.map _root_.Option.some) (k := k) hkxs]
          rw [Function.updates_of_not_mem (f := Function.update g k (_root_.Option.some y)) (xs := xs) (ys := ys.map _root_.Option.some) (k := k) hkxs]
          simp [Function.update]
      · exact ih (Function.update f x (_root_.Option.some y)) (Function.update g x (_root_.Option.some y)) ys hmem hlen

theorem updates_isSome_of_mem_map_some {α β} [DecidableEq α]
  (f : α → _root_.Option β) (xs : List α) (ys : List β) (k : α)
  (hmem : k ∈ xs) (hlen : xs.length = ys.length) :
  ((Function.updates f xs (ys.map _root_.Option.some)) k).isSome = true := by
  induction xs generalizing f ys with
  | nil => cases hmem
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp at hlen
      simp [Function.updates] at hmem ⊢
      rcases hmem with rfl | hmem
      · by_cases hkxs : k ∈ xs
        · exact ih (Function.update f k (_root_.Option.some y)) ys hkxs hlen
        · rw [Function.updates_of_not_mem (f := Function.update f k (_root_.Option.some y)) (xs := xs) (ys := ys.map _root_.Option.some) (k := k) hkxs]
          simp [Function.update]
      · exact ih (Function.update f x (_root_.Option.some y)) ys hmem hlen

end Function

namespace SMT

theorem Term.abstract.go.alt_def₂ (vs : List 𝒱) (P : SMT.Term) {α} {Δctx : 𝒱 → _root_.Option α}
  (αs : List α) (vs_αs_len : vs.length = αs.length)
  (Δ_isSome : ∀ v ∈ fv P, v ∉ vs → (Δctx v).isSome = true)
  (tmp₁ :
    ∀ v ∈ fv P, (Function.updates Δctx vs (List.map (Option.some ·) αs) v).isSome = true) :
  ((Term.abstract.go P vs Δctx Δ_isSome).uncurry fun ⟨i, hi⟩ => αs[i]'(by rwa [←vs_αs_len])) =
  (P.abstract (Function.updates Δctx vs (αs.map (Option.some ·))) tmp₁) := by
  induction vs, αs, vs_αs_len using List.induction₂ generalizing Δctx with
  | nil_nil =>
    simp only [List.length_nil, List.map_nil, Term.abstract.go, Function.updates, Function.OfArity.uncurry, Function.FromTypes.uncurry]
  | cons_cons v₀ vs α₀ αs len_eq ih =>
    cases vs with
    | nil =>
      obtain ⟨⟩ : αs = [] := by rw [←List.length_eq_zero_iff, ←len_eq, List.length_nil]
      simp only [Function.OfArity.uncurry, List.length_cons, List.length_nil, Nat.reduceAdd,
        Term.abstract.go, Matrix.head_fin_const, Fin.val_eq_zero, List.getElem_cons_zero,
        Function.FromTypes.uncurry_apply_succ, Function.FromTypes.uncurry, List.map_cons,
        List.map_nil, Function.updates]
    | cons v₁ vs =>
      obtain ⟨α₁, αs, rfl⟩ := List.exists_cons_of_length_eq_add_one len_eq.symm
      conv =>
        lhs
        simp only [List.reduce_cons_cons]
        rw [Term.abstract.go, Function.OfArity.uncurry, Function.FromTypes.uncurry]
        simp only [List.length_cons, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero,
          Function.FromTypes.uncurry_apply_succ]
      conv =>
        rhs
        simp [List.map_cons, Function.updates]
      simp_rw [List.length_cons, List.map_cons] at ih
      exact ih _ tmp₁

end SMT

namespace SMT.Typing

theorem mem_context_of_mem_fv {Γ : SMT.TypeContext} {t : SMT.Term} {τ : SMTType}
  (ht : Γ ⊢ˢ t : τ) {x : SMT.𝒱} (hx : x ∈ SMT.fv t) : x ∈ Γ := by
  induction ht generalizing x with
  | var Γ v τ hlookup =>
    simp [SMT.fv] at hx
    subst hx
    exact (AList.lookup_isSome).1 (Option.isSome_of_eq_some hlookup)
  | int =>
    simp [SMT.fv] at hx
  | bool =>
    simp [SMT.fv] at hx
  | app Γ f y α β typ_f typ_y ih_f ih_y =>
    simp [SMT.fv, List.mem_append] at hx
    exact hx.elim (ih_f ·) (ih_y ·)
  | lambda Γ vs τs t γ vs_Γ fresh len_pos len_eq typ_t ih =>
    simp [SMT.fv, List.mem_removeAll_iff] at hx
    obtain ⟨hx_t, hx_not_vs⟩ := hx
    have hx_upd : x ∈ Γ.update vs τs := ih hx_t
    rw [SMT.TypeContext.mem_update_iff (Γ := Γ) (v := x) (vs := vs) (τs := τs) (hlen := len_eq)] at hx_upd
    rcases hx_upd with hx_vs | hx_Γ
    · exact (hx_not_vs hx_vs).elim
    · exact hx_Γ
  | «forall» Γ vs τs P vs_Γ fresh len_pos len_eq typ_P ih =>
    simp [SMT.fv, List.mem_removeAll_iff] at hx
    obtain ⟨hx_P, hx_not_vs⟩ := hx
    have hx_upd : x ∈ Γ.update vs τs := ih hx_P
    rw [SMT.TypeContext.mem_update_iff (Γ := Γ) (v := x) (vs := vs) (τs := τs) (hlen := len_eq)] at hx_upd
    rcases hx_upd with hx_vs | hx_Γ
    · exact (hx_not_vs hx_vs).elim
    · exact hx_Γ
  | «exists» Γ vs τs P vs_Γ fresh len_pos len_eq typ_P ih =>
    simp [SMT.fv, List.mem_removeAll_iff] at hx
    obtain ⟨hx_P, hx_not_vs⟩ := hx
    have hx_upd : x ∈ Γ.update vs τs := ih hx_P
    rw [SMT.TypeContext.mem_update_iff (Γ := Γ) (v := x) (vs := vs) (τs := τs) (hlen := len_eq)] at hx_upd
    rcases hx_upd with hx_vs | hx_Γ
    · exact (hx_not_vs hx_vs).elim
    · exact hx_Γ
  | eq Γ t₁ t₂ σ typ₁ typ₂ ih₁ ih₂
  | and Γ t₁ t₂ typ₁ typ₂ ih₁ ih₂
  | or Γ t₁ t₂ typ₁ typ₂ ih₁ ih₂
  | imp Γ t₁ t₂ typ₁ typ₂ ih₁ ih₂
  | le Γ t₁ t₂ typ₁ typ₂ ih₁ ih₂
  | add Γ t₁ t₂ typ₁ typ₂ ih₁ ih₂
  | sub Γ t₁ t₂ typ₁ typ₂ ih₁ ih₂
  | mul Γ t₁ t₂ typ₁ typ₂ ih₁ ih₂
  | pair Γ t₁ τ₁ t₂ τ₂ typ₁ typ₂ ih₁ ih₂ =>
    simp [SMT.fv, List.mem_append] at hx
    exact hx.elim (ih₁ ·) (ih₂ ·)
  | not Γ t typ_t ih
  | some Γ t τ typ_t ih
  | the Γ t τ typ_t ih
  | fst Γ t τ σ typ_t ih
  | snd Γ t τ σ typ_t ih =>
    have hx_t : x ∈ SMT.fv t := by simpa [SMT.fv] using hx
    exact ih hx_t
  | ite Γ c t e τ typ_c typ_t typ_e ih_c ih_t ih_e =>
    simp [SMT.fv, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ih_c hx
    · rcases hx with hx | hx
      · exact ih_t hx
      · exact ih_e hx
  | none Γ τ =>
    simp [SMT.fv] at hx
  | distinct Γ ts σ typ_ts ih =>
    rw [SMT.fv] at hx
    rcases List.mem_flatten.mp hx with ⟨l, hl, hxl⟩
    rcases List.mem_map.mp hl with ⟨t, ht, rfl⟩
    exact ih t.1 t.2 hxl

end SMT.Typing

namespace SMT.RenamingContext

abbrev Context := SMT.𝒱 → Option SMT.Dom

/-- Context `«Δ»` provides all free variables of `t`. -/
abbrev CoversFV («Δ» : Context) (t : SMT.Term) : Prop :=
  ∀ v ∈ SMT.fv t, («Δ» v).isSome = true

/--
`Δ` is type-compatible with `Γ`: every variable binding selected by `Γ.lookup`
is mapped by `Δ` to a domain value carrying the same SMT type tag.
-/
abbrev RespectsTypeContext («Δ» : Context) (Γ : SMT.TypeContext) : Prop :=
  ∀ ⦃v : SMT.𝒱⦄ ⦃τ : SMTType⦄, Γ.lookup v = some τ →
    ∃ d : SMT.Dom, «Δ» v = some d ∧ d.2.1 = τ

/--
Canonical context induced by a type context: each `v` is mapped to the default
inhabitant of its declared type (when present in `Γ`).
-/
noncomputable def ofTypeContext (Γ : SMT.TypeContext) : Context :=
  fun v =>
    match Γ.lookup v with
    | some τ => some ⟨τ.defaultZFSet, τ, SMTType.mem_toZFSet_of_defaultZFSet⟩
    | none => none

theorem respectsTypeContext_of_ofTypeContext (Γ : SMT.TypeContext) :
  RespectsTypeContext (ofTypeContext Γ) Γ := by
  intro v τ hlookup
  refine ⟨⟨τ.defaultZFSet, τ, SMTType.mem_toZFSet_of_defaultZFSet⟩, ?_, rfl⟩
  simp [ofTypeContext, hlookup]

theorem coversFV_of_typing_and_respects
  {Γ : SMT.TypeContext} {t : SMT.Term} {τ : SMTType} {«Δ» : Context}
  (ht : Γ ⊢ˢ t : τ) (hΔ : RespectsTypeContext «Δ» Γ) :
  CoversFV «Δ» t := by
  intro v hv
  have hvΓ : v ∈ Γ := SMT.Typing.mem_context_of_mem_fv ht hv
  obtain ⟨τv, hlookup⟩ := Option.isSome_iff_exists.mp ((AList.lookup_isSome).2 hvΓ)
  obtain ⟨d, hd, _⟩ := hΔ hlookup
  rw [hd]
  simp

/-- Pointwise agreement of two contexts on a list of variables. -/
abbrev AgreesOn («Δ₁» «Δ₂» : Context) (xs : List SMT.𝒱) : Prop :=
  ∀ ⦃v : SMT.𝒱⦄, v ∈ xs → «Δ₁» v = «Δ₂» v

/-- Pointwise agreement of two contexts on the free variables of a term. -/
abbrev AgreesOnFV («Δ₁» «Δ₂» : Context) (t : SMT.Term) : Prop :=
  AgreesOn «Δ₁» «Δ₂» (SMT.fv t)

/-- `Δ₁` extends `Δ₂`: every binding present in `Δ₂` is preserved in `Δ₁`. -/
abbrev Extends («Δ₁» «Δ₂» : Context) : Prop :=
  ∀ ⦃v : SMT.𝒱⦄ ⦃d : SMT.Dom⦄, «Δ₂» v = some d → «Δ₁» v = some d

/--
`Δ'` extends the normalized source base induced by `Δ` on `B.fv t`.
Bindings outside `B.fv t` are intentionally unconstrained.
-/
abbrev ExtendsOnSourceFV (Δ' : Context) («Δ» : B.𝒱 → Option B.Dom) (t : B.Term) : Prop :=
  Extends Δ' (B.RenamingContext.toSMTOnFV «Δ» t)

/-- Left-biased merge of contexts. -/
def merge («Δ₁» «Δ₂» : Context) : Context :=
  fun v ↦ if («Δ₁» v).isSome then «Δ₁» v else «Δ₂» v

@[simp]
theorem merge_eq_left_of_isSome {«Δ₁» «Δ₂» : Context} {v : SMT.𝒱}
  (hv : («Δ₁» v).isSome = true) :
  merge «Δ₁» «Δ₂» v = «Δ₁» v := by
  simp [merge, hv]

@[simp]
theorem merge_eq_right_of_isSome_false {«Δ₁» «Δ₂» : Context} {v : SMT.𝒱}
  (hv : («Δ₁» v).isSome = false) :
  merge «Δ₁» «Δ₂» v = «Δ₂» v := by
  simp [merge, hv]

theorem agreesOn_refl («Δ» : Context) (xs : List SMT.𝒱) : AgreesOn «Δ» «Δ» xs := by
  intro _ _
  rfl

theorem agreesOn_symm {«Δ₁» «Δ₂» : Context} {xs : List SMT.𝒱}
  (h : AgreesOn «Δ₁» «Δ₂» xs) : AgreesOn «Δ₂» «Δ₁» xs := by
  intro v hv
  symm
  exact h hv

theorem agreesOn_trans {«Δ₁» «Δ₂» «Δ₃» : Context} {xs : List SMT.𝒱}
  (h12 : AgreesOn «Δ₁» «Δ₂» xs) (h23 : AgreesOn «Δ₂» «Δ₃» xs) :
  AgreesOn «Δ₁» «Δ₃» xs := by
  intro v hv
  rw [h12 hv, h23 hv]

theorem agreesOnFV_refl («Δ» : Context) (t : SMT.Term) : AgreesOnFV «Δ» «Δ» t :=
  agreesOn_refl «Δ» (SMT.fv t)

theorem agreesOnFV_symm {«Δ₁» «Δ₂» : Context} {t : SMT.Term}
  (h : AgreesOnFV «Δ₁» «Δ₂» t) : AgreesOnFV «Δ₂» «Δ₁» t :=
  agreesOn_symm h

theorem agreesOnFV_trans {«Δ₁» «Δ₂» «Δ₃» : Context} {t : SMT.Term}
  (h12 : AgreesOnFV «Δ₁» «Δ₂» t) (h23 : AgreesOnFV «Δ₂» «Δ₃» t) :
  AgreesOnFV «Δ₁» «Δ₃» t :=
  agreesOn_trans h12 h23

theorem extends_refl («Δ» : Context) : Extends «Δ» «Δ» := by
  intro _ _ h
  exact h

theorem extends_trans {«Δ₁» «Δ₂» «Δ₃» : Context}
  (h12 : Extends «Δ₁» «Δ₂») (h23 : Extends «Δ₂» «Δ₃») :
  Extends «Δ₁» «Δ₃» := by
  intro v d hv
  exact h12 (h23 hv)

theorem extends_update_of_none {«Δ» : Context} {x : SMT.𝒱} {d : SMT.Dom}
  (hxnone : «Δ» x = none) :
  Extends (Function.update «Δ» x (some d)) «Δ» := by
  intro v d' hv
  by_cases hvx : v = x
  · subst hvx
    rw [hxnone] at hv
    cases hv
  · rw [Function.update_of_ne hvx]
    exact hv

theorem extends_update_of_eq {«Δ» : Context} {x : SMT.𝒱} {d : SMT.Dom}
  (hxeq : «Δ» x = some d) :
  Extends (Function.update «Δ» x (some d)) «Δ» := by
  intro v d' hv
  by_cases hvx : v = x
  · subst hvx
    rw [Function.update_self]
    simpa [hxeq] using hv
  · rw [Function.update_of_ne hvx]
    exact hv

theorem extends_update_of_base_none {«Δ₁» «Δ₂» : Context} {x : SMT.𝒱} {d : SMT.Dom}
  (hext : Extends «Δ₁» «Δ₂») (hxnone : «Δ₂» x = none) :
  Extends (Function.update «Δ₁» x (some d)) «Δ₂» := by
  intro v d' hv
  by_cases hvx : v = x
  · subst hvx
    rw [hxnone] at hv
    cases hv
  · rw [Function.update_of_ne hvx]
    exact hext hv

theorem extendsOnSourceFV_update_of_not_mem_fv
  {Δ' : Context} {«Δ» : B.RenamingContext.Context} {t : B.Term}
  {x : SMT.𝒱} {d : SMT.Dom}
  (hext : ExtendsOnSourceFV Δ' «Δ» t) (hx : x ∉ B.fv t) :
  ExtendsOnSourceFV (Function.update Δ' x (some d)) «Δ» t := by
  unfold ExtendsOnSourceFV at hext ⊢
  have hbase_none : B.RenamingContext.toSMTOnFV «Δ» t x = none := by
    simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
      B.RenamingContext.restrictToFV_eq_none_of_not_mem (t := t) (v := x) hx]
  exact extends_update_of_base_none hext hbase_none

theorem extendsOnSourceFV_update_of_not_mem_used
  {Δ' : Context} {«Δ» : B.RenamingContext.Context} {t : B.Term}
  {used : List SMT.𝒱} {x : SMT.𝒱} {d : SMT.Dom}
  (hext : ExtendsOnSourceFV Δ' «Δ» t)
  (hcov : B.CoversUsedVars used t) (hx : x ∉ used) :
  ExtendsOnSourceFV (Function.update Δ' x (some d)) «Δ» t :=
  extendsOnSourceFV_update_of_not_mem_fv hext
    (B.not_mem_fv_of_not_mem_used hcov hx)

theorem extendsOnSourceFV_of_extends
  {Δ₁ Δ₂ : Context} {«Δ» : B.RenamingContext.Context} {t : B.Term}
  (hext : Extends Δ₁ Δ₂) (hsrc : ExtendsOnSourceFV Δ₂ «Δ» t) :
  ExtendsOnSourceFV Δ₁ «Δ» t := by
  unfold ExtendsOnSourceFV at hsrc ⊢
  exact extends_trans hext hsrc

theorem extendsOnSourceFV_of_fv_subset
  {Δ' : Context} {«Δ» : B.RenamingContext.Context} {t₁ t₂ : B.Term}
  (hsub : B.fv t₁ ⊆ B.fv t₂)
  (hsrc : ExtendsOnSourceFV Δ' «Δ» t₂) :
  ExtendsOnSourceFV Δ' «Δ» t₁ := by
  unfold ExtendsOnSourceFV at hsrc ⊢
  intro v d hv_t1
  have hv_mem_t1 : v ∈ B.fv t₁ := by
    by_contra hv_not_mem_t1
    have hv_none : B.RenamingContext.toSMTOnFV «Δ» t₁ v = none := by
      simp [B.RenamingContext.toSMTOnFV, B.RenamingContext.toSMT,
        B.RenamingContext.restrictToFV_eq_none_of_not_mem (t := t₁) (v := v) hv_not_mem_t1]
    rw [hv_none] at hv_t1
    cases hv_t1
  have hv_mem_t2 : v ∈ B.fv t₂ := hsub hv_mem_t1
  have hv_restrict_t1 : B.RenamingContext.restrictToFV «Δ» t₁ v = «Δ» v := by
    exact B.RenamingContext.restrictToFV_eq_of_mem (t := t₁) (v := v) hv_mem_t1
  have hv_restrict_t2 : B.RenamingContext.restrictToFV «Δ» t₂ v = «Δ» v := by
    exact B.RenamingContext.restrictToFV_eq_of_mem (t := t₂) (v := v) hv_mem_t2
  have hv_eq_t1 : B.RenamingContext.toSMTOnFV «Δ» t₁ v = B.RenamingContext.toSMT «Δ» v := by
    unfold B.RenamingContext.toSMTOnFV
    simp [B.RenamingContext.toSMT, hv_restrict_t1]
  have hv_eq_t2 : B.RenamingContext.toSMTOnFV «Δ» t₂ v = B.RenamingContext.toSMT «Δ» v := by
    unfold B.RenamingContext.toSMTOnFV
    simp [B.RenamingContext.toSMT, hv_restrict_t2]
  have hv_t2 : B.RenamingContext.toSMTOnFV «Δ» t₂ v = some d := by
    rw [hv_eq_t2, ←hv_eq_t1, hv_t1]
  exact hsrc hv_t2

theorem agreesOnFV_of_extends_of_coversFV {«Δ₁» «Δ₂» : Context} {t : SMT.Term}
  (hext : Extends «Δ₁» «Δ₂») (hcov : CoversFV «Δ₂» t) :
  AgreesOnFV «Δ₁» «Δ₂» t := by
  intro v hv
  have hsome : («Δ₂» v).isSome = true := hcov v hv
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hsome
  rw [hd]
  exact hext hd

theorem coversFV_of_extends_of_coversFV {«Δ₁» «Δ₂» : Context} {t : SMT.Term}
  (hext : Extends «Δ₁» «Δ₂») (hcov : CoversFV «Δ₂» t) :
  CoversFV «Δ₁» t := by
  intro v hv
  have hsome : («Δ₂» v).isSome = true := hcov v hv
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hsome
  have hnew : «Δ₁» v = some d := hext hd
  exact Option.isSome_of_eq_some hnew

theorem coversFV_of_agreesOnFV {«Δ₁» «Δ₂» : Context} {t : SMT.Term}
  (hag : AgreesOnFV «Δ₁» «Δ₂» t) (hcov : CoversFV «Δ₁» t) :
  CoversFV «Δ₂» t := by
  intro v hv
  rw [←hag hv]
  exact hcov v hv

theorem coversFV_of_agreesOnFV_symm {«Δ₁» «Δ₂» : Context} {t : SMT.Term}
  (hag : AgreesOnFV «Δ₁» «Δ₂» t) (hcov : CoversFV «Δ₂» t) :
  CoversFV «Δ₁» t :=
  coversFV_of_agreesOnFV (agreesOnFV_symm hag) hcov

theorem merge_agreesOnFV_left_of_coversFV {«Δ₁» «Δ₂» : Context} {t : SMT.Term}
  (hcov : CoversFV «Δ₁» t) : AgreesOnFV (merge «Δ₁» «Δ₂») «Δ₁» t := by
  intro v hv
  exact merge_eq_left_of_isSome (hcov v hv)

theorem merge_agreesOnFV_right_of_not_isSome {«Δ₁» «Δ₂» : Context} {t : SMT.Term}
  (hnone : ∀ v ∈ SMT.fv t, («Δ₁» v).isSome = false) :
  AgreesOnFV (merge «Δ₁» «Δ₂») «Δ₂» t := by
  intro v hv
  exact merge_eq_right_of_isSome_false (hnone v hv)

theorem coversFV_merge_left {«Δ₁» «Δ₂» : Context} {t : SMT.Term}
  (hcov : CoversFV «Δ₁» t) : CoversFV (merge «Δ₁» «Δ₂») t := by
  exact coversFV_of_agreesOnFV_symm (merge_agreesOnFV_left_of_coversFV hcov) hcov

theorem coversFV_merge_right {«Δ₁» «Δ₂» : Context} {t : SMT.Term}
  (hnone : ∀ v ∈ SMT.fv t, («Δ₁» v).isSome = false)
  (hcov : CoversFV «Δ₂» t) : CoversFV (merge «Δ₁» «Δ₂») t := by
  exact coversFV_of_agreesOnFV_symm (merge_agreesOnFV_right_of_not_isSome hnone) hcov

theorem coversFV_update_of_notMem {«Δ» : Context} {t : SMT.Term} {x : SMT.𝒱} {d : SMT.Dom}
  (hx : x ∉ SMT.fv t) (hcov : CoversFV «Δ» t) :
  CoversFV (Function.update «Δ» x (some d)) t := by
  intro v hv
  by_cases hvx : v = x
  · subst hvx
    exfalso
    exact hx hv
  · rw [Function.update_of_ne hvx]
    exact hcov v hv

theorem agreesOnFV_update_of_notMem {«Δ₁» «Δ₂» : Context} {t : SMT.Term} {x : SMT.𝒱}
  {d1 d2 : SMT.Dom}
  (hx : x ∉ SMT.fv t)
  (hag : AgreesOnFV «Δ₁» «Δ₂» t) :
  AgreesOnFV (Function.update «Δ₁» x (some d1)) (Function.update «Δ₂» x (some d2)) t := by
  intro v hv
  by_cases hvx : v = x
  · subst hvx
    exfalso
    exact hx hv
  · rw [Function.update_of_ne hvx, Function.update_of_ne hvx]
    exact hag hv

/-- Denotation of a concrete SMT term under a renaming context. -/
noncomputable def denote («Δ» : Context) (t : SMT.Term) (hcov : CoversFV «Δ» t) : Option SMT.Dom :=
  SMT.denote (t.abstract «Δ» hcov)

theorem denote_congr_of_abstract_eq {«Δ₁» «Δ₂» : Context} {t : SMT.Term}
  {h1 : CoversFV «Δ₁» t} {h2 : CoversFV «Δ₂» t}
  (habstract :
    t.abstract «Δ₁» (fun v hv ↦ by simpa using h1 v hv) =
    t.abstract «Δ₂» (fun v hv ↦ by simpa using h2 v hv)) :
  denote «Δ₁» t h1 = denote «Δ₂» t h2 := by
  simp [denote, habstract]

theorem abstract_eq_of_agreesOnFV
  {t : SMT.Term} {«Δ₁» «Δ₂» : Context}
  {h1 : CoversFV «Δ₁» t} {h2 : CoversFV «Δ₂» t}
  (hag : AgreesOnFV «Δ₁» «Δ₂» t) :
  t.abstract «Δ₁» (fun v hv ↦ by simpa using h1 v hv) =
  t.abstract «Δ₂» (fun v hv ↦ by simpa using h2 v hv) := by
  induction t using SMT.Term.rec' generalizing «Δ₁» «Δ₂» with
  | var v =>
    have hv : v ∈ SMT.fv (SMT.Term.var v) := by simp [SMT.fv]
    have hEq : «Δ₁» v = «Δ₂» v := hag hv
    have h1some : («Δ₁» v).isSome = true := h1 v hv
    have h2some : («Δ₂» v).isSome = true := h2 v hv
    obtain ⟨d1, hd1⟩ := Option.isSome_iff_exists.mp h1some
    obtain ⟨d2, hd2⟩ := Option.isSome_iff_exists.mp h2some
    rw [hd1, hd2] at hEq
    injection hEq with hdd
    subst hdd
    simp [SMT.Term.abstract, hd1, hd2]
  | int n => simp [SMT.Term.abstract]
  | bool b => simp [SMT.Term.abstract]
  | app f y ihf ihy =>
    have h1f : CoversFV «Δ₁» f := fun v hv => h1 v (by simpa [SMT.fv] using Or.inl hv)
    have h2f : CoversFV «Δ₂» f := fun v hv => h2 v (by simpa [SMT.fv] using Or.inl hv)
    have h1y : CoversFV «Δ₁» y := fun v hv => h1 v (by simpa [SMT.fv] using Or.inr hv)
    have h2y : CoversFV «Δ₂» y := fun v hv => h2 v (by simpa [SMT.fv] using Or.inr hv)
    have hf : AgreesOnFV «Δ₁» «Δ₂» f := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inl hv))
    have hy : AgreesOnFV «Δ₁» «Δ₂» y := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inr hv))
    have eqf := ihf hf (h1 := h1f) (h2 := h2f)
    have eqy := ihy hy (h1 := h1y) (h2 := h2y)
    simp [SMT.Term.abstract, eqf, eqy]
  | lambda vs τs P ih =>
    by_cases hlen : vs.length = τs.length
    · simp [SMT.Term.abstract, hlen]
      funext f
      have hcov1_body : ∀ v ∈ SMT.fv P, (Function.updates «Δ₁» vs (List.map Option.some (List.ofFn f)) v).isSome = true := by
        intro v hv
        by_cases hvs : v ∈ vs
        · exact Function.updates_isSome_of_mem_map_some «Δ₁» vs (List.ofFn f) v hvs (by simp)
        · rw [Function.updates_of_not_mem (f := «Δ₁») (xs := vs) (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          exact h1 v (SMT.fv.mem_lambda ⟨hv, hvs⟩)
      have hcov2_body : ∀ v ∈ SMT.fv P, (Function.updates «Δ₂» vs (List.map Option.some (List.ofFn f)) v).isSome = true := by
        intro v hv
        by_cases hvs : v ∈ vs
        · exact Function.updates_isSome_of_mem_map_some «Δ₂» vs (List.ofFn f) v hvs (by simp)
        · rw [Function.updates_of_not_mem (f := «Δ₂») (xs := vs) (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          exact h2 v (SMT.fv.mem_lambda ⟨hv, hvs⟩)
      have hgo1 := SMT.Term.abstract.go.alt_def₂ (vs := vs) (P := P)
        (Δctx := «Δ₁») (αs := List.ofFn f) (vs_αs_len := by simp)
        (Δ_isSome := by
          intro v hv hv_not_vs
          exact h1 v (SMT.fv.mem_lambda ⟨hv, hv_not_vs⟩))
        (tmp₁ := hcov1_body)
      have hgo2 := SMT.Term.abstract.go.alt_def₂ (vs := vs) (P := P)
        (Δctx := «Δ₂») (αs := List.ofFn f) (vs_αs_len := by simp)
        (Δ_isSome := by
          intro v hv hv_not_vs
          exact h2 v (SMT.fv.mem_lambda ⟨hv, hv_not_vs⟩))
        (tmp₁ := hcov2_body)
      have h_ofFn : (fun x => (List.ofFn f)[x]) = f := by
        funext x
        simp
      have hgo1f :
          (Term.abstract.go P vs «Δ₁»
            (fun v hv h =>
              h1 v (SMT.fv.mem_lambda ⟨hv, h⟩))).uncurry f
            = P.abstract (Function.updates «Δ₁» vs (List.map Option.some (List.ofFn f))) hcov1_body := by
        simpa [h_ofFn] using hgo1
      have hgo2f :
          (Term.abstract.go P vs «Δ₂»
            (fun v hv h =>
              h2 v (SMT.fv.mem_lambda ⟨hv, h⟩))).uncurry f
            = P.abstract (Function.updates «Δ₂» vs (List.map Option.some (List.ofFn f))) hcov2_body := by
        simpa [h_ofFn] using hgo2
      rw [hgo1f, hgo2f]
      have hag_body : AgreesOnFV
        (Function.updates «Δ₁» vs (List.map Option.some (List.ofFn f)))
        (Function.updates «Δ₂» vs (List.map Option.some (List.ofFn f))) P := by
        intro v hv
        by_cases hvs : v ∈ vs
        · exact Function.updates_eq_of_mem_map_some «Δ₁» «Δ₂» vs (List.ofFn f) v hvs (by simp)
        · rw [Function.updates_of_not_mem (f := «Δ₁») (xs := vs) (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          rw [Function.updates_of_not_mem (f := «Δ₂») (xs := vs) (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          exact hag (SMT.fv.mem_lambda ⟨hv, hvs⟩)
      exact ih hag_body (h1 := hcov1_body) (h2 := hcov2_body)
    · simp [SMT.Term.abstract, hlen]
  | «forall» vs τs P ih =>
    by_cases hlen : vs.length = τs.length
    · simp [SMT.Term.abstract, hlen]
      funext f
      have hcov1_body : ∀ v ∈ SMT.fv P, (Function.updates «Δ₁» vs (List.map Option.some (List.ofFn f)) v).isSome = true := by
        intro v hv
        by_cases hvs : v ∈ vs
        · exact Function.updates_isSome_of_mem_map_some «Δ₁» vs (List.ofFn f) v hvs (by simp)
        · rw [Function.updates_of_not_mem (f := «Δ₁») (xs := vs) (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          exact h1 v (SMT.fv.mem_forall ⟨hv, hvs⟩)
      have hcov2_body : ∀ v ∈ SMT.fv P, (Function.updates «Δ₂» vs (List.map Option.some (List.ofFn f)) v).isSome = true := by
        intro v hv
        by_cases hvs : v ∈ vs
        · exact Function.updates_isSome_of_mem_map_some «Δ₂» vs (List.ofFn f) v hvs (by simp)
        · rw [Function.updates_of_not_mem (f := «Δ₂») (xs := vs) (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          exact h2 v (SMT.fv.mem_forall ⟨hv, hvs⟩)
      have hgo1 := SMT.Term.abstract.go.alt_def₂ (vs := vs) (P := P)
        (Δctx := «Δ₁») (αs := List.ofFn f) (vs_αs_len := by simp)
        (Δ_isSome := by
          intro v hv hv_not_vs
          exact h1 v (SMT.fv.mem_forall ⟨hv, hv_not_vs⟩))
        (tmp₁ := hcov1_body)
      have hgo2 := SMT.Term.abstract.go.alt_def₂ (vs := vs) (P := P)
        (Δctx := «Δ₂») (αs := List.ofFn f) (vs_αs_len := by simp)
        (Δ_isSome := by
          intro v hv hv_not_vs
          exact h2 v (SMT.fv.mem_forall ⟨hv, hv_not_vs⟩))
        (tmp₁ := hcov2_body)
      have h_ofFn : (fun x => (List.ofFn f)[x]) = f := by
        funext x
        simp
      have hgo1f :
          (Term.abstract.go P vs «Δ₁»
            (fun v hv h =>
              h1 v (SMT.fv.mem_forall ⟨hv, h⟩))).uncurry f
            = P.abstract (Function.updates «Δ₁» vs (List.map Option.some (List.ofFn f))) hcov1_body := by
        simpa [h_ofFn] using hgo1
      have hgo2f :
          (Term.abstract.go P vs «Δ₂»
            (fun v hv h =>
              h2 v (SMT.fv.mem_forall ⟨hv, h⟩))).uncurry f
            = P.abstract (Function.updates «Δ₂» vs (List.map Option.some (List.ofFn f))) hcov2_body := by
        simpa [h_ofFn] using hgo2
      rw [hgo1f, hgo2f]
      have hag_body : AgreesOnFV
        (Function.updates «Δ₁» vs (List.map Option.some (List.ofFn f)))
        (Function.updates «Δ₂» vs (List.map Option.some (List.ofFn f))) P := by
        intro v hv
        by_cases hvs : v ∈ vs
        · exact Function.updates_eq_of_mem_map_some «Δ₁» «Δ₂» vs (List.ofFn f) v hvs (by simp)
        · rw [Function.updates_of_not_mem (f := «Δ₁») (xs := vs) (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          rw [Function.updates_of_not_mem (f := «Δ₂») (xs := vs) (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          exact hag (SMT.fv.mem_forall ⟨hv, hvs⟩)
      exact ih hag_body (h1 := hcov1_body) (h2 := hcov2_body)
    · simp [SMT.Term.abstract, hlen]
  | «exists» vs τs P ih =>
    by_cases hlen : vs.length = τs.length
    · simp [SMT.Term.abstract, hlen]
      apply congrArg (fun body => PHOAS.Term.exists (n := vs.length) (fun ⟨i, hi⟩ => τs[i]) body)
      funext f
      have hcov1_body : ∀ v ∈ SMT.fv P, (Function.updates «Δ₁» vs (List.map Option.some (List.ofFn f)) v).isSome = true := by
        intro v hv
        by_cases hvs : v ∈ vs
        · exact Function.updates_isSome_of_mem_map_some «Δ₁» vs (List.ofFn f) v hvs (by simp)
        · rw [Function.updates_of_not_mem (f := «Δ₁») (xs := vs) (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          exact h1 v (SMT.fv.mem_exists ⟨hv, hvs⟩)
      have hcov2_body : ∀ v ∈ SMT.fv P, (Function.updates «Δ₂» vs (List.map Option.some (List.ofFn f)) v).isSome = true := by
        intro v hv
        by_cases hvs : v ∈ vs
        · exact Function.updates_isSome_of_mem_map_some «Δ₂» vs (List.ofFn f) v hvs (by simp)
        · rw [Function.updates_of_not_mem (f := «Δ₂») (xs := vs) (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          exact h2 v (SMT.fv.mem_exists ⟨hv, hvs⟩)
      have hgo1 := SMT.Term.abstract.go.alt_def₂ (vs := vs) (P := P)
        (Δctx := «Δ₁») (αs := List.ofFn f) (vs_αs_len := by simp)
        (Δ_isSome := by
          intro v hv hv_not_vs
          exact h1 v (SMT.fv.mem_exists ⟨hv, hv_not_vs⟩))
        (tmp₁ := hcov1_body)
      have hgo2 := SMT.Term.abstract.go.alt_def₂ (vs := vs) (P := P)
        (Δctx := «Δ₂») (αs := List.ofFn f) (vs_αs_len := by simp)
        (Δ_isSome := by
          intro v hv hv_not_vs
          exact h2 v (SMT.fv.mem_exists ⟨hv, hv_not_vs⟩))
        (tmp₁ := hcov2_body)
      have h_ofFn : (fun x => (List.ofFn f)[x]) = f := by
        funext x
        simp
      have hgo1f :
          (Term.abstract.go P vs «Δ₁»
            (fun v hv h =>
              h1 v (SMT.fv.mem_exists ⟨hv, h⟩))).uncurry f
            = P.abstract (Function.updates «Δ₁» vs (List.map Option.some (List.ofFn f))) hcov1_body := by
        simpa [h_ofFn] using hgo1
      have hgo2f :
          (Term.abstract.go P vs «Δ₂»
            (fun v hv h =>
              h2 v (SMT.fv.mem_exists ⟨hv, h⟩))).uncurry f
            = P.abstract (Function.updates «Δ₂» vs (List.map Option.some (List.ofFn f))) hcov2_body := by
        simpa [h_ofFn] using hgo2
      rw [hgo1f, hgo2f]
      have hag_body : AgreesOnFV
        (Function.updates «Δ₁» vs (List.map Option.some (List.ofFn f)))
        (Function.updates «Δ₂» vs (List.map Option.some (List.ofFn f))) P := by
        intro v hv
        by_cases hvs : v ∈ vs
        · exact Function.updates_eq_of_mem_map_some «Δ₁» «Δ₂» vs (List.ofFn f) v hvs (by simp)
        · rw [Function.updates_of_not_mem (f := «Δ₁») (xs := vs) (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          rw [Function.updates_of_not_mem (f := «Δ₂») (xs := vs) (ys := (List.ofFn f).map Option.some) (k := v) hvs]
          exact hag (SMT.fv.mem_exists ⟨hv, hvs⟩)
      exact ih hag_body (h1 := hcov1_body) (h2 := hcov2_body)
    · simp [SMT.Term.abstract, hlen]
  | as t τ ih =>
    have hag' : AgreesOnFV «Δ₁» «Δ₂» t := fun v hv => hag (SMT.fv.mem_as hv)
    have h1' : CoversFV «Δ₁» t := fun v hv => h1 v (SMT.fv.mem_as hv)
    have h2' : CoversFV «Δ₂» t := fun v hv => h2 v (SMT.fv.mem_as hv)
    have eq_t := ih hag' (h1 := h1') (h2 := h2')
    cases t with
    | none => cases τ <;> simp [SMT.Term.abstract]
    | _ => simp only [SMT.Term.abstract, eq_t]
  | eq t₁ t₂ ih₁ ih₂ =>
    have h1t₁ : CoversFV «Δ₁» t₁ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inl hv)
    have h2t₁ : CoversFV «Δ₂» t₁ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inl hv)
    have h1t₂ : CoversFV «Δ₁» t₂ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inr hv)
    have h2t₂ : CoversFV «Δ₂» t₂ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inr hv)
    have hEq₁ : AgreesOnFV «Δ₁» «Δ₂» t₁ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inl hv))
    have hEq₂ : AgreesOnFV «Δ₁» «Δ₂» t₂ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inr hv))
    have eq₁ := ih₁ hEq₁ (h1 := h1t₁) (h2 := h2t₁)
    have eq₂ := ih₂ hEq₂ (h1 := h1t₂) (h2 := h2t₂)
    simp [SMT.Term.abstract, eq₁, eq₂]
  | and t₁ t₂ ih₁ ih₂ =>
    have h1t₁ : CoversFV «Δ₁» t₁ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inl hv)
    have h2t₁ : CoversFV «Δ₂» t₁ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inl hv)
    have h1t₂ : CoversFV «Δ₁» t₂ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inr hv)
    have h2t₂ : CoversFV «Δ₂» t₂ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inr hv)
    have hEq₁ : AgreesOnFV «Δ₁» «Δ₂» t₁ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inl hv))
    have hEq₂ : AgreesOnFV «Δ₁» «Δ₂» t₂ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inr hv))
    have eq₁ := ih₁ hEq₁ (h1 := h1t₁) (h2 := h2t₁)
    have eq₂ := ih₂ hEq₂ (h1 := h1t₂) (h2 := h2t₂)
    simp [SMT.Term.abstract, eq₁, eq₂]
  | or t₁ t₂ ih₁ ih₂ =>
    have h1t₁ : CoversFV «Δ₁» t₁ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inl hv)
    have h2t₁ : CoversFV «Δ₂» t₁ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inl hv)
    have h1t₂ : CoversFV «Δ₁» t₂ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inr hv)
    have h2t₂ : CoversFV «Δ₂» t₂ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inr hv)
    have hEq₁ : AgreesOnFV «Δ₁» «Δ₂» t₁ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inl hv))
    have hEq₂ : AgreesOnFV «Δ₁» «Δ₂» t₂ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inr hv))
    have eq₁ := ih₁ hEq₁ (h1 := h1t₁) (h2 := h2t₁)
    have eq₂ := ih₂ hEq₂ (h1 := h1t₂) (h2 := h2t₂)
    simp [SMT.Term.abstract, eq₁, eq₂]
  | not t ih =>
    have h1t : CoversFV «Δ₁» t := fun v hv => h1 v (by simpa [SMT.fv] using hv)
    have h2t : CoversFV «Δ₂» t := fun v hv => h2 v (by simpa [SMT.fv] using hv)
    have hEq : AgreesOnFV «Δ₁» «Δ₂» t := by
      intro v hv
      exact hag (by simpa [SMT.fv] using hv)
    have eqt := ih hEq (h1 := h1t) (h2 := h2t)
    simp [SMT.Term.abstract, eqt]
  | imp t₁ t₂ ih₁ ih₂ =>
    have h1t₁ : CoversFV «Δ₁» t₁ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inl hv)
    have h2t₁ : CoversFV «Δ₂» t₁ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inl hv)
    have h1t₂ : CoversFV «Δ₁» t₂ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inr hv)
    have h2t₂ : CoversFV «Δ₂» t₂ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inr hv)
    have hEq₁ : AgreesOnFV «Δ₁» «Δ₂» t₁ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inl hv))
    have hEq₂ : AgreesOnFV «Δ₁» «Δ₂» t₂ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inr hv))
    have eq₁ := ih₁ hEq₁ (h1 := h1t₁) (h2 := h2t₁)
    have eq₂ := ih₂ hEq₂ (h1 := h1t₂) (h2 := h2t₂)
    simp [SMT.Term.abstract, eq₁, eq₂]
  | ite c t e ihc iht ihe =>
    have h1c : CoversFV «Δ₁» c := fun v hv => h1 v (by simpa [SMT.fv] using Or.inl hv)
    have h2c : CoversFV «Δ₂» c := fun v hv => h2 v (by simpa [SMT.fv] using Or.inl hv)
    have h1t : CoversFV «Δ₁» t := fun v hv => h1 v (by simpa [SMT.fv] using Or.inr (Or.inl hv))
    have h2t : CoversFV «Δ₂» t := fun v hv => h2 v (by simpa [SMT.fv] using Or.inr (Or.inl hv))
    have h1e : CoversFV «Δ₁» e := fun v hv => h1 v (by simpa [SMT.fv] using Or.inr (Or.inr hv))
    have h2e : CoversFV «Δ₂» e := fun v hv => h2 v (by simpa [SMT.fv] using Or.inr (Or.inr hv))
    have hEqc : AgreesOnFV «Δ₁» «Δ₂» c := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inl hv))
    have hEqt : AgreesOnFV «Δ₁» «Δ₂» t := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inr (Or.inl hv)))
    have hEqe : AgreesOnFV «Δ₁» «Δ₂» e := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inr (Or.inr hv)))
    have eqc := ihc hEqc (h1 := h1c) (h2 := h2c)
    have eqt := iht hEqt (h1 := h1t) (h2 := h2t)
    have eqe := ihe hEqe (h1 := h1e) (h2 := h2e)
    simp [SMT.Term.abstract, eqc, eqt, eqe]
  | some t ih =>
    have h1t : CoversFV «Δ₁» t := fun v hv => h1 v (by simpa [SMT.fv] using hv)
    have h2t : CoversFV «Δ₂» t := fun v hv => h2 v (by simpa [SMT.fv] using hv)
    have hEq : AgreesOnFV «Δ₁» «Δ₂» t := by
      intro v hv
      exact hag (by simpa [SMT.fv] using hv)
    have eqt := ih hEq (h1 := h1t) (h2 := h2t)
    simp [SMT.Term.abstract, eqt]
  | the t ih =>
    have h1t : CoversFV «Δ₁» t := fun v hv => h1 v (by simpa [SMT.fv] using hv)
    have h2t : CoversFV «Δ₂» t := fun v hv => h2 v (by simpa [SMT.fv] using hv)
    have hEq : AgreesOnFV «Δ₁» «Δ₂» t := by
      intro v hv
      exact hag (by simpa [SMT.fv] using hv)
    have eqt := ih hEq (h1 := h1t) (h2 := h2t)
    simp [SMT.Term.abstract, eqt]
  | none => simp [SMT.Term.abstract]
  | pair t₁ t₂ ih₁ ih₂ =>
    have h1t₁ : CoversFV «Δ₁» t₁ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inl hv)
    have h2t₁ : CoversFV «Δ₂» t₁ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inl hv)
    have h1t₂ : CoversFV «Δ₁» t₂ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inr hv)
    have h2t₂ : CoversFV «Δ₂» t₂ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inr hv)
    have hEq₁ : AgreesOnFV «Δ₁» «Δ₂» t₁ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inl hv))
    have hEq₂ : AgreesOnFV «Δ₁» «Δ₂» t₂ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inr hv))
    have eq₁ := ih₁ hEq₁ (h1 := h1t₁) (h2 := h2t₁)
    have eq₂ := ih₂ hEq₂ (h1 := h1t₂) (h2 := h2t₂)
    simp [SMT.Term.abstract, eq₁, eq₂]
  | fst t ih =>
    have h1t : CoversFV «Δ₁» t := fun v hv => h1 v (by simpa [SMT.fv] using hv)
    have h2t : CoversFV «Δ₂» t := fun v hv => h2 v (by simpa [SMT.fv] using hv)
    have hEq : AgreesOnFV «Δ₁» «Δ₂» t := by
      intro v hv
      exact hag (by simpa [SMT.fv] using hv)
    have eqt := ih hEq (h1 := h1t) (h2 := h2t)
    simp [SMT.Term.abstract, eqt]
  | snd t ih =>
    have h1t : CoversFV «Δ₁» t := fun v hv => h1 v (by simpa [SMT.fv] using hv)
    have h2t : CoversFV «Δ₂» t := fun v hv => h2 v (by simpa [SMT.fv] using hv)
    have hEq : AgreesOnFV «Δ₁» «Δ₂» t := by
      intro v hv
      exact hag (by simpa [SMT.fv] using hv)
    have eqt := ih hEq (h1 := h1t) (h2 := h2t)
    simp [SMT.Term.abstract, eqt]
  | distinct ts ih =>
    simp [SMT.Term.abstract]
    let rec go (us : List SMT.Term)
      (h1us : CoversFV «Δ₁» (.distinct us))
      (h2us : CoversFV «Δ₂» (.distinct us))
      (hagus : AgreesOnFV «Δ₁» «Δ₂» (.distinct us))
      (ihus :
        ∀ t' ∈ us,
          ∀ {Δ₁ Δ₂ : Context} {h1 : CoversFV Δ₁ t'} {h2 : CoversFV Δ₂ t'},
            AgreesOnFV Δ₁ Δ₂ t' →
              t'.abstract Δ₁ (fun v hv ↦ by simpa using h1 v hv) =
              t'.abstract Δ₂ (fun v hv ↦ by simpa using h2 v hv))
      :
      SMT.Term.abstractList us «Δ₁» (fun t ht v hv ↦ by
        exact h1us v (SMT.fv.mem_distinct ⟨t, ht⟩ hv)) =
      SMT.Term.abstractList us «Δ₂» (fun t ht v hv ↦ by
        exact h2us v (SMT.fv.mem_distinct ⟨t, ht⟩ hv)) := by
      match us with
      | [] =>
        funext i
        exact Fin.elim0 i
      | t :: us =>
        funext i
        by_cases h0 : i = ⟨0, Nat.zero_lt_succ us.length⟩
        · subst h0
          simp [SMT.Term.abstractList]
          have h1t : CoversFV «Δ₁» t := by
            intro v hv
            exact h1us v (SMT.fv.mem_distinct ⟨t, (List.mem_cons_self : t ∈ t :: us)⟩ hv)
          have h2t : CoversFV «Δ₂» t := by
            intro v hv
            exact h2us v (SMT.fv.mem_distinct ⟨t, (List.mem_cons_self : t ∈ t :: us)⟩ hv)
          have hagt : AgreesOnFV «Δ₁» «Δ₂» t := by
            intro v hv
            exact hagus (SMT.fv.mem_distinct ⟨t, (List.mem_cons_self : t ∈ t :: us)⟩ hv)
          exact ihus t (List.mem_cons_self : t ∈ t :: us) hagt (h1 := h1t) (h2 := h2t)
        · have h1tail : CoversFV «Δ₁» (.distinct us) := by
            intro v hv
            rw [SMT.fv] at hv
            rcases List.mem_flatten.mp hv with ⟨l, hl, hvl⟩
            rcases List.mem_map.mp hl with ⟨t', ht', rfl⟩
            exact h1us v (SMT.fv.mem_distinct ⟨t'.1, List.mem_cons_of_mem _ t'.2⟩ hvl)
          have h2tail : CoversFV «Δ₂» (.distinct us) := by
            intro v hv
            rw [SMT.fv] at hv
            rcases List.mem_flatten.mp hv with ⟨l, hl, hvl⟩
            rcases List.mem_map.mp hl with ⟨t', ht', rfl⟩
            exact h2us v (SMT.fv.mem_distinct ⟨t'.1, List.mem_cons_of_mem _ t'.2⟩ hvl)
          have hagtail : AgreesOnFV «Δ₁» «Δ₂» (.distinct us) := by
            intro v hv
            rw [SMT.fv] at hv
            rcases List.mem_flatten.mp hv with ⟨l, hl, hvl⟩
            rcases List.mem_map.mp hl with ⟨t', ht', rfl⟩
            exact hagus (SMT.fv.mem_distinct ⟨t'.1, List.mem_cons_of_mem _ t'.2⟩ hvl)
          have ihus_tail :
              ∀ t' ∈ us,
                ∀ {Δ₁ Δ₂ : Context} {h1 : CoversFV Δ₁ t'} {h2 : CoversFV Δ₂ t'},
                  AgreesOnFV Δ₁ Δ₂ t' →
                    t'.abstract Δ₁ (fun v hv ↦ by simpa using h1 v hv) =
                    t'.abstract Δ₂ (fun v hv ↦ by simpa using h2 v hv) := by
            intro t' ht'
            exact ihus t' (List.mem_cons_of_mem _ ht')
          have h0zero : i ≠ ⟨0, Nat.zero_lt_succ us.length⟩ := h0
          have htail := go us h1tail h2tail hagtail ihus_tail
          have htailAt := congrArg (fun g => g (i.pred h0zero)) htail
          simp only [Term.abstractList]
          rw [dif_neg h0, dif_neg h0]
          exact htailAt
    exact go ts h1 h2 hag ih
  | le t₁ t₂ ih₁ ih₂ =>
    have h1t₁ : CoversFV «Δ₁» t₁ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inl hv)
    have h2t₁ : CoversFV «Δ₂» t₁ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inl hv)
    have h1t₂ : CoversFV «Δ₁» t₂ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inr hv)
    have h2t₂ : CoversFV «Δ₂» t₂ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inr hv)
    have hEq₁ : AgreesOnFV «Δ₁» «Δ₂» t₁ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inl hv))
    have hEq₂ : AgreesOnFV «Δ₁» «Δ₂» t₂ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inr hv))
    have eq₁ := ih₁ hEq₁ (h1 := h1t₁) (h2 := h2t₁)
    have eq₂ := ih₂ hEq₂ (h1 := h1t₂) (h2 := h2t₂)
    simp [SMT.Term.abstract, eq₁, eq₂]
  | add t₁ t₂ ih₁ ih₂ =>
    have h1t₁ : CoversFV «Δ₁» t₁ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inl hv)
    have h2t₁ : CoversFV «Δ₂» t₁ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inl hv)
    have h1t₂ : CoversFV «Δ₁» t₂ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inr hv)
    have h2t₂ : CoversFV «Δ₂» t₂ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inr hv)
    have hEq₁ : AgreesOnFV «Δ₁» «Δ₂» t₁ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inl hv))
    have hEq₂ : AgreesOnFV «Δ₁» «Δ₂» t₂ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inr hv))
    have eq₁ := ih₁ hEq₁ (h1 := h1t₁) (h2 := h2t₁)
    have eq₂ := ih₂ hEq₂ (h1 := h1t₂) (h2 := h2t₂)
    simp [SMT.Term.abstract, eq₁, eq₂]
  | sub t₁ t₂ ih₁ ih₂ =>
    have h1t₁ : CoversFV «Δ₁» t₁ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inl hv)
    have h2t₁ : CoversFV «Δ₂» t₁ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inl hv)
    have h1t₂ : CoversFV «Δ₁» t₂ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inr hv)
    have h2t₂ : CoversFV «Δ₂» t₂ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inr hv)
    have hEq₁ : AgreesOnFV «Δ₁» «Δ₂» t₁ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inl hv))
    have hEq₂ : AgreesOnFV «Δ₁» «Δ₂» t₂ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inr hv))
    have eq₁ := ih₁ hEq₁ (h1 := h1t₁) (h2 := h2t₁)
    have eq₂ := ih₂ hEq₂ (h1 := h1t₂) (h2 := h2t₂)
    simp [SMT.Term.abstract, eq₁, eq₂]
  | mul t₁ t₂ ih₁ ih₂ =>
    have h1t₁ : CoversFV «Δ₁» t₁ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inl hv)
    have h2t₁ : CoversFV «Δ₂» t₁ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inl hv)
    have h1t₂ : CoversFV «Δ₁» t₂ := fun v hv => h1 v (by simpa [SMT.fv] using Or.inr hv)
    have h2t₂ : CoversFV «Δ₂» t₂ := fun v hv => h2 v (by simpa [SMT.fv] using Or.inr hv)
    have hEq₁ : AgreesOnFV «Δ₁» «Δ₂» t₁ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inl hv))
    have hEq₂ : AgreesOnFV «Δ₁» «Δ₂» t₂ := by
      intro v hv
      exact hag (by simpa [SMT.fv] using (Or.inr hv))
    have eq₁ := ih₁ hEq₁ (h1 := h1t₁) (h2 := h2t₁)
    have eq₂ := ih₂ hEq₂ (h1 := h1t₂) (h2 := h2t₂)
    simp [SMT.Term.abstract, eq₁, eq₂]

theorem denote_congr_of_agreesOnFV {«Δ₁» «Δ₂» : Context} {t : SMT.Term}
  {h1 : CoversFV «Δ₁» t} {h2 : CoversFV «Δ₂» t}
  (hag : AgreesOnFV «Δ₁» «Δ₂» t) :
  denote «Δ₁» t h1 = denote «Δ₂» t h2 :=
  denote_congr_of_abstract_eq (h1 := h1) (h2 := h2)
    (abstract_eq_of_agreesOnFV (h1 := h1) (h2 := h2) hag)

theorem denote_update_of_notMem {«Δ» : Context} {t : SMT.Term} {x : SMT.𝒱} {d : SMT.Dom}
  {h : CoversFV «Δ» t}
  (hx : x ∉ SMT.fv t) :
  denote «Δ» t h =
    denote (Function.update «Δ» x (some d)) t (coversFV_update_of_notMem (x := x) (d := d) hx h) := by
  have hag : AgreesOnFV «Δ» (Function.update «Δ» x (some d)) t := by
    intro v hv
    by_cases hvx : v = x
    · subst hvx
      exfalso
      exact hx hv
    · rw [Function.update_of_ne hvx]
  exact denote_congr_of_agreesOnFV (h1 := h)
    (h2 := coversFV_update_of_notMem (x := x) (d := d) hx h) hag

end SMT.RenamingContext
