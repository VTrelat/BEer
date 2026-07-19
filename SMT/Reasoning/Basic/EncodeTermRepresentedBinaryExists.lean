import SMT.Reasoning.Basic.EncodeTermRepresentedBinders
import SMT.Reasoning.Basic.EncodeTermCorrectPFun

open SMT ZFSet Classical

/-!
# Two-binder existential denotation bridges

The Cartesian-product encoder characterizes membership with an existential
over two target representatives.  These lemmas expose the two semantic
directions needed by representation-aware constructor proofs without
unfolding the set-theoretic implementation of quantifiers at each call site.
-/

private theorem funBinaryForallTotalRep.{u}
    {Delta : SMT.RenamingContext.Context.{u}} {body : SMT.Term}
    {a b : SMT.𝒱} {rho sigma : SMTType}
    (hcovForall : SMT.RenamingContext.CoversFV Delta
      (SMT.Term.forall [a, b] [rho, sigma] body))
    (hgo : ∀ v, v ∈ SMT.fv body → v ∉ [a, b] →
      (Delta v).isSome = true)
    (hcovBody : ∀ A B : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Delta a (some A)) b (some B))
        body)
    (total : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma →
      (⟦body.abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovBody A B)⟧ˢ).isSome = true) :
    (⟦(SMT.Term.forall [a, b] [rho, sigma] body).abstract
      Delta hcovForall⟧ˢ).isSome = true := by
  rw [SMT.Term.abstract, dif_pos (by rfl), SMT.denote]
  have hlen : [a, b].length > 0 := by simp
  rw [dif_pos hlen]
  split_ifs with hsome
  · rfl
  · exfalso
    apply hsome
    intro w hw
    have hgoPair := funAbstractGoPair hgo hcovBody w (by
      intro i
      have hi : i.1 = 0 ∨ i.1 = 1 := by
        have hiLt : i.1 < 2 := i.2
        omega
      rcases hi with hi | hi
      · have hi' : i = ⟨0, by simp⟩ := Fin.ext hi
        cases hi'
        simpa using hw ⟨0, by simp⟩
      · have hi' : i = ⟨1, by simp⟩ := Fin.ext hi
        cases hi'
        simpa using hw ⟨1, by simp⟩)
    rw [hgoPair]
    exact total (w ⟨0, by simp⟩) (w ⟨1, by simp⟩)
      (by simpa using (hw ⟨0, by simp⟩).1)
      (by simpa using (hw ⟨1, by simp⟩).1)

private theorem funBinaryForallEqZffalseRep.{u}
    {Delta : SMT.RenamingContext.Context.{u}} {body : SMT.Term}
    {a b : SMT.𝒱} {rho sigma : SMTType}
    (hcovForall : SMT.RenamingContext.CoversFV Delta
      (SMT.Term.forall [a, b] [rho, sigma] body))
    (hgo : ∀ v, v ∈ SMT.fv body → v ∉ [a, b] →
      (Delta v).isSome = true)
    (hcovBody : ∀ A B : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Delta a (some A)) b (some B))
        body)
    (total : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma →
      (⟦body.abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovBody A B)⟧ˢ).isSome = true)
    (bodyType : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma → ∀ {D : SMT.Dom.{u}},
      ⟦body.abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovBody A B)⟧ˢ = some D → D.snd.fst = SMTType.bool)
    (A B : SMT.Dom.{u}) (hA : A.snd.fst = rho)
    (hB : B.snd.fst = sigma) {D : SMT.Dom.{u}}
    (hdenBody : ⟦body.abstract
      (Function.update (Function.update Delta a (some A)) b (some B))
      (hcovBody A B)⟧ˢ = some D)
    (hfalse : D.fst = ZFSet.zffalse) :
    ⟦(SMT.Term.forall [a, b] [rho, sigma] body).abstract
      Delta hcovForall⟧ˢ =
      some (⟨ZFSet.zffalse, SMTType.bool,
        ZFSet.ZFBool.zffalse_mem_𝔹⟩ : SMT.Dom) := by
  obtain ⟨Phi, hdenForall⟩ := Option.isSome_iff_exists.mp
    (funBinaryForallTotalRep hcovForall hgo hcovBody total)
  have hPhiType : Phi.snd.fst = SMTType.bool := by
    have h := hdenForall
    rw [SMT.Term.abstract, dif_pos (by rfl)] at h
    exact denote_forall_ty h
  have hPhiFalse : Phi.fst = ZFSet.zffalse := by
    have hbool : Phi.fst ∈ ZFSet.𝔹 := by
      simpa [hPhiType] using Phi.snd.snd
    rw [ZFSet.ZFBool.mem_𝔹_iff] at hbool
    rcases hbool with hPhiFalse | hPhiTrue
    · exact hPhiFalse
    · obtain ⟨D', hdenBody', hDTrue⟩ :=
        funBinaryForallTrueAt hcovForall hgo hcovBody total bodyType
          hdenForall hPhiTrue A B hA hB
      have hEq : D' = D := Option.some.inj (hdenBody'.symm.trans hdenBody)
      exact False.elim (ZFSet.zftrue_ne_zffalse
        (hDTrue.symm.trans
          ((congrArg (fun d : SMT.Dom => d.fst) hEq).trans hfalse)))
  rcases Phi with ⟨value, tau, hvalue⟩
  dsimp at hPhiType hPhiFalse
  subst tau
  subst value
  simpa only [proof_irrel_heq] using hdenForall

private theorem funBinaryNotGoEqRep.{u}
    {Delta : SMT.RenamingContext.Context.{u}} {body : SMT.Term}
    {a b : SMT.𝒱}
    (hgo : ∀ v, v ∈ SMT.fv body → v ∉ [a, b] →
      (Delta v).isSome = true)
    (hgoNot : ∀ v, v ∈ SMT.fv (¬ˢ body) → v ∉ [a, b] →
      (Delta v).isSome = true)
    (hcovBody : ∀ A B : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Delta a (some A)) b (some B))
        body)
    (hcovNot : ∀ A B : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Delta a (some A)) b (some B))
        (¬ˢ body)) :
    (Term.abstract.go (¬ˢ body) [a, b] Delta hgoNot).uncurry =
      fun x => ¬ˢ' (Term.abstract.go body [a, b] Delta hgo).uncurry x := by
  funext x
  let A0 := x ⟨0, by simp⟩
  let B0 := x ⟨1, by simp⟩
  have hxEq :
      (fun x' : Fin [a, b].length =>
        match x' with
        | ⟨i, _⟩ => [A0, B0][i]) = x := by
    funext i
    have hi : i.val = 0 ∨ i.val = 1 := by
      have hiLt : i.val < 2 := i.isLt
      omega
    rcases hi with hi | hi
    · have hi' : i = ⟨0, by simp⟩ := Fin.ext hi
      cases hi'
      rfl
    · have hi' : i = ⟨1, by simp⟩ := Fin.ext hi
      cases hi'
      rfl
  have hgoNot' :=
    SMT.Term.abstract.go.alt_def₂
      (vs := [a, b]) (P := ¬ˢ body) (Δctx := Delta)
      (αs := [A0, B0]) (vs_αs_len := by simp)
      (Δ_isSome := hgoNot)
      (tmp₁ := by
        intro y hy
        simpa [A0, B0, Function.updates] using hcovNot A0 B0 y hy)
  have hgoBody' :=
    SMT.Term.abstract.go.alt_def₂
      (vs := [a, b]) (P := body) (Δctx := Delta)
      (αs := [A0, B0]) (vs_αs_len := by simp)
      (Δ_isSome := hgo)
      (tmp₁ := by
        intro y hy
        simpa [A0, B0, Function.updates] using hcovBody A0 B0 y hy)
  rw [← hxEq, hgoNot', hgoBody', Term.abstract]

/-- A typed pair of witnesses whose body is true makes the corresponding
two-binder existential true. -/
theorem funBinaryExistsEqZftrueAtWitness.{u}
    {Delta : SMT.RenamingContext.Context.{u}} {body : SMT.Term}
    {a b : SMT.𝒱} {rho sigma : SMTType}
    (hcovExists : SMT.RenamingContext.CoversFV Delta
      (SMT.Term.exists [a, b] [rho, sigma] body))
    (hgo : ∀ v, v ∈ SMT.fv body → v ∉ [a, b] →
      (Delta v).isSome = true)
    (hcovBody : ∀ A B : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Delta a (some A)) b (some B))
        body)
    (total : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma →
      (⟦body.abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovBody A B)⟧ˢ).isSome = true)
    (bodyType : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma → ∀ {D : SMT.Dom.{u}},
      ⟦body.abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovBody A B)⟧ˢ = some D → D.snd.fst = SMTType.bool)
    (A B : SMT.Dom.{u}) (hA : A.snd.fst = rho)
    (hB : B.snd.fst = sigma) {D : SMT.Dom.{u}}
    (hdenBody : ⟦body.abstract
      (Function.update (Function.update Delta a (some A)) b (some B))
      (hcovBody A B)⟧ˢ = some D)
    (htrue : D.fst = ZFSet.zftrue) :
    ⟦(SMT.Term.exists [a, b] [rho, sigma] body).abstract
      Delta hcovExists⟧ˢ =
      some (⟨ZFSet.zftrue, SMTType.bool,
        ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom) := by
  have hcovForallNot : SMT.RenamingContext.CoversFV Delta
      (SMT.Term.forall [a, b] [rho, sigma] (¬ˢ body)) := by
    intro v hv
    exact hcovExists v (by simpa [SMT.fv] using hv)
  have hgoNot : ∀ v, v ∈ SMT.fv (¬ˢ body) → v ∉ [a, b] →
      (Delta v).isSome = true := by
    intro v hv hnot
    exact hgo v (by simpa [SMT.fv] using hv) hnot
  have hcovNot : ∀ A B : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Delta a (some A)) b (some B))
        (¬ˢ body) := by
    intro A B v hv
    exact hcovBody A B v (by simpa [SMT.fv] using hv)
  have totalNot : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma →
      (⟦(¬ˢ body).abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovNot A B)⟧ˢ).isSome = true := by
    intro A B hA hB
    obtain ⟨DBody, hden⟩ := Option.isSome_iff_exists.mp
      (total A B hA hB)
    exact funNotAbstractIsSomeOfSomeBool
      (hcov_t := hcovBody A B) hden (bodyType A B hA hB hden)
      (hcovNot A B)
  have typeNot : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma → ∀ {D : SMT.Dom.{u}},
      ⟦(¬ˢ body).abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovNot A B)⟧ˢ = some D → D.snd.fst = SMTType.bool := by
    intro A B hA hB D hden
    rw [SMT.Term.abstract] at hden
    exact denote_not_ty hden
  have hdenNotFalse :
      ⟦(¬ˢ body).abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovNot A B)⟧ˢ =
      some (⟨ZFSet.zffalse, SMTType.bool,
        ZFSet.ZFBool.zffalse_mem_𝔹⟩ : SMT.Dom) := by
    rw [SMT.Term.abstract]
    simpa only [proof_irrel_heq] using
      denote_not_eq_zffalse_of_some_zftrue hdenBody
        (bodyType A B hA hB hdenBody) htrue
  have hforallNotFalse := funBinaryForallEqZffalseRep
    hcovForallNot hgoNot hcovNot totalNot typeNot A B hA hB
    hdenNotFalse rfl
  have hnotForallTrue := denote_not_eq_zftrue_of_some_zffalse
    hforallNotFalse rfl rfl
  have hgoNotEq := funBinaryNotGoEqRep hgo hgoNot hcovBody hcovNot
  simpa [SMT.Term.abstract, SMT.PHOAS.Term.exists,
    hgoNotEq, proof_irrel_heq] using hnotForallTrue

private theorem funBinaryExistsEqZffalseRep.{u}
    {Delta : SMT.RenamingContext.Context.{u}} {body : SMT.Term}
    {a b : SMT.𝒱} {rho sigma : SMTType}
    (hcovExists : SMT.RenamingContext.CoversFV Delta
      (SMT.Term.exists [a, b] [rho, sigma] body))
    (hgo : ∀ v, v ∈ SMT.fv body → v ∉ [a, b] →
      (Delta v).isSome = true)
    (hcovBody : ∀ A B : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Delta a (some A)) b (some B))
        body)
    (total : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma →
      (⟦body.abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovBody A B)⟧ˢ).isSome = true)
    (bodyType : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma → ∀ {D : SMT.Dom.{u}},
      ⟦body.abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovBody A B)⟧ˢ = some D → D.snd.fst = SMTType.bool)
    (bodyFalse : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma →
      ∃ D : SMT.Dom.{u},
        ⟦body.abstract
          (Function.update (Function.update Delta a (some A)) b (some B))
          (hcovBody A B)⟧ˢ = some D ∧ D.fst = ZFSet.zffalse) :
    ⟦(SMT.Term.exists [a, b] [rho, sigma] body).abstract
      Delta hcovExists⟧ˢ =
      some (⟨ZFSet.zffalse, SMTType.bool,
        ZFSet.ZFBool.zffalse_mem_𝔹⟩ : SMT.Dom) := by
  have hcovForallNot : SMT.RenamingContext.CoversFV Delta
      (SMT.Term.forall [a, b] [rho, sigma] (¬ˢ body)) := by
    intro v hv
    exact hcovExists v (by simpa [SMT.fv] using hv)
  have hgoNot : ∀ v, v ∈ SMT.fv (¬ˢ body) → v ∉ [a, b] →
      (Delta v).isSome = true := by
    intro v hv hnot
    exact hgo v (by simpa [SMT.fv] using hv) hnot
  have hcovNot : ∀ A B : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Delta a (some A)) b (some B))
        (¬ˢ body) := by
    intro A B v hv
    exact hcovBody A B v (by simpa [SMT.fv] using hv)
  have totalNot : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma →
      (⟦(¬ˢ body).abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovNot A B)⟧ˢ).isSome = true := by
    intro A B hA hB
    obtain ⟨D, hden⟩ := Option.isSome_iff_exists.mp (total A B hA hB)
    exact funNotAbstractIsSomeOfSomeBool
      (hcov_t := hcovBody A B) hden (bodyType A B hA hB hden)
      (hcovNot A B)
  have typeNot : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma → ∀ {D : SMT.Dom.{u}},
      ⟦(¬ˢ body).abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovNot A B)⟧ˢ = some D → D.snd.fst = SMTType.bool := by
    intro A B hA hB D hden
    rw [SMT.Term.abstract] at hden
    exact denote_not_ty hden
  have bodyTrueNot : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma →
      ∃ D : SMT.Dom.{u},
        ⟦(¬ˢ body).abstract
          (Function.update (Function.update Delta a (some A)) b (some B))
          (hcovNot A B)⟧ˢ = some D ∧ D.fst = ZFSet.zftrue := by
    intro A B hA hB
    obtain ⟨D, hden, hfalse⟩ := bodyFalse A B hA hB
    refine ⟨⟨ZFSet.zftrue, SMTType.bool,
      ZFSet.ZFBool.zftrue_mem_𝔹⟩, ?_, rfl⟩
    rw [SMT.Term.abstract]
    simpa only [proof_irrel_heq] using
      denote_not_eq_zftrue_of_some_zffalse hden
        (bodyType A B hA hB hden) hfalse
  have hforallNotTrue :
      ⟦(SMT.Term.forall [a, b] [rho, sigma] (¬ˢ body)).abstract
        Delta hcovForallNot⟧ˢ =
        some (⟨ZFSet.zftrue, SMTType.bool,
          ZFSet.ZFBool.zftrue_mem_𝔹⟩ : SMT.Dom) := by
    exact funBinaryForallEqZftrue hcovForallNot hgoNot hcovNot
      totalNot typeNot bodyTrueNot
  have hgoNotEq := funBinaryNotGoEqRep hgo hgoNot hcovBody hcovNot
  have hnotForallFalse := denote_not_eq_zffalse_of_some_zftrue
    hforallNotTrue rfl rfl
  simpa [SMT.Term.abstract, SMT.PHOAS.Term.exists,
    hgoNotEq, proof_irrel_heq] using hnotForallFalse

/-- If a total Boolean two-binder existential is true, then typed witnesses
exist and make its body true. -/
theorem funBinaryExistsTrueWitness.{u}
    {Delta : SMT.RenamingContext.Context.{u}} {body : SMT.Term}
    {a b : SMT.𝒱} {rho sigma : SMTType}
    (hcovExists : SMT.RenamingContext.CoversFV Delta
      (SMT.Term.exists [a, b] [rho, sigma] body))
    (hgo : ∀ v, v ∈ SMT.fv body → v ∉ [a, b] →
      (Delta v).isSome = true)
    (hcovBody : ∀ A B : SMT.Dom.{u},
      SMT.RenamingContext.CoversFV
        (Function.update (Function.update Delta a (some A)) b (some B))
        body)
    (total : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma →
      (⟦body.abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovBody A B)⟧ˢ).isSome = true)
    (bodyType : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma → ∀ {D : SMT.Dom.{u}},
      ⟦body.abstract
        (Function.update (Function.update Delta a (some A)) b (some B))
        (hcovBody A B)⟧ˢ = some D → D.snd.fst = SMTType.bool)
    {Phi : SMT.Dom.{u}}
    (hdenExists :
      ⟦(SMT.Term.exists [a, b] [rho, sigma] body).abstract
        Delta hcovExists⟧ˢ = some Phi)
    (htrue : Phi.fst = ZFSet.zftrue) :
    ∃ A B : SMT.Dom.{u}, A.snd.fst = rho ∧ B.snd.fst = sigma ∧
      ∃ D : SMT.Dom.{u},
        ⟦body.abstract
          (Function.update (Function.update Delta a (some A)) b (some B))
          (hcovBody A B)⟧ˢ = some D ∧ D.fst = ZFSet.zftrue := by
  by_contra hnone
  push_neg at hnone
  have bodyFalse : ∀ A B : SMT.Dom.{u}, A.snd.fst = rho →
      B.snd.fst = sigma →
      ∃ D : SMT.Dom.{u},
        ⟦body.abstract
          (Function.update (Function.update Delta a (some A)) b (some B))
          (hcovBody A B)⟧ˢ = some D ∧ D.fst = ZFSet.zffalse := by
    intro A B hA hB
    obtain ⟨D, hden⟩ := Option.isSome_iff_exists.mp (total A B hA hB)
    have hDType := bodyType A B hA hB hden
    have hDmem : D.fst ∈ ZFSet.𝔹 := by
      simpa [hDType] using D.snd.snd
    rw [ZFSet.ZFBool.mem_𝔹_iff] at hDmem
    rcases hDmem with hfalse | htrueD
    · exact ⟨D, hden, hfalse⟩
    · exact False.elim (hnone A B hA hB D hden htrueD)
  have hdenFalse := funBinaryExistsEqZffalseRep hcovExists hgo hcovBody
    total bodyType bodyFalse
  have hPhiEq : Phi =
      (⟨ZFSet.zffalse, SMTType.bool,
        ZFSet.ZFBool.zffalse_mem_𝔹⟩ : SMT.Dom) :=
    Option.some.inj (hdenExists.symm.trans hdenFalse)
  exact ZFSet.zftrue_ne_zffalse
    (htrue.symm.trans (congrArg (fun D : SMT.Dom => D.fst) hPhiEq))
