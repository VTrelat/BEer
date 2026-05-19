import B.Typing.Basic
import B.Syntax.Extra

open Batteries
namespace B

section
set_option hygiene false
local notation:90 Γ:90 " ⊢ᴮ " x " : " τ:90 => Typing Γ x τ
-- local notation:90 Γ:90 " ⊩ " xs " : " τs:90 => Typing' Γ xs τs

inductive Typing : TypeContext → Term → BType → Prop where
  | var {Γ v τ} :
      Γ.find? v = some τ
    ----------------------
    → Γ ⊢ᴮ .var v : τ
  | int {Γ n} : Γ ⊢ᴮ .int n : .int
  | bool {Γ b} : Γ ⊢ᴮ .bool b : .bool
  | maplet {Γ α β x y}:
      Γ ⊢ᴮ x : α
    → Γ ⊢ᴮ y : β
    ----------------------------
    → Γ ⊢ᴮ x ↦ᴮ y : α ×ᴮ β
  | add {Γ x y} :
      Γ ⊢ᴮ x : .int
    → Γ ⊢ᴮ y : .int
    -------------------------
    → Γ ⊢ᴮ x +ᴮ y : .int
  | sub {Γ x y} :
      Γ ⊢ᴮ x : .int
    → Γ ⊢ᴮ y : .int
    -------------------------
    → Γ ⊢ᴮ x -ᴮ y : .int
  | mul {Γ x y} :
      Γ ⊢ᴮ x : .int
    → Γ ⊢ᴮ y : .int
    -------------------------
    → Γ ⊢ᴮ x *ᴮ y : .int
  | and {Γ x y} :
      Γ ⊢ᴮ x : .bool
    → Γ ⊢ᴮ y : .bool
    -------------------------
    → Γ ⊢ᴮ x ∧ᴮ y : .bool
  | not {Γ x} :
      Γ ⊢ᴮ x : .bool
    ------------------------
    → Γ ⊢ᴮ ¬ᴮ x : .bool
  | eq {Γ α x y} :
      Γ ⊢ᴮ x : α
    → Γ ⊢ᴮ y : α
    ------------------------
    → Γ ⊢ᴮ x =ᴮ y : .bool
  | le {Γ x y} :
      Γ ⊢ᴮ x : .int
    → Γ ⊢ᴮ y : .int
    ------------------------
    → Γ ⊢ᴮ x ≤ᴮ y : .bool
  | ℤ {Γ} : Γ ⊢ᴮ .ℤ : .set .int
  | 𝔹 {Γ} : Γ ⊢ᴮ .𝔹 : .set .bool
  | mem {Γ α x S}:
      Γ ⊢ᴮ x : α
    → Γ ⊢ᴮ S : .set α
    --------------------------
    → Γ ⊢ᴮ x ∈ᴮ S : .bool
  | collect {Γ : TypeContext} {vs : List 𝒱} {αs : List BType} {D : List Term} {P : Term} :
      (vs_nemp : vs ≠ [])
    → (vs_nodup : vs.Nodup)
    → (vs_Γ_disj : ∀ v ∈ vs, v ∉ Γ)
    → (vs_αs_len : vs.length = αs.length)
    → (vs_D_len : vs.length = D.length)
    -- → (typD : ∀ i, Γ ⊢ᴮ D.get! i : αs.get! i)
    → (typD : List.Forall₂' D αs (λ Dᵢ αᵢ => Γ ⊢ᴮ Dᵢ : .set αᵢ) (vs_D_len ▸ vs_αs_len))
    → (typP : (vs.zipToAList αs ∪ Γ) ⊢ᴮ P : .bool) -- left-biased union
    --------------------------------------------------
    → Γ ⊢ᴮ .collect vs (D.reduce (· ⨯ᴮ ·) (by simpa [vs_D_len, ← List.length_pos_iff] using vs_nemp)) P : .set (αs.reduce (· ×ᴮ ·) (by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp))
  | pow {Γ α S}:
      Γ ⊢ᴮ S : .set α
    ---------------------------------
    → Γ ⊢ᴮ 𝒫ᴮ S : .set (.set α)
  | cprod {Γ α β S T}:
      Γ ⊢ᴮ S : .set α
    → Γ ⊢ᴮ T : .set β
    -----------------------------
    → Γ ⊢ᴮ S ⨯ᴮ T : .set (α ×ᴮ β)
  | union {Γ α S T}:
      Γ ⊢ᴮ S : .set α
    → Γ ⊢ᴮ T : .set α
    -----------------------------
    → Γ ⊢ᴮ S ∪ᴮ T : .set α
  | inter {Γ α S T}:
      Γ ⊢ᴮ S : .set α
    → Γ ⊢ᴮ T : .set α
    -----------------------------
    → Γ ⊢ᴮ S ∩ᴮ T : .set α
  | pfun {Γ α β S T}:
      Γ ⊢ᴮ S : .set α
    → Γ ⊢ᴮ T : .set β
    -----------------------------
    → Γ ⊢ᴮ S ⇸ᴮ T : .set (.set (α ×ᴮ β))
  | all {Γ : TypeContext} {vs : List 𝒱} {αs : List BType} {D : List Term} {P : Term} :
      (vs_nemp : vs ≠ [])
    → (vs_nodup : vs.Nodup)
    → (vs_Γ_disj : ∀ v ∈ vs, v ∉ Γ)
    → (vs_αs_len : vs.length = αs.length)
    → (vs_D_len : vs.length = D.length)
    -- → (typD : ∀ i, Γ ⊢ᴮ D.get! i : αs.get! i)
    → (typD : List.Forall₂' D αs (λ Dᵢ αᵢ => Γ ⊢ᴮ Dᵢ : .set αᵢ) (vs_D_len ▸ vs_αs_len))
    → (typP : (vs.zipToAList αs ∪ Γ) ⊢ᴮ P : .bool) -- left-biased union
    --------------------------------------------------
    → Γ ⊢ᴮ .all vs (D.reduce (· ⨯ᴮ ·) (by simpa [vs_D_len, ← List.length_pos_iff] using vs_nemp)) P : .bool
  | lambda {Γ : TypeContext} {vs : List 𝒱} {αs : List BType} {β : BType} {D : List Term} {e : Term} :
      (vs_nemp : vs ≠ [])
    → (vs_nodup : vs.Nodup)
    → (vs_Γ_disj : ∀ v ∈ vs, v ∉ Γ)
    → (vs_αs_len : vs.length = αs.length)
    → (vs_D_len : vs.length = D.length)
    -- → (typD : ∀ i, Γ ⊢ᴮ D.get! i : αs.get! i)
    → (typD : List.Forall₂' D αs (λ Dᵢ αᵢ => Γ ⊢ᴮ Dᵢ : .set αᵢ) (vs_D_len ▸ vs_αs_len))
    → (typP : (vs.zipToAList αs ∪ Γ) ⊢ᴮ e : β) -- left-biased union
    --------------------------------------------------
    → Γ ⊢ᴮ .lambda vs (D.reduce (· ⨯ᴮ ·) (by simpa [vs_D_len, ← List.length_pos_iff] using vs_nemp)) e : .set (αs.reduce (· ×ᴮ ·) (by simpa [vs_αs_len, ←List.length_pos_iff] using vs_nemp) ×ᴮ β)
  | app {Γ α β f x}:
      Γ ⊢ᴮ f : .set (α ×ᴮ β)
    → Γ ⊢ᴮ x : α
    ------------------------
    → Γ ⊢ᴮ .app f x : β
  | card {Γ α S}:
      Γ ⊢ᴮ S : .set α
    ------------------------
    → Γ ⊢ᴮ |S|ᴮ : .int
  | min {Γ S}:
      Γ ⊢ᴮ S : .set .int
    ------------------------
    → Γ ⊢ᴮ .min S : .int
  | max {Γ S}:
      Γ ⊢ᴮ S : .set .int
    ------------------------
    → Γ ⊢ᴮ .max S : .int
end

notation:90 Γ:90 " ⊢ᴮ " x " : " τ:90 => Typing Γ x τ
notation:90 "⊢ᴮ " x " : "  τ:90 => Typing ∅ x τ

section RuleInversion

theorem Typing.varE     {Γ v τ} : Γ ⊢ᴮ .var v : τ → Γ.find? v = some τ := λ h => match h with | var h => h
theorem Typing.intE     {Γ n τ} : Γ ⊢ᴮ .int n : τ → τ = .int := λ h => match h with | int => rfl
theorem Typing.boolE     {Γ b τ} : Γ ⊢ᴮ .bool b : τ → τ = .bool := λ h => match h with | bool => rfl
theorem Typing.mapletE  {Γ τ x y} : Γ ⊢ᴮ x ↦ᴮ y : τ → ∃ α β, τ = α ×ᴮ β ∧ Γ ⊢ᴮ x : α ∧ Γ ⊢ᴮ y : β := λ h => match h with | maplet h h' => ⟨_, _, rfl, h, h'⟩
theorem Typing.addE     {Γ x y τ} : Γ ⊢ᴮ x +ᴮ y : τ → τ = .int ∧ Γ ⊢ᴮ x : .int ∧ Γ ⊢ᴮ y : .int := λ h => match h with | add h h' => ⟨rfl, h, h'⟩
theorem Typing.subE     {Γ x y τ} : Γ ⊢ᴮ x -ᴮ y : τ → τ = .int ∧ Γ ⊢ᴮ x : .int ∧ Γ ⊢ᴮ y : .int := λ h => match h with | sub h h' => ⟨rfl, h, h'⟩
theorem Typing.mulE     {Γ x y τ} : Γ ⊢ᴮ x *ᴮ y : τ → τ = .int ∧ Γ ⊢ᴮ x : .int ∧ Γ ⊢ᴮ y : .int := λ h => match h with | mul h h' => ⟨rfl, h, h'⟩
theorem Typing.andE     {Γ x y τ} : Γ ⊢ᴮ x ∧ᴮ y : τ → τ = .bool ∧ Γ ⊢ᴮ x : .bool ∧ Γ ⊢ᴮ y : .bool := λ h => match h with | and h h' => ⟨rfl, h, h'⟩
theorem Typing.notE     {Γ x τ} : Γ ⊢ᴮ ¬ᴮ x : τ → τ = .bool ∧ Γ ⊢ᴮ x : .bool := λ h => match h with | not h => ⟨rfl, h⟩
theorem Typing.eqE      {Γ x y τ} : Γ ⊢ᴮ x =ᴮ y : τ → τ = .bool ∧ ∃ α, Γ ⊢ᴮ x : α ∧ Γ ⊢ᴮ y : α := λ h => match h with | eq h h' => ⟨rfl, _, h, h'⟩
theorem Typing.leE      {Γ x y τ} : Γ ⊢ᴮ x ≤ᴮ y : τ → τ = .bool ∧ Γ ⊢ᴮ x : .int ∧ Γ ⊢ᴮ y : .int := λ h => match h with | le h h' => ⟨rfl, h, h'⟩
theorem Typing.memE     {Γ x S τ} : Γ ⊢ᴮ x ∈ᴮ S : τ → τ  = .bool ∧ ∃ α, Γ ⊢ᴮ x : α ∧ Γ ⊢ᴮ S : .set α := λ h => match h with | mem h h' => ⟨rfl, _, h, h'⟩
theorem Typing.powE     {Γ S τ} : Γ ⊢ᴮ 𝒫ᴮ S : τ → ∃ β, τ = .set (.set β) ∧ Γ ⊢ᴮ S : .set β := λ h => match h with | pow h => ⟨_, rfl, h⟩
theorem Typing.cprodE   {Γ S T τ} : Γ ⊢ᴮ S ⨯ᴮ T : τ → ∃ α β, τ = .set (α ×ᴮ β) ∧ Γ ⊢ᴮ S : .set α ∧ Γ ⊢ᴮ T : .set β := by rintro ⟨⟩; rename_i α β _ _; exists α, β
theorem Typing.unionE   {Γ S T τ} : Γ ⊢ᴮ S ∪ᴮ T : τ → ∃ α, τ = .set α ∧ Γ ⊢ᴮ S : .set α ∧ Γ ⊢ᴮ T : .set α := λ h => match h with | union h h' => ⟨_, rfl, h, h'⟩
theorem Typing.interE   {Γ S T τ} : Γ ⊢ᴮ S ∩ᴮ T : τ → ∃ α, τ = .set α ∧ Γ ⊢ᴮ S : .set α ∧ Γ ⊢ᴮ T : .set α := λ h => match h with | inter h h' => ⟨_, rfl, h, h'⟩
theorem Typing.pfunE    {Γ S T τ} : Γ ⊢ᴮ S ⇸ᴮ T : τ → ∃ α β, τ = .set (.set (α ×ᴮ β)) ∧ Γ ⊢ᴮ S : .set α ∧ Γ ⊢ᴮ T : .set β := λ h => match h with | pfun h h' => ⟨_, _, rfl, h, h'⟩
theorem Typing.collectE {Γ vs D P τ} : Γ ⊢ᴮ .collect vs D P : τ → (∃ (αs : List BType) (Ds : List Term) (vs_nemp : vs ≠ []) (vs_αs_len : vs.length = αs.length) (vs_Ds_len : vs.length = Ds.length),
    τ = .set (αs.reduce (· ×ᴮ ·) (by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp))
  ∧ vs.Nodup
  ∧ D = Ds.reduce (· ⨯ᴮ ·) (by simpa [vs_Ds_len, ← List.length_pos_iff] using vs_nemp)
  ∧ List.Forall₂ (λ Dᵢ αᵢ => Γ ⊢ᴮ Dᵢ : .set αᵢ) Ds αs
  ∧ (vs.zipToAList αs ∪ Γ) ⊢ᴮ P : .bool
  ∧ (∀ v ∈ vs, v ∉ Γ)) := by
  rintro ⟨⟩
  rename_i αs Ds vs_nemp vs_nodup vs_αs_len vs_D_len vs_Γ_disj typD typP
  exists αs, Ds, vs_nemp, vs_αs_len, vs_D_len
  and_intros
  · rfl
  · exact vs_nodup
  · rfl
  · rw [← List.Forall₂_eq_Forall₂'] at typD
    exact typD
  · exact typP
  · exact vs_Γ_disj
theorem Typing.lambdaE  {Γ vs D e τ} : Γ ⊢ᴮ .lambda vs D e : τ → (∃ (β : BType)(αs : List BType) (Ds : List Term) (vs_nemp : vs ≠ []) (vs_αs_len : vs.length = αs.length) (vs_D_len : vs.length = Ds.length),
    τ = .set (αs.reduce (· ×ᴮ ·) (by simpa [vs_αs_len, ← List.length_pos_iff] using vs_nemp) ×ᴮ β)
  ∧ vs.Nodup
  ∧ D = Ds.reduce (· ⨯ᴮ ·) (by simpa [vs_D_len, ← List.length_pos_iff] using vs_nemp)
  ∧ List.Forall₂ (λ Dᵢ αᵢ => Γ ⊢ᴮ Dᵢ : .set αᵢ) Ds αs
  ∧ (vs.zipToAList αs ∪ Γ) ⊢ᴮ e : β
  ∧ (∀ v ∈ vs, v ∉ Γ)) := by
  rintro ⟨⟩
  rename_i αs β Ds vs_nemp vs_nodup vs_αs_len vs_D_len vs_Γ_disj typD typP
  exists β, αs, Ds, vs_nemp, vs_αs_len, vs_D_len
  and_intros
  · rfl
  · exact vs_nodup
  · rfl
  · rw [← List.Forall₂_eq_Forall₂'] at typD
    exact typD
  · exact typP
  · exact vs_Γ_disj
theorem Typing.allE {Γ vs D P β} : Γ ⊢ᴮ .all vs D P : β → β = .bool ∧ (∃ (vs_nemp : vs ≠ []) (αs : List BType) (Ds : List Term) (_ : vs.length = αs.length) (vs_Ds_len : vs.length = Ds.length),
  D = Ds.reduce (· ⨯ᴮ ·) (by simpa [vs_Ds_len, ← List.length_pos_iff] using vs_nemp)
  ∧ vs.Nodup
  ∧ List.Forall₂ (λ Dᵢ αᵢ => Γ ⊢ᴮ Dᵢ : .set αᵢ) Ds αs
  ∧ (vs.zipToAList αs ∪ Γ) ⊢ᴮ P : .bool
  ∧ (∀ v ∈ vs, v ∉ Γ)) := by
  rintro ⟨⟩
  rename_i αs Ds vs_nemp vs_nodup vs_αs_len vs_D_len vs_Γ_disj typD typP
  and_intros
  · rfl
  · exists vs_nemp, αs, Ds, vs_αs_len, vs_D_len
    and_intros
    · rfl
    · exact vs_nodup
    · rw [← List.Forall₂_eq_Forall₂'] at typD
      exact typD
    · exact typP
    · exact vs_Γ_disj
theorem Typing.appE    {Γ β f x} : Γ ⊢ᴮ .app f x : β → ∃ α, Γ ⊢ᴮ f : .set (α ×ᴮ β) ∧ Γ ⊢ᴮ x : α := λ h => match h with | app h h' => ⟨_, h, h'⟩
theorem Typing.cardE   {Γ S τ} : Γ ⊢ᴮ |S|ᴮ : τ → τ = .int ∧ ∃ α, Γ ⊢ᴮ S : .set α := λ h => match h with | card h => ⟨rfl, _, h⟩
theorem Typing.minE    {Γ S τ} : Γ ⊢ᴮ .min S : τ → τ = .int ∧ Γ ⊢ᴮ S : .set .int := λ h => match h with | min h => ⟨rfl, h⟩
theorem Typing.maxE    {Γ S τ} : Γ ⊢ᴮ .max S : τ → τ = .int ∧ Γ ⊢ᴮ S : .set .int := λ h => match h with | max h => ⟨rfl, h⟩

end RuleInversion

example {Γ : TypeContext} : (Γ.insert "x" .int) ⊢ᴮ .var "x" : .int := by
  apply Typing.var
  simp only [AList.lookup_insert]

example {Γ : TypeContext} : (Γ.insert "x" .int) ⊢ᴮ .var "x" ∈ᴮ .ℤ : .bool := by
  apply Typing.mem
  · apply Typing.var
    simp only [AList.lookup_insert, Option.some.injEq]
    rfl
  · apply Typing.ℤ

theorem Typing.or {Γ : TypeContext} {x y : Term} : Γ ⊢ᴮ x : .bool → Γ ⊢ᴮ y : .bool → Γ ⊢ᴮ x ∨ᴮ y : .bool :=
  λ hx hy => (Typing.not (Typing.and (Typing.not hx) (Typing.not hy)))

theorem BType.prod.fold_injective {αs βs : List BType} {α β : BType} (h : αs.length = βs.length) : αs.foldl (· ×ᴮ ·) α = βs.foldl (· ×ᴮ ·) β ↔ α = β ∧ αs = βs := by
  constructor
  · intro fold_eq
    induction αs, βs, h using List.induction₂ generalizing α β with
    | nil_nil => trivial
    | cons_cons α' αs β' βs _ ih =>
      simp [List.foldl] at fold_eq
      obtain ⟨l, rfl⟩ := ih fold_eq
      injection l with α_eq_β α'_eq_β'
      subst α_eq_β α'_eq_β'
      exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem Term.prod.fold_injective {αs βs : List Term} {α β : Term} (h : αs.length = βs.length) : αs.foldl (· ⨯ᴮ ·) α = βs.foldl (· ⨯ᴮ ·) β ↔ α = β ∧ αs = βs := by
  constructor
  · intro fold_eq
    induction αs, βs, h using List.induction₂ generalizing α β with
    | nil_nil => trivial
    | cons_cons α' αs β' βs _ ih =>
      simp [List.foldl] at fold_eq
      obtain ⟨l, rfl⟩ := ih fold_eq
      injection l with α_eq_β α'_eq_β'
      subst α_eq_β α'_eq_β'
      exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem Typing.reduce_prod_inj {αs αs' : List BType} (h : αs ≠ []) (h' : αs.length = αs'.length) :
  (αs.map .set).reduce (· ×ᴮ ·) (by simpa) = (αs'.map .set).reduce (· ×ᴮ ·) (by simpa using (by rwa [← List.length_pos_iff, ← h', List.length_pos_iff] : αs' ≠ [])) → αs = αs' := by
  let α::αs := αs
  let α'::αs' := αs'
  simp [List.reduce]
  have : (αs.map BType.set).length = (αs'.map BType.set).length := by simpa using h'
  let this := (BType.prod.fold_injective (α := α.set) (β := α'.set) this).mp
  intro h
  obtain ⟨l, r⟩ := this h
  injection l with α_eq_α'
  exact ⟨α_eq_α', List.map_ext @BType.set.inj r⟩

theorem Term.reduce_prod_inj {αs αs' : List Term} (h : αs ≠ []) (h' : αs.length = αs'.length) :
  αs.reduce (· ⨯ᴮ ·) h = αs'.reduce (· ⨯ᴮ ·) (by simpa using (by rwa [← List.length_pos_iff, ← h', List.length_pos_iff] : αs' ≠ [])) → αs = αs' := by
  let α::αs := αs
  let α'::αs' := αs'
  simp [List.reduce]
  have : αs.length = αs'.length := Nat.add_right_cancel h'
  let this := (Term.prod.fold_injective (α := α) (β := α') this).mp
  intro h
  exact this h

theorem Typing.reduce_of_Forall₂''
  {Ds : List Term} {αs : List BType} {Γ : B.TypeContext}
  {D₀ : Term} {α₀ : BType}
  (Ds_αs_len : (D₀ :: Ds).length = (α₀ :: αs).length) :
  (D₀ :: Ds).Forall₂' (α₀ :: αs) (Γ ⊢ᴮ · : ·.set) Ds_αs_len ↔ Γ ⊢ᴮ Ds.foldl (· ⨯ᴮ ·) D₀ : (αs.foldl (· ×ᴮ ·) α₀).set := by
  simp_rw [List.length_cons, Nat.succ_inj] at Ds_αs_len
  induction Ds, αs, Ds_αs_len using List.induction₂ generalizing D₀ α₀ with
  | nil_nil =>
    simp only [List.Forall₂', List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff,
      List.get_eq_getElem, List.getElem_singleton, forall_eq, List.foldl_nil]
  | cons_cons D₁ Ds α₁ αs len_eq ih =>
    rw [List.Forall₂'_cons]
    constructor
    · rintro ⟨typD₀, typDs⟩
      rw [List.foldl_cons, List.foldl_cons,
        ← @ih (D₀ ⨯ᴮ D₁) (α₀ ×ᴮ α₁) (by rwa [List.length_cons, List.length_cons, Nat.succ_inj] at Ds_αs_len)]
      rw [List.Forall₂'_cons] at typDs ⊢
      obtain ⟨typD₁, typDs⟩ := typDs
      and_intros
      · exact cprod typD₀ typD₁
      · exact typDs
    · intro h
      rw [List.foldl_cons, List.foldl_cons,
        ←ih (by rwa [List.length_cons, List.length_cons, Nat.succ_inj] at Ds_αs_len)] at h
      rw [List.Forall₂'_cons] at h ⊢
      obtain ⟨⟨⟩, typDs⟩ := h
      and_intros <;> assumption

theorem Typing.reduce_of_Forall₂'
  {Ds : List Term} {αs : List BType} {Γ : B.TypeContext}
  (Ds_nemp : Ds ≠ [])
  (Ds_αs_len : Ds.length = αs.length) :
  Ds.Forall₂' αs (Γ ⊢ᴮ · : ·.set) Ds_αs_len ↔ Γ ⊢ᴮ Ds.reduce (· ⨯ᴮ ·) Ds_nemp : (αs.reduce (· ×ᴮ ·) (by rwa [←List.length_pos_iff, ← Ds_αs_len, List.length_pos_iff])).set := by
  obtain ⟨D₀, Ds, rfl⟩ := List.exists_cons_of_ne_nil Ds_nemp
  obtain ⟨α₀, αs, rfl⟩ := List.exists_cons_of_length_eq_add_one Ds_αs_len.symm
  exact Typing.reduce_of_Forall₂'' Ds_αs_len

theorem Typing.det {Γ : TypeContext} {x : Term} {α β : BType} : Γ ⊢ᴮ x : α → Γ ⊢ᴮ x : β → α = β := by
  intro h₁ h₂
  induction h₁ generalizing β with
    | var v₁ =>
      rcases h₂ with ⟨v₂⟩
      rw [v₁] at v₂
      injection v₂
    | int | bool | add | sub | mul | and | not | eq | «ℤ» | 𝔹 | mem | le =>
      cases h₂
      rfl
    | maplet _ _ ih₁ ih₂ =>
      cases h₂ with
      | maplet x₂ y₂ =>
        congr
        exact ih₁ x₂
        exact ih₂ y₂
    | pow _ ih =>
      cases h₂ with
      | pow S₂ =>
        congr
        injection ih S₂
    | cprod _ _ ih₁ ih₂ =>
      cases h₂ with
      | cprod S₂ T₂ =>
        congr
        injection ih₁ S₂
        injection ih₂ T₂
    | union _ _ ih₁ _ =>
      cases h₂ with
      | union S₂ T₂ =>
        exact ih₁ S₂
    | inter _ _ ih₁ _ =>
      cases h₂ with
      | inter S₂ T₂ =>
        exact ih₁ S₂
    | pfun _ _ ihS ihT =>
      cases h₂ with
      | pfun hS' hT' =>
        congr
        injection ihS hS'
        injection ihT hT'
    | app _ _ ihF _ =>
      cases h₂ with
      | app F₂ X₂ =>
        injection ihF F₂
        rename_i h
        injection h
    | card _ _
    | min _ ih
    | max _ ih => cases h₂; rfl
    | all => exact Typing.allE h₂ |>.left.symm
    | collect =>
      expose_names
      obtain ⟨αs', Ds', vs_nemp, vs_αs'_len, vs_Ds'_len, rfl, vs_nodup, red_D_eq_red_Ds, typ_Ds, typ_P, vs_fresh⟩ := Typing.collectE h₂
      have D_Ds'_len : D.length = Ds'.length := by rwa [vs_D_len] at vs_Ds'_len
      obtain rfl := @Term.reduce_prod_inj D Ds' (by rwa [←List.length_pos_iff, ←vs_D_len, List.length_pos_iff]) D_Ds'_len red_D_eq_red_Ds
      congr
      rw [vs_αs_len] at vs_αs'_len
      rw [vs_D_len] at vs_Ds'_len
      apply List.ext_get vs_αs'_len
      intro i hi hi'
      rw [List.Forall₂_eq_Forall₂' (List.Forall₂.length_eq typ_Ds)] at typ_Ds
      injection typD_ih i _ (typ_Ds i (by rwa [←‹vs.length = D.length›, vs_αs_len]))
    | lambda =>
      expose_names
      obtain ⟨γ, αs', Ds', vs_nemp, vs_αs'_len, vs_Ds'_len, rfl, vs_nodup, red_D_eq_red_Ds, typ_Ds, typ_P, vs_fresh⟩ := Typing.lambdaE h₂
      have D_Ds'_len : D.length = Ds'.length := by rwa [vs_D_len] at vs_Ds'_len
      obtain rfl := @Term.reduce_prod_inj D Ds' (by rwa [←List.length_pos_iff, ←vs_D_len, List.length_pos_iff]) D_Ds'_len red_D_eq_red_Ds
      obtain rfl : αs = αs' := by
        rw [vs_αs_len] at vs_αs'_len
        rw [vs_D_len] at vs_Ds'_len
        apply List.ext_get vs_αs'_len
        intro i hi hi'
        rw [List.Forall₂_eq_Forall₂' (List.Forall₂.length_eq typ_Ds)] at typ_Ds
        injection typD_ih i _ (typ_Ds i (by rwa [←‹vs.length = D.length›, vs_αs_len]))
      congr
      exact typP_ih typ_P

theorem Typing.typed_by_fv {Γ : TypeContext} {e : Term} {τ : BType} : Γ ⊢ᴮ e : τ → fv e ⊆ Γ.keys := by
  intro h
  induction h with
  | var hv =>
    unfold fv
    simp only [List.cons_subset, List.nil_subset, and_true]
    exact TypeContext.find_in_dom hv
  | int | bool | «ℤ» | 𝔹 =>
    simp [fv]
  | @maplet Γ _ _ _ _ _ _ hx hy
  | @add Γ _ _ _ _ hx hy
  | @sub Γ _ _ _ _ hx hy
  | @mul Γ _ _ _ _ hx hy
  | @and Γ _ _ _ _ hx hy
  | @eq  Γ _ _ _ _ _ hx hy
  | @le Γ _ _ _ _ hx hy
  | @mem Γ _ _ _ _ _ hx hy
  | @cprod Γ _ _ _ _ _ _ hx hy
  | @union Γ _ _ _ _ _ hx hy
  | @inter Γ _ _ _ _ _ hx hy =>
    intro v hv; simp [fv] at hv; exact hv.elim (hx ·) (hy ·)
  | @pow Γ _ _ hx hy | @not Γ _ _ hx =>
    assumption
  | @pfun Γ _ _ _ _ _ _ hS hT | @app Γ _ _ _ _ _ _ hS hT =>
    intro v hv; simp [fv] at hv; exact hv.elim (hS ·) (hT ·)
  | card hS | min hS | max hS => rwa [fv]
  | @collect Γ vs αs D P vs_nemp vs_nodup vs_Γ_disj vs_αs_len ihD ihP typP typD_ih typP_ih =>
    intro v hv; simp [fv] at hv
    rcases hv with hv_D | hv_P
    · -- fv of List.reduce (⨯ᴮ) D
      have : ∀ (acc : Term) (rest : List Term),
          v ∈ fv (rest.foldl (· ⨯ᴮ ·) acc) → v ∈ fv acc ∨ ∃ D' ∈ rest, v ∈ fv D' := by
        intro acc rest
        induction rest generalizing acc with
        | nil => intro h; exact Or.inl h
        | cons D rest ih =>
          intro h; rcases ih _ h with h | ⟨D', hD', hx_D'⟩
          · rw [fv, List.mem_append] at h
            exact h.elim Or.inl (fun h => Or.inr ⟨D, List.mem_cons_self .., h⟩)
          · exact Or.inr ⟨D', List.mem_cons_of_mem _ hD', hx_D'⟩
      rw [List.reduce] at hv_D
      rcases this _ _ hv_D with hv_head | ⟨D', hD', hv_D'⟩
      · have hne : 0 < D.length := List.length_pos_of_ne_nil
            (by simpa [ihD, ← List.length_pos_iff] using vs_nemp)
        rw [List.head_eq_getElem] at hv_head
        exact typD_ih 0 hne hv_head
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_tail hD')
        exact typD_ih i hi hv_D'
    · -- fv P removeAll vs
      rw [List.mem_removeAll_iff] at hv_P
      have hP : v ∈ (vs.zipToAList αs ∪ Γ) := typP_ih hv_P.1
      have hv_not_zip : v ∉ vs.zipToAList αs :=
        fun h => hv_P.2 (AList.mem_zipToAList h)
      exact AList.mem_union.mp hP |>.elim (absurd · hv_not_zip) id
  | @all Γ vs αs Ds P vs_nemp vs_nodup vs_Γ_disj vs_αs_len ihD ihP typP typD_ih typP_ih
  | @lambda Γ vs αs γ Ds P vs_nemp vs_nodup vs_Γ_disj vs_αs_len ihD ihP typP typD_ih typP_ih =>
    simp [fv]
    constructor
    · -- fv of List.reduce (⨯ᴮ) Ds
      intro v hv
      have : ∀ (acc : Term) (rest : List Term),
          v ∈ fv (rest.foldl (· ⨯ᴮ ·) acc) → v ∈ fv acc ∨ ∃ D' ∈ rest, v ∈ fv D' := by
        intro acc rest; induction rest generalizing acc with
        | nil => exact Or.inl
        | cons D rest ih =>
          intro h; rcases ih _ h with h | ⟨D', hD', hx_D'⟩
          · rw [fv, List.mem_append] at h
            exact h.elim Or.inl (fun h => Or.inr ⟨D, List.mem_cons_self .., h⟩)
          · exact Or.inr ⟨D', List.mem_cons_of_mem _ hD', hx_D'⟩
      rw [List.reduce] at hv
      rcases this _ _ hv with hv_head | ⟨D', hD', hv_D'⟩
      · have hne : 0 < Ds.length := List.length_pos_of_ne_nil
            (by simpa [ihD, ← List.length_pos_iff] using vs_nemp)
        rw [List.head_eq_getElem] at hv_head
        exact typD_ih 0 hne hv_head
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_tail hD')
        exact typD_ih i hi hv_D'
    · -- fv P removeAll vs
      intro v hv; rw [List.mem_removeAll_iff] at hv
      have hP : v ∈ (vs.zipToAList αs ∪ Γ) := typP_ih hv.1
      exact AList.mem_union.mp hP |>.elim (absurd · (fun h => hv.2 (AList.mem_zipToAList h))) id

/-- Typing only depends on the `find?` behaviour of the context. -/
theorem Typing.context_perm {Γ Δ : TypeContext} {e : Term} {τ : BType} :
    (∀ x, Γ.find? x = Δ.find? x) → Γ ⊢ᴮ e : τ → Δ ⊢ᴮ e : τ := by
  intro h he
  induction e generalizing Γ Δ τ with
  | var v =>
    apply Typing.var
    rw [← h v]
    exact Typing.varE he
  | int n
  | bool b =>
    first
    | obtain rfl := Typing.intE he; exact Typing.int
    | obtain rfl := Typing.boolE he; exact Typing.bool
  | «ℤ»
  | 𝔹 =>
    rcases he
    first
    | exact Typing.ℤ
    | exact Typing.𝔹
  | maplet a b a_ih b_ih
  | add a b a_ih b_ih
  | sub a b a_ih b_ih
  | mul a b a_ih b_ih
  | le a b a_ih b_ih
  | and a b a_ih b_ih
  | eq a b a_ih b_ih
  | mem a b a_ih b_ih
  | cprod a b a_ih b_ih
  | union a b a_ih b_ih
  | inter a b a_ih b_ih
  | app a b a_ih b_ih
  | pfun a b a_ih b_ih =>
    first
    | obtain ⟨σ, ρ, rfl, typ_a, typ_b⟩ := Typing.mapletE he
    | obtain ⟨rfl, typ_a, typ_b⟩ := Typing.addE he
    | obtain ⟨rfl, typ_a, typ_b⟩ := Typing.subE he
    | obtain ⟨rfl, typ_a, typ_b⟩ := Typing.mulE he
    | obtain ⟨rfl, typ_a, typ_b⟩ := Typing.leE he
    | obtain ⟨rfl, typ_a, typ_b⟩ := Typing.andE he
    | obtain ⟨rfl, _, typ_a, typ_b⟩ := Typing.eqE he
    | obtain ⟨rfl, _, typ_a, typ_b⟩ := Typing.memE he
    | obtain ⟨_, _, rfl, typ_a, typ_b⟩ := Typing.cprodE he
    | obtain ⟨_, rfl, typ_a, typ_b⟩ := Typing.unionE he
    | obtain ⟨_, rfl, typ_a, typ_b⟩ := Typing.interE he
    | obtain ⟨_, typ_a, typ_b⟩ := Typing.appE he
    | obtain ⟨_, _, rfl, typ_a, typ_b⟩ := Typing.pfunE he
    first
    | exact Typing.maplet (a_ih h typ_a) (b_ih h typ_b)
    | exact Typing.add (a_ih h typ_a) (b_ih h typ_b)
    | exact Typing.sub (a_ih h typ_a) (b_ih h typ_b)
    | exact Typing.mul (a_ih h typ_a) (b_ih h typ_b)
    | exact Typing.le (a_ih h typ_a) (b_ih h typ_b)
    | exact Typing.and (a_ih h typ_a) (b_ih h typ_b)
    | exact Typing.eq (a_ih h typ_a) (b_ih h typ_b)
    | exact Typing.mem (a_ih h typ_a) (b_ih h typ_b)
    | exact Typing.cprod (a_ih h typ_a) (b_ih h typ_b)
    | exact Typing.union (a_ih h typ_a) (b_ih h typ_b)
    | exact Typing.inter (a_ih h typ_a) (b_ih h typ_b)
    | exact Typing.app (a_ih h typ_a) (b_ih h typ_b)
    | exact Typing.pfun (a_ih h typ_a) (b_ih h typ_b)
  | not x ih
  | pow x ih
  | card x ih
  | min x ih
  | max x ih =>
    first
    | obtain ⟨rfl, typ_x⟩ := Typing.notE he
    | obtain ⟨_, rfl, typ_x⟩ := Typing.powE he
    | obtain ⟨rfl, _, typ_x⟩ := Typing.cardE he
    | obtain ⟨rfl, typ_x⟩ := Typing.minE he
    | obtain ⟨rfl, typ_x⟩ := Typing.maxE he
    first
    | exact Typing.not (ih h typ_x)
    | exact Typing.pow (ih h typ_x)
    | exact Typing.card (ih h typ_x)
    | exact Typing.min (ih h typ_x)
    | exact Typing.max (ih h typ_x)
  | collect vs D P D_ih P_ih =>
    obtain ⟨αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, rfl, vs_nodup, rfl, typD, typP, vs_Γ_disj⟩ :=
      Typing.collectE he
    have Ds_nemp : Ds ≠ [] := by
      rwa [← List.length_pos_iff, ← vs_Ds_len, List.length_pos_iff]
    rw [List.Forall₂_eq_Forall₂' (List.Forall₂.length_eq typD),
      Typing.reduce_of_Forall₂' Ds_nemp] at typD
    refine Typing.collect vs_nemp vs_nodup (fun v hv hc => ?_) vs_αs_len vs_Ds_len ?_ ?_
    · exact vs_Γ_disj v hv (TypeContext.mem_of_find?_eq h hc)
    · rw [Typing.reduce_of_Forall₂' Ds_nemp]
      exact D_ih h typD
    · exact P_ih (TypeContext.union_find?_congr h) typP
  | all vs D P D_ih P_ih =>
    obtain ⟨rfl, vs_nemp, αs, Ds, vs_αs_len, vs_Ds_len, rfl, vs_nodup, typD, typP, vs_Γ_disj⟩ :=
      Typing.allE he
    have Ds_nemp : Ds ≠ [] := by
      rwa [← List.length_pos_iff, ← vs_Ds_len, List.length_pos_iff]
    rw [List.Forall₂_eq_Forall₂' (List.Forall₂.length_eq typD),
      Typing.reduce_of_Forall₂' Ds_nemp] at typD
    refine Typing.all vs_nemp vs_nodup (fun v hv hc => ?_) vs_αs_len vs_Ds_len ?_ ?_
    · exact vs_Γ_disj v hv (TypeContext.mem_of_find?_eq h hc)
    · rw [Typing.reduce_of_Forall₂' Ds_nemp]
      exact D_ih h typD
    · exact P_ih (TypeContext.union_find?_congr h) typP
  | lambda vs D P D_ih P_ih =>
    obtain ⟨ρ, αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, rfl, vs_nodup, rfl, typD, typP, vs_Γ_disj⟩ :=
      Typing.lambdaE he
    have Ds_nemp : Ds ≠ [] := by
      rwa [← List.length_pos_iff, ← vs_Ds_len, List.length_pos_iff]
    rw [List.Forall₂_eq_Forall₂' (List.Forall₂.length_eq typD),
      Typing.reduce_of_Forall₂' Ds_nemp] at typD
    refine Typing.lambda vs_nemp vs_nodup (fun v hv hc => ?_) vs_αs_len vs_Ds_len ?_ ?_
    · exact vs_Γ_disj v hv (TypeContext.mem_of_find?_eq h hc)
    · rw [Typing.reduce_of_Forall₂' Ds_nemp]
      exact D_ih h typD
    · exact P_ih (TypeContext.union_find?_congr h) typP

/-- Weakening by a whole block of fresh variables. The `v ∉ bv e` hypothesis is
necessary: a variable matching one of `e`'s bound names would break the binder
disjointness premises (`vs_Γ_disj`). -/
theorem Typing.context_weakening' {Γ} {vs : List 𝒱} {αs} {α} {e} :
    Γ ⊢ᴮ e : α → (∀ v ∈ vs, v ∉ Γ) → (∀ v ∈ vs, v ∉ bv e) → (vs.zipToAList αs ∪ Γ) ⊢ᴮ e : α := by
  intro h disj hbv
  induction e generalizing Γ α with
  | var v =>
    apply Typing.var
    have hvΓ : v ∈ Γ := AList.mem_keys.mp (TypeContext.find_in_dom (Typing.varE h))
    have hvvs : v ∉ vs := fun hc => disj v hc hvΓ
    unfold TypeContext.find?
    rw [AList.lookup_union_right (fun hc => hvvs (AList.mem_zipToAList hc))]
    exact Typing.varE h
  | int n
  | bool b =>
    first
    | (obtain rfl := Typing.intE h; exact Typing.int)
    | (obtain rfl := Typing.boolE h; exact Typing.bool)
  | «ℤ»
  | 𝔹 =>
    rcases h
    first
    | exact Typing.ℤ
    | exact Typing.𝔹
  | maplet a b a_ih b_ih
  | add a b a_ih b_ih
  | sub a b a_ih b_ih
  | mul a b a_ih b_ih
  | le a b a_ih b_ih
  | and a b a_ih b_ih
  | eq a b a_ih b_ih
  | mem a b a_ih b_ih
  | cprod a b a_ih b_ih
  | union a b a_ih b_ih
  | inter a b a_ih b_ih
  | app a b a_ih b_ih
  | pfun a b a_ih b_ih =>
    have ha : ∀ v ∈ vs, v ∉ bv a := fun v hv hc =>
      hbv v hv (by simp only [bv, List.mem_append]; exact Or.inl hc)
    have hb : ∀ v ∈ vs, v ∉ bv b := fun v hv hc =>
      hbv v hv (by simp only [bv, List.mem_append]; exact Or.inr hc)
    first
    | obtain ⟨σ, ρ, rfl, typ_a, typ_b⟩ := Typing.mapletE h
    | obtain ⟨rfl, typ_a, typ_b⟩ := Typing.addE h
    | obtain ⟨rfl, typ_a, typ_b⟩ := Typing.subE h
    | obtain ⟨rfl, typ_a, typ_b⟩ := Typing.mulE h
    | obtain ⟨rfl, typ_a, typ_b⟩ := Typing.leE h
    | obtain ⟨rfl, typ_a, typ_b⟩ := Typing.andE h
    | obtain ⟨rfl, _, typ_a, typ_b⟩ := Typing.eqE h
    | obtain ⟨rfl, _, typ_a, typ_b⟩ := Typing.memE h
    | obtain ⟨_, _, rfl, typ_a, typ_b⟩ := Typing.cprodE h
    | obtain ⟨_, rfl, typ_a, typ_b⟩ := Typing.unionE h
    | obtain ⟨_, rfl, typ_a, typ_b⟩ := Typing.interE h
    | obtain ⟨_, typ_a, typ_b⟩ := Typing.appE h
    | obtain ⟨_, _, rfl, typ_a, typ_b⟩ := Typing.pfunE h
    first
    | exact Typing.maplet (a_ih typ_a disj ha) (b_ih typ_b disj hb)
    | exact Typing.add (a_ih typ_a disj ha) (b_ih typ_b disj hb)
    | exact Typing.sub (a_ih typ_a disj ha) (b_ih typ_b disj hb)
    | exact Typing.mul (a_ih typ_a disj ha) (b_ih typ_b disj hb)
    | exact Typing.le (a_ih typ_a disj ha) (b_ih typ_b disj hb)
    | exact Typing.and (a_ih typ_a disj ha) (b_ih typ_b disj hb)
    | exact Typing.eq (a_ih typ_a disj ha) (b_ih typ_b disj hb)
    | exact Typing.mem (a_ih typ_a disj ha) (b_ih typ_b disj hb)
    | exact Typing.cprod (a_ih typ_a disj ha) (b_ih typ_b disj hb)
    | exact Typing.union (a_ih typ_a disj ha) (b_ih typ_b disj hb)
    | exact Typing.inter (a_ih typ_a disj ha) (b_ih typ_b disj hb)
    | exact Typing.app (a_ih typ_a disj ha) (b_ih typ_b disj hb)
    | exact Typing.pfun (a_ih typ_a disj ha) (b_ih typ_b disj hb)
  | not x ih
  | pow x ih
  | card x ih
  | min x ih
  | max x ih =>
    have hx : ∀ v ∈ vs, v ∉ bv x := fun v hv hc =>
      hbv v hv (by simp only [bv]; exact hc)
    first
    | obtain ⟨rfl, typ_x⟩ := Typing.notE h
    | obtain ⟨_, rfl, typ_x⟩ := Typing.powE h
    | obtain ⟨rfl, _, typ_x⟩ := Typing.cardE h
    | obtain ⟨rfl, typ_x⟩ := Typing.minE h
    | obtain ⟨rfl, typ_x⟩ := Typing.maxE h
    first
    | exact Typing.not (ih typ_x disj hx)
    | exact Typing.pow (ih typ_x disj hx)
    | exact Typing.card (ih typ_x disj hx)
    | exact Typing.min (ih typ_x disj hx)
    | exact Typing.max (ih typ_x disj hx)
  | collect ws D P D_ih P_ih =>
    apply Typing.collectE at h
    obtain ⟨βs, Ds, ws_nemp, ws_βs_len, ws_Ds_len, rfl, ws_nodup, rfl, typD, typP, ws_Γ_disj⟩ := h
    have Ds_nemp : Ds ≠ [] := by rwa [← List.length_pos_iff, ← ws_Ds_len, List.length_pos_iff]
    rw [List.Forall₂_eq_Forall₂' (List.Forall₂.length_eq typD),
      Typing.reduce_of_Forall₂' Ds_nemp] at typD
    have vs_ws_disj : ∀ v ∈ vs, v ∉ ws := fun v hv hc =>
      hbv v hv (by simp only [bv, List.mem_append]; exact Or.inl (Or.inl hc))
    have hbvD : ∀ v ∈ vs, v ∉ bv (Ds.reduce (· ⨯ᴮ ·) Ds_nemp) := fun v hv hc =>
      hbv v hv (by simp only [bv, List.mem_append]; exact Or.inl (Or.inr hc))
    have hbvP : ∀ v ∈ vs, v ∉ bv P := fun v hv hc =>
      hbv v hv (by simp only [bv, List.mem_append]; exact Or.inr hc)
    have vs_zip_ws_disj : ∀ x, x ∈ vs.zipToAList αs → x ∉ ws.zipToAList βs := fun x hx hc =>
      vs_ws_disj x (AList.mem_zipToAList hx) (AList.mem_zipToAList hc)
    refine Typing.collect ws_nemp ws_nodup (fun w hw hc => ?_) ws_βs_len ws_Ds_len ?_ ?_
    · exact (AList.mem_union.mp hc).elim
        (fun h1 => vs_ws_disj w (AList.mem_zipToAList h1) hw) (ws_Γ_disj w hw)
    · rw [Typing.reduce_of_Forall₂' Ds_nemp]
      exact D_ih typD disj hbvD
    · refine Typing.context_perm (TypeContext.union_swap_find? vs_zip_ws_disj)
        (P_ih typP (fun v hv hc => ?_) hbvP)
      exact (AList.mem_union.mp hc).elim
        (fun h1 => vs_ws_disj v hv (AList.mem_zipToAList h1)) (disj v hv)
  | all ws D P D_ih P_ih =>
    apply Typing.allE at h
    obtain ⟨rfl, ws_nemp, βs, Ds, ws_βs_len, ws_Ds_len, rfl, ws_nodup, typD, typP, ws_Γ_disj⟩ := h
    have Ds_nemp : Ds ≠ [] := by rwa [← List.length_pos_iff, ← ws_Ds_len, List.length_pos_iff]
    rw [List.Forall₂_eq_Forall₂' (List.Forall₂.length_eq typD),
      Typing.reduce_of_Forall₂' Ds_nemp] at typD
    have vs_ws_disj : ∀ v ∈ vs, v ∉ ws := fun v hv hc =>
      hbv v hv (by simp only [bv, List.mem_append]; exact Or.inl (Or.inl hc))
    have hbvD : ∀ v ∈ vs, v ∉ bv (Ds.reduce (· ⨯ᴮ ·) Ds_nemp) := fun v hv hc =>
      hbv v hv (by simp only [bv, List.mem_append]; exact Or.inl (Or.inr hc))
    have hbvP : ∀ v ∈ vs, v ∉ bv P := fun v hv hc =>
      hbv v hv (by simp only [bv, List.mem_append]; exact Or.inr hc)
    have vs_zip_ws_disj : ∀ x, x ∈ vs.zipToAList αs → x ∉ ws.zipToAList βs := fun x hx hc =>
      vs_ws_disj x (AList.mem_zipToAList hx) (AList.mem_zipToAList hc)
    refine Typing.all ws_nemp ws_nodup (fun w hw hc => ?_) ws_βs_len ws_Ds_len ?_ ?_
    · exact (AList.mem_union.mp hc).elim
        (fun h1 => vs_ws_disj w (AList.mem_zipToAList h1) hw) (ws_Γ_disj w hw)
    · rw [Typing.reduce_of_Forall₂' Ds_nemp]
      exact D_ih typD disj hbvD
    · refine Typing.context_perm (TypeContext.union_swap_find? vs_zip_ws_disj)
        (P_ih typP (fun v hv hc => ?_) hbvP)
      exact (AList.mem_union.mp hc).elim
        (fun h1 => vs_ws_disj v hv (AList.mem_zipToAList h1)) (disj v hv)
  | lambda ws D P D_ih P_ih =>
    apply Typing.lambdaE at h
    obtain ⟨ρ, βs, Ds, ws_nemp, ws_βs_len, ws_Ds_len, rfl, ws_nodup, rfl, typD, typP, ws_Γ_disj⟩ := h
    have Ds_nemp : Ds ≠ [] := by rwa [← List.length_pos_iff, ← ws_Ds_len, List.length_pos_iff]
    rw [List.Forall₂_eq_Forall₂' (List.Forall₂.length_eq typD),
      Typing.reduce_of_Forall₂' Ds_nemp] at typD
    have vs_ws_disj : ∀ v ∈ vs, v ∉ ws := fun v hv hc =>
      hbv v hv (by simp only [bv, List.mem_append]; exact Or.inl (Or.inl hc))
    have hbvD : ∀ v ∈ vs, v ∉ bv (Ds.reduce (· ⨯ᴮ ·) Ds_nemp) := fun v hv hc =>
      hbv v hv (by simp only [bv, List.mem_append]; exact Or.inl (Or.inr hc))
    have hbvP : ∀ v ∈ vs, v ∉ bv P := fun v hv hc =>
      hbv v hv (by simp only [bv, List.mem_append]; exact Or.inr hc)
    have vs_zip_ws_disj : ∀ x, x ∈ vs.zipToAList αs → x ∉ ws.zipToAList βs := fun x hx hc =>
      vs_ws_disj x (AList.mem_zipToAList hx) (AList.mem_zipToAList hc)
    refine Typing.lambda ws_nemp ws_nodup (fun w hw hc => ?_) ws_βs_len ws_Ds_len ?_ ?_
    · exact (AList.mem_union.mp hc).elim
        (fun h1 => vs_ws_disj w (AList.mem_zipToAList h1) hw) (ws_Γ_disj w hw)
    · rw [Typing.reduce_of_Forall₂' Ds_nemp]
      exact D_ih typD disj hbvD
    · refine Typing.context_perm (TypeContext.union_swap_find? vs_zip_ws_disj)
        (P_ih typP (fun v hv hc => ?_) hbvP)
      exact (AList.mem_union.mp hc).elim
        (fun h1 => vs_ws_disj v hv (AList.mem_zipToAList h1)) (disj v hv)

/-- Weakening by a single fresh variable. As with `context_weakening'`, `y ∉ bv e`
is necessary to preserve binder disjointness. -/
theorem Typing.context_weakening {Γ} {y} {α β} {e}
    (h : Γ ⊢ᴮ e : α) (hy : y ∉ Γ) (hbv : y ∉ bv e) : (Γ.insert y β) ⊢ᴮ e : α := by
  have key := Typing.context_weakening' (vs := [y]) (αs := [β]) h
    (by intro v hv; rw [List.mem_singleton] at hv; exact hv ▸ hy)
    (by intro v hv; rw [List.mem_singleton] at hv; exact hv ▸ hbv)
  rwa [show List.zipToAList [y] [β] ∪ Γ = Γ.insert y β by
    rw [AList.zipToAList_cons, ← AList.insert_union]; rfl] at key

theorem Typing.context_strengthening {Γ} {y} {α β} {e} : (Γ.insert y β) ⊢ᴮ e : α → y ∉ fv e → Γ ⊢ᴮ e : α := by
  intro h hy
  induction e generalizing Γ y α with
  | var v =>
    apply Typing.varE at h
    rw [fv, List.mem_singleton, ←ne_eq] at hy
    unfold TypeContext.find? at h
    rw [AList.lookup_insert_ne hy.symm] at h
    exact Typing.var h
  | int n
  | bool b =>
    first
    | obtain rfl := Typing.intE h; exact Typing.int
    | obtain rfl := Typing.boolE h; exact Typing.bool
  | «ℤ»
  | 𝔹 =>
    rcases h
    first
    | exact Typing.ℤ
    | exact Typing.𝔹
  | maplet a b a_ih b_ih
  | add a b a_ih b_ih
  | sub a b a_ih b_ih
  | mul a b a_ih b_ih
  | le a b a_ih b_ih
  | and a b a_ih b_ih
  | eq a b a_ih b_ih
  | mem a b a_ih b_ih
  | cprod a b a_ih b_ih
  | union a b a_ih b_ih
  | inter a b a_ih b_ih
  | app a b a_ih b_ih
  | pfun a b a_ih b_ih =>
    rw [fv, List.mem_append, not_or] at hy
    first
    | obtain ⟨σ, τ, rfl, typ_a, typ_b⟩ := Typing.mapletE h
    | obtain ⟨rfl, typ_a, typ_b⟩ := Typing.addE h
    | obtain ⟨rfl, typ_a, typ_b⟩ := Typing.subE h
    | obtain ⟨rfl, typ_a, typ_b⟩ := Typing.mulE h
    | obtain ⟨rfl, typ_a, typ_b⟩ := Typing.leE h
    | obtain ⟨rfl, typ_a, typ_b⟩ := Typing.andE h
    | obtain ⟨rfl, _, typ_a, typ_b⟩ := Typing.eqE h
    | obtain ⟨rfl, _, typ_a, typ_b⟩ := Typing.memE h
    | obtain ⟨_, _, rfl, typ_a, typ_b⟩ := Typing.cprodE h
    | obtain ⟨_, rfl, typ_a, typ_b⟩ := Typing.unionE h
    | obtain ⟨_, rfl, typ_a, typ_b⟩ := Typing.interE h
    | obtain ⟨_, typ_a, typ_b⟩ := Typing.appE h
    | obtain ⟨_, _, rfl, typ_a, typ_b⟩ := Typing.pfunE h
    specialize a_ih typ_a hy.1
    specialize b_ih typ_b hy.2
    first
    | exact Typing.maplet a_ih b_ih
    | exact Typing.add a_ih b_ih
    | exact Typing.sub a_ih b_ih
    | exact Typing.mul a_ih b_ih
    | exact Typing.le a_ih b_ih
    | exact Typing.and a_ih b_ih
    | exact Typing.eq a_ih b_ih
    | exact Typing.mem a_ih b_ih
    | exact Typing.cprod a_ih b_ih
    | exact Typing.union a_ih b_ih
    | exact Typing.inter a_ih b_ih
    | exact Typing.app a_ih b_ih
    | exact Typing.pfun a_ih b_ih
  | not x ih
  | pow x ih
  | card x ih
  | min x ih
  | max x ih =>
    first
    | obtain ⟨rfl, typ_x⟩ := Typing.notE h
    | obtain ⟨_, rfl, typ_x⟩ := Typing.powE h
    | obtain ⟨rfl, _, typ_x⟩ := Typing.cardE h
    | obtain ⟨rfl, typ_x⟩ := Typing.minE h
    | obtain ⟨rfl, typ_x⟩ := Typing.maxE h
    specialize ih typ_x
    first
    | exact not (ih hy)
    | exact pow (ih hy)
    | exact card (ih hy)
    | exact min (ih hy)
    | exact max (ih hy)
  | all vs D P D_ih P_ih =>
    apply Typing.allE at h
    obtain ⟨rfl, vs_nemp, αs, Ds, vs_αs_len, vs_Ds_len, rfl, vs_nodup, typD, typP, vs_Γ_disj⟩ := h

    simp only [AList.mem_insert, not_or] at vs_Γ_disj
    rw [fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not] at hy
    obtain ⟨y_notin_Ds, y_notin_P⟩ := hy
    have y_notin_vs : y ∉ vs := fun contra ↦ nomatch vs_Γ_disj y contra
    apply (Or.resolve_right · y_notin_vs) at y_notin_P

    rw [
      List.Forall₂_eq_Forall₂' (List.Forall₂.length_eq typD),
      Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff])] at typD
    specialize D_ih typD y_notin_Ds
    have hy_z : y ∉ vs.zipToAList αs := fun hc => y_notin_vs (AList.mem_zipToAList hc)
    have typP' : (vs.zipToAList αs ∪ Γ).insert y β ⊢ᴮ P : BType.bool :=
      Typing.context_perm (TypeContext.union_insert_find? hy_z) typP
    apply Typing.all vs_nemp vs_nodup (fun v hv => vs_Γ_disj v hv |>.2) vs_αs_len vs_Ds_len
    · rwa [Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff])]
    · exact P_ih typP' y_notin_P
  | collect vs D P D_ih P_ih =>
    apply Typing.collectE at h
    obtain ⟨αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, rfl, vs_nodup, rfl, typD, typP, vs_Γ_disj⟩ := h
    simp only [AList.mem_insert, not_or] at vs_Γ_disj
    rw [fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not] at hy
    obtain ⟨y_notin_Ds, y_notin_P⟩ := hy
    have y_notin_vs : y ∉ vs := fun contra ↦ nomatch vs_Γ_disj y contra
    apply (Or.resolve_right · y_notin_vs) at y_notin_P
    rw [
      List.Forall₂_eq_Forall₂' (List.Forall₂.length_eq typD),
      Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff])] at typD
    specialize D_ih typD y_notin_Ds
    have hy_z : y ∉ vs.zipToAList αs := fun hc => y_notin_vs (AList.mem_zipToAList hc)
    have typP' : (vs.zipToAList αs ∪ Γ).insert y β ⊢ᴮ P : BType.bool :=
      Typing.context_perm (TypeContext.union_insert_find? hy_z) typP
    apply Typing.collect vs_nemp vs_nodup (fun v hv => vs_Γ_disj v hv |>.2) vs_αs_len vs_Ds_len
    · rwa [Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff])]
    · exact P_ih typP' y_notin_P
  | lambda vs D P D_ih P_ih =>
    apply Typing.lambdaE at h
    obtain ⟨ρ, αs, Ds, vs_nemp, vs_αs_len, vs_Ds_len, rfl, vs_nodup, rfl, typD, typP, vs_Γ_disj⟩ := h
    simp only [AList.mem_insert, not_or] at vs_Γ_disj
    rw [fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not] at hy
    obtain ⟨y_notin_Ds, y_notin_P⟩ := hy
    have y_notin_vs : y ∉ vs := fun contra ↦ nomatch vs_Γ_disj y contra
    apply (Or.resolve_right · y_notin_vs) at y_notin_P
    rw [
      List.Forall₂_eq_Forall₂' (List.Forall₂.length_eq typD),
      Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff])] at typD
    specialize D_ih typD y_notin_Ds
    have hy_z : y ∉ vs.zipToAList αs := fun hc => y_notin_vs (AList.mem_zipToAList hc)
    have typP' : (vs.zipToAList αs ∪ Γ).insert y β ⊢ᴮ P : ρ :=
      Typing.context_perm (TypeContext.union_insert_find? hy_z) typP
    apply Typing.lambda vs_nemp vs_nodup (fun v hv => vs_Γ_disj v hv |>.2) vs_αs_len vs_Ds_len
    · rwa [Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff])]
    · exact P_ih typP' y_notin_P

theorem Typing.context_strengthening' {Γ} {vs : List 𝒱} {αs} {α} {e} : (vs.zipToAList αs ∪ Γ) ⊢ᴮ e : α → (∀ v ∈ vs, v ∉ fv e) → Γ ⊢ᴮ e : α := by
  intro h hv
  induction vs generalizing αs Γ with
  | nil =>
    exact h
  | cons v₀ vs' ih =>
    cases αs with
    | nil =>
      exact h
    | cons α₀ αs' =>
      rw [AList.zipToAList_cons, ← AList.insert_union] at h
      exact ih (Typing.context_strengthening h (hv v₀ (List.mem_cons_self ..)))
        (fun v hm => hv v (List.mem_cons_of_mem v₀ hm))


/-- Bound variables of a well-typed term are not in the typing context. -/
theorem Typing.bv_notMem_context {Γ : TypeContext} {e : Term} {τ : BType} :
    Γ ⊢ᴮ e : τ → ∀ v ∈ bv e, v ∉ Γ.keys := by
  intro h
  induction h with
  | var _ | int | bool | «ℤ» | 𝔹 =>
    intro v hv; simp [bv] at hv
  | @maplet Γ _ _ _ _ _ _ ihx ihy
  | @add Γ _ _ _ _ ihx ihy
  | @sub Γ _ _ _ _ ihx ihy
  | @mul Γ _ _ _ _ ihx ihy
  | @and Γ _ _ _ _ ihx ihy
  | @eq Γ _ _ _ _ _ ihx ihy
  | @le Γ _ _ _ _ ihx ihy
  | @mem Γ _ _ _ _ _ ihx ihy
  | @cprod Γ _ _ _ _ _ _ ihx ihy
  | @union Γ _ _ _ _ _ ihx ihy
  | @inter Γ _ _ _ _ _ ihx ihy
  | @pfun Γ _ _ _ _ _ _ ihx ihy
  | @app Γ _ _ _ _ _ _ ihx ihy =>
    intro v hv; simp [bv, List.mem_append] at hv
    exact hv.elim (ihx v ·) (ihy v ·)
  | not _ ih
  | pow _ ih
  | card _ ih
  | min _ ih
  | max _ ih =>
    intro v hv; exact ih v hv
  | @collect Γ vs αs Ds P vs_nemp vs_nodup vs_Γ_disj vs_αs_len ihD ihP typP ihD_ih ihP_ih =>
    intro v hv; simp [bv, List.mem_append] at hv
    rcases hv with hv_vs | hv_bvDs | hv_bvP
    · exact vs_Γ_disj v hv_vs
    · have : ∀ (acc : Term) (rest : List Term),
          v ∈ bv (rest.foldl (· ⨯ᴮ ·) acc) → v ∈ bv acc ∨ ∃ D' ∈ rest, v ∈ bv D' := by
        intro acc rest
        induction rest generalizing acc with
        | nil => intro h; exact Or.inl h
        | cons D rest ih_inner =>
          intro h; rcases ih_inner _ h with h | ⟨D', hD', hbv_D'⟩
          · rw [bv, List.mem_append] at h
            exact h.elim Or.inl (fun h => Or.inr ⟨D, List.mem_cons_self .., h⟩)
          · exact Or.inr ⟨D', List.mem_cons_of_mem _ hD', hbv_D'⟩
      rw [List.reduce] at hv_bvDs
      rcases this _ _ hv_bvDs with hv_head | ⟨D', hD', hv_D'⟩
      · have hne : 0 < Ds.length := List.length_pos_of_ne_nil
            (by simpa [ihD, ← List.length_pos_iff] using vs_nemp)
        rw [List.head_eq_getElem] at hv_head
        exact ihD_ih 0 hne v hv_head
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_tail hD')
        exact ihD_ih i hi v hv_D'
    · have hP := ihP_ih v hv_bvP
      intro hΓ
      exact hP (AList.mem_union.mpr (Or.inr hΓ))
  | @all Γ vs αs Ds P vs_nemp vs_nodup vs_Γ_disj vs_αs_len ihD ihP typP ihD_ih ihP_ih
  | @lambda Γ vs αs _ Ds P vs_nemp vs_nodup vs_Γ_disj vs_αs_len ihD ihP typP ihD_ih ihP_ih =>
    intro v hv; simp [bv, List.mem_append] at hv
    rcases hv with hv_vs | hv_bvDs | hv_bvP
    · exact vs_Γ_disj v hv_vs
    · have : ∀ (acc : Term) (rest : List Term),
          v ∈ bv (rest.foldl (· ⨯ᴮ ·) acc) → v ∈ bv acc ∨ ∃ D' ∈ rest, v ∈ bv D' := by
        intro acc rest
        induction rest generalizing acc with
        | nil => intro h; exact Or.inl h
        | cons D rest ih_inner =>
          intro h; rcases ih_inner _ h with h | ⟨D', hD', hbv_D'⟩
          · rw [bv, List.mem_append] at h
            exact h.elim Or.inl (fun h => Or.inr ⟨D, List.mem_cons_self .., h⟩)
          · exact Or.inr ⟨D', List.mem_cons_of_mem _ hD', hbv_D'⟩
      rw [List.reduce] at hv_bvDs
      rcases this _ _ hv_bvDs with hv_head | ⟨D', hD', hv_D'⟩
      · have hne : 0 < Ds.length := List.length_pos_of_ne_nil
            (by simpa [ihD, ← List.length_pos_iff] using vs_nemp)
        rw [List.head_eq_getElem] at hv_head
        exact ihD_ih 0 hne v hv_head
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_tail hD')
        exact ihD_ih i hi v hv_D'
    · have hP := ihP_ih v hv_bvP
      intro hΓ
      exact hP (AList.mem_union.mpr (Or.inr hΓ))

/-- Bound variables of a well-typed term are not free variables. -/
theorem Typing.bv_notMem_fv_of_typed {Γ : TypeContext} {e : Term} {τ : BType}
    (h : Γ ⊢ᴮ e : τ) (v : 𝒱) (hbv : v ∈ bv e) : v ∉ fv e := by
  intro hfv
  exact h.bv_notMem_context v hbv (h.typed_by_fv hfv)

end B
