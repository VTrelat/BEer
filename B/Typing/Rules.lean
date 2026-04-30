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
    | collect => admit
    | lambda => admit

theorem Typing.context_weakening {Γ} {y} {α β} {e} : Γ ⊢ᴮ e : α → y ∉ Γ → (Γ.insert y β) ⊢ᴮ e : α := by
  admit

theorem Typing.context_weakening' {Γ} {vs : List 𝒱} {αs} {α} {e} : Γ ⊢ᴮ e : α → (∀ v ∈ vs, v ∉ Γ) → (vs.zipToAList αs ∪ Γ) ⊢ᴮ e : α := by
  admit

theorem Typing.context_strengthening {Γ} {y} {α β} {e} : (Γ.insert y β) ⊢ᴮ e : α → y ∉ fv e → Γ ⊢ᴮ e : α := by
  intro h hy
  induction e generalizing Γ y α β with
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
    rw [fv, List.mem_append, List.mem_removeAll_iff, not_or] at hy

    rw [
      List.Forall₂_eq_Forall₂' (List.Forall₂.length_eq typD),
      Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff])] at typD
    specialize D_ih typD hy.1
    have typP' : (vs.zipToAList αs ∪ Γ).insert y β ⊢ᴮ P : BType.bool := by
      admit
    apply Typing.all vs_nemp vs_nodup (fun v hv => vs_Γ_disj v hv |>.2) vs_αs_len vs_Ds_len
    · rwa [Typing.reduce_of_Forall₂' (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff])]
    · apply P_ih
      · exact typP'
      · rw [not_and'] at hy
        apply hy.2
        intro contr
        specialize vs_Γ_disj y contr
        nomatch vs_Γ_disj.1
  | collect vs D P D_ih P_ih => sorry
  | lambda vs D P D_ih P_ih => sorry

theorem Typing.context_strengthening' {Γ} {vs : List 𝒱} {αs} {α} {e} : (vs.zipToAList αs ∪ Γ) ⊢ᴮ e : α → (∀ v ∈ vs, v ∉ fv e) → Γ ⊢ᴮ e : α := by
  admit


-- theorem Finmap.zipToFinmap_keys {Γ : TypeContext} {vs : List 𝒱} {αs : List BType} (h : vs.length = αs.length) : (vs.zipToFinmap αs).keys = vs.toAList := by
--   induction vs, αs, h using List.induction₂ with
--   | nil_nil => rfl
--   | cons_cons v vs α αs _ ih =>
--     rw [List.zipToFinmap.eq_def]
--     simp only [List.zipWith_cons_cons, List.toFinset_cons]
--     rw [Finmap.toFinmap_cons, ← List.zipToFinmap.eq_def, ← ih]
--     admit

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

/-

theorem Typing.union_find?_iff {Γ Δ : TypeContext} {x : 𝒱} {τ : BType} : (Γ ∪ Δ).find? x = τ ↔ Γ.find? x = τ ∨ (x ∉ Γ ∧ Δ.find? x = τ) := by
  simp only [AList.lookup_union_eq_some, TypeContext.find?]
  admit

theorem Typing.union_extend_left {Γ Δ₁ Δ₂ : TypeContext} : Δ₁.find? = Δ₂.find? → ∀ {x : 𝒱}, (Γ ∪ Δ₁).find? x = (Γ ∪ Δ₂).find? x := by
  admit

theorem Typing.context_perm {Γ Δ : TypeContext} {e : Term} {τ : BType}: (∀ x, Γ.find? x = Δ.find? x) → Γ ⊢ᴮ e : τ → Δ ⊢ᴮ e : τ := by
  intro h he
  induction e generalizing τ Γ Δ with
  | var v =>
    cases he
    apply Typing.var
    rwa [←h]
  | int _ | bool _ =>
    cases he
    first
    | exact Typing.int
    | exact Typing.bool
  | maplet x y xih yih =>
    rcases he with _ | _ | _ | ⟨hx, hy⟩
    replace hx := xih h hx
    replace hy := yih h hy
    apply Typing.maplet <;> assumption
  | le x y xih yih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |  ⟨hx, hy⟩
    replace hx := xih h hx
    replace hy := yih h hy
    apply Typing.le <;> assumption
  | add x y xih yih =>
    rcases he with _ | _ | _ | _ | ⟨hx, hy⟩
    replace hx := xih h hx
    replace hy := yih h hy
    apply Typing.add <;> assumption
  | sub x y xih yih =>
    rcases he with _ | _ | _ | _ | _ | ⟨hx, hy⟩
    replace hx := xih h hx
    replace hy := yih h hy
    apply Typing.sub <;> assumption
  | mul x y xih yih =>
    rcases he with _ | _ | _ | _ | _ | _ | ⟨hx, hy⟩
    replace hx := xih h hx
    replace hy := yih h hy
    apply Typing.mul <;> assumption
  | and x y xih yih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | ⟨hx, hy⟩
    replace hx := xih h hx
    replace hy := yih h hy
    apply Typing.and <;> assumption
  | not x xih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | hx
    replace hx := xih h hx
    apply Typing.not
    assumption
  | eq x y xih yih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hx, hy⟩
    replace hx := xih h hx
    replace hy := yih h hy
    apply Typing.eq <;> assumption
  | «ℤ» =>
    cases he
    exact Typing.ℤ
  | 𝔹 =>
    cases he
    exact Typing.𝔹
  | mem x S xih Sih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |_ |  ⟨hx, Sh⟩
    replace hx := xih h hx
    replace Sh := Sih h Sh
    apply Typing.mem <;> assumption
  | collect vs D P Dih Pih =>
    admit
  | all vs D P Dih Pih =>
    admit
  | pow S Sih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS⟩
    replace hS := Sih h hS
    apply Typing.pow
    assumption
  | cprod S T Sih Tih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS, hT⟩
    replace hS := Sih h hS
    replace hT := Tih h hT
    apply Typing.cprod <;> assumption
  | union S T Sih Tih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS, hT⟩
    replace hS := Sih h hS
    replace hT := Tih h hT
    apply Typing.union <;> assumption
  | inter S T Sih Tih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS, hT⟩
    replace hS := Sih h hS
    replace hT := Tih h hT
    apply Typing.inter <;> assumption
  | pfun S T Sih Tih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS, hT⟩
    apply Typing.pfun
    · exact Sih h hS
    · exact Tih h hT
  | lambda v D P Dih Pih =>
    admit
  | app f x fih xih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hx, Ph⟩
    apply Typing.app
    · exact fih h hx
    · exact xih h Ph
  | card S Sih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS⟩
    apply Typing.card
    exact Sih h hS
  | min S Sih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS⟩
    apply Typing.min
    exact Sih h hS
  | max S Sih =>
    rcases he with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨hS⟩
    apply Typing.max
    exact Sih h hS

theorem Typing.context_swap {Γ : TypeContext} {x y} {α β τ} {e} : (Γ.insert x α).insert y β ⊢ᴮ e : τ → x ≠ y → (Γ.insert y β).insert x α ⊢ᴮ e : τ := by
  admit

-/

end B
