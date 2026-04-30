import SMT.Syntax
import SMT.PHOAS.SMTPHOAS
import SMT.HOTyping.Rules
import Mathlib.Data.List.Basic
import Extra.Utils

namespace SMT

abbrev TypeContext := AList fun _ : 𝒱 ↦ SMTType

def TypeContext.update (Γ : TypeContext) (vs : List 𝒱) (τs : List SMTType) (hlen : vs.length = τs.length := by assumption) : TypeContext :=
  Fin.foldl vs.length (fun Δ i ↦ Δ.insert vs[i] τs[i] ) Γ

theorem TypeContext.mem_update_singleton (Γ : TypeContext) (v₀ v : 𝒱) (τ₀ τ : SMTType) :
    v ∈ (Γ.update [v₀] [τ₀] rfl) ↔ v = v₀ ∨ v ∈ Γ := by
  simp only [update, List.length_cons, List.length_nil, zero_add, Fin.foldl_succ, Nat.reduceAdd,
    Fin.cast_eq_self, Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero, Fin.isValue,
    Fin.foldl_zero, AList.mem_insert]

theorem TypeContext.mem_update_iff (Γ : TypeContext) (v : 𝒱) (vs : List 𝒱) (τs : List SMTType)
  (hlen : vs.length = τs.length := by assumption) :
    v ∈ (Γ.update vs τs) ↔ v ∈ vs ∨ v ∈ Γ := by
  induction vs, τs, hlen using List.reverse_induction₂ with
  | nil_nil =>
    simp only [update, List.length_nil, Fin.getElem_fin, Fin.foldl_zero, List.not_mem_nil, false_or]
  | cons_cons vₙ vs τₙ τs hlen ih =>
    simp only [update, List.concat_eq_append, List.length_append, List.length_cons, List.length_nil,
      zero_add, Fin.foldl_succ_last, Fin.getElem_fin, Fin.coe_cast, Fin.val_last, le_refl,
      List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero, Fin.coe_castSucc, Fin.is_lt,
      List.getElem_append_left, AList.mem_insert, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false]
    conv =>
      enter [1,2,1]
      change ?fold
    have : ?fold = Γ.update vs τs := by
      congr
      funext Ξ ⟨i, hi⟩
      rw [List.getElem_append_left (Std.Rio.Internal.get_elem_helper_upper_open hi hlen)]
      rfl
    rw [this]
    clear this
    rw [ih, ←or_assoc, or_comm (a := v = vₙ)]

theorem TypeContext.lookup_update (Γ : TypeContext) (v : 𝒱) (vs : List 𝒱) (τs : List SMTType) (hlen : vs.length = τs.length := by assumption) (hv : v ∉ vs) :
    (Γ.update vs τs).lookup v = Γ.lookup v := by
  induction vs, τs, hlen using List.reverse_induction₂ with
  | nil_nil =>
    simp only [update, List.length_nil, Fin.getElem_fin, Fin.foldl_zero]
  | cons_cons vₙ vs τₙ τs hlen ih =>
    rw [List.concat_eq_append, List.mem_append, List.mem_singleton, not_or] at hv
    simp only [update, List.concat_eq_append, List.length_append, List.length_cons, List.length_nil,
      zero_add, Fin.foldl_succ_last, Fin.getElem_fin, Fin.coe_cast, Fin.val_last, le_refl,
      List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero, Fin.coe_castSucc, Fin.is_lt,
      List.getElem_append_left, AList.lookup_insert_ne hv.2]
    conv =>
      enter [1,2]
      change ?fold
    have hfold : ?fold = Γ.update vs τs hlen := by
      unfold TypeContext.update
      congr
      funext Ξ ⟨i, hi⟩
      rw [List.getElem_append_left (by simpa [hlen] using hi)]
      rfl
    rw [hfold]
    exact ih hv.1

theorem TypeContext.insert_mono {Γ Δ : TypeContext} {v : 𝒱} {τ : SMTType} :
    Γ.entries ⊆ Δ.entries → (Γ.insert v τ).entries ⊆ (Δ.insert v τ).entries := by
  intro h x hx
  rcases x with ⟨k, σ⟩
  rw [← AList.mem_lookup_iff] at hx ⊢
  by_cases hk : k = v
  · subst hk
    simpa using hx
  · rw [AList.lookup_insert_ne hk] at hx ⊢
    exact AList.mem_lookup_iff.mpr <| h <| AList.mem_lookup_iff.mp hx

theorem TypeContext.update_mono (Γ Δ : TypeContext) {vs τs} (hlen : vs.length = τs.length := by assumption) (h : Γ.entries ⊆ Δ.entries) :
  (Γ.update vs τs).entries ⊆ (Δ.update vs τs).entries := by
  induction vs, τs, hlen using List.reverse_induction₂ with
  | nil_nil =>
    simpa [TypeContext.update] using h
  | cons_cons vₙ vs τₙ τs hlen ih =>
    simp only [TypeContext.update, List.concat_eq_append, List.length_append, List.length_cons,
      List.length_nil, zero_add, Fin.foldl_succ_last, Fin.getElem_fin, Fin.coe_cast, Fin.val_last,
      le_refl, List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero, Fin.coe_castSucc]
    conv =>
      enter [1,1,3]
      change ?foldΓ
    conv =>
      enter [2,1,3]
      change ?foldΔ
    have hfoldΓ : ?foldΓ = Γ.update vs τs hlen := by
      unfold TypeContext.update
      congr
      funext Ξ ⟨i, hi⟩
      rw [List.getElem_append_left (by simpa using hi)]
      rw [List.getElem_append_left (by simpa [hlen] using hi)]
      rfl
    have hfoldΔ : ?foldΔ = Δ.update vs τs hlen := by
      unfold TypeContext.update
      congr
      funext Ξ ⟨i, hi⟩
      rw [List.getElem_append_left hi, List.getElem_append_left (Nat.lt_of_lt_of_eq hi hlen)]
      rfl
    rw [hfoldΓ, hfoldΔ]
    exact insert_mono ih

theorem TypeContext.entries_subset_insert_of_notMem {Γ : TypeContext} {v : 𝒱} {τ : SMTType}
    (hv : v ∉ Γ) : Γ.entries ⊆ (Γ.insert v τ).entries := by
  rw [AList.entries_insert_of_notMem hv]
  intro e he
  exact List.mem_cons_of_mem _ he

open Classical in
noncomputable def TypeContext.abstract (Γ : TypeContext) {𝒯} [DecidableEq 𝒯] («Δ» : SMT.𝒱 → Option 𝒯) :
  PHOAS.TypeContext 𝒯 := fun x : 𝒯 =>
    if h : ∃ k, «Δ» k = .some x ∧ k ∈ Γ then
      Γ.lookup <| choose h
    else .none

section
set_option hygiene false
local notation:90 Γ:90 " ⊢ˢ " x " : " τ:90 => Typing Γ x τ

inductive Typing : TypeContext → Term → SMTType → Prop where
  | var (Γ : TypeContext) (v τ) :
      Γ.lookup v = some τ
    ----------------
    → Γ ⊢ˢ .var v : τ
  | int (Γ) (n : Int) : Γ ⊢ˢ .int n : .int
  | bool (Γ) (b : Bool) : Γ ⊢ˢ .bool b : .bool
  | app (Γ) (f x τ σ) :
      Γ ⊢ˢ f : .fun τ σ
    → Γ ⊢ˢ x : τ
    ------------------
    → Γ ⊢ˢ .app f x : σ
  | lambda (Γ : TypeContext) (vs : List 𝒱) (τs : List SMTType) (t : Term) (γ) :
    (∀ v ∈ vs, v ∉ Γ)
    → (fresh : ∀ v ∈ vs, v ∉ bv t)
    → (len_pos : 0 < vs.length)
    → (len_eq : vs.length = τs.length)
    → (Γ.update vs τs) ⊢ˢ t : γ
    ------------------------------
    → Γ ⊢ˢ .lambda vs τs t : (τs.dropLast.foldr (init := τs.getLast (by rwa [←List.length_pos_iff, ←len_eq])) fun τ acc ↦ τ.pair acc).fun γ
  | forall (Γ) (vs : List 𝒱) (τs : List SMTType) (P : Term) :
    (∀ v ∈ vs, v ∉ Γ)
    → (fresh : ∀ v ∈ vs, v ∉ bv P)
    → (len_pos : 0 < vs.length)
    → (len_eq : vs.length = τs.length)
    → (Γ.update vs τs) ⊢ˢ P : .bool
    ------------------------------
    → Γ ⊢ˢ .forall vs τs P : .bool
  | exists (Γ) (vs : List 𝒱) (τs : List SMTType) (P : Term) :
    (∀ v ∈ vs, v ∉ Γ)
    → (fresh : ∀ v ∈ vs, v ∉ bv P)
    → (len_pos : 0 < vs.length)
    → (len_eq : vs.length = τs.length)
    → (Γ.update vs τs) ⊢ˢ P : .bool
    ------------------------------
    → Γ ⊢ˢ .exists vs τs P : .bool
  | eq (Γ) (t₁ t₂ τ) :
      Γ ⊢ˢ t₁ : τ
    → Γ ⊢ˢ t₂ : τ
    -----------------------
    → Γ ⊢ˢ .eq t₁ t₂ : .bool
  | and (Γ) (t₁ t₂) :
      Γ ⊢ˢ t₁ : .bool
    → Γ ⊢ˢ t₂ : .bool
    ------------------------
    → Γ ⊢ˢ .and t₁ t₂ : .bool
  | or (Γ) (t₁ t₂) :
      Γ ⊢ˢ t₁ : .bool
    → Γ ⊢ˢ t₂ : .bool
    -----------------------
    → Γ ⊢ˢ .or t₁ t₂ : .bool
  | not (Γ) (t) :
      Γ ⊢ˢ t : .bool
    --------------------
    → Γ ⊢ˢ .not t : .bool
  | imp (Γ) (t₁ t₂) :
      Γ ⊢ˢ t₁ : .bool
    → Γ ⊢ˢ t₂ : .bool
    ------------------------
    → Γ ⊢ˢ .imp t₁ t₂ : .bool
  | ite (Γ) (c t e τ) :
      Γ ⊢ˢ c : .bool
    → Γ ⊢ˢ t : τ
    → Γ ⊢ˢ e : τ
    --------------------
    → Γ ⊢ˢ .ite c t e : τ
  | some (Γ) (t τ) :
      Γ ⊢ˢ t : τ
    -----------------
    → Γ ⊢ˢ .some t : .option τ
  | none (Γ τ) : Γ ⊢ˢ .as .none (.option τ) : .option τ
  | the (Γ) (t τ) :
      Γ ⊢ˢ t : .option τ
    -----------------
    → Γ ⊢ˢ .the t : τ
  | pair (Γ) (t₁ τ₁ t₂ τ₂) :
      Γ ⊢ˢ t₁ : τ₁
    → Γ ⊢ˢ t₂ : τ₂
    -----------------------
    → Γ ⊢ˢ .pair t₁ t₂ : .pair τ₁ τ₂
  | fst (Γ) (t τ σ) :
      Γ ⊢ˢ t : .pair τ σ
    -------------------
    → Γ ⊢ˢ .fst t : τ
  | snd (Γ) (t τ σ) :
      Γ ⊢ˢ t : .pair τ σ
    -------------------
    → Γ ⊢ˢ .snd t : σ
  | distinct (Γ) (ts : List Term) (τ) :
      (∀ t ∈ ts, Γ ⊢ˢ t : τ)
    -------------------------
    → Γ ⊢ˢ .distinct ts : .bool
  | le (Γ) (t₁ t₂) :
      Γ ⊢ˢ t₁ : .int
    → Γ ⊢ˢ t₂ : .int
    -----------------------
    → Γ ⊢ˢ .le t₁ t₂ : .bool
  | add (Γ) (t₁ t₂) :
      Γ ⊢ˢ t₁ : .int
    → Γ ⊢ˢ t₂ : .int
    ------------------------
    → Γ ⊢ˢ .add t₁ t₂ : .int
  | sub (Γ) (t₁ t₂) :
      Γ ⊢ˢ t₁ : .int
    → Γ ⊢ˢ t₂ : .int
    ------------------------
    → Γ ⊢ˢ .sub t₁ t₂ : .int
  | mul (Γ) (t₁ t₂) :
      Γ ⊢ˢ t₁ : .int
    → Γ ⊢ˢ t₂ : .int
    ------------------------
    → Γ ⊢ˢ .mul t₁ t₂ : .int
end

notation:90 Γ:90 " ⊢ˢ " x " : " τ:90 => Typing Γ x τ


namespace Typing
section RuleInversion

theorem varE      {Γ : TypeContext} {v τ} : Γ ⊢ˢ .var v : τ → Γ.lookup v = .some τ := λ | var _ _ _ h => h
theorem intE      {Γ : TypeContext} {n τ} : Γ ⊢ˢ .int n : τ → τ = .int := λ | int _ _ => rfl
theorem boolE     {Γ : TypeContext} {b τ} : Γ ⊢ˢ .bool b : τ → τ = .bool := λ | bool _ _ => rfl
theorem appE      {Γ : TypeContext} {f x σ} : Γ ⊢ˢ .app f x : σ → ∃ τ, Γ ⊢ˢ f : .fun τ σ ∧ Γ ⊢ˢ x : τ := λ | app _ _ _ _ _ h₁ h₂ => ⟨_, h₁, h₂⟩
theorem eqE       {Γ : TypeContext} {x y τ} : Γ ⊢ˢ .eq x y : τ → τ = .bool ∧ ∃ σ, Γ ⊢ˢ x : σ ∧ Γ ⊢ˢ y : σ := λ | eq _ _ _ _ hx hy => ⟨rfl, _, hx, hy⟩
theorem andE      {Γ : TypeContext} {x y τ} : Γ ⊢ˢ .and x y : τ → τ = .bool ∧ Γ ⊢ˢ x : .bool ∧ Γ ⊢ˢ y : .bool := λ | and _ _ _ hx hy => ⟨rfl, hx, hy⟩
theorem orE       {Γ : TypeContext} {x y τ} : Γ ⊢ˢ .or x y : τ → τ = .bool ∧ Γ ⊢ˢ x : .bool ∧ Γ ⊢ˢ y : .bool := λ | or _ _ _ hx hy => ⟨rfl, hx, hy⟩
theorem impE      {Γ : TypeContext} {x y τ} : Γ ⊢ˢ .imp x y : τ → τ = .bool ∧ Γ ⊢ˢ x : .bool ∧ Γ ⊢ˢ y : .bool := λ | imp _ _ _ hx hy => ⟨rfl, hx, hy⟩
theorem notE      {Γ : TypeContext} {x τ} : Γ ⊢ˢ .not x : τ → τ = .bool ∧ Γ ⊢ˢ x : .bool := λ | not _ _ h => ⟨rfl, h⟩
theorem iteE      {Γ : TypeContext} {c t f τ} : Γ ⊢ˢ .ite c t f : τ → Γ ⊢ˢ c : .bool ∧ Γ ⊢ˢ t : τ ∧ Γ ⊢ˢ f : τ := λ | ite _ _ _ _ _ hc ht hf => ⟨hc,ht,hf⟩
theorem someE     {Γ : TypeContext} {t τ} : Γ ⊢ˢ .some t : τ → ∃ σ, τ = .option σ ∧ Γ ⊢ˢ t : σ := λ | some _ _ _ h => ⟨_, rfl, h⟩
theorem theE      {Γ : TypeContext} {t τ} : Γ ⊢ˢ .the t : τ → Γ ⊢ˢ t : τ.option := λ | the _ _ _ ht => ht
theorem asE       {Γ : TypeContext} {t ξ τ} : Γ ⊢ˢ .as t ξ : τ → t = .none ∧ ξ = τ ∧ ∃ ζ, τ = .option ζ := λ | .none .. => ⟨rfl, rfl, _, rfl⟩
theorem noneE     {Γ : TypeContext} {τ} : ¬ Γ ⊢ˢ .none : τ := by rintro ⟨⟩
theorem pairE     {Γ : TypeContext} {x y τ} : Γ ⊢ˢ .pair x y : τ → ∃ α β, τ = .pair α β ∧ Γ ⊢ˢ x : α ∧ Γ ⊢ˢ y : β := λ | pair _ _ _ _ _ hx hy => ⟨_,_,rfl,hx,hy⟩
theorem fstE      {Γ : TypeContext} {x τ} : Γ ⊢ˢ .fst x : τ → ∃ σ, Γ ⊢ˢ x : .pair τ σ := λ | fst _ _ _ _ hx => ⟨_,hx⟩
theorem sndE      {Γ : TypeContext} {x τ} : Γ ⊢ˢ .snd x : τ → ∃ σ, Γ ⊢ˢ x : .pair σ τ := λ | snd _ _ _ _ hx => ⟨_,hx⟩
theorem distinctE {Γ : TypeContext} {xs : List Term} {τ} : Γ ⊢ˢ .distinct xs : τ → τ = .bool ∧ ∃ σ, ∀ x ∈ xs, Γ ⊢ˢ x : σ := λ | distinct _ _ σ h => ⟨rfl, σ, h⟩
theorem leE       {Γ : TypeContext} {x y τ} : Γ ⊢ˢ .le x y : τ → τ = .bool ∧ Γ ⊢ˢ x : .int ∧ Γ ⊢ˢ y : .int := λ | le _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem addE      {Γ : TypeContext} {x y τ} : Γ ⊢ˢ .add x y : τ → τ = .int ∧ Γ ⊢ˢ x : .int ∧ Γ ⊢ˢ y : .int := λ | add _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem subE      {Γ : TypeContext} {x y τ} : Γ ⊢ˢ .sub x y : τ → τ = .int ∧ Γ ⊢ˢ x : .int ∧ Γ ⊢ˢ y : .int := λ | sub _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem mulE      {Γ : TypeContext} {x y τ} : Γ ⊢ˢ .mul x y : τ → τ = .int ∧ Γ ⊢ˢ x : .int ∧ Γ ⊢ˢ y : .int := λ | mul _ _ _ hx hy => ⟨rfl,hx,hy⟩
theorem lambdaE   {Γ : TypeContext} {vs : List 𝒱} {τs : List SMTType} {t : Term} {τ} (h : Γ ⊢ˢ .lambda vs τs t : τ) :
  ∃ (len_pos : 0 < vs.length) (len_eq : vs.length = τs.length) (γ : SMTType),
    (∀ v ∈ vs, v ∉ Γ) ∧ (∀ v ∈ vs, v ∉ bv t) ∧ τ = (τs.dropLast.foldr (init := τs.getLast (by rwa [←List.length_pos_iff, ←len_eq])) fun τ acc ↦ τ.pair acc).fun γ ∧ (Γ.update vs τs) ⊢ˢ t : γ := by
  obtain ⟨⟩ := h
  exists ‹_›, ‹_›, ‹_›
theorem forallE   {Γ : TypeContext} {vs : List 𝒱} {τs : List SMTType} {P : Term} {τ} (h : Γ ⊢ˢ .forall vs τs P : τ) :
  τ = .bool ∧ (∀ v ∈ vs, v ∉ Γ) ∧ (∀ v ∈ vs, v ∉ bv P) ∧ ∃ (_ : 0 < vs.length) (len_eq : vs.length = τs.length), Γ.update vs τs ⊢ˢ P : .bool := by
    obtain ⟨⟩ := h
    apply And.intro rfl
    apply And.intro ‹_›
    apply And.intro ‹_›
    exists ‹_›, ‹_›
theorem existsE   {Γ : TypeContext} {vs : List 𝒱} {τs : List SMTType} {P : Term} {τ} (h : Γ ⊢ˢ .exists vs τs P : τ) :
  τ = .bool ∧ (∀ v ∈ vs, v ∉ Γ) ∧ (∀ v ∈ vs, v ∉ bv P) ∧ ∃ (_ : 0 < vs.length) (len_eq : vs.length = τs.length), Γ.update vs τs ⊢ˢ P : .bool := by
    obtain ⟨⟩ := h
    apply And.intro rfl
    apply And.intro ‹_›
    apply And.intro ‹_›
    exists ‹_›, ‹_›

end RuleInversion

theorem weakening {Γ Δ : TypeContext} (h : Γ.entries ⊆ Δ.entries) {t : Term} {τ : SMTType}
  (typ : Γ ⊢ˢ t : τ) : Δ ⊢ˢ t : τ := by
  induction typ generalizing Δ with
  | var Γ v τ hv =>
    apply var Δ v τ
    specialize h (AList.mem_lookup_iff.mp hv)
    rwa [←AList.mem_lookup_iff] at h
  | int Γ n => exact int Δ n
  | bool Γ b => exact bool Δ b
  | app Γ f x τ σ typ_f typ_x f_ih x_ih =>
    apply app Δ f x τ σ
    · exact f_ih h
    · exact x_ih h
  | eq Γ t₁ t₂ τ typ₁ typ₂ ih₁ ih₂ =>
    apply eq Δ t₁ t₂ τ
    · exact ih₁ h
    · exact ih₂ h
  | and Γ t₁ t₂ typ₁ typ₂ ih₁ ih₂ =>
    apply and Δ t₁ t₂
    · exact ih₁ h
    · exact ih₂ h
  | or Γ t₁ t₂ typ₁ typ₂ ih₁ ih₂ =>
    apply or Δ t₁ t₂
    · exact ih₁ h
    · exact ih₂ h
  | not Γ t typ ih =>
    apply not Δ t
    exact ih h
  | imp Γ t₁ t₂ typ₁ typ₂ ih₁ ih₂ =>
    apply imp Δ t₁ t₂
    · exact ih₁ h
    · exact ih₂ h
  | ite Γ c t e τ typ_c typ_t typ_e ih_c ih_t ih_e =>
    apply ite Δ c t e τ
    · exact ih_c h
    · exact ih_t h
    · exact ih_e h
  | some Γ t τ typ ih =>
    apply some Δ t τ
    exact ih h
  | none Γ τ => apply none Δ τ
  | the Γ t τ typ ih =>
    apply the Δ t τ
    exact ih h
  | pair Γ t₁ τ₁ t₂ τ₂ typ₁ typ₂ ih₁ ih₂ =>
    apply pair Δ t₁ τ₁ t₂ τ₂
    · exact ih₁ h
    · exact ih₂ h
  | fst Γ t τ σ typ ih =>
    apply fst Δ t τ σ
    exact ih h
  | snd Γ t τ σ typ ih =>
    apply snd Δ t τ σ
    exact ih h
  | distinct Γ ts τ typ ih =>
    apply distinct Δ ts τ
    intro t ht
    exact ih t ht h
  | le Γ t₁ t₂ typ₁ typ₂ ih₁ ih₂ =>
    apply le Δ t₁ t₂
    · exact ih₁ h
    · exact ih₂ h
  | add Γ t₁ t₂ typ₁ typ₂ ih₁ ih₂ =>
    apply add Δ t₁ t₂
    · exact ih₁ h
    · exact ih₂ h
  | sub Γ t₁ t₂ typ₁ typ₂ ih₁ ih₂ =>
    apply sub Δ t₁ t₂
    · exact ih₁ h
    · exact ih₂ h
  | mul Γ t₁ t₂ typ₁ typ₂ ih₁ ih₂ =>
    apply mul Δ t₁ t₂
    · exact ih₁ h
    · exact ih₂ h
  | lambda Γ vs τs t γ vs_Γ vs_fresh len_pos len_eq ih₁ ih₂ =>
    apply lambda Δ vs τs t γ _ vs_fresh len_pos len_eq
    apply ih₂ (TypeContext.update_mono Γ Δ len_eq h)
    admit
  | «forall» Γ vs τs P typ vs_fresh len_pos len_eq h₁ h₂ =>
    apply «forall» Δ vs τs P _ vs_fresh len_pos len_eq
    apply h₂ (TypeContext.update_mono Γ Δ len_eq h)
    admit
  | «exists» Γ vs τs P typ vs_fresh len_pos len_eq h₁ h₂ =>
    apply «exists» Δ vs τs P _ vs_fresh len_pos len_eq
    apply h₂ (TypeContext.update_mono Γ Δ len_eq h)
    admit

theorem bv_disjoint {Γ : TypeContext} {t : Term} {τ : SMTType} (h : Γ ⊢ˢ t : τ) : (bv t).Disjoint Γ.keys := by
  induction h with
  | var Γ | int Γ | bool Γ =>
    rw [bv]
    exact List.disjoint_nil_left Γ.keys
  | app Γ f x τ σ _ _ ihf ihx =>
    rw [bv, List.disjoint_append_left]
    exact ⟨ihf, ihx⟩
  | lambda Γ vs τs t γ vs_Γ _ _ len_eq _ ih =>
    have hvs : vs.Disjoint Γ.keys := by
      rw [List.disjoint_left]
      intro v hv_vs hv_Γ
      exact vs_Γ v hv_vs ((AList.mem_keys).mpr hv_Γ)
    have hbody : (bv t).Disjoint Γ.keys := by
      rw [List.disjoint_left] at ih ⊢
      intro v hv_bv hv_Γ
      apply ih hv_bv
      apply (AList.mem_keys).mp
      rw [TypeContext.mem_update_iff (hlen := len_eq)]
      exact Or.inr ((AList.mem_keys).mpr hv_Γ)
    rw [bv, List.disjoint_append_left]
    exact ⟨vs_Γ, hbody⟩
  | «forall» Γ vs τs P vs_Γ _ _ len_eq _ ih =>
    have hvs : vs.Disjoint Γ.keys := by
      rw [List.disjoint_left]
      intro v hv_vs hv_Γ
      exact vs_Γ v hv_vs ((AList.mem_keys).mpr hv_Γ)
    have hbody : (bv P).Disjoint Γ.keys := by
      rw [List.disjoint_left] at ih ⊢
      intro v hv_bv hv_Γ
      apply ih hv_bv
      apply (AList.mem_keys).mp
      rw [TypeContext.mem_update_iff (hlen := len_eq)]
      exact Or.inr ((AList.mem_keys).mpr hv_Γ)
    rw [bv, List.disjoint_append_left]
    exact ⟨hvs, hbody⟩
  | «exists» Γ vs τs P vs_Γ _ _ len_eq _ ih =>
    have hvs : vs.Disjoint Γ.keys := by
      rw [List.disjoint_left]
      intro v hv_vs hv_Γ
      exact vs_Γ v hv_vs ((AList.mem_keys).mpr hv_Γ)
    have hbody : (bv P).Disjoint Γ.keys := by
      rw [List.disjoint_left] at ih ⊢
      intro v hv_bv hv_Γ
      apply ih hv_bv
      apply (AList.mem_keys).mp
      rw [TypeContext.mem_update_iff (hlen := len_eq)]
      exact Or.inr ((AList.mem_keys).mpr hv_Γ)
    rw [bv, List.disjoint_append_left]
    exact ⟨hvs, hbody⟩
  | eq Γ t₁ t₂ τ _ _ ih₁ ih₂
  | and Γ t₁ t₂ _ _ ih₁ ih₂
  | or Γ t₁ t₂ _ _ ih₁ ih₂
  | pair Γ t₁ τ₁ t₂ τ₂ _ _ ih₁ ih₂
  | le Γ t₁ t₂ _ _ ih₁ ih₂
  | add Γ t₁ t₂ _ _ ih₁ ih₂
  | sub Γ t₁ t₂ _ _ ih₁ ih₂
  | mul Γ t₁ t₂ _ _ ih₁ ih₂
  | imp Γ t₁ t₂ _ _ ih₁ ih₂ =>
    rw [bv, List.disjoint_append_left]
    exact ⟨ih₁, ih₂⟩
  | not Γ t _ ih => rwa [bv]
  | ite Γ c t e τ _ _ _ ihc iht ihe =>
    rw [bv, List.disjoint_append_left, List.disjoint_append_left, and_assoc]
    exact ⟨ihc, iht, ihe⟩
  | some Γ t τ _ ih => rwa [bv]
  | none Γ τ =>
    rw [bv, bv]
    exact List.disjoint_nil_left Γ.keys
  | the Γ t τ _ ih =>
    rwa [bv]
  | fst Γ t τ σ _ ih
  | snd Γ t τ σ _ ih => rwa [bv]
  | distinct Γ ts τ _ ih =>
    rw [List.disjoint_left]
    intro v hv hk
    rw [bv] at hv
    rcases List.mem_flatten.mp hv with ⟨l, hl, hvl⟩
    rcases List.mem_map.mp hl with ⟨t, _, rfl⟩
    exact ih t.1 t.2 hvl hk

theorem bv_notMem_context {Γ : TypeContext} {t : Term} {τ : SMTType}
  (h : Γ ⊢ˢ t : τ) : ∀ v ∈ bv t, v ∉ Γ := fun _ hv hvΓ ↦
    List.disjoint_left.mp (bv_disjoint h) hv (AList.mem_keys.mpr hvΓ)

theorem bv_notMem_insert_of_fresh {Γ : TypeContext} {t : Term} {τ ξ : SMTType} {x : 𝒱}
    (h : Γ ⊢ˢ t : τ) (hx : x ∉ bv t) :
    ∀ v ∈ bv t, v ∉ Γ.insert x ξ := by
  intro v hv hvins
  rcases (AList.mem_insert (s := Γ) (a := v) (a' := x) (b' := ξ)).1 hvins with rfl | hvΓ
  · exact hx hv
  · exact (bv_notMem_context h v hv) hvΓ

theorem bv_notMem_of_subset {Γ₁ Γ₂ : SMT.TypeContext} {t : SMT.Term} {τ : SMTType}
  (hsub : Γ₁.keys ⊆ Γ₂.keys) (typ_t : Γ₂ ⊢ˢ t : τ) :
  ∀ v ∈ SMT.bv t, v ∉ Γ₁ :=
    fun v hv hvin => Typing.bv_notMem_context typ_t v hv (hsub hvin)

theorem strengthening_of_fv_subset
  {Γ₁ Γ₂ : SMT.TypeContext} {t : SMT.Term} {τ : SMTType}
  (hsub : Γ₁.entries ⊆ Γ₂.entries)
  (ht : Γ₂ ⊢ˢ t : τ)
  (hfv : ∀ v ∈ SMT.fv t, v ∈ Γ₁) :
  Γ₁ ⊢ˢ t : τ := by
  induction ht generalizing Γ₁ with
  | var Γ₂ v τ hlookup =>
    apply SMT.Typing.var
    have hvΓ₁ : v ∈ Γ₁ := hfv v (by simp [SMT.fv])
    obtain ⟨τv, hlookup₁⟩ := Option.isSome_iff_exists.mp ((AList.lookup_isSome).2 hvΓ₁)
    have hlookup₂ := (AList.mem_lookup_iff).2 (hsub ((AList.mem_lookup_iff).1 hlookup₁))
    rw [hlookup] at hlookup₂
    injection hlookup₂ with hτ
    simpa [hτ] using hlookup₁
  | int Γ₂ n =>
    exact SMT.Typing.int Γ₁ n
  | bool Γ₂ b =>
    exact SMT.Typing.bool Γ₁ b
  | app Γ₂ f x τ σ typ_f typ_x ih_f ih_x =>
    apply SMT.Typing.app Γ₁ f x τ σ
    · apply ih_f hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inl hv))
    · apply ih_x hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inr hv))
  | lambda Γ₂ vs τs t γ vs_Γ fresh len_pos len_eq typ_t ih =>
    refine SMT.Typing.lambda Γ₁ vs τs t γ ?_ ?_ ?_ ?_ ?_
    · intro v hvvs hvΓ₁
      obtain ⟨τv, hlookup₁⟩ := Option.isSome_iff_exists.mp ((AList.lookup_isSome).2 hvΓ₁)
      have hlookup₂ := (AList.mem_lookup_iff).2 (hsub ((AList.mem_lookup_iff).1 hlookup₁))
      have hvΓ₂ : v ∈ Γ₂ := (AList.lookup_isSome).1 (Option.isSome_of_eq_some hlookup₂)
      exact vs_Γ v hvvs hvΓ₂
    · exact fresh
    · exact len_pos
    · exact len_eq
    · apply ih (Γ₁ := Γ₁.update vs τs)
      · exact SMT.TypeContext.update_mono Γ₁ Γ₂ len_eq hsub
      · intro v hv
        by_cases hvvs : v ∈ vs
        · rw [SMT.TypeContext.mem_update_iff (Γ := Γ₁) (v := v) (vs := vs) (τs := τs) (hlen := len_eq)]
          exact Or.inl hvvs
        · rw [SMT.TypeContext.mem_update_iff (Γ := Γ₁) (v := v) (vs := vs) (τs := τs) (hlen := len_eq)]
          exact Or.inr (hfv v (SMT.fv.mem_lambda ⟨hv, hvvs⟩))
  | «forall» Γ₂ vs τs P vs_Γ fresh len_pos len_eq typ_P ih =>
    refine SMT.Typing.forall Γ₁ vs τs P ?_ ?_ ?_ ?_ ?_
    · intro v hvvs hvΓ₁
      obtain ⟨τv, hlookup₁⟩ := Option.isSome_iff_exists.mp ((AList.lookup_isSome).2 hvΓ₁)
      have hlookup₂ := (AList.mem_lookup_iff).2 (hsub ((AList.mem_lookup_iff).1 hlookup₁))
      have hvΓ₂ : v ∈ Γ₂ := (AList.lookup_isSome).1 (Option.isSome_of_eq_some hlookup₂)
      exact vs_Γ v hvvs hvΓ₂
    · exact fresh
    · exact len_pos
    · exact len_eq
    · apply ih (Γ₁ := Γ₁.update vs τs)
      · exact SMT.TypeContext.update_mono Γ₁ Γ₂ len_eq hsub
      · intro v hv
        by_cases hvvs : v ∈ vs
        · rw [SMT.TypeContext.mem_update_iff (Γ := Γ₁) (v := v) (vs := vs) (τs := τs) (hlen := len_eq)]
          exact Or.inl hvvs
        · rw [SMT.TypeContext.mem_update_iff (Γ := Γ₁) (v := v) (vs := vs) (τs := τs) (hlen := len_eq)]
          exact Or.inr (hfv v (SMT.fv.mem_forall ⟨hv, hvvs⟩))
  | «exists» Γ₂ vs τs P vs_Γ fresh len_pos len_eq typ_P ih =>
    refine SMT.Typing.exists Γ₁ vs τs P ?_ ?_ ?_ ?_ ?_
    · intro v hvvs hvΓ₁
      obtain ⟨τv, hlookup₁⟩ := Option.isSome_iff_exists.mp ((AList.lookup_isSome).2 hvΓ₁)
      have hlookup₂ := (AList.mem_lookup_iff).2 (hsub ((AList.mem_lookup_iff).1 hlookup₁))
      have hvΓ₂ : v ∈ Γ₂ := (AList.lookup_isSome).1 (Option.isSome_of_eq_some hlookup₂)
      exact vs_Γ v hvvs hvΓ₂
    · exact fresh
    · exact len_pos
    · exact len_eq
    · apply ih (Γ₁ := Γ₁.update vs τs)
      · exact SMT.TypeContext.update_mono Γ₁ Γ₂ len_eq hsub
      · intro v hv
        by_cases hvvs : v ∈ vs
        · rw [SMT.TypeContext.mem_update_iff (Γ := Γ₁) (v := v) (vs := vs) (τs := τs) (hlen := len_eq)]
          exact Or.inl hvvs
        · rw [SMT.TypeContext.mem_update_iff (Γ := Γ₁) (v := v) (vs := vs) (τs := τs) (hlen := len_eq)]
          exact Or.inr (hfv v (SMT.fv.mem_exists ⟨hv, hvvs⟩))
  | eq Γ₂ t₁ t₂ σ typ₁ typ₂ ih₁ ih₂ =>
    apply SMT.Typing.eq Γ₁ t₁ t₂ σ
    · apply ih₁ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inl hv))
    · apply ih₂ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inr hv))
  | and Γ₂ t₁ t₂ typ₁ typ₂ ih₁ ih₂ =>
    apply SMT.Typing.and Γ₁ t₁ t₂
    · apply ih₁ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inl hv))
    · apply ih₂ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inr hv))
  | or Γ₂ t₁ t₂ typ₁ typ₂ ih₁ ih₂ =>
    apply SMT.Typing.or Γ₁ t₁ t₂
    · apply ih₁ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inl hv))
    · apply ih₂ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inr hv))
  | not Γ₂ t typ ih =>
    apply SMT.Typing.not Γ₁ t
    apply ih hsub
    intro v hv
    exact hfv v (by simpa [SMT.fv] using hv)
  | imp Γ₂ t₁ t₂ typ₁ typ₂ ih₁ ih₂ =>
    apply SMT.Typing.imp Γ₁ t₁ t₂
    · apply ih₁ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inl hv))
    · apply ih₂ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inr hv))
  | ite Γ₂ c t e τ typ_c typ_t typ_e ih_c ih_t ih_e =>
    apply SMT.Typing.ite Γ₁ c t e τ
    · apply ih_c hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append, or_assoc] using (Or.inl hv))
    · apply ih_t hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append, or_assoc] using (Or.inr (Or.inl hv)))
    · apply ih_e hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append, or_assoc] using (Or.inr (Or.inr hv)))
  | some Γ₂ t σ typ ih =>
    apply SMT.Typing.some Γ₁ t σ
    apply ih hsub
    intro v hv
    exact hfv v (by simpa [SMT.fv] using hv)
  | none Γ₂ τ =>
    exact SMT.Typing.none Γ₁ τ
  | the Γ₂ t σ typ ih =>
    apply SMT.Typing.the Γ₁ t σ
    apply ih hsub
    intro v hv
    exact hfv v (by simpa [SMT.fv] using hv)
  | pair Γ₂ t₁ τ₁ t₂ τ₂ typ₁ typ₂ ih₁ ih₂ =>
    apply SMT.Typing.pair Γ₁ t₁ τ₁ t₂ τ₂
    · apply ih₁ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inl hv))
    · apply ih₂ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inr hv))
  | fst Γ₂ t τ σ typ ih =>
    apply SMT.Typing.fst Γ₁ t τ σ
    apply ih hsub
    intro v hv
    exact hfv v (by simpa [SMT.fv] using hv)
  | snd Γ₂ t τ σ typ ih =>
    apply SMT.Typing.snd Γ₁ t τ σ
    apply ih hsub
    intro v hv
    exact hfv v (by simpa [SMT.fv] using hv)
  | distinct Γ₂ ts σ typ_ts ih =>
    apply SMT.Typing.distinct Γ₁ ts σ
    intro t ht
    apply ih t ht hsub
    intro v hv
    exact hfv v (by
      rw [SMT.fv]
      apply List.mem_flatten.mpr
      refine ⟨SMT.fv t, ?_, hv⟩
      apply List.mem_map.mpr
      exact ⟨⟨t, ht⟩, by simp, rfl⟩)
  | le Γ₂ t₁ t₂ typ₁ typ₂ ih₁ ih₂ =>
    apply SMT.Typing.le Γ₁ t₁ t₂
    · apply ih₁ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inl hv))
    · apply ih₂ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inr hv))
  | add Γ₂ t₁ t₂ typ₁ typ₂ ih₁ ih₂ =>
    apply SMT.Typing.add Γ₁ t₁ t₂
    · apply ih₁ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inl hv))
    · apply ih₂ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inr hv))
  | sub Γ₂ t₁ t₂ typ₁ typ₂ ih₁ ih₂ =>
    apply SMT.Typing.sub Γ₁ t₁ t₂
    · apply ih₁ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inl hv))
    · apply ih₂ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inr hv))
  | mul Γ₂ t₁ t₂ typ₁ typ₂ ih₁ ih₂ =>
    apply SMT.Typing.mul Γ₁ t₁ t₂
    · apply ih₁ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inl hv))
    · apply ih₂ hsub
      intro v hv
      exact hfv v (by simpa [SMT.fv, List.mem_append] using (Or.inr hv))

end Typing
