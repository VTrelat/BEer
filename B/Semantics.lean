import B.Typing
import ZFC.Basic
import LeanSearchClient
import Mathlib.Tactic.ExtractGoal
noncomputable section

namespace B

def BType.toZFSet : BType → ZFSet
  | .int => .Int
  | .bool => .𝔹
  | .set α => .powerset α.toZFSet
  | .prod α β => .prod α.toZFSet β.toZFSet

lemma ZFSet.Int.nonempty : ZFSet.Int ≠ ∅ := by
  intro h
  rw [ZFSet.ext_iff] at h
  simp only [ZFSet.not_mem_empty, iff_false] at h
  nomatch h (ZFSet.ofInt 0) (ZFSet.mem_ofInt_Int 0)

lemma ZFSet.𝔹.nonempty : ZFSet.𝔹 ≠ ∅ := by
  intro h
  rw [ZFSet.ext_iff] at h
  simp only [ZFSet.not_mem_empty, iff_false] at h
  nomatch h ZFSet.zffalse (ZFSet.ZFBool.zffalse_mem_𝔹)

lemma ZFSet.powerset.nonempty {x} : ZFSet.powerset x ≠ ∅ := by
  intro h
  rw [ZFSet.ext_iff] at h
  simp only [ZFSet.not_mem_empty, iff_false] at h
  nomatch h x <| (@ZFSet.mem_powerset x x).mpr fun x => id

lemma ZFSet.prod.nonempty {x y} : x ≠ ∅ → y ≠ ∅ → ZFSet.prod x y ≠ ∅ := by classical
  intro hx hy h'
  simp only [ZFSet.ext_iff, ZFSet.mem_prod, ZFSet.not_mem_empty, iff_false, not_exists, not_and, not_forall] at h'
  obtain ⟨a, ha⟩ := ZFSet.nonempty_exists_iff.mp hx
  obtain ⟨b, hb⟩ := ZFSet.nonempty_exists_iff.mp hy
  obtain ⟨_, h'⟩ := h' (a.pair b) _ ha _ hb
  exact h' (Eq.to_iff rfl)

theorem BType.toZFSet_nonempty {α : BType} : (α : BType).toZFSet ≠ ∅ := by
  induction α <;> apply_rules [
    ZFSet.Int.nonempty,
    ZFSet.𝔹.nonempty,
    ZFSet.powerset.nonempty,
    ZFSet.prod.nonempty
  ]

abbrev WellTyped (t : Term) := Σ' Γ τ, Γ ⊢ t : τ

section
set_option hygiene false

local notation "⟦" t "⟧ᴮ" => denote t


notation "⟰" => ZFSet.instEquivZFIntInt.toFun
notation "⟱" => ZFSet.instEquivZFIntInt.invFun

@[simp] theorem ZFSet.int_equiv_right_simp {x} : ⟰ (⟱ x) = x := ZFSet.instEquivZFIntInt.right_inv x
@[simp] theorem ZFSet.int_equiv_left_simp  {x} : ⟱ (⟰ x) = x := ZFSet.instEquivZFIntInt.left_inv x

scoped[Classical] attribute [instance high] Classical.allZFSetDefinable -- what a trick!

open Classical Function in
def overloadBinOp
  {α β : Sort _}
  {A B : ZFSet}
  («↓» : { x // x ∈ A } → α)
  («↑» : β → {x // x ∈ B})
  (default : β)
  (op : α → α → β)
  (x y : ZFSet) : ZFSet :=
  «↑» <| if h : x ∈ A ∧ y ∈ A then (op on «↓») ⟨x, h.1⟩ ⟨y, h.2⟩ else default

open Classical in
def overloadUnaryOp {α β : Sort _} {A B : ZFSet} («↓» : { x // x ∈ A } → α) («↑» : β → {x // x ∈ B}) (default : β) (op : α → β) (x : ZFSet) : ZFSet :=
  «↑» <| if h : x ∈ A then op («↓» ⟨x, h⟩) else default

def overloadBinOp_Int (op : ZFSet.ZFInt → ZFSet.ZFInt → ZFSet.ZFInt) (x y : ZFSet) : ZFSet := overloadBinOp (⟱ ·) (⟰ ·) 0 op x y
infixl:65 " +ᶻ " => overloadBinOp ⟱ ⟰ 0 (· + ·)
infixl:65 " -ᶻ " => overloadBinOp ⟱ ⟰ 0 (· - ·)
infixl:65 " *ᶻ " => overloadBinOp ⟱ ⟰ 0 (· * ·)
open Classical in infixl:65 " ≤ᶻ " => overloadBinOp ⟱ (λ p => if p then (⊤ : ZFSet.ZFBool) else (⊥ : ZFSet.ZFBool)) ⊥ (· ≤ ·)
open Classical in infixl:65 " <ᶻ " => overloadBinOp ⟱ (λ p => if p then (⊤ : ZFSet.ZFBool) else (⊥ : ZFSet.ZFBool)) ⊥ (· < ·)
open Classical in infixl:65 " =ᶻ " => overloadBinOp (·.val) (λ p => if p then ZFSet.ZFBool.true else ZFSet.ZFBool.false) ⊥ (· = ·)
open Classical in infixl:65 " ∈ᶻ " => λ X T => overloadUnaryOp (A := T) (B := ZFSet.𝔹) («↓» := (·.val)) («↑» := λ p => if p then ⊤ else ⊥) (default := ⊥) (· ∈ T) X

def overloadBinOp_𝔹 (op : ZFSet.ZFBool → ZFSet.ZFBool → ZFSet.ZFBool) (x y : ZFSet) : ZFSet := overloadBinOp id id ZFSet.ZFBool.false op x y
infixl:65 " ⋀ᶻ " => overloadBinOp id id ZFSet.ZFBool.false (· ⋀ ·)
infixl:65 " ⋁ᶻ " => overloadBinOp id id ZFSet.ZFBool.false (· ⋁ ·)

prefix:90 " ¬ᶻ " => overloadUnaryOp id id ZFSet.ZFBool.false ZFSet.ZFBool.not

@[simp]
theorem overloaded_add_unfold {x y : ZFSet} (hx : x ∈ ZFSet.Int) (hy : y ∈ ZFSet.Int) : x +ᶻ y = ⟰ (⟱ ⟨x, hx⟩ + ⟱ ⟨y, hy⟩) := by
  unfold overloadBinOp
  rw [dif_pos ⟨hx, hy⟩]

theorem overloaded_add_comm {x y : ZFSet} : x +ᶻ y = y +ᶻ x := by
  unfold overloadBinOp
  split_ifs with h₁ h₂ h₂
  · rw [Function.onFun, ZFSet.ZFInt.add_comm]
  · nomatch h₂ h₁.symm
  · nomatch h₁ h₂.symm
  · rfl

theorem overloadBinOp_mem {α β : Sort _} {x y A B : ZFSet} (hx : x ∈ A) (hy : y ∈ A) {op : α → α → β} {«↓» : {x // x ∈ A} → α} {«↑» : β → {x // x ∈ B}} {d : β} :
  overloadBinOp «↓» «↑» d op x y ∈ B := by
  unfold overloadBinOp
  rw [dif_pos ⟨hx, hy⟩]
  apply Subtype.property

theorem overloadUnaryOp_false_eq_default {α β : Sort _} {x A B : ZFSet} (hx : x ∉ A) {op : α → β} {«↓» : {x // x ∈ A} → α} {«↑» : β → {x // x ∈ B}} {d : β} :
  overloadUnaryOp «↓» «↑» d op x = «↑» d := by
  unfold overloadUnaryOp
  rw [dif_neg hx]

theorem overloadUnaryOp_mem {α β : Sort _} {x A B : ZFSet} {op : α → β} {«↓» : {x // x ∈ A} → α} {«↑» : β → {x // x ∈ B}} {d : β} :
  overloadUnaryOp «↓» «↑» d op x ∈ B := by
  by_cases hx : x ∈ A
  · unfold overloadUnaryOp
    rw [dif_pos hx]
    apply Subtype.property
  · rw [overloadUnaryOp_false_eq_default («↓» := «↓») («↑» := «↑») (op := op) (d := d) (hx := hx)]
    apply Subtype.property


open Classical in
theorem overloadBinOp_endo
  {X Y A B : ZFSet} {α β} {«↓» : {x // x ∈ A} → α} {«↑» : β → {x // x ∈ B}} {op : α → α → β} (d : β) (hX : X ⊆ A) (hY : Y ⊆ A) :
  (X.prod Y).image (λ z => overloadBinOp «↓» «↑» d op z.π₁ z.π₂) ⊆ B := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := ZFSet.mem_image.mp hz
  obtain ⟨_, ha, _, hb, rfl⟩ := ZFSet.mem_prod.mp hw
  rw [ZFSet.π₁_pair, ZFSet.π₂_pair]
  apply overloadBinOp_mem (hX ha) (hY hb)

open Classical in
theorem overloadUnaryOp_endo
  {X A B : ZFSet} {α β} {«↓» : {x // x ∈ A} → α} {«↑» : β → {x // x ∈ B}} {op : α → β} (d : β) :
  X.image (overloadUnaryOp «↓» «↑» d op) ⊆ B := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := ZFSet.mem_image.mp hz
  apply overloadUnaryOp_mem

theorem List.orderedPairSublist {α} {a b : α} {l : List α} {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hij : i < j) (ha : l[i] = a) (hb : l[j] = b) : [a, b].Sublist l := by
  rw [List.cons_sublist_iff]
  exists l.take (i+1), l.drop (i+1)
  and_intros
  · symm
    exact List.take_append_drop (i + 1) l
  · rw [List.mem_take_iff_getElem]
    exists i, (by rw [Nat.lt_min]; exact ⟨Nat.lt_add_one i, hi⟩)
  · rw [List.singleton_sublist, List.mem_drop_iff_getElem]
    exists j - (i + 1)
    apply Exists.intro
    · conv =>
        enter [1,2]
        rw [Nat.add_sub_of_le hij]
      assumption
    · conv =>
        enter [1]
        rw [Nat.sub_add_cancel hij]
      assumption


theorem mem_zip_lookup (Γ : TypeContext) (v : 𝒱) (α : BType) (vs : List 𝒱) (αs : List BType) (vs_αs_len : vs.length = αs.length) (h : (v, α) ∈ vs.zip αs) : (vs.zipToAList αs ∪ Γ).lookup v = some α := by
  rw [AList.lookup_union_eq_some]
  left
  rw [Option.ext_iff]
  intro τ
  rw [Option.mem_some_iff, AList.mem_lookup_iff]
  have h' : ⟨v, α⟩ ∈ (vs.zipToAList αs).entries := by
    unfold List.zipToAList List.zipWith
    induction vs, αs, vs_αs_len using List.induction₂ with
    | nil_nil =>
      rw [List.zip_nil_right] at h
      nomatch List.not_mem_nil (v, α), h
    | cons_cons v' vs α' αs len_eq ih =>
      rw [List.zip_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · injection h; subst_eqs
        exact List.mem_of_mem_head? rfl
      · admit
  constructor
  · intro h
    have := List.nodupKeys_iff_pairwise.mp (vs.zipToAList αs).nodupKeys
    rw [List.pairwise_iff_forall_sublist] at this
    have sublist : [⟨v, α⟩, ⟨v, τ⟩].Sublist (vs.zipToAList αs).entries ∨ [⟨v, τ⟩, ⟨v, α⟩].Sublist (vs.zipToAList αs).entries ∨ α = τ:= by
      rw [@List.mem_iff_getElem] at h' h
      obtain ⟨i, i_len, hi⟩ := h'
      obtain ⟨j, j_len, hj⟩ := h
      rcases Nat.lt_trichotomy i j with lt | rfl | gt
      · left
        exact List.orderedPairSublist i_len j_len lt hi hj
      · right
        right
        rw [hi] at hj
        injection hj
      · right
        left
        exact List.orderedPairSublist j_len i_len gt hj hi
    rcases sublist with sublist | sublist | rfl
    · nomatch this sublist
    · nomatch this sublist
    · rfl
  · rintro rfl
    assumption

-- set_option trace.profiler true in
open Classical in
def denote : (t : Term) → (wt : WellTyped t) → Option {x : ZFSet // let ⟨_,τ,_⟩ := wt; x ∈ τ.toZFSet} -- denote is no longer total, sadly
  | B.Term.var _, ⟨Γ, τ, _⟩ =>
    let e : ZFSet := ε τ.toZFSet
    have he : e ∈ τ.toZFSet := ZFSet.epsilon_mem (BType.toZFSet_nonempty)
    return ⟨e, he⟩
  | B.Term.int n, ⟨Γ, .int, _⟩ => return ⟨.ofInt n, ZFSet.mem_ofInt_Int n⟩
  | B.Term.bool b, ⟨_, .bool, hb⟩ => return ⟨.ofBool b, ZFSet.mem_ofBool_𝔹 b⟩
  | x ↦ᴮ y, ⟨Γ, α ×ᴮ β, h⟩ => do
    let ⟨X, hX⟩ ← ⟦x⟧ᴮ ⟨Γ, α, B.Typing.mapletE h |>.left⟩
    let ⟨Y, hY⟩ ← ⟦y⟧ᴮ ⟨Γ, β, B.Typing.mapletE h |>.right⟩
    have hXY : X.pair Y ∈ (α ×ᴮ β).toZFSet := by
      rw [BType.toZFSet, ZFSet.pair_mem_prod]
      exact ⟨hX, hY⟩
    return ⟨X.pair Y, hXY⟩
  | p ∧ᴮ q, ⟨Γ, .bool, h⟩ => do
    let ⟨p', hp'⟩ ← ⟦p⟧ᴮ ⟨Γ, .bool, B.Typing.andE h |>.right |>.left⟩
    let ⟨q', hq'⟩ ← ⟦q⟧ᴮ ⟨Γ, .bool, B.Typing.andE h |>.right |>.right⟩
    return ⟨p' ⋀ᶻ q', overloadBinOp_mem hp' hq'⟩
  | x +ᴮ y, ⟨Γ, .int, h⟩ => do
    let ⟨X, hX⟩ ← ⟦x⟧ᴮ ⟨Γ, .int, B.Typing.addE h |>.right |>.left⟩
    let ⟨Y, hY⟩ ← ⟦y⟧ᴮ ⟨Γ, .int, B.Typing.addE h |>.right |>.right⟩
    return ⟨X +ᶻ Y, overloadBinOp_mem hX hY⟩
  | x -ᴮ y, ⟨Γ, .int, h⟩ => do
    let ⟨X, hX⟩ ← ⟦x⟧ᴮ ⟨Γ, .int, B.Typing.subE h |>.right |>.left⟩
    let ⟨Y, hY⟩ ← ⟦y⟧ᴮ ⟨Γ, .int, B.Typing.subE h |>.right |>.right⟩
    return ⟨X -ᶻ Y, overloadBinOp_mem hX hY⟩
  | x *ᴮ y, ⟨Γ, .int, h⟩ => do
    let ⟨X, hX⟩ ← ⟦x⟧ᴮ ⟨Γ, .int, B.Typing.mulE h |>.right |>.left⟩
    let ⟨Y, hY⟩ ← ⟦y⟧ᴮ ⟨Γ, .int, B.Typing.mulE h |>.right |>.right⟩
    return ⟨X *ᶻ Y, overloadBinOp_mem hX hY⟩
  | x ≤ᴮ y, ⟨Γ, .bool, h⟩ => do
    let ⟨X, hX⟩ ← ⟦x⟧ᴮ ⟨Γ, .int, B.Typing.leE h |>.right |>.left⟩
    let ⟨Y, hY⟩ ← ⟦y⟧ᴮ ⟨Γ, .int, B.Typing.leE h |>.right |>.right⟩
    return ⟨X ≤ᶻ Y, overloadBinOp_mem hX hY⟩
  | ¬ᴮ x, ⟨Γ, .bool, h⟩ => do
    let ⟨X, hX⟩ ← ⟦x⟧ᴮ ⟨Γ, .bool, B.Typing.notE h |>.right⟩
    return ⟨¬ᶻ X, overloadUnaryOp_mem⟩
  | x =ᴮ y, ⟨Γ, .bool, h⟩ => do
    let α := choose (B.Typing.eqE h |>.right)
    let ⟨hx, hy⟩ := choose_spec (B.Typing.eqE h |>.right)
    let ⟨X, hX⟩ ← ⟦x⟧ᴮ ⟨Γ, α, hx⟩
    let ⟨Y, hY⟩ ← ⟦y⟧ᴮ ⟨Γ, α, hy⟩
    return ⟨X =ᶻ Y,  overloadBinOp_mem hX hY⟩
  | B.Term.ℤ, ⟨Γ, .set .int, _⟩ => return ⟨ZFSet.Int, ZFSet.mem_powerset_self⟩
  | B.Term.𝔹, ⟨Γ, .set .bool, _⟩ => return ⟨ZFSet.𝔹, ZFSet.mem_powerset_self⟩
  | x ∈ᴮ S, ⟨Γ, .bool, h⟩ => do
    let α := choose (B.Typing.memE h |>.right)
    let ⟨hx, hS⟩ := choose_spec (B.Typing.memE h |>.right)
    let ⟨X, hX⟩ ← ⟦x⟧ᴮ ⟨Γ, α, hx⟩
    let ⟨T, hT⟩ ← ⟦S⟧ᴮ ⟨Γ, .set α, hS⟩
    return ⟨X ∈ᶻ T, overloadUnaryOp_mem⟩
  | S ⨯ᴮ T, ⟨Γ, .set (.prod α β), h⟩ => do
    let α' := choose (B.Typing.cprodE h)
    let hα' := choose_spec (B.Typing.cprodE h)
    let β' := choose hα'
    let ⟨hβ', hS, hT⟩ := choose_spec hα'
    have eq : α = α' ∧ β = β' := by apply And.intro <;> injections hβ'
    let ⟨X, hX⟩ ← ⟦S⟧ᴮ ⟨Γ, .set α, eq.left ▸ hS⟩
    let ⟨Y, hY⟩ ← ⟦T⟧ᴮ ⟨Γ, .set β, eq.right ▸ hT⟩
    return ⟨X.prod Y, by
      dsimp [BType.toZFSet] at hX hY ⊢
      rw [ZFSet.mem_powerset] at hX hY ⊢
      intros _ hz
      rw [ZFSet.mem_prod] at hz ⊢
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      exact ⟨a, hX ha, b, hY hb, rfl⟩
    ⟩
  | 𝒫ᴮ S, ⟨Γ, .set (.set α), h⟩ => do
    let α' := choose (B.Typing.powE h)
    let ⟨hα', hS⟩ := choose_spec (B.Typing.powE h)
    have α_eq : α = α' := by injections hα'
    let ⟨X, hX⟩ ← ⟦S⟧ᴮ ⟨Γ, .set α, α_eq ▸ hS⟩
    return ⟨X.powerset, by
      dsimp [BType.toZFSet] at hX ⊢
      rw [ZFSet.mem_powerset] at hX ⊢
      exact ZFSet.powerset_mono.mpr hX⟩
  | S ∪ᴮ T, ⟨Γ, .set α, h⟩ => do
    let α' := choose (B.Typing.unionE h)
    let ⟨hα', hS, hT⟩ := choose_spec (B.Typing.unionE h)
    have eq : α = α' := by injections hα'
    let ⟨X, hX⟩ ← ⟦S⟧ᴮ ⟨Γ, .set α, eq ▸ hS⟩
    let ⟨Y, hY⟩ ← ⟦T⟧ᴮ ⟨Γ, .set α, eq ▸ hT⟩
    return ⟨X ∪ Y, by
      dsimp [BType.toZFSet] at hX hY ⊢
      rw [ZFSet.mem_powerset] at hX hY ⊢
      exact ZFSet.union_mono hX hY⟩
  | S ∩ᴮ T, ⟨Γ, .set α, h⟩ => do
    let α' := choose (B.Typing.interE h)
    let ⟨hα', hS, hT⟩ := choose_spec (B.Typing.interE h)
    have eq : α = α' := by injections hα'
    let ⟨X, hX⟩ ← ⟦S⟧ᴮ ⟨Γ, .set α, eq ▸ hS⟩
    let ⟨Y, hY⟩ ← ⟦T⟧ᴮ ⟨Γ, .set α, eq ▸ hT⟩
    return ⟨X ∩ Y, by
      dsimp [BType.toZFSet] at hX hY ⊢
      rw [ZFSet.mem_powerset] at hX hY ⊢
      exact ZFSet.inter_mono hX hY⟩
  | B.Term.min S, ⟨Γ, .int, h⟩ => do
    let ⟨X, hX⟩ ← ⟦S⟧ᴮ ⟨Γ, .set .int, B.Typing.minE h |>.right⟩
    have linord : LinearOrder {x // x ∈ X} :=
      ZFSet.LinearOrder.ofSubset (by dsimp [BType.toZFSet] at hX; rw [← ZFSet.mem_powerset]; exact hX) inferInstance
    if fin_nempX : X.IsFinite ∧ X.Nonempty then
      -- NOTE: non-empty finite sets are guaranteed to have a minimum
      return ⟨ZFSet.Min X, ZFSet.mem_powerset.mp hX (ZFSet.Min_mem ⟨X, fin_nempX.left⟩ fin_nempX.right)⟩
    else failure
  | B.Term.max S, ⟨Γ, .int, h⟩ => do
    let ⟨X, hX⟩ ← ⟦S⟧ᴮ ⟨Γ, .set .int, B.Typing.maxE h |>.right⟩
    have linord : LinearOrder {x // x ∈ X} :=
      ZFSet.LinearOrder.ofSubset (by dsimp [BType.toZFSet] at hX; rw [← ZFSet.mem_powerset]; exact hX) inferInstance
    if fin_nempX : X.IsFinite ∧ X.Nonempty then
      -- NOTE: non-empty finite sets are guaranteed to have a maximum
      return ⟨ZFSet.Max X, ZFSet.mem_powerset.mp hX (ZFSet.Max_mem ⟨X, fin_nempX.left⟩ fin_nempX.right)⟩
    else failure
  | |S|ᴮ, ⟨Γ, .int, h⟩ => do
    let α := choose (B.Typing.cardE h |>.right)
    let hS := choose_spec (B.Typing.cardE h |>.right)
    let ⟨X, hX⟩ ← ⟦S⟧ᴮ ⟨Γ, .set α, hS⟩
    if finX : X.IsFinite then
      -- NOTE: the cardinality of a finite set is well-defined
      return ⟨⟰ (ZFSet.Card ⟨X, finX⟩), by apply Subtype.property⟩
    else failure
  | B.Term.app f x, ⟨Γ, β, h⟩ => do
    let α := choose (B.Typing.appE h)
    let ⟨hF, hX⟩ := choose_spec (B.Typing.appE h)
    let ⟨F, mem_F⟩ ← ⟦f⟧ᴮ ⟨Γ, .set (α ×ᴮ β), hF⟩
    let ⟨X, mem_X⟩ ← ⟦x⟧ᴮ ⟨Γ, α, hX⟩
    if ispfun : F.IsPFunc α.toZFSet β.toZFSet then
      if X_dom : X ∈ F.Dom ispfun then
        return F.fapply ispfun ⟨X, X_dom⟩
      else failure
    else failure
    /- NOTE: same as above with an exists (seen as a dependent and) in the condition.
    if hF : ∃ (hf : F.IsPFunc α.toZFSet β.toZFSet), X ∈ F.Dom hf then
      let hf := choose hF
      let X_dom := choose_spec hF
      return F.fapply hf ⟨X, X_dom⟩
    else failure
    -/
  | X ⇸ᴮ Y, ⟨Γ, .set (.set (α ×ᴮ β)), h⟩ => do
    let α' := choose (B.Typing.pfunE h)
    let β' := choose <| choose_spec (B.Typing.pfunE h)
    let ⟨eq, hX, hY⟩ := choose_spec <| choose_spec (B.Typing.pfunE h)
    have eq : α = α' ∧ β = β' := by apply And.intro <;> injections eq
    let ⟨A, hA⟩ ← ⟦X⟧ᴮ ⟨Γ, .set α, eq.left ▸ hX⟩
    let ⟨B, hB⟩ ← ⟦Y⟧ᴮ ⟨Γ, .set β, eq.right ▸ hY⟩
    return ⟨A.prod B |>.powerset |>.sep (λ f => f.IsPFunc A B),
      ZFSet.prod_sep_ispfunc_mem (ZFSet.mem_powerset.mp hA) (ZFSet.mem_powerset.mp hB)⟩
  | B.Term.collect vs D P, ⟨Γ, .set τ, h⟩ => do
    let αs := choose (B.Typing.collectE h)
    let Ds := choose <| choose_spec (B.Typing.collectE h)
    let vs_nemp := choose <| choose_spec <| choose_spec (B.Typing.collectE h)
    let vs_αs_len := choose <| choose_spec <| choose_spec <| choose_spec (B.Typing.collectE h)
    let ⟨eq,vs'_αs_len,typD,typP⟩ := choose_spec <| choose_spec <| choose_spec <| choose_spec (B.Typing.collectE h)
    have eq : τ = List.reduce (· ×ᴮ ·) αs (by rwa [← List.length_pos, vs_αs_len, List.length_pos] at vs_nemp) := by injections eq
    let mut vs' : List ZFSet := []
    for ⟨⟨v, α⟩, h⟩ in vs.zip αs |>.attach do
      let ⟨V, hV⟩ ← ⟦.var v⟧ᴮ ⟨vs.zipToAList αs ∪ Γ, α, by
        -- obtain ⟨i, i_len, hi⟩ := List.getElem_of_mem h
        apply B.Typing.var
      ⟩
      vs' := vs'.push V
    failure
  | _, _ => failure
  -- | B.Term.lambda vs D P, ⟨Γ, τ, h⟩ => sorry
  -- | B.Term.all vs D P, ⟨Γ, τ, h⟩ => sorry

end
end B

end
