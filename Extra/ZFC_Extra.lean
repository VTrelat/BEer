import CustomPrelude
import ZFLean

namespace ZFSet.ZFBool

theorem and_elim {x y : ZFBool} (h : x ⋀ y = ⊤) : x = ⊤ ∧ y = ⊤ := and_iff x y |>.mp h
theorem or_elim {x y : ZFBool} (h : x ⋁ y = ⊤) : x = ⊤ ∨ y = ⊤ := or_iff x y |>.mp h

theorem not_intro (x : ZFBool) (h : x = ⊤ → False) : ZFBool.not x = ⊤ := by
  cases x
  · exact not_false_eq_true
  · nomatch h rfl

theorem not_elim {x : ZFBool} (h : ZFBool.not x = ⊤) : x = ⊥ := by
  cases x
  · rfl
  · rw [not_true_eq_false] at h
    nomatch true_ne_false h.symm

@[simp]
theorem not_not (x : ZFBool) : .not (.not x) = x := by cases x <;> simp

theorem not_or (x y : ZFBool) : .not (x ⋁ y) = .not x ⋀ .not y := by
  cases x <;> cases y <;>
  first
  | rw [or_false, not_false_eq_true, and_true]
  | rw [or_true, not_true_eq_false, and_false]

theorem not_and (x y : ZFBool) : .not (x ⋀ y) = .not x ⋁ .not y := by
  cases x <;> cases y <;>
  first
  | rw [and_false, not_false_eq_true, or_true]
  | rw [and_true, not_true_eq_false, or_false]

theorem and_or_assoc (x y z : ZFBool) : x ⋀ (y ⋁ z) = (x ⋀ y) ⋁ (x ⋀ z) := by
  cases x
  · rw [and_comm, and_false, and_comm, and_false, or_comm, or_false, and_comm, and_false]
  · rw [and_comm, and_true, and_comm, and_true, and_comm, and_true]

theorem or_and_assoc (x y z : ZFBool) : x ⋁ (y ⋀ z) = (x ⋁ y) ⋀ (x ⋁ z) := by
  cases x
  · rw [or_comm, or_false, or_comm, or_false, or_comm, or_false]
  · rw [or_comm, or_true, or_comm, or_true, or_comm, or_true, and_true]

def implies (x y : ZFBool) : ZFBool := .not x ⋁ y
infixr:51 " ⇒ " => implies

theorem implies_intro (x y : ZFBool) (h : x = ⊤ → y = ⊤) : x ⇒ y = ⊤ := by
  cases x
  · rw [implies, not_false_eq_true, or_comm, or_true]
  · rw [implies, not_true_eq_false, or_comm, or_false]
    exact h rfl

theorem implies_elim {x y : ZFBool} (h : x ⇒ y = ⊤) (h' : x = ⊤) : y = ⊤ := by
  subst h'
  rwa [implies, not_true_eq_false, or_comm, or_false] at h

syntax "zand_intro" : tactic
macro_rules
  | `(tactic| zand_intro) => `(tactic| refine ZFBool.and_intro ?_ ?_ (And.intro ?_ ?_))

syntax "zand_intros" : tactic
macro_rules
  | `(tactic| zand_intros) => `(tactic| repeat' zand_intro)

syntax "zleft" : tactic
macro_rules
  | `(tactic| zleft) => `(tactic| refine ZFBool.or_intro _ _ (Or.inl ?_))
syntax "zright" : tactic
macro_rules
  | `(tactic| zright) => `(tactic| refine ZFBool.or_intro _ _ (Or.inr ?_))

syntax "zintro" (colGt ident)? : tactic
macro_rules
  | `(tactic| zintro $h) => `(tactic| refine ZFBool.implies_intro _ _ (fun $h => ?_))
  | `(tactic| zintro) => `(tactic| refine ZFBool.implies_intro _ _ (fun _ => ?_))

theorem eq_of_imp_imp_iff (x y : ZFBool) : x = y ↔ (x ⇒ y) ⋀ (y ⇒ x) = ⊤ := by
  constructor
  · rintro rfl
    zand_intro <;> (zintro; assumption)
  · intro h
    obtain ⟨l, r⟩ := and_elim h
    replace l := implies_elim l
    replace r := implies_elim r
    cases x <;> cases y
    · rfl
    · nomatch true_ne_false.symm <| r rfl
    · nomatch true_ne_false.symm <| l rfl
    · rfl

syntax "zintros" (colGt ident)* : tactic
macro_rules
  | `(tactic| zintros) => `(tactic| repeat zintro)
  | `(tactic| zintros $h) => `(tactic| zintro $h)
  | `(tactic| zintros $h₁ $h₂ $hs*) => `(tactic| (zintro $h₁; zintros $h₂ $hs*))

theorem true_implies (x : ZFBool) : ⊤ ⇒ x = x := by
  rw [implies, not_true_eq_false, or_comm, or_false]

example (x y z : ZFBool) : (x ⋀ y ⇒ z) = (x ⇒ y ⇒ z) := by
  rw [eq_of_imp_imp_iff]
  zand_intros
  · zintros h₁ h₂ h₃
    subst x y
    rwa [and_true, true_implies] at h₁
  · zintros h h'
    obtain ⟨rfl, rfl⟩ := and_elim h'
    rwa [true_implies, true_implies] at h

example (x y z : ZFBool) : (x ⋀ y ⋀ z) = (y ⋀ z ⋀ x) := by
  rw [eq_of_imp_imp_iff]
  zand_intros
  · zintros h
    obtain ⟨l, rfl⟩ := and_elim h
    obtain ⟨rfl, rfl⟩ := and_elim l
    ac_nf
  · zintros h
    obtain ⟨l, rfl⟩ := and_elim h
    obtain ⟨rfl, rfl⟩ := and_elim l
    ac_nf

end ZFSet.ZFBool

noncomputable section

theorem epsilon_mem {y : ZFSet} (hy : y ≠ ∅) : ε y ∈ y :=
  Classical.epsilon_spec_aux _ _ <| ZFSet.nonempty_exists_iff.mp hy

theorem powerset_mono {s t : ZFSet} : s.powerset ⊆ t.powerset ↔ s ⊆ t := by
  constructor
  · intro h x hx
    simp_rw [ZFSet.subset_def, ZFSet.mem_powerset, ZFSet.subset_def] at h
    specialize @h {x}
    simp_rw [ZFSet.mem_singleton, forall_eq] at h
    exact h hx
  · intro h x hx
    rw [ZFSet.mem_powerset] at hx ⊢
    exact λ _ h' => h (hx h')

theorem sep_mono {s t : ZFSet} {P} (h : s ⊆ t) : s.sep P ⊆ t := by
  intro x hx
  rw [ZFSet.mem_sep] at hx
  exact h hx.1

theorem union_mono {x y z : ZFSet} :  x ⊆ z → y ⊆ z → x ∪ y ⊆ z := by
  intro hx hy
  intro a ha
  rw [ZFSet.mem_union] at ha
  rcases ha with _ | _
  · exact hx ‹_›
  · exact hy ‹_›

theorem inter_mono {x y z : ZFSet} :  x ⊆ z → y ⊆ z → x ∩ y ⊆ z := by
  intro hx hy
  intro a ha
  rw [ZFSet.mem_inter] at ha
  exact hx ha.1

theorem ZFSet.powerset_nonempty {S : ZFSet} : S.powerset ≠ ∅ := by
  intro h
  rw [ZFSet.ext_iff] at h
  specialize h ∅
  rw [ZFSet.mem_powerset] at h
  nomatch h.mp (ZFSet.empty_subset S)

theorem ZFSet.prod_nonempty {A B : ZFSet} (hA : A ≠ ∅) (hB : B ≠ ∅) : A.prod B ≠ ∅ := by
  intro h
  rw [ZFSet.nonempty_exists_iff] at hA hB
  obtain ⟨x, hx⟩ := hA
  obtain ⟨y, hy⟩ := hB
  rw [ZFSet.ext_iff] at h
  specialize h (x.pair y)
  rw [ZFSet.pair_mem_prod] at h
  nomatch ZFSet.notMem_empty _ <| h.mp ⟨hx, hy⟩

namespace ZFSet.ZFInt
-- attribute [-instance] instEquivZFIntInt
-- attribute [-instance] instPreorderSubtypeMemInt
-- attribute [-instance] instLinearOrderSubtypeMemInt

def ZFNat.toNat (x : ZFNat) : ℕ := ZFNat.rec x 0 (fun _ n => n + 1)

theorem ZFNat.toNat_zero : ZFNat.toNat 0 = 0 := by
  unfold ZFNat.toNat
  rw [ZFNat.rec_zero]

theorem ZFNat.toNat_succ (x : ZFNat) : ZFNat.toNat (x + 1) = ZFNat.toNat x + 1 := by
  unfold ZFNat.toNat
  rw [ZFNat.add_one_eq_succ, ZFNat.rec_succ]

theorem ZFNat.toNat_add (x y : ZFNat) : ZFNat.toNat (x + y) = ZFNat.toNat x + ZFNat.toNat y := by
  induction x generalizing y with
  | zero => rw [ZFNat.toNat_zero, ZFNat.zero_add, Nat.zero_add]
  | succ n ih =>
    rw [ZFNat.toNat_succ, Nat.add_assoc, Nat.add_comm 1, ←ZFNat.toNat_succ, ←ih]
    congr 1
    rw [ZFNat.add_comm y, ZFNat.add_assoc]

theorem ZFNat.toNat_ofNat (n : ℕ) : ZFNat.toNat (ZFNat.ofNat n) = n := by
  induction n with
  | zero => exact ZFNat.toNat_zero
  | succ n ih =>
    rw [ZFNat.ofNat, ZFNat.nsmul, ←ZFNat.ofNat, ZFNat.add_comm]
    rw [ZFNat.toNat_succ, ih]

theorem ZFNat.ofNat_toNat (n : ZFNat) : ZFNat.ofNat (ZFNat.toNat n) = n := by
  induction n with
  | zero =>
    rw [ZFNat.toNat_zero]
    rfl
  | succ n ih =>
    rw [ZFNat.toNat_succ, ZFNat.ofNat, ZFNat.nsmul, ZFNat.add_comm, ←ZFNat.ofNat, ih]

instance : ZFNat ≃ ℕ where
  toFun := ZFNat.toNat
  invFun := ZFNat.ofNat
  left_inv := ZFNat.ofNat_toNat
  right_inv := ZFNat.toNat_ofNat

-- theorem exists_mono_bij_linear :
--   Nonempty {f : ZFInt → {x // x ∈ Int} // Function.Bijective f ∧ (∀ x y, f x < f y ↔ x < y) ∧ (∀ k a b, f (k*a + b) = k.into * (f a) + (f b))} := by admit

-- instance instEquivZFIntInt : ZFInt ≃ {x // x ∈ Int} :=
--   let ⟨f, bij, _mono, _linear⟩ := Classical.choice exists_mono_bij_linear
--   Equiv.ofBijective f bij

-- theorem instEquivZFIntInt.mono_iff (x y : { x // x ∈ Int }) :
--   instEquivZFIntInt.invFun x < instEquivZFIntInt.invFun y ↔ x < y := by
--   constructor
--   · intro h
--     dsimp [instEquivZFIntInt] at h
--     split at h
--     rename_i f' f bij mono linear eq; clear f' eq
--     unfold Equiv.ofBijective at h
--     dsimp at h
--     have := mono
--       (Function.surjInv (Function.Bijective.surjective bij) x)
--       (Function.surjInv (Function.Bijective.surjective bij) y) |>.mpr h
--     iterate 2 rw [Function.rightInverse_surjInv (Function.Bijective.surjective bij)] at this
--     exact this
--   · intro h
--     dsimp [instEquivZFIntInt]
--     split
--     rename_i f' f bij mono linear eq; clear f' eq
--     let f' := Function.surjInv (Function.Bijective.surjective bij)
--     have mono' : ∀ x y, f' x < f' y ↔ x < y := by
--       intro x y
--       have := mono (f' x) (f' y)
--       iterate 2 rw [Function.rightInverse_surjInv (Function.Bijective.surjective bij)] at this
--       exact this.symm
--     unfold Equiv.ofBijective
--     dsimp
--     exact mono' x y |>.mpr h

instance instPreorderSubtypeMemInt : Preorder {x // x ∈ Int} where
  le x y := ZFInt.instPartialOrder.le x y
  le_refl x := ZFInt.instLinearOrder.le_refl x
  le_trans x y z := ZFInt.instLinearOrder.le_trans x y z
  lt_iff_le_not_ge x y := by
    symm
    trans
    · exact ZFInt.instLinearOrder.lt_iff_le_not_ge x y |>.symm
    · exact ZFSet.instEquivZFIntInt.mono_iff x y

instance instLinearOrderSubtypeMemInt : LinearOrder {x // x ∈ Int} where
  le := (ZFInt.instLinearOrder.le · ·)
  le_refl := (ZFInt.instLinearOrder.le_refl ·)
  le_trans := (ZFInt.instLinearOrder.le_trans · · ·)
  le_antisymm x y h h' := by
    have := ZFInt.instLinearOrder.le_antisymm x y h h'
    rwa [Equiv.invFun_as_coe, EmbeddingLike.apply_eq_iff_eq] at this
  le_total := (ZFInt.instLinearOrder.le_total · ·)
  toDecidableLE := (ZFInt.instLinearOrder.toDecidableLE · ·)
  lt_iff_le_not_ge _ _ := _root_.lt_iff_le_not_ge

end ZFSet.ZFInt

section instEquivZFIntInt
namespace ZFSet.ZFInt


theorem instEquivZFIntInt.invFun_zero_eq : instEquivZFIntInt.invFun ⟨ofInt 0, ZFSet.mem_ofInt_Int 0⟩ = 0 := by
  admit
  stop
  unfold instEquivZFIntInt
  split using _ f bij mono linear f_def
  simp only [Equiv.invFun_as_coe]
  have := Equiv.symm_apply_apply (Equiv.ofBijective f bij) 0
  rw [Equiv.ofBijective_apply] at this
  rw [←this]
  congr 1

  specialize linear 0 0
  simp_rw [mul_zero, zero_add] at linear
  unfold overloadBinOp_Int overloadBinOp Function.onFun at linear
  dsimp at linear
  conv at linear =>
    enter [2, 2, 1, 2, 1, 1, 2, 1, 2]
    rw [ite_cond_eq_true _ _ (eq_true ⟨Subtype.property _, Subtype.property _⟩)]
  simp only [SetLike.coe_mem, and_self, ↓reduceIte, Equiv.symm_apply_apply, SetLike.coe_eq_coe] at linear
  sorry

theorem instEquivZFIntInt.invFun_one_eq : instEquivZFIntInt.invFun ⟨ofInt 1, ZFSet.mem_ofInt_Int 1⟩ = 1 := by
  admit

end ZFSet.ZFInt
end instEquivZFIntInt


notation "⟰" => ZFSet.instEquivZFIntInt.toFun
notation "⟱" => ZFSet.instEquivZFIntInt.invFun

@[simp] theorem ZFSet.int_equiv_right_simp {x} : ⟰ (⟱ x) = x := ZFSet.instEquivZFIntInt.right_inv x
@[simp] theorem ZFSet.int_equiv_left_simp  {x} : ⟱ (⟰ x) = x := ZFSet.instEquivZFIntInt.left_inv x

scoped[Classical] attribute [instance high] Classical.allZFSetDefinable -- what a trick!
noncomputable instance : DecidableEq ZFSet := (Classical.propDecidable <| · = ·)
instance : Inhabited ZFSet.ZFBool := ⟨⊤⟩

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

abbrev overloadBinOp_Int (op : ZFSet.ZFInt → ZFSet.ZFInt → ZFSet.ZFInt) (x y : ZFSet) : ZFSet := overloadBinOp (⟱ ·) (⟰ ·) 0 op x y
infixl:65 " +ᶻ " => overloadBinOp_Int (· + ·)
infixl:65 " -ᶻ " => overloadBinOp_Int (· - ·)
infixl:65 " *ᶻ " => overloadBinOp_Int (· * ·)

set_option hygiene false in section
open Classical in infixl:65 " ≤ᶻ " => overloadBinOp ⟱ (λ p => if p then (⊤ : ZFSet.ZFBool) else (⊥ : ZFSet.ZFBool)) ⊥ (· ≤ ·)
open Classical in infixl:65 " <ᶻ " => overloadBinOp ⟱ (λ p => if p then (⊤ : ZFSet.ZFBool) else (⊥ : ZFSet.ZFBool)) ⊥ (· < ·)
open Classical in infixl:65 " =ᶻ " => overloadBinOp (·.val) (λ p => if p then ZFSet.ZFBool.true else ZFSet.ZFBool.false) ⊥ (· = ·)
open Classical in infixl:65 " ∈ᶻ " => λ X T => overloadUnaryOp (A := T) (B := ZFSet.𝔹) («↓» := (·.val)) («↑» := λ p => if p then ⊤ else ⊥) (default := ⊥) (· ∈ T) X
end

abbrev overloadBinOp_𝔹 (op : ZFSet.ZFBool → ZFSet.ZFBool → ZFSet.ZFBool) (x y : ZFSet) : ZFSet := overloadBinOp id id ZFSet.ZFBool.false op x y
infixl:65 " ⋀ᶻ " => overloadBinOp_𝔹 (· ⋀ ·)
infixl:65 " ⋁ᶻ " => overloadBinOp_𝔹 (· ⋁ ·)
infixl:65 " ⇒ᶻ " => overloadBinOp_𝔹 (λ x y => (ZFSet.ZFBool.not x) ⋁ y)
prefix:30 " ¬ᶻ " => overloadUnaryOp id id ZFSet.ZFBool.false ZFSet.ZFBool.not

@[simp]
theorem overloaded_add_unfold {x y : ZFSet} (hx : x ∈ ZFSet.Int) (hy : y ∈ ZFSet.Int) : x +ᶻ y = ⟰ (⟱ ⟨x, hx⟩ + ⟱ ⟨y, hy⟩) := by
  unfold overloadBinOp_Int overloadBinOp
  rw [dif_pos ⟨hx, hy⟩]

theorem overloaded_add_comm {x y : ZFSet} : x +ᶻ y = y +ᶻ x := by
  unfold overloadBinOp_Int overloadBinOp
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

theorem overloadBinOp_𝔹_endo {op x y} (stable : ∀ x y, op x y ∈ ZFSet.𝔹) : overloadBinOp_𝔹 op x y ∈ ZFSet.𝔹 := by
  unfold overloadBinOp_𝔹 overloadBinOp
  split_ifs with h₁
  · apply stable
  · apply Subtype.property

theorem overloadBinOp_𝔹_endo_foldl {xs : List ZFSet} {init : ZFSet} {op}
  (hinit : init ∈ ZFSet.𝔹) (stable : ∀ x y, op x y ∈ ZFSet.𝔹) :
  xs.foldl (overloadBinOp_𝔹 op · ·) init ∈ ZFSet.𝔹 := by
  induction xs generalizing init with
  | nil =>
    rw [List.foldl_nil]
    exact hinit
  | cons x xs ih =>
    rw [List.foldl_cons]
    exact ih <| overloadBinOp_𝔹_endo stable
