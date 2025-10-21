import B.HOTyping
import Extra.ZFC_Extra
-- import Mathlib.Order.CompleteLattice
-- import Mathlib.Tactic.ExtractGoal
noncomputable section

namespace B
def BType.toZFSet : BType → ZFSet
  | .int => .Int
  | .bool => .𝔹
  | .set α => .powerset α.toZFSet
  | .prod α β => .prod α.toZFSet β.toZFSet

notation:max "⟦" z "⟧ᶻ" => BType.toZFSet z

def BType.default {𝒱} : BType → PHOAS.Term 𝒱
  | .int => .int 0
  | .bool => .bool false
  | .set α => .collect (n := 1) α.toTerm' fun _ => .bool false
  | .prod α β => α.default ↦ᴮ' β.default

def BType.defaultZFSet.{u} : BType → ZFSet.{u}
  | .int => ZFSet.ofInt 0
  | .bool => ZFSet.zffalse
  | .set α => α.toZFSet.sep (fun _ => False)
  | .prod α β => (α.defaultZFSet.pair β.defaultZFSet)

theorem BType.mem_toZFSet_of_defaultZFSet {α : BType} : α.defaultZFSet ∈ α.toZFSet := by
  induction α with
  | int => exact ZFSet.mem_ofInt_Int 0
  | bool => exact ZFSet.ZFBool.mem_ofBool_𝔹 false
  | set α ih =>
    rw [BType.toZFSet, ZFSet.mem_powerset]
    exact ZFSet.sep_subset_self
  | prod α β =>
    rw [BType.defaultZFSet, BType.toZFSet, ZFSet.pair_mem_prod]
    and_intros <;> assumption

theorem BType.toZFSet_nonempty {α : BType} : (α : BType).toZFSet ≠ ∅ := by
  induction α <;> apply_rules [
    ZFSet.Int.nonempty,
    ZFSet.ZFBool.𝔹.nonempty,
    ZFSet.powerset_nonempty,
    ZFSet.prod_nonempty]

theorem ZFSet.prod_sep_mem_toZFSet {τ γ : BType} {D R : ZFSet} {P : ZFSet → Prop} : D ∈ τ.toZFSet.powerset → R ∈ γ.toZFSet.powerset → (D.prod R).sep P ∈ (τ.toZFSet.prod γ.toZFSet).powerset := by
  intro hD hR
  rw [ZFSet.mem_powerset, ZFSet.subset_def] at hD hR ⊢
  intro _ hz
  obtain ⟨d, hd, r, hr, rfl⟩ := ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  rw [ZFSet.pair_mem_prod]
  exact ⟨hD hd, hR hr⟩

section Denotation

open Classical B.PHOAS in
def denote_aux.all {n} {D} {P : (Fin n → ZFSet) → B.PHOAS.Term ZFSet} {Γ}
  (denoteD : (wt : WellTyped D) → Option {x : ZFSet // let ⟨_,τ,_⟩ := wt; x ∈ τ.toZFSet})
  (denoteP : (z : Fin n → ZFSet) → (wt : WellTyped (P z)) → Option {x : ZFSet // let ⟨_,τ,_⟩ := wt; x ∈ τ.toZFSet})
  (h : Γ ⊢ .all D P : .bool) : Option {x : ZFSet // x ∈ ZFSet.𝔹} := do
    let αs_Ds := choose (Typing.allE h).2.2; let αs := αs_Ds.1
    let n_pos := (Typing.allE h).2.1
    let ⟨𝒟, _⟩ ← denoteD ⟨Γ, .set (Fin.foldl (n-1) (λ d ⟨i, hi⟩ => d ×ᴮ αs ⟨i+1, Nat.add_lt_of_lt_sub hi⟩) (αs ⟨0, n_pos⟩)), PHOAS.Typing.all_dom h⟩
    let ℙ (z : ZFSet) : ZFSet :=
      if z.hasArity n then
        match denoteP (z.get n) ⟨Γ.update (z.get n) αs, .bool, PHOAS.Typing.all_pred h⟩ with
        | some Pz => Pz
        | none => ZFSet.zffalse
      else ZFSet.zffalse
    return ⟨ZFSet.sInter (ZFSet.𝔹.sep λ y => ∃ x ∈ 𝒟, y = ℙ x), ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 λ _ => id⟩

open Classical B.PHOAS in
def denote_aux.lambda {n} {D} {P : (Fin n → ZFSet) → B.PHOAS.Term ZFSet} {Γ} {τ γ : BType}
  (denoteD : (wt : WellTyped D) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (denoteP : (z : Fin n → ZFSet) → (wt : WellTyped (P z)) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (h : Γ ⊢ .lambda D P : (τ ×ᴮ γ).set) : Option {x : ZFSet // x ∈ (τ ×ᴮ γ).set.toZFSet} := do
    let β_αs_Ds := choose (Typing.lambdaE h).2; let β := β_αs_Ds.1; let αs := β_αs_Ds.2.1
    let ⟨𝒟, h𝒟⟩ ← denoteD ⟨Γ, .set τ, PHOAS.Typing.lambda_dom h⟩
    let ℙ (xy : ZFSet) := xy.hasArity 2 ∧
      (let x := xy.π₁
      let y := xy.π₂
      x.hasArity n ∧
        match denoteP (x.get n) ⟨Γ.update (x.get n) αs, β, PHOAS.Typing.lambda_exp h⟩ with
        | some ⟨Pz, _⟩ => Pz = y
        | none => False)
    return ⟨(𝒟.prod γ.toZFSet).sep ℙ, ZFSet.prod_sep_mem_toZFSet h𝒟 (ZFSet.mem_powerset.mpr fun _ => id)⟩

open Classical B.PHOAS in
def denote_aux.collect {n} {D} {P : (Fin n → ZFSet) → B.PHOAS.Term ZFSet} {Γ} {τ : BType}
  (denoteD : (wt : WellTyped D) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (denoteP : (z : Fin n → ZFSet) → (wt : WellTyped (P z)) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (h : Γ ⊢ .collect D P : τ.set) : Option {x : ZFSet // x ∈ τ.set.toZFSet} := do
    let αs_Ds := choose (Typing.collectE h).2; let αs := αs_Ds.1
    let ⟨𝒟, h𝒟⟩ ← denoteD ⟨Γ, τ.set, PHOAS.Typing.collect_dom (h := h)⟩
    let ℙ z :=
      if z.hasArity n then
        match denoteP (z.get n) ⟨Γ.update (z.get n) αs, .bool, PHOAS.Typing.collect_pred h⟩ with
        | some ⟨Pz, _⟩ => Pz = ZFSet.zftrue
        | none => False
      else False
    return ⟨𝒟.sep ℙ, (ZFSet.sep_mem_powerset h𝒟)⟩

open Classical B.PHOAS in
/- NOTE: same as above with an exists (seen as a dependent and) in the condition.
  if hF : ∃ (hf : F.IsPFunc α.toZFSet β.toZFSet), X ∈ F.Dom hf then
    let hf := choose hF
    let X_dom := choose_spec hF
    return F.fapply hf ⟨X, X_dom⟩
  else failure
-/
def denote_aux.pfun {A B : PHOAS.Term ZFSet} {Γ} {α β : BType}
  (denoteA : (wt : WellTyped A) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (denoteB : (wt : WellTyped B) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (h : Γ ⊢ .pfun A B : (α ×ᴮ β).set.set) : Option {x : ZFSet // x ∈ (α ×ᴮ β).set.set.toZFSet} := do
    let α' := choose (Typing.pfunE h)
    let β' := choose <| choose_spec (Typing.pfunE h)
    let ⟨eq, hX, hY⟩ := choose_spec <| choose_spec (Typing.pfunE h)
    have eq : α = α' ∧ β = β' := by apply And.intro <;> injections
    let ⟨A, hA⟩ ← denoteA ⟨Γ, .set α, eq.left ▸ hX⟩
    let ⟨B, hB⟩ ← denoteB ⟨Γ, .set β, eq.right ▸ hY⟩
    return ⟨A.prod B |>.powerset |>.sep (λ f => f.IsPFunc A B), ZFSet.prod_sep_is_pfunc_mem (ZFSet.mem_powerset.mp hA) (ZFSet.mem_powerset.mp hB)⟩

open Classical B.PHOAS in
def denote_aux.apply {f x : PHOAS.Term ZFSet} {Γ} {β : BType}
  (denotef : (wt : WellTyped f) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (denotex : (wt : WellTyped x) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (h : Γ ⊢ .app f x : β) : Option {x : ZFSet // x ∈ β.toZFSet} := do
    let α := choose (Typing.appE h)
    let ⟨hF, hX⟩ := choose_spec (Typing.appE h)
    let ⟨F, _⟩ ← denotef ⟨Γ, .set (α ×ᴮ β), hF⟩
    let ⟨X, _⟩ ← denotex ⟨Γ, α, hX⟩
    if ispfun : F.IsPFunc α.toZFSet β.toZFSet then
      if X_dom : X ∈ F.Dom then
        return F.fapply ispfun ⟨X, X_dom⟩
      else failure
    else failure

open Classical B.PHOAS in
def denote_aux.card {S : PHOAS.Term ZFSet} {Γ}
  (denoteS : (wt : WellTyped S) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (h : Γ ⊢ |S|ᴮ' : .int) : Option {x : ZFSet // x ∈ ZFSet.Int} := do
    let α := choose (Typing.cardE h |>.right)
    let hS := choose_spec (Typing.cardE h |>.right)
    let ⟨X, _⟩ ← denoteS ⟨Γ, .set α, hS⟩
    if finX : X.IsFinite then
      -- NOTE: the cardinality of a finite set is well-defined
      return ⟨⟰ (ZFSet.ZFInt.ofZFNat <| ZFSet.Card ⟨X, finX⟩), Subtype.property _⟩
    else failure

open Classical B.PHOAS in
def denote_aux.max {S : PHOAS.Term ZFSet} {Γ}
  (denoteS : (wt : WellTyped S) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (h : Γ ⊢ .max S : .int) : Option {x : ZFSet // x ∈ ZFSet.Int} := do
    let ⟨X, hX⟩ ← denoteS ⟨Γ, .set .int, Typing.maxE h |>.right⟩
    have linord : LinearOrder {x // x ∈ X} :=
      ZFSet.LinearOrder.ofSubset (by dsimp [BType.toZFSet] at hX; rw [← ZFSet.mem_powerset]; exact hX)
    if fin_nempX : X.IsFinite ∧ X.Nonempty then
      -- NOTE: non-empty finite sets are guaranteed to have a maximum
      return ⟨ZFSet.Max X, ZFSet.mem_powerset.mp hX (ZFSet.Max_mem ⟨X, fin_nempX.left⟩ fin_nempX.right)⟩
    else failure

open Classical B.PHOAS in
def denote_aux.min {S : PHOAS.Term ZFSet} {Γ}
  (denoteS : (wt : WellTyped S) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (h : Γ ⊢ .min S : .int) : Option {x : ZFSet // x ∈ ZFSet.Int} := do
    let ⟨X, hX⟩ ← denoteS ⟨Γ, .set .int, Typing.minE h |>.right⟩
    have linord : LinearOrder {x // x ∈ X} :=
      ZFSet.LinearOrder.ofSubset (by dsimp [BType.toZFSet] at hX; rw [← ZFSet.mem_powerset]; exact hX)
    if fin_nempX : X.IsFinite ∧ X.Nonempty then
      -- NOTE: non-empty finite sets are guaranteed to have a minimum
      return ⟨ZFSet.Min X, ZFSet.mem_powerset.mp hX (ZFSet.Min_mem ⟨X, fin_nempX.left⟩ fin_nempX.right)⟩
    else failure

open Classical B.PHOAS
def denote_aux.inter {X Y : PHOAS.Term ZFSet} {Γ} {α : BType}
  (denoteX : (wt : WellTyped X) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (denoteY : (wt : WellTyped Y) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (h : Γ ⊢ X ∩ᴮ' Y : α.set) : Option {x : ZFSet // x ∈ α.set.toZFSet} := do
    let α' := choose (Typing.interE h)
    let ⟨hα', hS, hT⟩ := choose_spec (Typing.interE h)
    have eq : α = α' := by injections hα'
    let ⟨X, hX⟩ ← denoteX ⟨Γ, .set α, eq ▸ hS⟩
    let ⟨Y, hY⟩ ← denoteY ⟨Γ, .set α, eq ▸ hT⟩
    return ⟨X ∩ Y, by
      dsimp [BType.toZFSet] at hX hY ⊢
      rw [ZFSet.mem_powerset] at hX hY ⊢
      exact inter_mono hX hY⟩

open Classical B.PHOAS
def denote_aux.union {X Y : PHOAS.Term ZFSet} {Γ} {α : BType}
  (denoteX : (wt : WellTyped X) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (denoteY : (wt : WellTyped Y) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (h : Γ ⊢ X ∪ᴮ' Y : α.set) : Option {x : ZFSet // x ∈ α.set.toZFSet} := do
    let α' := choose (Typing.unionE h)
    let ⟨hα', hS, hT⟩ := choose_spec (Typing.unionE h)
    have eq : α = α' := by injections hα'
    let ⟨X, hX⟩ ← denoteX ⟨Γ, .set α, eq ▸ hS⟩
    let ⟨Y, hY⟩ ← denoteY ⟨Γ, .set α, eq ▸ hT⟩
    return ⟨X ∪ Y, by
      dsimp [BType.toZFSet] at hX hY ⊢
      rw [ZFSet.mem_powerset] at hX hY ⊢
      exact union_mono hX hY⟩

open Classical B.PHOAS
def denote_aux.powerset {S : PHOAS.Term ZFSet} {Γ} {α : BType}
  (denoteS : (wt : WellTyped S) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (h : Γ ⊢ 𝒫ᴮ' S : α.set.set) : Option {x : ZFSet // x ∈ α.set.set.toZFSet} := do
    let α' := choose (Typing.powE h)
    let ⟨hα', hS⟩ := choose_spec (Typing.powE h)
    have α_eq : α = α' := by injections hα'
    let ⟨X, hX⟩ ← denoteS ⟨Γ, .set α, α_eq ▸ hS⟩
    return ⟨X.powerset, by
      dsimp [BType.toZFSet] at hX ⊢
      rw [ZFSet.mem_powerset] at hX ⊢
      exact powerset_mono.mpr hX⟩

open Classical B.PHOAS
def denote_aux.cprod {X Y : PHOAS.Term ZFSet} {Γ} {α β : BType}
  (denoteX : (wt : WellTyped X) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (denoteY : (wt : WellTyped Y) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (h : Γ ⊢ X ⨯ᴮ' Y : (α ×ᴮ β).set) : Option {x : ZFSet // x ∈ (α ×ᴮ β).set.toZFSet} := do
    let α' := choose (Typing.cprodE h)
    let hα' := choose_spec (Typing.cprodE h)
    let β' := choose hα'
    let ⟨hβ', hS, hT⟩ := choose_spec hα'
    have eq : α = α' ∧ β = β' := by apply And.intro <;> injections hβ'
    let ⟨X, hX⟩ ← denoteX ⟨Γ, .set α, eq.left ▸ hS⟩
    let ⟨Y, hY⟩ ← denoteY ⟨Γ, .set β, eq.right ▸ hT⟩
    return ⟨X.prod Y, by
      dsimp [BType.toZFSet] at hX hY ⊢
      rw [ZFSet.mem_powerset] at hX hY ⊢
      intros _ hz
      rw [ZFSet.mem_prod] at hz ⊢
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      exact ⟨a, hX ha, b, hY hb, rfl⟩
    ⟩

open Classical B.PHOAS
def denote_aux.mem {x S : PHOAS.Term ZFSet} {Γ}
  (denotex : (wt : WellTyped x) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (denoteS : (wt : WellTyped S) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (h : Γ ⊢ x ∈ᴮ' S : .bool) : Option {x : ZFSet // x ∈ ZFSet.𝔹} := do
    let α := choose (Typing.memE h |>.right)
    let ⟨hx, hS⟩ := choose_spec (Typing.memE h |>.right)
    let ⟨X, _⟩ ← denotex ⟨Γ, α, hx⟩
    let ⟨T, _⟩ ← denoteS ⟨Γ, .set α, hS⟩
    return ⟨X ∈ᶻ T, overloadUnaryOp_mem⟩

open Classical B.PHOAS
def denote_aux.eq {x y : PHOAS.Term ZFSet} {Γ}
  (denotex : (wt : WellTyped x) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (denotey : (wt : WellTyped y) → Option {x : ZFSet // let ⟨_,ξ,_⟩ := wt; x ∈ ξ.toZFSet})
  (h : Γ ⊢ x =ᴮ' y : .bool) : Option {x : ZFSet // x ∈ ZFSet.𝔹} := do
    let α := choose (Typing.eqE h |>.right)
    let ⟨hx, hy⟩ := choose_spec (Typing.eqE h |>.right)
    let ⟨X, hX⟩ ← denotex ⟨Γ, α, hx⟩
    let ⟨Y, hY⟩ ← denotey ⟨Γ, α, hy⟩
    return ⟨X =ᶻ Y,  overloadBinOp_mem hX hY⟩

def BType.get (τ : BType) (length : ℕ) (i : Fin length) : BType :=
  match length, i, τ with
  | 0, i, _ => nomatch i.prop
  | 1, i, τ => if h : i.val = 0 then τ else nomatch h (Fin.val_eq_zero i)
  | n+2, ⟨i, hi⟩, τ =>
    match τ with
    | .prod α β =>
      if h : i = n+1 then β else get α (n+1) ⟨i, by omega⟩
    | _ => τ

theorem BType.get_of_foldl {n : ℕ} {αs : Fin (n + 1) → BType} {i : Fin (n + 1)}:
  (Fin.foldl n (fun d i => d ×ᴮ αs i.succ) (αs 0)).get (n + 1) i = αs i := by
  induction n with
  | zero =>
    rcases Fin.fin_one_eq_zero i
    rw [Fin.foldl_zero, BType.get]
    rfl
  | succ n ih =>
    rw [Fin.foldl_succ_last, BType.get]
    split_ifs with hi
    · congr
      exact Fin.eq_of_val_eq hi.symm
    · apply @ih (fun ⟨i, hi⟩ => αs ⟨i, Nat.lt_add_right 1 hi⟩)

theorem PHOAS.Term.get_of_foldl_defaultZFSet {n : ℕ} {αs : Fin (n + 1) → BType} {i : Fin (n + 1)} :
  (Fin.foldl n (fun d i => d ×ᴮ αs i.succ) (αs 0)).defaultZFSet.get (n + 1) i = (αs i).defaultZFSet := by
  induction n with
  | zero =>
    rcases Fin.fin_one_eq_zero i
    rw [Fin.foldl_zero, ZFSet.get]
  | succ n ih =>
    rw [Fin.foldl_succ_last, ZFSet.get]
    split_ifs with hi
    · rw [BType.defaultZFSet, ZFSet.π₂_pair, Fin.last, Fin.succ_mk]
      congr
      symm
      rwa [Fin.ext_iff] at hi
    · rw [BType.defaultZFSet, ZFSet.π₁_pair]
      exact @ih
        (fun i => αs ⟨i.val, Nat.lt_add_right 1 i.is_lt⟩)
        ⟨i, Nat.lt_iff_le_and_ne.mpr ⟨Fin.is_le i, by rwa [Fin.ext_iff] at hi⟩⟩

open Classical in
def BType.hasArity : BType → ℕ → Prop
  | _, 0 => False
  | _, 1 => True
  | τ, n+2 =>
    match τ with
    | .prod α _ => α.hasArity (n+1)
    | _ => False

theorem BType.hasArity_of_foldl_defaultZFSet {α : BType} {n : ℕ} (hα : α.hasArity n) :
  α.defaultZFSet.hasArity n := by
  induction n generalizing α with
  | zero =>
    unfold BType.hasArity at hα
    nomatch hα
  | succ n ih =>
    cases n with
    | zero => trivial
    | succ n =>
      unfold BType.hasArity at hα
      unfold BType.defaultZFSet
      cases α with
      | prod τ σ =>
        dsimp at hα ⊢
        simp only [ZFSet.hasArity, ZFSet.pair_inj, exists_and_left, exists_eq', and_true, ↓reduceIte, ZFSet.π₁_pair]
        exact ih hα
      | _ => nomatch hα

theorem get_mem_type_of_isTuple {n : ℕ} {i : Fin n} {τ : BType} {z : ZFSet}
  (hz : z.hasArity n) (hτ : τ.hasArity n) (hz' : z ∈ τ.toZFSet) :
    z.get n i ∈ (τ.get n i).toZFSet := by
    fun_induction ZFSet.hasArity generalizing τ with
    | case1 => nomatch hz
    | case2 =>
      rcases Fin.fin_one_eq_zero i
      unfold ZFSet.get BType.get
      exact hz'
    | case3 x n npos hx ih =>
      cases n with
      | zero =>
        rcases Fin.fin_one_eq_zero i
        unfold ZFSet.get BType.get
        exact hz'
      | succ n =>
        unfold BType.hasArity at hτ
        unfold ZFSet.get BType.get
        split at hτ using α β
        · split_ifs with _ hi hi
          · rw [BType.toZFSet, ZFSet.mem_prod] at hz'
            obtain ⟨_, hα, _, hβ, rfl⟩ := hz'
            rwa [ZFSet.π₂_pair]
          · rw [Fin.ext_iff] at hi
            contradiction
          · rw [Fin.ext_iff] at hi
            contradiction
          · letI i' : Fin (n+1) := ⟨i, Nat.lt_iff_le_and_ne.mpr ⟨Nat.le_of_lt_succ i.prop, by rwa [Fin.ext_iff] at hi⟩⟩
            have := ih (i := i.castPred hi) hz hτ
            rw [BType.toZFSet, ZFSet.mem_prod] at hz'
            obtain ⟨_, hα, _, hβ, rfl⟩ := hz'
            apply ih hz hτ
            rwa [ZFSet.π₁_pair]
        · nomatch hτ
    | case4 x n npos hx =>
      cases n with
      | zero =>
        rcases Fin.fin_one_eq_zero i
        unfold ZFSet.get BType.get
        exact hz'
      | succ n =>
        unfold BType.hasArity at hτ
        unfold ZFSet.get BType.get
        split at hτ using α β
        · rw [BType.toZFSet, ZFSet.mem_prod] at hz'
          nomatch hz
        · nomatch hτ

set_option hygiene false
local notation "⟦" t "⟧ᴮ" => denote t

abbrev Dom := Σ' (x : ZFSet) (τ : BType), x ∈ τ.toZFSet

def ZFSet.ofFinDom {n : ℕ} (x : Fin n → Dom) : ZFSet :=
  match n with
  | 0 => ∅
  | n+1 => Fin.foldl n (fun (z : ZFSet) i => z.pair (x i.succ).1) (x 0).1

-- set_option trace.profiler true in
open Classical B.PHOAS in
def denote (t : PHOAS.Term Dom) : Option Dom :=
  match t with
  | B.PHOAS.Term.var v => return v
  | B.PHOAS.Term.int n => return ⟨.ofInt n, .int, ZFSet.mem_ofInt_Int n⟩
  | B.PHOAS.Term.bool b => return ⟨ZFSet.ZFBool.ofBool b, .bool, ZFSet.ZFBool.mem_ofBool_𝔹 b⟩
  | x ↦ᴮ' y => do
    let ⟨X, α, hX⟩ ← ⟦x⟧ᴮ
    let ⟨Y, β, hY⟩ ← ⟦y⟧ᴮ
    have hXY : X.pair Y ∈ (α ×ᴮ β).toZFSet := by
      rw [BType.toZFSet, ZFSet.pair_mem_prod]
      exact ⟨hX, hY⟩
    return ⟨X.pair Y, α ×ᴮ β, hXY⟩
  | p ∧ᴮ' q => do
    let ⟨p', .bool, hp'⟩ ← ⟦p⟧ᴮ | failure
    let ⟨q', .bool, hq'⟩ ← ⟦q⟧ᴮ | failure
    return ⟨p' ⋀ᶻ q', .bool, overloadBinOp_mem hp' hq'⟩
  | x +ᴮ' y => do
    let ⟨X, .int, hX⟩ ← ⟦x⟧ᴮ | failure
    let ⟨Y, .int, hY⟩ ← ⟦y⟧ᴮ | failure
    return ⟨X +ᶻ Y, .int, overloadBinOp_mem hX hY⟩
  | x -ᴮ' y => do
    let ⟨X, .int, hX⟩ ← ⟦x⟧ᴮ | failure
    let ⟨Y, .int, hY⟩ ← ⟦y⟧ᴮ | failure
    return ⟨X -ᶻ Y, .int, overloadBinOp_mem hX hY⟩
  | x *ᴮ' y => do
    let ⟨X, .int, hX⟩ ← ⟦x⟧ᴮ | failure
    let ⟨Y, .int, hY⟩ ← ⟦y⟧ᴮ | failure
    return ⟨X *ᶻ Y, .int, overloadBinOp_mem hX hY⟩
  | x ≤ᴮ' y => do
    let ⟨X, .int, hX⟩ ← ⟦x⟧ᴮ | failure
    let ⟨Y, .int, hY⟩ ← ⟦y⟧ᴮ | failure
    return ⟨X ≤ᶻ Y, .bool, overloadBinOp_mem hX hY⟩
  | ¬ᴮ' x => do
    let ⟨X, .bool, hX⟩ ← ⟦x⟧ᴮ | failure
    return ⟨¬ᶻ X, .bool, overloadUnaryOp_mem⟩
  | x =ᴮ' y => do
    -- denote_aux.eq ⟦x⟧ᴮ ⟦y⟧ᴮ h
    let ⟨X, α, hX⟩ ← ⟦x⟧ᴮ
    let ⟨Y, β, hY⟩ ← ⟦y⟧ᴮ
    if α_eq_β : α = β then
      return ⟨X =ᶻ Y, .bool, overloadBinOp_mem hX (α_eq_β ▸ hY)⟩
    else failure
  | B.PHOAS.Term.ℤ => return ⟨ZFSet.Int, .set .int, ZFSet.mem_powerset.mpr fun _ => id⟩
  | B.PHOAS.Term.𝔹 => return ⟨ZFSet.𝔹, .set .bool, ZFSet.mem_powerset.mpr fun _ => id⟩
  | x ∈ᴮ' S => do
    -- denote_aux.mem ⟦x⟧ᴮ ⟦S⟧ᴮ h
    let ⟨X, α, hX⟩ ← ⟦x⟧ᴮ
    let ⟨S', .set β, hS'⟩ ← ⟦S⟧ᴮ | failure
    if α_eq_β : α = β then
      return ⟨X ∈ᶻ S', .bool, overloadUnaryOp_mem⟩
    else failure
  | S ⨯ᴮ' T => do
    -- denote_aux.cprod ⟦S⟧ᴮ ⟦T⟧ᴮ h
    let ⟨S', .set α, hS'⟩ ← ⟦S⟧ᴮ | failure
    let ⟨T', .set β, hT'⟩ ← ⟦T⟧ᴮ | failure
    return ⟨S'.prod T', .set (α ×ᴮ β), by
      dsimp [BType.toZFSet] at hS' hT' ⊢
      rw [ZFSet.mem_powerset] at hS' hT' ⊢
      intros _ hz
      rw [ZFSet.mem_prod] at hz ⊢
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      exact ⟨a, hS' ha, b, hT' hb, rfl⟩
      ⟩
  | 𝒫ᴮ' S => do
    -- denote_aux.powerset ⟦S⟧ᴮ h
    let ⟨S', .set α, hS'⟩ ← ⟦S⟧ᴮ | failure
    return ⟨S'.powerset, α.set.set, by
      dsimp [BType.toZFSet] at hS' ⊢
      rw [ZFSet.mem_powerset] at hS' ⊢
      exact powerset_mono.mpr hS'⟩
  | S ∪ᴮ' T => do
    -- denote_aux.union ⟦S⟧ᴮ ⟦T⟧ᴮ h
    let ⟨S', .set α, hS'⟩ ← ⟦S⟧ᴮ | failure
    let ⟨T', .set β, hT'⟩ ← ⟦T⟧ᴮ | failure
    if α_eq_β : α = β then
      return ⟨S'.union T', .set α, by
        dsimp [BType.toZFSet] at hS' hT' ⊢
        rw [ZFSet.mem_powerset] at hS' hT' ⊢
        exact union_mono hS' (α_eq_β ▸ hT')⟩
    else failure
  | S ∩ᴮ' T => do
    -- denote_aux.inter ⟦S⟧ᴮ ⟦T⟧ᴮ h
    let ⟨S', .set α, hS'⟩ ← ⟦S⟧ᴮ | failure
    let ⟨T', .set β, hT'⟩ ← ⟦T⟧ᴮ | failure
    if α_eq_β : α = β then
      return ⟨S'.inter T', .set α, by
        dsimp [BType.toZFSet] at hS' hT' ⊢
        rw [ZFSet.mem_powerset] at hS' hT' ⊢
        exact inter_mono hS' (α_eq_β ▸ hT')⟩
    else failure
  | B.PHOAS.Term.min S => do
    -- denote_aux.min ⟦S⟧ᴮ h
    let ⟨S', .set .int, hS'⟩ ← ⟦S⟧ᴮ | failure
    have linord : LinearOrder {x // x ∈ S'} :=
      ZFSet.LinearOrder.ofSubset (by dsimp [BType.toZFSet] at hS' ⊢; rw [← ZFSet.mem_powerset]; exact hS')
    if fin_nempS' : S'.IsFinite ∧ S'.Nonempty then
      -- NOTE: non-empty finite sets are guaranteed to have a minimum
      return ⟨ZFSet.Min S', .int, ZFSet.mem_powerset.mp hS' (ZFSet.Min_mem ⟨S', fin_nempS'.1⟩ fin_nempS'.2)⟩
    else failure
  | B.PHOAS.Term.max S => do
    -- denote_aux.max ⟦S⟧ᴮ h
    let ⟨S', .set .int, hS'⟩ ← ⟦S⟧ᴮ | failure
    have linord : LinearOrder {x // x ∈ S'} :=
      ZFSet.LinearOrder.ofSubset (by dsimp [BType.toZFSet] at hS' ⊢; rw [← ZFSet.mem_powerset]; exact hS')
    if fin_nempS' : S'.IsFinite ∧ S'.Nonempty then
      -- NOTE: non-empty finite sets are guaranteed to have a maximum
      return ⟨ZFSet.Max S', .int, ZFSet.mem_powerset.mp hS' (ZFSet.Max_mem ⟨S', fin_nempS'.1⟩ fin_nempS'.2)⟩
    else failure
  | |S|ᴮ' => do
    -- denote_aux.card ⟦S⟧ᴮ h
    let ⟨S', .set α, hS'⟩ ← ⟦S⟧ᴮ | failure
    if finS' : S'.IsFinite then
      -- NOTE: the cardinality of a finite set is well-defined
      return ⟨⟰ (ZFSet.ZFInt.ofZFNat <| ZFSet.Card ⟨S', finS'⟩), .int, Subtype.property _⟩
    else failure
  | B.PHOAS.Term.app f x => do
    -- denote_aux.apply ⟦f⟧ᴮ ⟦x⟧ᴮ h
    let ⟨F, .set (τ ×ᴮ σ), hF⟩ ← ⟦f⟧ᴮ | failure
    let ⟨X, τ', hX⟩ ← ⟦x⟧ᴮ
    if τ_eq_τ' : τ = τ' then
      if ispfun : F.IsPFunc τ.toZFSet σ.toZFSet then
        if X_dom : X ∈ F.Dom then
          let ⟨Y, hY⟩ := F.fapply ispfun ⟨X, X_dom⟩
          return ⟨Y, σ, hY⟩
        else failure
      else failure
    else failure
  | X ⇸ᴮ' Y => do
    -- denote_aux.pfun ⟦X⟧ᴮ ⟦Y⟧ᴮ h
    let ⟨A, .set α, hA⟩ ← ⟦X⟧ᴮ | failure
    let ⟨B, .set β, hB⟩ ← ⟦Y⟧ᴮ | failure
    return ⟨
      A.prod B |>.powerset |>.sep (λ f => f.IsPFunc A B),
      .set (.set (α ×ᴮ β)),
      ZFSet.prod_sep_is_pfunc_mem (ZFSet.mem_powerset.mp hA) (ZFSet.mem_powerset.mp hB)⟩
  | @B.PHOAS.Term.collect _ n D P => do
    -- denote_aux.collect ⟦D⟧ᴮ (λ z => ⟦P z⟧ᴮ) h
    let ⟨𝒟, .set τ, h𝒟⟩ ← ⟦D⟧ᴮ | failure
    if den_P : ∀ {x}, ZFSet.ofFinDom x ∈ 𝒟 → ⟦P x⟧ᴮ.isSome then
      if typP_det : ∀ x y, (x_𝒟 : ZFSet.ofFinDom x ∈ 𝒟) → (y_𝒟 : ZFSet.ofFinDom y ∈ 𝒟) → ⟦P x⟧ᴮ.get (den_P x_𝒟) |>.2.1 = (⟦P y⟧ᴮ.get (den_P y_𝒟) |>.2.1) then
        let ℙ z :=
          if hz : z.hasArity n ∧ τ.hasArity n ∧ z ∈ τ.toZFSet then
            let zₙ : Fin n → Dom := fun i => ⟨z.get n i, τ.get n i, get_mem_type_of_isTuple hz.1 hz.2.1 hz.2.2⟩
            match ⟦P zₙ⟧ᴮ with
            | some ⟨Pz, _, _⟩ => Pz = ZFSet.zftrue
            | none => False
          else False
        return ⟨𝒟.sep ℙ, .set τ, (ZFSet.sep_mem_powerset h𝒟)⟩
      else failure
    else failure
  | @B.PHOAS.Term.lambda _ n D E => do
    -- denote_aux.lambda ⟦D⟧ᴮ (λ z => ⟦E z⟧ᴮ) h
    let ⟨𝒟, .set τ, h𝒟⟩ ← ⟦D⟧ᴮ | failure
    if hτ : τ.hasArity n then
      -- check if the domain is non-empty (should be provable not a conditional)
      if den_E : ∀ {x}, ZFSet.ofFinDom x ∈ 𝒟 → ⟦E x⟧ᴮ.isSome then
        if typE_det : ∀ x y, (x_𝒟 : ZFSet.ofFinDom x ∈ 𝒟) → (y_𝒟 : ZFSet.ofFinDom y ∈ 𝒟) → ⟦E x⟧ᴮ.get (den_E x_𝒟) |>.2.1 = (⟦E y⟧ᴮ.get (den_E y_𝒟) |>.2.1) then
          if 𝒟_nemp : 𝒟 ≠ ∅ then
            /- compute the return type γ of the function -/
            let x := choose (ZFSet.nonempty_exists_iff.mp 𝒟_nemp)
            let x_def := choose_spec (ZFSet.nonempty_exists_iff.mp 𝒟_nemp)
            -- `x`  must have arity `n` by definition, however we can put it in a conditional for now
            if hx : x.hasArity n ∧ x ∈ τ.toZFSet then
              let xₙ : Fin n → Dom := fun i => ⟨x.get n i, τ.get n i, get_mem_type_of_isTuple hx.1 hτ hx.2⟩
              let ⟨_, γ, _⟩ ← ⟦E xₙ⟧ᴮ

              /- compute the denotation of `E` -/
              let ℰ (xy : ZFSet) :=
                if hxy : xy.hasArity 2 then
                  let x := xy.π₁
                  let y := xy.π₂
                  if hx : x.hasArity n ∧ x ∈ 𝒟 then
                    let xₙ : Fin n → Dom := fun i => ⟨x.get n i, τ.get n i, by
                      rw [BType.toZFSet, ZFSet.mem_powerset] at h𝒟
                      exact get_mem_type_of_isTuple hx.1 hτ (h𝒟 hx.2)⟩
                    match (motive := Option Dom → Prop) ⟦E xₙ⟧ᴮ with
                    | some ⟨ex, ξ, _⟩ => if ξ = γ then ex = y else False
                    | none => False
                  else False
                else False
              return ⟨(𝒟.prod γ.toZFSet).sep ℰ, .set (τ ×ᴮ γ), ZFSet.prod_sep_mem_toZFSet h𝒟 (ZFSet.mem_powerset.mpr fun _ => id)⟩
            else failure
          else
            if h : τ.defaultZFSet.hasArity n ∧ τ.hasArity n then
              let xₙ : Fin n → Dom := fun i => ⟨τ.defaultZFSet.get n i, τ.get n i, get_mem_type_of_isTuple h.1 h.2 BType.mem_toZFSet_of_defaultZFSet⟩
              let ⟨_, γ, _⟩ ← ⟦E xₙ⟧ᴮ
              return ⟨∅, (τ ×ᴮ γ).set, by rw [BType.toZFSet, ZFSet.mem_powerset]; apply ZFSet.empty_subset⟩
            else failure
        else failure
      else failure
    else failure
  | @B.PHOAS.Term.all _ n D P => do
    -- denote_aux.all ⟦D⟧ᴮ (λ z => ⟦P z⟧ᴮ) h
    -- let ⟨𝒟, _⟩ ← denoteD ⟨Γ, .set (Fin.foldl (n-1) (λ d ⟨i, hi⟩ => d ×ᴮ αs ⟨i+1, Nat.add_lt_of_lt_sub hi⟩) (αs ⟨0, n_pos⟩)), PHOAS.Typing.all_dom h⟩
    let ⟨𝒟, .set τ, h𝒟⟩ ← ⟦D⟧ᴮ | failure
    if hτ : τ.hasArity n then
      if den_P : ∀ {x}, ZFSet.ofFinDom x ∈ 𝒟 → ⟦P x⟧ᴮ.isSome then
        if typP_det : ∀ x y, (x_𝒟 : ZFSet.ofFinDom x ∈ 𝒟) → (y_𝒟 : ZFSet.ofFinDom y ∈ 𝒟) → ⟦P x⟧ᴮ.get (den_P x_𝒟) |>.2.1 = (⟦P y⟧ᴮ.get (den_P y_𝒟) |>.2.1) then
          /- compute the denotation of `P` -/
          let ℙ (x : ZFSet) :=
            if hx : x.hasArity n ∧ x ∈ τ.toZFSet then
              let xₙ : Fin n → Dom := fun i => ⟨x.get n i, τ.get n i, get_mem_type_of_isTuple hx.1 hτ hx.2⟩
              match ⟦P xₙ⟧ᴮ  with
              | some ⟨Px, _, _⟩ => Px
              | none => ZFSet.zffalse
            else ZFSet.zffalse
          return ⟨ZFSet.sInter (ZFSet.𝔹.sep fun (y : ZFSet) => ∃ x ∈ 𝒟, y = ℙ x), .bool, ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 λ _ => id⟩
        else failure
      else failure
    else failure

end Denotation

notation "⟦" t "⟧ᴮ" => denote t

end B
