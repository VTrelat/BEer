import SMT.HOTyping
import Extra.ZFC_Extra

noncomputable section

namespace SMT
namespace SMTType

abbrev toZFSet : SMTType → ZFSet
  | .bool => ZFSet.𝔹
  | .int => ZFSet.Int
  | .unit => {∅}
  | .fun τ σ => (τ.toZFSet).funs σ.toZFSet
  | .option τ => ZFSet.Option.toZFSet τ.toZFSet
  | .pair α β => α.toZFSet.prod β.toZFSet
notation:max "⟦" z "⟧ᶻ" => SMTType.toZFSet z

def default {𝒱} : SMTType → PHOAS.Term 𝒱
  | .int => .int 0
  | .bool => .bool false
  | .pair α β => .pair α.default β.default
  | .option α => .none α
  | .«fun» α β => @PHOAS.Term.lambda 𝒱 1 (fun _ ↦ α) (fun _ ↦ β.default)
  | .unit => .«()»

def defaultZFSet.{u} : SMTType → ZFSet.{u}
  | .int => ZFSet.ofInt 0
  | .bool => ZFSet.zffalse
  | .pair α β => α.defaultZFSet.pair β.defaultZFSet
  | .option α => (ZFSet.Option.none (S := α.toZFSet)).1
  | .«fun» α β => (α.toZFSet.prod β.toZFSet).sep fun z ↦ z.π₂ = β.defaultZFSet
  | .unit => ∅

theorem default_type_correct {𝒱} [DecidableEq 𝒱] {Γ : PHOAS.TypeContext 𝒱} (τ : SMTType) : Γ ⊢ τ.default : τ := by
  induction τ generalizing Γ with
  | bool => apply PHOAS.Typing.bool
  | int => apply PHOAS.Typing.int
  | unit => apply PHOAS.Typing.«()»
  | «fun» τ σ τ_ih σ_ih => apply PHOAS.Typing.lambda _ _ _ _ (fun _ ↦ σ_ih) Nat.one_pos
  | option τ ih => apply PHOAS.Typing.none
  | pair α β α_ih β_ih => apply PHOAS.Typing.pair _ _ _ _ _ α_ih β_ih

theorem mem_toZFSet_of_defaultZFSet {α : SMTType} : α.defaultZFSet ∈ α.toZFSet := by
  induction α with
  | bool => exact ZFSet.ZFBool.zffalse_mem_𝔹
  | int => exact ZFSet.mem_ofInt_Int 0
  | unit => exact ZFSet.mem_singleton.mpr rfl
  | «fun» α β α_ih β_ih =>
    rw [SMTType.defaultZFSet, SMTType.toZFSet, ZFSet.mem_funs]
    and_intros
    · exact ZFSet.sep_subset_self
    · intro x x_mem_α
      exists β.defaultZFSet
      and_intros
      · beta_reduce
        rw [ZFSet.mem_sep, ZFSet.pair_mem_prod, ZFSet.π₂_pair, eq_self, and_true]
        exact ⟨x_mem_α, β_ih⟩
      · intro y hy
        rw [ZFSet.mem_sep, ZFSet.pair_mem_prod, ZFSet.π₂_pair] at hy
        exact hy.2
  | option τ ih => exact SetLike.coe_mem ZFSet.Option.none
  | pair α β α_ih β_ih =>
    rw [SMTType.defaultZFSet, SMTType.toZFSet, ZFSet.pair_mem_prod]
    and_intros <;> assumption

theorem toZFSet_nonempty {α : SMTType} : α.toZFSet ≠ ∅ := by
  induction α with
  | bool =>
    rw [SMTType.toZFSet]
    exact ZFSet.ZFBool.𝔹.nonempty
  | int =>
    rw [SMTType.toZFSet]
    exact ZFSet.Int.nonempty
  | unit =>
    rw [SMTType.toZFSet]
    intro contr
    rw [ZFSet.ext_iff] at contr
    simp only [ZFSet.mem_singleton, ZFSet.notMem_empty, iff_false, forall_eq] at contr
  | «fun» arg ret arg_ih ret_ih => exact ZFSet.funs.nonempty ret_ih
  | option τ ih =>
    rw [SMTType.toZFSet, ZFSet.Option.toZFSet]
    intro contr
    rw [ZFSet.ext_iff] at contr
    specialize contr <| ZFSet.pair ZFSet.ZFBool.false ∅
    simp at contr
  | pair α β α_ih β_ih =>
    rw [SMTType.toZFSet]
    intro contr
    rw [ZFSet.ext_iff] at contr
    obtain ⟨a, ha⟩ := ZFSet.nonempty_exists_iff.mp α_ih
    obtain ⟨b, hb⟩ := ZFSet.nonempty_exists_iff.mp β_ih
    specialize contr <| ZFSet.pair a b
    rw [ZFSet.pair_mem_prod] at contr
    nomatch ZFSet.notMem_empty (a.pair b) <| contr.mp ⟨ha, hb⟩

example {τ : SMTType} : ∀ x : ZFSet.Option τ.toZFSet, x.1 ∈ (SMTType.option τ).toZFSet := λ ⟨_,h⟩ => h
example {τ : SMTType} : ∀ x ∈ (SMTType.option τ).toZFSet, x ∈ (ZFSet.prod ({↑ZFSet.ZFBool.false} : ZFSet) {∅}) ∪ ({↑ZFSet.ZFBool.true} : ZFSet).prod τ.toZFSet := λ _ => id

end SMTType

section Semantics

set_option hygiene false
local notation "⟦" t "⟧ˢ" => denote t

abbrev Dom := Σ' (x : ZFSet) (τ : SMTType), x ∈ τ.toZFSet
instance : Inhabited Dom := ⟨ZFSet.ofInt 0, .int, ZFSet.mem_ofInt_Int 0⟩

open Classical SMT.PHOAS in
def denote_distinct : List Dom → ZFSet.ZFBool
  | [] => ⊤
  | x::xs =>
    let not_mem := ZFSet.ZFBool.ofBool <| decide <| x ∉ xs
    let dist := denote_distinct xs
    ⟨not_mem ⋀ᶻ dist, overloadBinOp_𝔹_endo (fun _ _ ↦ Subtype.property _)⟩

open Classical PHOAS in
def denote : PHOAS.Term Dom → Option Dom
  | .var v => return v
  | .int n => return ⟨.ofInt n, .int, ZFSet.mem_ofInt_Int n⟩
  | .bool b => return ⟨ZFSet.ZFBool.ofBool b, .bool, ZFSet.ZFBool.mem_ofBool_𝔹 b⟩
  | .app f x => do
    let ⟨F, .fun σ τ, hF⟩ ← ⟦f⟧ˢ | failure
    let ⟨X, σ', hX⟩ ← ⟦x⟧ˢ
    if σ_eq_σ' : σ = σ' then
      if ispfun : F.IsPFunc σ.toZFSet τ.toZFSet then
        if X_dom : X ∈ F.Dom then
          let ⟨Y, hY⟩ := F.fapply ispfun ⟨X, X_dom⟩
          return ⟨Y, τ, hY⟩
        else failure
      else failure
    else failure
  | @SMT.PHOAS.Term.lambda _ n τs t => do
    if n_pos : n > 0 then
      if den_t_isSome : ∀ {x : Fin n → Dom}, (∀ i, (x i).1 ∈ (τs i).toZFSet) → ⟦t x⟧ˢ.isSome then
        if den_t_typ_det : ∀ x y : Fin n → Dom, (hx : ∀ i, (x i).1 ∈ (τs i).toZFSet) → (hy : ∀ i, (y i).1 ∈ (τs i).toZFSet) → ⟦t x⟧ˢ.get (den_t_isSome hx) |>.2.1 = (⟦t y⟧ˢ.get (den_t_isSome hy) |>.2.1) then
          -- compute the return type
          let xₙ : Fin n → Dom := fun i ↦ ⟨(τs i).defaultZFSet, τs i, SMTType.mem_toZFSet_of_defaultZFSet⟩
          let γ := ⟦t xₙ⟧ˢ.get (den_t_isSome (fun i ↦ SMTType.mem_toZFSet_of_defaultZFSet)) |>.2.1
          let τ : SMTType := Fin.foldr (n-1) (fun ⟨i, hi⟩ acc ↦ (τs ⟨i, Nat.lt_of_lt_pred hi⟩).pair acc) (τs ⟨n-1, Nat.sub_one_lt_of_lt n_pos⟩)

          have γ_out (x : Fin n → Dom) (hx : ∀ i, (x i).1 ∈ (τs i).toZFSet) :
              ⟦t x⟧ˢ.get (den_t_isSome hx) |>.2.1 = γ := by
            specialize den_t_typ_det x xₙ hx ?_
            · intro
              exact SMTType.mem_toZFSet_of_defaultZFSet
            · exact den_t_typ_det

          -- compute the denotation of `t`
          let T (x : ZFSet) : ZFSet :=
            if hx : x.hasArity n ∧ (∀ i, x.get n i ∈ (τs i).toZFSet) then
              let xₙ : Fin n → Dom := fun i ↦ ⟨x.get n i, τs i, hx.2 i⟩
              ⟦t xₙ⟧ˢ.get (den_t_isSome hx.2) |>.1
            else γ.defaultZFSet

          have range_T {x : ZFSet} (hx : x ∈ τ.toZFSet) : T x ∈ γ.toZFSet := by
            unfold T
            split_ifs with cond
            · extract_lets xₙ
              specialize γ_out xₙ ?_
              · exact cond.2
              · rw [←γ_out]
                exact ⟦t xₙ⟧ˢ.get _ |>.2.2
            · exact SMTType.mem_toZFSet_of_defaultZFSet

          return ⟨ZFSet.lambda τ.toZFSet γ.toZFSet T, τ.fun γ, ZFSet.mem_funs_of_lambda range_T⟩
        else failure
      else failure
    else failure
  | @PHOAS.Term.forall _ n τs P => do
    if n_pos : n > 0 then
      if den_t_isSome : ∀ {x : Fin n → Dom}, (∀ i, (x i).1 ∈ (τs i).toZFSet) → ⟦P x⟧ˢ.isSome then
        -- compute the denotation of `P`
        let ℙ (xy : ZFSet) :=
          if hxy : xy.hasArity 2 then
            let x := xy.π₁
            let y := xy.π₂
            if hx : x.hasArity n ∧ (∀ i, x.get n i ∈ (τs i).toZFSet) then
              ⟦P (fun i => ⟨x.get n i, τs i, hx.2 i⟩)⟧ˢ.get (den_t_isSome hx.2) |>.1
            else ZFSet.zffalse
          else ZFSet.zffalse
        let 𝒟 := Fin.foldl (n-1) (fun acc ⟨i, hi⟩ ↦ acc.prod (τs ⟨i+1, Nat.add_lt_of_lt_sub hi⟩).toZFSet) (τs ⟨0, n_pos⟩).toZFSet
        return ⟨ZFSet.sInter (ZFSet.𝔹.sep fun y ↦ ∃ x ∈ 𝒟, y = ℙ x : ZFSet), .bool, ZFSet.sInter_sep_subset_of_𝔹_mem_𝔹 fun _ ↦ id⟩
      else failure
    else failure
  -- | @PHOAS.Term.exists _ n τs P =>
  --   if n_pos : n > 0 then
  --     if den_t_isSome : ∀ {x : Fin n → Dom}, (∀ i, (x i).1 ∈ (τs i).toZFSet) → ⟦P x⟧ˢ.isSome then
  --       -- compute the denotation of `P`
  --       let ℙ (xy : ZFSet) :=
  --         if hxy : xy.hasArity 2 then
  --           let x := xy.π₁
  --           let y := xy.π₂
  --           if hx : x.hasArity n ∧ (∀ i, x.get n i ∈ (τs i).toZFSet) then
  --             ⟦P (fun i => ⟨x.get n i, τs i, hx.2 i⟩)⟧ˢ.get (den_t_isSome hx.2) |>.1
  --           else ZFSet.zffalse
  --         else ZFSet.zffalse
  --       let 𝒟 := Fin.foldl (n-1) (fun acc ⟨i, hi⟩ ↦ acc.prod (τs ⟨i+1, Nat.add_lt_of_lt_sub hi⟩).toZFSet) (τs ⟨0, n_pos⟩).toZFSet
  --       return ⟨⋃₀ ZFSet.𝔹.sep fun y ↦ ∃ x ∈ 𝒟, y = ℙ x, .bool, ZFSet.sUnion_sep_subset_of_𝔹_mem_𝔹 fun _ ↦ id⟩
  --     else failure
  --   else failure
  | x =ˢ' y => do
    let ⟨X, α, hX⟩ ← ⟦x⟧ˢ
    let ⟨Y, β, hY⟩ ← ⟦y⟧ˢ
    if α_eq_β : α = β then
      return ⟨X =ᶻ Y, .bool, overloadBinOp_mem hX (α_eq_β ▸ hY)⟩
    else failure
  | p ∧ˢ' q => do
    let ⟨P, .bool, hP⟩ ← ⟦p⟧ˢ | failure
    let ⟨Q, .bool, hQ⟩ ← ⟦q⟧ˢ | failure
    return ⟨P ⋀ᶻ Q, .bool, overloadBinOp_mem hP hQ⟩
  -- | p ∨ˢ' q => do
  --   let ⟨P, .bool, hP⟩ ← ⟦p⟧ˢ | failure
  --   let ⟨Q, .bool, hQ⟩ ← ⟦q⟧ˢ | failure
  --   return ⟨P ⋁ᶻ Q, .bool, overloadBinOp_mem hP hQ⟩
  | ¬ˢ' x => do
    let ⟨X, .bool, hX⟩ ← ⟦x⟧ˢ | failure
    return ⟨¬ᶻ X, .bool, overloadUnaryOp_mem⟩
  -- | p ⇒ˢ' q => do
  --   let ⟨P, .bool, hP⟩ ← ⟦p⟧ˢ | failure
  --   let ⟨Q, .bool, hQ⟩ ← ⟦q⟧ˢ | failure
  --   return ⟨P ⇒ᶻ Q, .bool, overloadBinOp_mem hP hQ⟩
  | .ite c t f => do
    let ⟨C, .bool, hC⟩ ← ⟦c⟧ˢ | failure
    if ZFSet.ZFBool.toBool ⟨C, hC⟩ then ⟦t⟧ˢ else ⟦f⟧ˢ
  | .some t => do
    let ⟨T, τ, hTτ⟩ ← ⟦t⟧ˢ
    return ⟨ZFSet.Option.some ⟨T, hTτ⟩ |>.1, τ.option, SetLike.coe_mem (ZFSet.Option.some ⟨T, hTτ⟩)⟩
  | .none τ =>
    return ⟨@ZFSet.Option.none τ.toZFSet |>.1, τ.option, SetLike.coe_mem ZFSet.Option.none⟩
  | .«()» =>
    return ⟨∅, .unit, ZFSet.mem_singleton.mpr rfl⟩
  | .the t => do
    let ⟨T, .option τ, hTτ⟩ ← ⟦t⟧ˢ | failure
    return ⟨ZFSet.Option.the SMTType.toZFSet_nonempty ⟨T, hTτ⟩, τ, SetLike.coe_mem _⟩
  | .pair x y => do
    let ⟨X, α, hX⟩ ← ⟦x⟧ˢ
    let ⟨Y, β, hY⟩ ← ⟦y⟧ˢ
    return ⟨X.pair Y, α.pair β, by
      rw [ZFSet.pair_mem_prod]
      exact ⟨hX, hY⟩⟩
  | .fst t => do
    let ⟨T, .pair α β, hT⟩ ← ⟦t⟧ˢ | failure
    return ⟨T.π₁, α, by
      rw [SMTType.toZFSet, ZFSet.mem_prod] at hT
      obtain ⟨T₁, hT₁, T₂, hT₂, rfl⟩ := hT
      rwa [ZFSet.π₁_pair]⟩
  | .snd t => do
    let ⟨T, .pair α β, hT⟩ ← ⟦t⟧ˢ | failure
    return ⟨T.π₂, β, by
      rw [SMTType.toZFSet, ZFSet.mem_prod] at hT
      obtain ⟨T₁, hT₁, T₂, hT₂, rfl⟩ := hT
      rwa [ZFSet.π₂_pair]⟩
  | x ≤ˢ' y => do
    let ⟨X, .int, hX⟩ ← ⟦x⟧ˢ | failure
    let ⟨Y, .int, hY⟩ ← ⟦y⟧ˢ | failure
    return ⟨X ≤ᶻ Y, .bool,  overloadBinOp_mem hX hY⟩
  | .add x y => do
    let ⟨X, .int, hX⟩ ← ⟦x⟧ˢ | failure
    let ⟨Y, .int, hY⟩ ← ⟦y⟧ˢ | failure
    return ⟨X +ᶻ Y, .int, overloadBinOp_mem hX hY⟩
  | .sub x y => do
    let ⟨X, .int, hX⟩ ← ⟦x⟧ˢ | failure
    let ⟨Y, .int, hY⟩ ← ⟦y⟧ˢ | failure
    return ⟨X -ᶻ Y, .int, overloadBinOp_mem hX hY⟩
  | .mul x y => do
    let ⟨X, .int, hX⟩ ← ⟦x⟧ˢ | failure
    let ⟨Y, .int, hY⟩ ← ⟦y⟧ˢ | failure
    return ⟨X *ᶻ Y, .int, overloadBinOp_mem hX hY⟩
  | @PHOAS.Term.distinct _ n ts => do
    let Ts ← List.ofFn (fun i ↦ ⟦ts i⟧ˢ) |>.allSome
    return ⟨denote_distinct Ts, .bool, by exact SetLike.coe_mem _⟩
end Semantics

notation "⟦" t "⟧ˢ" => denote t

end SMT
end
