import B.SemanticsPHOAS
import B.Environment

namespace B

def ProofObligation.fvars (PO : ProofObligation) : Set 𝒱 :=
  (PO.hyps.map fv ++ PO.goals.map (λ sg => fv sg.goal)).flatten.toFinset.toSet \ (PO.defs.map fv).flatten.toFinset.toSet

def ProofObligation.defines (PO : ProofObligation) : Set 𝒱 :=
  go PO.defs ∅
  where
    go : List Term → Set 𝒱 → Set 𝒱
    | [], acc => acc
    | d :: defs, acc =>
      go defs <| acc ∪ (fv d).toFinset

abbrev ProofObligation.isClosed (PO : ProofObligation) := PO.fvars = ∅

namespace PHOAS

structure SimpleGoal (𝒱) where
  hyps : List <| Term 𝒱
  goal : Term 𝒱
  deriving Inhabited

structure SimpleGoal.WF {𝒱} [DecidableEq 𝒱] (sg : SimpleGoal 𝒱) (Γ : TypeContext 𝒱) where
  hyps_wf {h : Term 𝒱} (hh : h ∈ sg.hyps) : Γ ⊢ h : .bool
  goal_wf : Γ ⊢ sg.goal : .bool

structure ProofObligation (𝒱) where
  defs : List <| Term 𝒱
  hyps : List <| Term 𝒱
  goals : List <| SimpleGoal 𝒱

structure ProofObligation.WF {𝒱} [DecidableEq 𝒱] (PO : ProofObligation 𝒱) (Γ : TypeContext 𝒱) where
  TC_wf (d : Term 𝒱) (hd : d ∈ PO.defs) : match d with
    | .eq (.var v) _ | .mem (.var v) _ => Γ v |>.isSome
    | _ => False
  defs_wf (d : Term 𝒱) (hd : d ∈ PO.defs) : Γ ⊢ d : .bool
  hyps_wf (h : Term 𝒱) (hh : h ∈ PO.hyps) : Γ ⊢ h : .bool
  goals_wf (sg : SimpleGoal 𝒱) (hsg : sg ∈ PO.goals) : sg.WF Γ

end PHOAS

def ProofObligation.abstract {𝒱} (PO : B.ProofObligation) (ρ : B.𝒱 → Option 𝒱) (hρ : ∀ {t}, ∀ v ∈ fv t, (ρ v).isSome = true) : PHOAS.ProofObligation 𝒱 where
  defs := PO.defs.map abs
  hyps := PO.hyps.map abs
  goals := PO.goals.map (λ sg => {
      hyps := sg.hyps.map abs
      goal := abs sg.goal})
  where abs := (·.abstract ρ hρ)


-- def PO : B.ProofObligation where
--   defs := [.var "x" ∈ᴮ .ℤ]
--   hyps := [.var "x" =ᴮ .int 0]
--   goals := [{hyps := [], goal := .all ["y"] .ℤ (.var "y" ≤ᴮ .var "x")}]

-- example : (PO.abstract (fun | "x" => some (ZFSet.ZFNat.ofNat 1) | _ => none) (by admit)).goals.head!.goal = (.all .ℤ fun v : Fin 1 → _ => .var (v 0) ≤ᴮ' .var ((ZFSet.ZFNat.ofNat 1))) := by
--   unfold PO
--   dsimp [B.ProofObligation.abstract]
--   rw [ProofObligation.abstract.abs]
--   simp [Term.abstract, Function.OfArity.uncurry, Function.FromTypes.uncurry, Term.abstract.go]

section Denotation

namespace PHOAS

noncomputable def mk_conj (Γ : TypeContext ZFSet) {PO_item : List (Term ZFSet)} : List {x : Term ZFSet // x ∈ PO_item} → (_ : ∀ x ∈ PO_item, Γ ⊢ x : .bool) → ZFSet.ZFBool → Option ZFSet.ZFBool
  | [], _, acc => acc
  | ⟨h, hh⟩ :: hyps, h', acc => do
    let H ← ⟦h⟧ᴮ ⟨Γ , .bool, h' h hh⟩
    let out ← mk_conj Γ hyps h' acc
    return H ⋀ out

noncomputable def SimpleGoal.denote (sg : PHOAS.SimpleGoal ZFSet) (Γ : TypeContext ZFSet) (wf : sg.WF Γ) : Option ZFSet.ZFBool := do
  let SG ← ⟦sg.goal⟧ᴮ ⟨Γ ,.bool, wf.goal_wf⟩
  let Hyps ← mk_conj Γ sg.hyps.attach (fun _ => wf.hyps_wf) ⊤
  return Hyps ⇒ SG

noncomputable def ProofObligation.denote (PO : PHOAS.ProofObligation ZFSet) (Γ : TypeContext ZFSet) (wf : PO.WF Γ) : Option ZFSet.ZFBool := do
  let Defs ← mk_conj Γ PO.defs.attach wf.defs_wf ⊤
  let Hyps ← mk_conj Γ PO.hyps.attach wf.hyps_wf ⊤
  let Goals ← mk_conj_goals PO.goals.attach wf.goals_wf ⊤
  return Defs ⇒ Hyps ⇒ Goals
where
  mk_conj_goals {goals : List (SimpleGoal ZFSet)} : List {x : SimpleGoal ZFSet // x ∈ goals} → (_ : ∀ g ∈ goals, g.WF Γ) → ZFSet.ZFBool → Option ZFSet.ZFBool
  | [], _, acc => acc
  | ⟨sg, hsg⟩ :: goals, h, acc => do
    let G ← @sg.denote Γ (h sg hsg)
    let out ← mk_conj_goals goals h acc
    return G ⋀ out

end PHOAS

end Denotation

section

variable (PO : B.ProofObligation) (ρ : B.𝒱 → Option ZFSet) (hρ : ∀ {t}, ∀ v ∈ fv t, (ρ v).isSome = true) (Γ : PHOAS.TypeContext ZFSet)

theorem PHOAS.ProofObligation.ofAbstractWF : PHOAS.ProofObligation.WF (PO.abstract ρ hρ) Γ where
  TC_wf := sorry
  defs_wf := sorry
  hyps_wf := sorry
  goals_wf := sorry

#check PHOAS.ProofObligation.denote (PO.abstract ρ hρ) Γ

end

end B
