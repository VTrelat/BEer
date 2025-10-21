import SMT.HOTyping
import Extra.Prettifier
import Extra.Utils

open Batteries

namespace SMT.PHOAS

inductive Instr (𝒱)
  | declare_const (v : 𝒱) (τ : SMTType)
  | define_fun (v : 𝒱) (τ : SMTType) (σ : SMTType) (t : Term 𝒱)
  | define_const (v : 𝒱) (τ : SMTType) (t : Term 𝒱)
  | assert (t : Term 𝒱)
  | push (n : Nat)
  | pop (n : Nat)
  | check_sat
  deriving Inhabited

abbrev Chunk 𝒱 := List (Instr 𝒱)

inductive Stages 𝒱 where
  | instr : Chunk 𝒱 → Stages 𝒱
  | asserts : List (Stages 𝒱) → Stages 𝒱
  deriving Inhabited

def Stages.toList {𝒱} : Stages 𝒱 → (n : Nat := 0) → List (Nat × (Instr 𝒱))
  | .instr is, n => is.map (λ i => (n, i))
  | .asserts as, n => (n, PHOAS.Instr.push 1) :: ((as.attach.map (λ ⟨a, _⟩ => a.toList (n+1))) |>.flatten) ++ [(n, PHOAS.Instr.pop 1)]
termination_by s => s
decreasing_by
  all_goals simp_wf
  decreasing_trivial

def Stages.map {𝒱} (f : Chunk 𝒱 → Chunk 𝒱) : Stages 𝒱 → Stages 𝒱
  | .instr is => .instr (f is)
  | .asserts as => .asserts (as.attach.map (λ ⟨a,_⟩ => a.map f))

structure Env (𝒱) where
  declarations : Chunk 𝒱 := []
  asserts : Stages 𝒱 := .asserts []
  freshvarsc : Nat := 0
  deriving Inhabited

end SMT.PHOAS
