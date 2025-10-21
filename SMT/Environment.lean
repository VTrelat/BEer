import SMT.Typing
import Extra.Prettifier
import Extra.Utils

open Batteries

namespace SMT

inductive Instr
  | declare_const (v : 𝒱) (τ : SMTType)
  | define_fun (v : 𝒱) (τ : SMTType) (σ : SMTType) (t : Term)
  | define_const (v : 𝒱) (τ : SMTType) (t : Term)
  | assert (t : Term)
  | push (n : Nat)
  | pop (n : Nat)
  | check_sat
  deriving Inhabited, BEq

def Instr.toString : Instr → String
  | .declare_const v τ => s!"(declare-const {v} {SMTType.toString τ})"
  | .define_fun v τ σ t => s!"(define-fun {v} {SMTType.toString τ} {SMTType.toString σ} {Term.toString t})"
  | .define_const v τ t => s!"(define-const {v} {SMTType.toString τ} {Term.toString t})"
  | .assert t => s!"(assert {Term.toString t})"
  | .push n => s!"(push {n})"
  | .pop n => s!"(pop {n})"
  | .check_sat => "(check-sat)"

instance : ToString Instr := ⟨Instr.toString⟩

abbrev Chunk := List Instr

inductive Stages where
  | instr : Chunk → SMT.Stages
  | asserts : List SMT.Stages → SMT.Stages
  deriving Inhabited

def Stages.toString' : Stages → (indent : Nat := 0) → String
  | .instr is, n => s!"{"  ".dup n}instr [" :: is.map (λ i => s!"{"  ".dup (n+1)}{i}") ++ [s!"{"  ".dup n}]"] |> String.intercalate "\n"
  | .asserts as, n => s!"{"  ".dup n}asserts [" :: as.map (λ a => a.toString' (n+1)) ++ [s!"{"  ".dup n}]"] |> String.intercalate "\n"

def Stages.toList : SMT.Stages → (n : Nat := 0) → List (Nat × Instr)
  | .instr is, n => is.map (λ i => (n, i))
  | .asserts as, n => (n, Instr.push 1) :: ((as.attach.map (λ ⟨a, _⟩ => a.toList (n+1))) |>.flatten) ++ [(n, Instr.pop 1)]
termination_by s => s
decreasing_by
  all_goals simp_wf
  decreasing_trivial

instance : ToString Stages where
  toString := λ s => String.intercalate "\n" <| s.toList.map λ ⟨n, a⟩ => s!"{"  ".dup n}{a}"

def Stages.map (f : Chunk → Chunk) : Stages → Stages
  | .instr is => .instr (f is)
  | .asserts as => .asserts (as.attach.map (λ ⟨a,_⟩ => a.map f))

structure Env where
  declarations : Chunk := []
  asserts : Stages := .asserts []
  freshvarsc : Nat := 0
  deriving Inhabited

instance : ToString Env where
  toString E :=
    let nl := "\n"
    let nltab := nl++"  "
    s!"Env:{nltab}declarations:{nl}{E.declarations.printLines}{nltab}asserts:{nl}{E.asserts}"

end SMT
