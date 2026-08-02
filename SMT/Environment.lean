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

/-- The same instructions as `toList`, without the `push`/`pop` bracketing.

A script that holds a single `check-sat` never returns to a popped scope, so the
brackets say nothing there — they only force the solver into incremental mode.
`--per-goal` renders through this; every other path keeps the nesting. -/
def Stages.toFlatList : SMT.Stages → Chunk
  | .instr is => is
  | .asserts as => (as.attach.map (λ ⟨a, _⟩ => a.toFlatList)) |>.flatten
termination_by s => s
decreasing_by
  all_goals simp_wf
  decreasing_trivial

def Stages.toFlatString (s : Stages) : String :=
  String.intercalate "\n" <| s.toFlatList.map Instr.toString

def Stages.map (f : Chunk → Chunk) : Stages → Stages
  | .instr is => .instr (f is)
  | .asserts as => .asserts (as.attach.map (λ ⟨a,_⟩ => a.map f))

structure Env where
  /-- Emitted in order.  An array rather than a `Chunk`: the encoder appends
  one instruction at a time, and `List.concat` made that quadratic. -/
  declarations : Array Instr := #[]
  asserts : Stages := .asserts []
  freshvarsc : Nat := 0
  /-- Every name ever handed out, as a set: `freshVar` tests it on every call,
  which was the dominant cost when it was a list. -/
  usedVars : Std.HashSet SMT.𝒱 := ∅
  deriving Inhabited

/-- The names an instruction *uses*, as opposed to the one it introduces.

`Term.builtin` heads are not counted: they name prelude symbols (`bdiv`,
`bmod`, `bpow`), which are never `declare-const`s. -/
def Instr.refs : Instr → List 𝒱
  | .define_fun _ _ _ t | .define_const _ _ t | .assert t => fv t
  | .declare_const _ _ | .push _ | .pop _ | .check_sat => []

def Stages.refs : Stages → List 𝒱
  | .instr is => (is.map Instr.refs).flatten
  | .asserts as => (as.attach.map (λ ⟨a, _⟩ => a.refs)).flatten
termination_by s => s
decreasing_by
  all_goals simp_wf
  decreasing_trivial

/-- Drop the `declare-const`s nothing refers to.

`freshVar` records every generated name in the type context, and the
bulk-declare passes turn whatever is left there into a declaration.  A binder
variable that survives its `eraseFromContext` therefore reaches the file as a
free constant occurring nowhere else — measured at 2032 of the 2919
declarations of a median per-goal script, a quarter of its bytes.  An
unconstrained constant says nothing logically, but it is still a term the
solver's quantifier instantiation has to consider, so it is not free.

Only `declare-const` is dropped: a `define-fun` may be the definition that a
later `assert` names, and a name that occurs solely as a binder is shadowed
there anyway, so it is right for it not to count as a use. -/
def Env.pruneUnused (E : Env) : Env :=
  let used : Std.HashSet 𝒱 :=
    ((E.declarations.toList.map Instr.refs).flatten ++ E.asserts.refs).foldl
      (·.insert ·) ∅
  { E with declarations := E.declarations.filter fun
      | .declare_const v _ => used.contains v
      | _ => true }

instance : ToString Env where
  toString E :=
    let nl := "\n"
    let nltab := nl++"  "
    s!"Env:{nltab}declarations:{nl}{E.declarations.toList.printLines}{nltab}asserts:{nl}{E.asserts}{nltab}usedVars: {E.usedVars.toList}"

end SMT
