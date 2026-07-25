import Lean.Data.Xml
import Extra.Utils
import B.Environment
import Batteries.CodeAction

open Batteries Lean B

instance : Inhabited Xml.Element := ⟨⟨"", Std.TreeMap.empty, #[]⟩⟩

structure DecoderState where
  env : Env
  types : Array BType

instance : EmptyCollection DecoderState where
  emptyCollection := { env := ∅, types := #[] }

abbrev Decoder := StateT DecoderState (ExceptT String IO)

instance : ToString DecoderState where
  toString st := s!"⟪env:\n{st.env}\ntypes:\n{st.types}⟫"

def incrementFreshVarC : Decoder Nat :=
  modifyGet λ st => (st.env.freshvarsc, { st with env := { st.env with freshvarsc := st.env.freshvarsc + 1 } })

def addFunctionFlag (name : String) : Decoder Unit :=
  modifyGet λ st => ((), { st with env := { st.env with flags := st.env.flags.insert name } })

def addToContext (v : String) (τ : BType) : Decoder Unit :=
  modify λ st => { st with env := { st.env with context := st.env.context.insert v τ } }

def freshVar (τ : BType) : Decoder 𝒱 := do
  let x := s!"x{← incrementFreshVarC}"
  addToContext x τ
  return x

def freshVarList : List BType → Decoder (List 𝒱)
  | [] => return []
  | τ::τs => .cons <$> freshVar τ <*> freshVarList τs

def getQuantifier : String → Decoder (List 𝒱 → B.Term → B.Term → B.Term)
  | "!" => pure .all
  | "#" => pure .exists
  | "%" => pure .lambda
  | s => throw s!"Unknown quantifier {s}"

/-- Quantified *expressions*.  `%` is λ-abstraction and is handled by
`getQuantifier`; `UNION`/`INTER` build a set and so need the result type and a
fresh variable, hence the `Decoder`-valued body.

`UNION vs.(P | E)` is `{y | ∃ vs ∈ {vs | P}. y ∈ E}` and `INTER` is the same
with `∀`. -/
def getExpQuantifier (kind : String) (τ : BType) :
    Decoder (List 𝒱 → B.Term → B.Term → Decoder B.Term) :=
  match kind with
  | "iSIGMA" | "iPI" =>
    -- `SIGMA vs.(P | E)` sums `E` over `{vs | P}`, which is exactly folding the
    -- function `λ vs ∈ {vs | P}. E`.
    return fun vs D E => return .fold (kind == "iSIGMA") (.lambda vs D E)
  | "UNION" | "INTER" => do
    let .set σ := τ | throw s!"{kind} expects a set type, got {τ}"
    let quant := if kind == "UNION" then B.Term.exists else B.Term.all
    return fun vs D E => do
      let y ← freshVar σ
      return .collect [y] σ.toTerm (quant vs D (.var y ∈ᴮ E))
  | k => do
    let q ← getQuantifier k
    return fun vs D E => return q vs D E

def stackQuantifiers : List 𝒱 → B.Term → (𝒱 → B.Term → B.Term → B.Term) → Decoder B.Term
  | [], b, _ => pure b
  | v::vs, b, q => do
    let D := ((← get).env.context.find? v |>.get!).toTerm
    return q v D (← stackQuantifiers vs b q)

def mkMapletfromType : List B.Term → BType → Decoder B.Term
  | x::xs, .prod _ β => .maplet x <$> (mkMapletfromType xs β) -- check that ⊢ x : _?
  | [x], _ => return x
  | _, _ => throw "mkMapletfromType: Empty list or malformed type"

def B.BType.getFunctionType : BType → Decoder (BType × BType)
  | .set (.set (.prod τ σ)) => return ⟨τ, σ⟩
  | ξ => throw s!"Cannot cast {ξ} to a function type"

def B.Term.getType : Term → Decoder B.BType
  | .var v => return (← get).env.context.find? v |>.get!
  | .int _ | .add _ _ | .sub _ _ | .mul _ _ | .card _
  | .div _ _ | .mod _ _ | .exp _ _
  -- `min`/`max` take a set of integers to an integer.
  | .min _ | .max _ | .fold _ _ => return .int
  | .bool _ | .finite _ => return .bool
  | .maplet x y => return .prod (← x.getType) (← y.getType)
  | .le _ _ | .and _ _ | .not _ | .eq _ _ | .mem _ _ | .all _ _ _ => return .bool
  | .ℤ => return .set .int
  | .𝔹 => return .set .bool
  | .collect _ D _ => return ← D.getType
  | .pow S => return .set (← S.getType)
  | .cprod S T => do
    match ← S.getType, ← T.getType with
    | .set α, .set β => return .set (.prod α β)
    | τ, σ => throw s!"Cannot form cartesian product of {τ} and {σ}"
  | .union S _ | .inter S _ | .closure _ S | .iterate S _ => return (← S.getType)
  | .app f x => do
    match ← f.getType with
    | .set (.prod τ σ) =>
      let ξ ← x.getType
      if τ = ξ then return σ else throw s!"Type mismatch: {τ} ≠ {ξ}"
    | _ => throw s!"Expected a function type, got {← f.getType}"
  | .lambda _ D P => do
    match ← D.getType with
    | .set δ => return .set (.prod δ (← P.getType))
    | τ => throw s!"B.Term.getType:lambda: Expected a set type, got {τ}"
  | .pfun A B => return .set (.prod (← A.getType) (← B.getType))
