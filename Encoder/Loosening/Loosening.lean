import Encoder.Basic
import Encoder.Simplifier
import Encoder.Loosening.Rules
open SMT

/-- Reify an option-valued function as its graph, leaving anything else alone.

Used as `castEq`'s last resort: the relational operators now *preserve* the
partial-function representation, so an equality can have one side stored as
`α → Option β` and the other as the characteristic predicate of its graph, with
the two also disagreeing on the representation of the *element* type.  The
castable relation relates one such change at a time, not both at once; putting
both sides in graph form first is what the derived comprehensions used to do
unconditionally. -/
private def reifyGraph (name : String) (t : Term) (τ : SMTType) :
    Encoder (Term × SMTType) :=
  match τ with
  | .fun α (.option β) => do
    let ⟨g, spec⟩ ← loosenAux_prf name
      (castPath.graph (castPath.reflexive α) (castPath.reflexive β)) t
    declareConstWithSpec g (.fun (.pair α β) .bool) spec
    return (.var g, .fun (.pair α β) .bool)
  | _ => return (t, τ)

private def castEqCore : Term × SMTType → Term × SMTType → Encoder (Term × SMTType) | (A, α), (B, β) => do
  if h : α = β then do
    /-
      A : α    B : β    α = β
      -----------------------
      A = B    ↪    A =ˢ B
    -/
    return (A =ˢ B, .bool)
  else if h : α ⊑ β then
    let ⟨A!, A!_spec⟩ ← loosenAux_prf "eq!" (castable?.toCastPath h) A
    declareConstWithSpec A! β A!_spec
    return (((.var A!) =ˢ B) ∧ˢ A!_spec, .bool)
  else if h : β ⊑ α then
    let ⟨B!, B!_spec⟩ ← loosenAux_prf "eq!" (castable?.toCastPath h) B
    declareConstWithSpec B! α B!_spec
    return (((.var B!) =ˢ A) ∧ˢ B!_spec, .bool)
  else throw s!"castEq: Failed to unify {α} with {β}"

def castEq (a b : Term × SMTType) : Encoder (Term × SMTType) := do
  try castEqCore a b
  catch e =>
    let (A, α) ← reifyGraph "eq!" a.1 a.2
    let (B, β) ← reifyGraph "eq!" b.1 b.2
    -- Nothing to reify means the original failure stands.
    if α == a.2 && β == b.2 then throw e else castEqCore (A, α) (B, β)

/-- A loosening of `x` to `β`, shared with any earlier occurrence of the same
term at the same target type.

Two loosenings of one term along one type change have the same specification,
so sharing them is a matter of not saying the same thing twice.  Only for
callers that do *not* thread the specification into the term they return: the
specification is asserted once, next to the declaration.  Sites are cleared per
obligation and hidden at binders, so a shared constant is never referred to
from a scope it is not declared in. -/
private def loosenShared (name : String) {α β : SMTType} (c : α ~> β) (x : Term) :
    Encoder 𝒱 := do
  let op := s!"loosen:{β}"
  if let some v ← findSite op x then return v
  let ⟨x!, spec⟩ ← loosenAux_prf name c x
  declareConstWithSpec x! β spec
  recordSite op x β x!
  return x!

/-- The partial-function form of an encoded relation `R : (τ × σ) → bool`,
pinned down by `R⟨u,v⟩ ↔ f u = some v`.

Memoised on `R`, like the `card`/`finite` sites: a machine that applies the
same function three times used to get three constants, three copies of that
axiom, and the obligation to prove them equal before any of them could be used.
The site table is cleared per obligation and hidden at binders, so the sharing
never crosses a scope the constant is not declared in. -/
private def asPartialFun (R : Term) (τ σ : SMTType) : Encoder 𝒱 := do
  if let some c ← findSite "asFun" R then return c
  let f ← freshVar (τ.fun (.option σ)) "app!"
  declareConst f (τ.fun (.option σ))
  let u ← freshVar τ
  let v ← freshVar σ
  let spec : Term := .forall [u, v] [τ, σ] (.eq
    (.app R (.pair (.var u) (.var v)))
    (.eq (.app (.var f) (.var u)) (.some (.var v))))
  -- `u` and `v` occur only below the universal binder.
  eraseFromContext u
  eraseFromContext v
  addSpec f spec
  recordSite "asFun" R τ f
  return f

def castApp : Term × SMTType → Term × SMTType → Encoder (Term × SMTType)
  | (f, .fun (.pair τ σ) .bool), (x, ξ) => do
    /- NOTE: This is the only special case where a relation is cast to a function -/
    if h : τ ⊑ ξ then
      -- loosen f
      let «f!» ← loosenShared "app!" (β := (.fun (.pair ξ σ) .bool)) (.chpred (.pair h.toCastPath (castPath.reflexive σ))) f

      -- cast to function
      let f!! ← asPartialFun (.var «f!») ξ σ
      return (.the (.app (.var «f!!») x), σ)
    else if h : ξ ⊑ τ then
      -- loosen x
      let x! ← loosenShared "app!" h.toCastPath x

      -- cast to function
      let «f!» ← asPartialFun f τ σ
      return (.the (.app (.var «f!») (.var x!)), σ)
    else throw s!"encodeTerm:app: Failed to unify {τ} with {ξ}"
  | (f, .fun α .bool), (x, α') => do
    if h : α ⊑ α' then
      let «f!» ← loosenShared "app!" (castPath.chpred h.toCastPath) f
      return (.app (.var «f!») x, .bool)
    else if h : α' ⊑ α then
      let x! ← loosenShared "app!" (castPath.chpred h.toCastPath) x
      return (.app f (.var x!), .bool)
    else throw s!"encodeTerm:app: Failed to unify {α} with {α'}"
  | (f, .fun τ (.option σ)), (x, ξ) => do
    if h : τ ⊑ ξ then
      let «f!» ← loosenShared "app!" (β := ξ.fun (.option σ)) (castPath.fun (by nofun) h.toCastPath (castPath.reflexive σ.option)) f
      return (.the (.app (.var «f!») x), σ)
    else if h : ξ ⊑ τ then
      let x! ← loosenShared "app!" h.toCastPath x
      return (.the (.app f (.var x!)), σ)
    else throw s!"encodeTerm:app: Failed to unify {τ} with {ξ}"
  | (_, τ), _ => throw s!"encodeTerm:app: Expected a function, got {τ}"

/-- Membership in an option-valued relation after casting the pair argument to
the function's endpoint representation. -/
def castMembership.optionForward (x S : Term)
    {α β ρ τ : SMTType} (cα : α ~> ρ) (cβ : β ~> τ) :
    Encoder (Term × SMTType) := do
  let ⟨x!, x!_spec⟩ ← loosenAux_prf "mem!" (.pair cα cβ) x
  declareConstWithSpec x! (.pair ρ τ) x!_spec
  return (x!_spec ∧ˢ
    (.app S (.fst (.var x!)) =ˢ .some (.snd (.var x!))), .bool)

/-- Normalize an option-valued relation to a common endpoint representation,
then use the forward option-membership encoding. -/
def castMembership.optionCommon (x S : Term)
    {α β α' β' ρ τ : SMTType}
    (cxα : α ~> ρ) (cxβ : β ~> τ)
    (cSα : α' ~> ρ) (cSβ : β' ~> τ) :
    Encoder (Term × SMTType) := do
  let cS : SMTType.fun α' (.option β') ~>
      SMTType.fun ρ (.option τ) :=
    .fun (by simp) cSα (.opt cSβ)
  let ⟨S!, S!_spec⟩ ← loosenAux_prf "mem!" cS S
  declareConstWithSpec S! (.fun ρ (.option τ)) S!_spec
  let ⟨t, σ⟩ ← castMembership.optionForward x (.var S!) cxα cxβ
  return (S!_spec ∧ˢ t, σ)

def castMembership : Term × SMTType → Term × SMTType → Encoder (Term × SMTType) := λ ⟨x, α⟩ ⟨S, τ⟩ =>
  match τ with
  | .fun α' .bool => do
    if h : α = α' then do
    /-
      x : α    S : α -> bool
      ----------------------
      x ∈ S    ↪    S x
    -/
      return (.app S x, .bool)
    else if h : α ⊑ α' then do
    /-
      x : α    S : α' -> bool    α ⊑ α'    α ≠ α'
      ----------------------------------------------
      x ∈ S    ↪    x!_spec ⇒ S x!
    -/
      let ⟨x!, x!_spec⟩ ← loosenAux_prf "mem!" h.toCastPath x
      declareConstWithSpec x! α' x!_spec
      return (x!_spec ∧ˢ .app S (.var x!), .bool)
    else if h : α' ⊑ α then do
    /-
      x : α    S : α' -> bool    α' ⊑ α
      ---------------------------------
      x ∈ S    ↪    S!_spec ⇒ S! x
    -/
      let ⟨S!, S!_spec⟩ ← loosenAux_prf "mem!" (castPath.chpred h.toCastPath) S
      declareConstWithSpec S! (.fun α .bool) S!_spec
      return (S!_spec ∧ˢ .app (.var S!) x, .bool)
    else throw s!"castMembership:1: Failed to unify {α} with {α'}"
  | .fun α' (.option β') => do
    match α with
    | .pair α β => do
      if hα : α ⊑ α' then
        if hβ : β ⊑ β' then
        /-
          x : α × β    S : α' -> Option β'    α ⊑ α'    β ⊑ β'
          ----------------------------------------------------
          x ∈ S    ↪    x!_spec ⇒ S (fst x!) = some (snd x!)
        -/
          castMembership.optionForward x S hα.toCastPath hβ.toCastPath
        else if hβ : β' ⊑ β then
        /-
          x : α × β    S : α' -> Option β'    α ⊑ α'    β' ⊑ β
          ------------------------------------------------------
          x ∈ S    ↪    x!_spec ∧ S!_spec ⇒ S! (fst x!) = some (snd x)
        -/
          castMembership.optionCommon x S
            hα.toCastPath (castPath.reflexive β)
            (castPath.reflexive α') hβ.toCastPath
        else throw s!"castMembership:3: Failed to unify {β} with {β'}"
      else if hα : α' ⊑ α then
        if hβ : β ⊑ β' then
        /-
          x : α × β    S : α' -> Option β'    α' ⊑ α    β ⊑ β'
          ------------------------------------------------------
          x ∈ S    ↪    y!_spec ∧ S!_spec ⇒ S! (fst x) = some y!
        -/
          castMembership.optionCommon x S
            (castPath.reflexive α) hβ.toCastPath
            hα.toCastPath (castPath.reflexive β')
        else if hβ : β' ⊑ β then
        /-
          x : α × β    S : α' -> Option β'    α' ⊑ α    β' ⊑ β
          ------------------------------------------------------
          x ∈ S    ↪    S!_spec ⇒ S! (fst x) = some (snd x)
        -/
          castMembership.optionCommon x S
            (castPath.reflexive α) (castPath.reflexive β)
            hα.toCastPath hβ.toCastPath
        else throw s!"castMembership:4: Failed to unify {β} with {β'}"
      else throw s!"castMembership:5: Failed to unify {α} with {α'}"
    | _ => throw s!"castMembership: Expected a pair type, got {α}"
  | _ => throw s!"encodeTerm:mem:6: Failed to unify {α} with {τ}"

/--
Given `⊢ˢ S : α → β?` and `⊢ˢ T : (α' × β') → bool`, and casts `c_α : α ~> α'` and `c_β : β ~> β'`,
encodes `S ∪ T : (α' × β') → bool`.
-/
def castUnion.graph (S T : Term) {α β α' β' : SMTType} (c_α : α ~> α') (c_β : β ~> β') : Encoder (Term × SMTType) := do
  -- S : α.fun (β.option), T : (.pair α' β').fun .bool
  -- Loosen S to graph representation, then pointwise OR
  let ⟨S!, S!_spec⟩ ← loosenAux_prf "union!" (castPath.graph c_α c_β) S
  declareConst S! (.fun (.pair α' β') .bool)
  addSpec S! S!_spec
  let x ← freshVar (.pair α' β') "union!"
  eraseFromContext x
  return (.lambda [x] [.pair α' β'] (.or (.app (.var S!) (.var x)) (.app T (.var x))), .fun (.pair α' β') .bool)
def castUnion.fun (S T : Term) {α β α' β' : SMTType} (hβ : β ≠ .bool) (c_α : α ~> α') (c_β : β ~> β') : Encoder (Term × SMTType) := do
  -- S : α.fun β, T : α'.fun β', β ≠ .bool
  -- Loosen S to α'.fun β', then convert to graph union
  let ⟨S!, S!_spec⟩ ← loosenAux_prf "union!" (castPath.fun hβ c_α c_β) S
  declareConst S! (.fun α' β')
  addSpec S! S!_spec
  match β' with
  | .option σ =>
    let p ← freshVar (.pair α' σ) "union!"
    eraseFromContext p
    return (.lambda [p] [.pair α' σ]
      (.or (.eq (.app (.var S!) (.fst (.var p))) (.some (.snd (.var p))))
           (.eq (.app T (.fst (.var p))) (.some (.snd (.var p))))),
      .fun (.pair α' σ) .bool)
  | _ => throw s!"castUnion.fun: Unexpected codomain type {β'}"
def castUnion.chpred (S T : Term) {α α' : SMTType} (c_α : α ~> α') : Encoder (Term × SMTType) := do
  -- S : α.fun .bool, T : α'.fun .bool
  -- Loosen S to α'.fun .bool, then pointwise OR
  let ⟨S!, S!_spec⟩ ← loosenAux_prf "union!" (castPath.chpred c_α) S
  declareConst S! (.fun α' .bool)
  addSpec S! S!_spec
  let x ← freshVar α' "union!"
  eraseFromContext x
  return (.lambda [x] [α'] (.or (.app (.var S!) (.var x)) (.app T (.var x))), .fun α' .bool)
def castUnion.opt (S T : Term) {α α' : SMTType} (c_α : α ~> α') : Encoder (Term × SMTType) := do
  throw s!"castUnion.opt: Union on option type is not expected from B set operations."
def castUnion.pair (S T : Term) {α β α' β' : SMTType} (c_α : α ~> α') (c_β : β ~> β') : Encoder (Term × SMTType) := do
  throw s!"castUnion.pair: Union on pair type is not expected from B set operations."
def castUnion.refl (S T : Term) (α : SMTType) : Encoder (Term × SMTType) := do
  throw s!"castUnion.refl: Union on base type {α} is not expected from B set operations."

/--
Given `⊢ˢ S : α`, `⊢ˢ T : β`, and a cast `𝕔 : α ~> β`,
encodes `S ∪ T` depending on the structure of `𝕔`.
-/
def castUnionAux (S T : Term) {α β : SMTType} : α ~> β → Encoder (Term × SMTType)
  | .graph c_α c_β     => castUnion.graph S T c_α c_β
  | .fun hβ c_α c_β    => castUnion.fun S T hβ c_α c_β
  | .chpred c_α        => castUnion.chpred S T c_α
  | .opt c_α           => castUnion.opt S T c_α
  | .pair c_α c_β      => castUnion.pair S T c_α c_β
  | @castPath.refl α _ => castUnion.refl S T α

/--
Wrapper around `castUnionAux` that tries to unify the types in both directions.
-/
def castUnion : Term × SMTType → Term × SMTType → Encoder (Term × SMTType) := λ ⟨S, α⟩ ⟨T, β⟩ => do
  if h : α = β then do
    match α, β, h with
    | .fun γ .bool, _, rfl => do
      /-
        S : γ → bool    T : γ → bool
        ----------------------------------------
        S ∪ T    ↪    λ x : γ. S(x) ∨ T(x)
      -/
      let x ← freshVar γ "union!"
      SMT.eraseFromContext x
      return (.lambda [x] [γ] (.or (.app S (.var x)) (.app T (.var x))), .fun γ .bool)
    | .fun γ (.option δ), _, rfl =>
      castUnion.fun S T (by simp) (castPath.reflexive γ)
        (castPath.reflexive (.option δ))
    | _, _, rfl => throw s!"castUnion: direct path requires function-to-bool type, got {α}"
  else if h : α ⊑ β then castUnionAux S T h.toCastPath
  else if h : β ⊑ α then castUnionAux T S h.toCastPath
  else throw s!"castUnion: cannot loosen {α} to {β} and vice versa"

def castInter.graph (S T : Term) {α β α' β' : SMTType}
    (c_α : α ~> α') (c_β : β ~> β') : Encoder (Term × SMTType) := do
  let ⟨S!, S!_spec⟩ ←
    loosenAux_prf "inter!" (castPath.graph c_α c_β) S
  declareConst S! (.fun (.pair α' β') .bool)
  addSpec S! S!_spec
  let x ← freshVar (.pair α' β') "inter!"
  eraseFromContext x
  return (.lambda [x] [.pair α' β']
    (.and (.app (.var S!) (.var x)) (.app T (.var x))),
    .fun (.pair α' β') .bool)

def castInter.fun (S T : Term) {α β α' β' : SMTType}
    (hβ : β ≠ .bool) (c_α : α ~> α') (c_β : β ~> β') :
    Encoder (Term × SMTType) := do
  let ⟨S!, S!_spec⟩ ←
    loosenAux_prf "inter!" (castPath.fun hβ c_α c_β) S
  declareConst S! (.fun α' β')
  addSpec S! S!_spec
  match β' with
  | .option σ =>
    let x ← freshVar α' "inter!"
    eraseFromContext x
    return (.lambda [x] [α']
      (.ite (.eq (.app (.var S!) (.var x)) (.app T (.var x)))
        (.app (.var S!) (.var x))
        (noneCast σ)),
      .fun α' (.option σ))
  | _ => throw s!"castInterAux.fun: Unexpected codomain type {β'}"

def castInter.chpred (S T : Term) {α α' : SMTType}
    (c_α : α ~> α') : Encoder (Term × SMTType) := do
  let ⟨S!, S!_spec⟩ ←
    loosenAux_prf "inter!" (castPath.chpred c_α) S
  declareConst S! (.fun α' .bool)
  addSpec S! S!_spec
  let x ← freshVar α' "inter!"
  eraseFromContext x
  return (.lambda [x] [α']
    (.and (.app (.var S!) (.var x)) (.app T (.var x))),
    .fun α' .bool)

def castInter.opt (S T : Term) {α α' : SMTType}
    (_c_α : α ~> α') : Encoder (Term × SMTType) := do
  throw s!"castInterAux: Intersection on option type is not expected."

def castInter.pair (S T : Term) {α β α' β' : SMTType}
    (_c_α : α ~> α') (_c_β : β ~> β') : Encoder (Term × SMTType) := do
  throw s!"castInterAux: Intersection on pair type is not expected."

def castInter.refl (S T : Term) (α : SMTType) :
    Encoder (Term × SMTType) := do
  throw s!"castInterAux: Intersection on base type {α} is not expected."

def castInterAux (S T : Term) {α β : SMTType} :
    α ~> β → Encoder (Term × SMTType)
  | .graph c_α c_β     => castInter.graph S T c_α c_β
  | .fun hβ c_α c_β    => castInter.fun S T hβ c_α c_β
  | .chpred c_α        => castInter.chpred S T c_α
  | .opt c_α           => castInter.opt S T c_α
  | .pair c_α c_β      => castInter.pair S T c_α c_β
  | @castPath.refl α _ => castInter.refl S T α

def castInter : Term × SMTType → Term × SMTType → Encoder (Term × SMTType) := λ ⟨S, α⟩ ⟨T, β⟩ => do
  if h : α = β then do
    match α, β, h with
    | .fun γ .bool, _, rfl => do
      /-
        S : γ → bool    T : γ → bool
        ----------------------------------------
        S ∩ T    ↪    λ x : γ. S(x) ∧ T(x)
      -/
      let x ← freshVar γ "inter!"
      SMT.eraseFromContext x
      return (.lambda [x] [γ] (.and (.app S (.var x)) (.app T (.var x))), .fun γ .bool)
    | .fun γ (.option δ), _, rfl => do
      /-
        S : γ → Option δ    T : γ → Option δ
        -----------------------------------------------------
        S ∩ T    ↪    λ x : γ. if S(x) = T(x) then S(x) else none
      -/
      let x ← freshVar γ "inter!"
      SMT.eraseFromContext x
      return (.lambda [x] [γ]
        (.ite (.eq (.app S (.var x)) (.app T (.var x)))
          (.app S (.var x))
          (noneCast δ)),
        .fun γ (.option δ))
    | _, _, rfl => throw s!"castInter: direct path requires function-to-bool type, got {α}"
  else if h : α ⊑ β then castInterAux S T h.toCastPath
  else if h : β ⊑ α then castInterAux T S h.toCastPath
  else throw s!"castInter: cannot loosen {α} to {β} and vice versa"
