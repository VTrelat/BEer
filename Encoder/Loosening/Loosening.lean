import Encoder.Basic
import Encoder.Simplifier
import Encoder.Loosening.Rules
open SMT

def castEq : Term × SMTType → Term × SMTType → Encoder (Term × SMTType) | (A, α), (B, β) => do
  if h : α = β then do
    /-
      A : α    B : β    α = β
      -----------------------
      A = B    ↪    A =ˢ B
    -/
    return (A =ˢ B, .bool)
  else if h : α ⊑ β then
    let ⟨A!, A!_spec⟩ ← loosenAux_prf "eq!" (castable?.toCastPath h) A
    declareConst A! β
    return (((.var A!) =ˢ B) ∧ˢ A!_spec, .bool)
  else if h : β ⊑ α then
    let ⟨B!, B!_spec⟩ ← loosenAux_prf "eq!" (castable?.toCastPath h) B
    declareConst B! α
    return (((.var B!) =ˢ A) ∧ˢ B!_spec, .bool)
  else throw s!"castEq: Failed to unify {α} with {β}"

def castApp : Term × SMTType → Term × SMTType → Encoder (Term × SMTType)
  | (f, .fun (.pair τ σ) .bool), (x, ξ) => do
    /- NOTE: This is the only special case where a relation is cast to a function -/
    if h : τ ⊑ ξ then
      -- loosen f
      let ⟨«f!», f!_spec⟩ ← loosenAux_prf "app!" (β := (.fun (.pair ξ σ) .bool)) (.chpred (.pair h.toCastPath (castPath.reflexive σ))) f
      declareConst «f!» (.fun (.pair ξ σ) .bool)
      addSpec «f!» f!_spec

      -- cast to function
      let f!! ← freshVar (ξ.fun (.option σ)) "app!!"
      declareConst f!! (ξ.fun (.option σ))
      let u ← freshVar τ
      let v ← freshVar σ
      let f!!_spec : Term := .forall [u, v] [τ, σ] (.eq
        (.app (.var «f!») (.pair (.var u) (.var v)))
        (.eq (.app (.var f!!) (.var u)) (.some (.var v))))
      addSpec f!! f!!_spec
      return (.the (.app (.var «f!!») x), σ)
    else if h : ξ ⊑ τ then
      -- loosen x
      let ⟨x!, x!_spec⟩ ← loosenAux_prf "app!" h.toCastPath x
      declareConst x! τ
      addSpec x! x!_spec

      -- cast to function
      let «f!» ← freshVar (τ.fun (.option σ)) "app!"
      declareConst «f!» (τ.fun (.option σ))
      let u ← freshVar τ
      let v ← freshVar σ
      let f!_spec : Term := .forall [u, v] [τ, σ] (.eq
        (.app f (.pair (.var u) (.var v)))
        (.eq (.app (.var «f!») (.var u)) (.some (.var v))))
      addSpec «f!» f!_spec
      return (.the (.app (.var «f!») (.var x!)), σ)
    else throw s!"encodeTerm:app: Failed to unify {τ} with {ξ}"
  | (f, .fun α .bool), (x, α') => do
    if h : α ⊑ α' then
      let ⟨«f!», f!_spec⟩ ← loosenAux_prf "app!" (castPath.chpred h.toCastPath) f
      declareConst «f!» (α'.fun .bool)
      addSpec «f!» f!_spec
      return (.app (.var «f!») x, .bool)
    else if h : α' ⊑ α then
      let ⟨x!, x!_spec⟩ ← loosenAux_prf "app!" (castPath.chpred h.toCastPath) x
      declareConst x! α
      addSpec x! x!_spec
      return (.app f (.var x!), .bool)
    else throw s!"encodeTerm:app: Failed to unify {α} with {α'}"
  | (f, .fun τ (.option σ)), (x, ξ) => do
    if h : τ ⊑ ξ then
      let ⟨«f!», f!_spec⟩ ← loosenAux_prf "app!" (β := ξ.fun (.option σ)) (castPath.fun (by nofun) h.toCastPath (castPath.reflexive σ.option)) f
      declareConst «f!» (ξ.fun (.option σ))
      addSpec «f!» f!_spec
      return (.the (.app (.var «f!») x), σ)
    else if h : ξ ⊑ τ then
      let ⟨x!, x!_spec⟩ ← loosenAux_prf "app!" h.toCastPath x
      declareConst x! τ
      addSpec x! x!_spec
      return (.the (.app f (.var x!)), σ)
    else throw s!"encodeTerm:app: Failed to unify {τ} with {ξ}"
  | (_, τ), _ => throw s!"encodeTerm:app: Expected a function, got {τ}"

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
      declareConst x! α'
      return (x!_spec ∧ˢ .app S (.var x!), .bool)
    else if h : α' ⊑ α then do
    /-
      x : α    S : α' -> bool    α' ⊑ α
      ---------------------------------
      x ∈ S    ↪    S!_spec ⇒ S! x
    -/
      let ⟨S!, S!_spec⟩ ← loosenAux_prf "mem!" (castPath.chpred h.toCastPath) S
      declareConst S! (.fun α .bool)
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
          let ⟨x!, x!_spec⟩ ← loosenAux_prf "mem!" (α := .pair α β) (β := .pair α' β') (.pair hα.toCastPath hβ.toCastPath) x
          declareConst x! (.pair α' β')
          return (x!_spec ∧ˢ (.app S (.fst (.var x!)) =ˢ .some (.snd (.var x!))), .bool)
        else if hβ : β' ⊑ β then
        /-
          x : α × β    S : α' -> Option β'    α ⊑ α'    β' ⊑ β
          ------------------------------------------------------
          x ∈ S    ↪    x!_spec ∧ S!_spec ⇒ S! (fst x!) = some (snd x)
        -/
          let ⟨x!, x!_spec⟩ ← loosenAux_prf "mem!" hα.toCastPath (.fst x)
          declareConst x! α'
          let ⟨S!, S!_spec⟩ ← loosenAux_prf "mem!" (β := .fun α' (.option β)) (.fun (not_eq_of_beq_eq_false rfl) (castPath.reflexive α') (.opt hβ.toCastPath)) S
          declareConst S! (.fun α' (.option β))
          return (x!_spec ∧ˢ S!_spec ∧ˢ (.app (.var S!) (.var x!) =ˢ .some (.snd x)), .bool)
        else throw s!"castMembership:3: Failed to unify {β} with {β'}"
      else if hα : α' ⊑ α then
        if hβ : β ⊑ β' then
        /-
          x : α × β    S : α' -> Option β'    α' ⊑ α    β ⊑ β'
          ------------------------------------------------------
          x ∈ S    ↪    y!_spec ∧ S!_spec ⇒ S! (fst x) = some y!
        -/
          let ⟨y!, y!_spec⟩ ← loosenAux_prf "mem!" hβ.toCastPath (.snd x)
          declareConst y! β'
          let ⟨S!, S!_spec⟩ ← loosenAux_prf "mem!"
            (β := .fun α (.option β'))
            (.fun (not_eq_of_beq_eq_false rfl) hα.toCastPath (castPath.reflexive (.option β'))) S
          declareConst S! (.fun α (.option β'))
          return (y!_spec ∧ˢ S!_spec ∧ˢ (.app (.var S!) (.fst x) =ˢ .some (.var y!)), .bool)
        else if hβ : β' ⊑ β then
        /-
          x : α × β    S : α' -> Option β'    α' ⊑ α    β' ⊑ β
          ------------------------------------------------------
          x ∈ S    ↪    S!_spec ⇒ S! (fst x) = some (snd x)
        -/
          let ⟨S!, S!_spec⟩ ← loosenAux_prf "mem!"
            (β := .fun α (.option β))
            (.fun (not_eq_of_beq_eq_false rfl) hα.toCastPath (.opt hβ.toCastPath)) S
          declareConst S! (.fun α (.option β))
          return (S!_spec ∧ˢ (.app (.var S!) (.fst x) =ˢ .some (.snd x)), .bool)
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
      return (.lambda [x] [γ] (.or (.app S (.var x)) (.app T (.var x))), .fun γ .bool)
    | _, _, rfl => throw s!"castUnion: direct path requires function-to-bool type, got {α}"
  else if h : α ⊑ β then castUnionAux S T h.toCastPath
  else if h : β ⊑ α then castUnionAux T S h.toCastPath
  else throw s!"castUnion: cannot loosen {α} to {β} and vice versa"

def castInterAux (S T : Term) {α β : SMTType} : α ~> β → Encoder (Term × SMTType)
  | @castPath.graph _ _ α' β' c_α c_β => do
    let ⟨S!, S!_spec⟩ ← loosenAux_prf "inter!" (castPath.graph c_α c_β) S
    declareConst S! (.fun (.pair α' β') .bool)
    addSpec S! S!_spec
    let x ← freshVar (.pair α' β') "inter!"
    return (.lambda [x] [.pair α' β'] (.and (.app (.var S!) (.var x)) (.app T (.var x))), .fun (.pair α' β') .bool)
  | @castPath.fun _ _ α' β' hβ c_α c_β => do
    let ⟨S!, S!_spec⟩ ← loosenAux_prf "inter!" (castPath.fun hβ c_α c_β) S
    declareConst S! (.fun α' β')
    addSpec S! S!_spec
    match β' with
    | .option σ =>
      let p ← freshVar (.pair α' σ) "inter!"
      return (.lambda [p] [.pair α' σ]
        (.and (.eq (.app (.var S!) (.fst (.var p))) (.some (.snd (.var p))))
             (.eq (.app T (.fst (.var p))) (.some (.snd (.var p))))),
        .fun (.pair α' σ) .bool)
    | _ => throw s!"castInterAux.fun: Unexpected codomain type {β'}"
  | @castPath.chpred _ α' c_α => do
    let ⟨S!, S!_spec⟩ ← loosenAux_prf "inter!" (castPath.chpred c_α) S
    declareConst S! (.fun α' .bool)
    addSpec S! S!_spec
    let x ← freshVar α' "inter!"
    return (.lambda [x] [α'] (.and (.app (.var S!) (.var x)) (.app T (.var x))), .fun α' .bool)
  | .opt _ => do throw s!"castInterAux: Intersection on option type is not expected."
  | .pair _ _ => do throw s!"castInterAux: Intersection on pair type is not expected."
  | @castPath.refl α' _ => do throw s!"castInterAux: Intersection on base type {α'} is not expected."

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
      return (.lambda [x] [γ] (.and (.app S (.var x)) (.app T (.var x))), .fun γ .bool)
    | _, _, rfl => throw s!"castInter: direct path requires function-to-bool type, got {α}"
  else if h : α ⊑ β then castInterAux S T h.toCastPath
  else if h : β ⊑ α then castInterAux T S h.toCastPath
  else throw s!"castInter: cannot loosen {α} to {β} and vice versa"
