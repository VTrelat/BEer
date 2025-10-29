import Encoder.Basic
import Encoder.Simplifier
open SMT

def castable? : SMTType → SMTType → Bool
  | .fun α (.option β), .fun (.pair α' β') .bool
  | .fun α (.option β), .fun α' (.option β')
  | .fun (.pair α β) .bool, .fun (.pair α' β') .bool => (castable? α α') && (castable? β β')
  | .fun α .bool, .fun α' .bool => castable? α α'
  | .pair α β, .pair α' β' => (castable? α α') && (castable? β β')
  | .option α, .option α' => castable? α α'
  | .int, .int => true
  | .bool, .bool => true
  | .unit, .unit => true
  | _, _ => false
infix:70 " ⊑ " => castable?

-- ℤ +-> ℤ ⊑ ℤ <-> ℤ
-- #eval (.fun (.pair .int .int) .bool) ⊑ (.fun .int (.option .int))

-- TODO: document cases as done in castMembership
def loosen (name : String) (x : Term) : SMTType → SMTType → Encoder (𝒱 × Term) -- term × spec
  -- | .fun (.pair α β) .bool, .fun (.pair α' β') .bool =>
  | .fun α .bool, .fun α' .bool => do
    unless α ⊑ α' do throw s!"loosen:set,set: Cannot loosen {α} to {α'}"
    let x! ← freshVar (.fun α' .bool) name
    if α == α' then return ⟨x!, x =ˢ .var x!⟩ -- NOTE: adding this in a terminal case would produce too many variables.
    else
      let z ← freshVar α
      let ⟨z!, z!_spec⟩ ← loosen name (.var z) α α'
      return ⟨x!,
        -- .forall [z] [α] (.app x (.var z) =ˢ .exists [z!] [α'] (.app (.var x!) (.var z!) ∧ˢ z!_spec))
        .var x! =ˢ (.lambda [z!] [α'] (.exists [z] [α] ((.app x (.var z)) ∧ˢ z!_spec)))
      ⟩
  | .fun α (.option β), .fun (.pair α' β') .bool => do
    unless α ⊑ α' ∧ β ⊑ β' do throw s!"loosen: Cannot loosen {SMTType.fun α (.option β)} to {SMTType.fun (.pair α' β') .bool}"
    let x! ← freshVar (.fun (.pair α' β') .bool) name
    let z ← freshVar (.pair α β) s!"{x!}_{name}"
    if α == α' ∧ β == β' then return ⟨x!, .var x! =ˢ .lambda [z] [.pair α β] ((.app x (.fst (.var z))) =ˢ .some (.snd (.var z)))⟩
    else
      let ⟨z!, z!_spec⟩ ← loosen name (.var z) (.pair α β) (.pair α' β')
      return ⟨x!,
        .forall [z] [.pair α β] (((.app x (.fst (.var z))) =ˢ .some (.snd (.var z))) =ˢ
          .exists [z!] [.pair α' β'] (.app (.var x!) (.var z!) ∧ˢ z!_spec))
      ⟩
  | .fun α (.option β), .fun α' (.option β') => do
    unless α ⊑ α' ∧ β ⊑ β' do throw s!"loosen: Cannot loosen {SMTType.fun α (.option β)} to {SMTType.fun α' (.option β')}"
    let x! ← freshVar (.fun α' (.option β')) name
    let z ← freshVar (.pair α β) s!"{x!}_{name}"
    if α == α' then
      if β == β' then
        return ⟨x!, .var x! =ˢ x⟩
      else
        let ⟨v!, v!_spec⟩ ← loosen name (.snd (.var z)) β β'
        return ⟨x!,
          .forall [z] [.pair α β] (((.app x (.fst (.var z))) =ˢ .some (.snd (.var z))) =ˢ
            .exists [v!] [β'] ((.app (.var x!) (.fst (.var z)) =ˢ .some (.var v!)) ∧ˢ v!_spec))
        ⟩
    else
      if β == β' then
        let ⟨u!, u!_spec⟩ ← loosen name (.fst (.var z)) α α'
        return ⟨x!,
          .forall [z] [.pair α β] (((.app x (.fst (.var z))) =ˢ .some (.snd (.var z))) =ˢ
            .exists [u!] [α'] (((.app (.var x!) (.var u!)) =ˢ .some (.snd (.var z))) ∧ˢ u!_spec))
        ⟩
      else
        let ⟨z!, z!_spec⟩ ← loosen name (.var z) (.pair α β) (.pair α' β')
        return ⟨x!,
          .forall [z] [.pair α β] (((.app x (.fst (.var z))) =ˢ .some (.snd (.var z))) =ˢ
            .exists [z!] [.pair α' β'] (((.app (.var x!) (.fst (.var z!))) =ˢ .some (.snd (.var z!))) ∧ˢ z!_spec))
        ⟩
  | .pair α β, .pair α' β' => do
    unless α ⊑ α' ∧ β ⊑ β' do throw s!"loosen: Cannot loosen term {SMTType.pair α β} to {SMTType.pair α' β'}"
    let x! ← freshVar (.pair α' β') "x!"
    if α == α' then
      if β == β' then return ⟨x!, .var x! =ˢ x⟩
      else
        let ⟨v!, v!_spec⟩ ← loosen name (.snd x) β β'
        return ⟨x!,
          .exists [v!] [β'] ((.var x! =ˢ .pair (.fst x) (.var v!)) ∧ˢ v!_spec)
        ⟩
    else
      if β == β' then
        let ⟨u!, u!_spec⟩ ← loosen name (.fst x) α α'
        return ⟨x!,
          .exists [u!] [α'] ((.var x! =ˢ .pair (.var u!) (.snd x)) ∧ˢ u!_spec)
        ⟩
      else
        let ⟨u!, u!_spec⟩ ← loosen name (.fst x) α α'
        let ⟨v!, v!_spec⟩ ← loosen name (.snd x) β β'
        return ⟨x!,
          .exists [u!, v!] [α', β'] ((.var x! =ˢ .pair (.var u!) (.var v!)) ∧ˢ u!_spec ∧ˢ v!_spec)
        ⟩
  | α, β => do
    unless α == β do throw s!"loosen: Cannot loosen {α} to {β}"
    return ⟨"", .bool true⟩

def castEq : Term × SMTType → Term × SMTType → Encoder (Term × SMTType) | (A, α), (B, β) => do
  if α == β then return (A =ˢ B, .bool)
  else if α ⊑ β then do
    let ⟨A!, A!_spec⟩ ← loosen "eq!" A α β
    declareConst A! β
    return (A!_spec ∧ˢ ((.var A!) =ˢ B), .bool)
  else if β ⊑ α then do
    let ⟨B!, B!_spec⟩ ← loosen "eq!" B β α
    declareConst B! α
    return (B!_spec ∧ˢ (A =ˢ .var B!), .bool)
  else match α, β with
  | .option α, _ =>
    unless α == β do throw s!"castEq: Failed to unify {α} with {β}"
    return (.the A =ˢ B, .bool)
  | _, .option β =>
    unless α == β do throw s!"castEq: Failed to unify {α} with {β}"
    return (A =ˢ .the B, .bool)
  | _, _ =>
    throw s!"castEq: Failed to unify {α} with {β}"

def castApp' : Term × SMTType → Term × SMTType → Encoder (Term × SMTType)
  | (f, .fun τ σ), (x, ξ) => do
    if τ == ξ then
      match σ with
      | .bool => return (.app f x, .bool)
      | .option σ => return (.the (.app f x), σ)
      | _ => throw s!"encodeTerm:app: Expected an option, got {σ}"
    else match σ with
    | .bool =>
      if τ ⊑ ξ then do
        let ⟨«f!», f!_spec⟩ ← loosen "app!" x ξ τ
        return (f!_spec ∧ˢ .app (.var «f!») x, .bool)
      else if ξ ⊑ τ then do
        let ⟨x!, x!_spec⟩ ← loosen "app!" f τ ξ
        return (x!_spec ∧ˢ .app f (.var x!), .bool)
      else throw s!"encodeTerm:app: Unification failed {τ} ≠ {ξ}"
    | _ => throw s!"encodeTerm:app: Unification failed {τ} ≠ {ξ}" -- NOTE: for the moment, reject any other case (where do we put the spec?)
  | (_, τ), _ => throw s!"encodeTerm:app: Expected a function, got {τ}"

def castApp : Term × SMTType → Term × SMTType → Encoder (Term × SMTType)
  | (f, .fun (.pair τ σ) .bool), (x, ξ) => do
    -- dbg_trace "castApp: f : {f} : {τ} × {σ} -> bool, x : {x} : {ξ}"
    /- NOTE: This is the only special case where a relation is cast to a function -/
    if τ == ξ then
      let «f!» ← freshVar (τ.fun (.option σ)) "app!"
      declareConst «f!» (τ.fun (.option σ))
      let u ← freshVar τ
      let v ← freshVar σ
      let f!_spec : Term := .forall [u, v] [τ, σ] (.eq
        (.app f (.pair (.var u) (.var v)))
        (.eq (.app (.var «f!») (.var u)) (.some (.var v))))
      addSpec «f!» f!_spec
      return (.the (.app (.var «f!») x), σ)
    else if τ ⊑ ξ then
      -- loosen f
      let ⟨«f!», f!_spec⟩ ← loosen "app!" f (.fun (.pair τ σ) .bool) (.fun (.pair ξ σ) .bool)
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
    else if ξ ⊑ τ then
      -- loosen x
      let ⟨x!, x!_spec⟩ ← loosen "app!" x ξ τ
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
    if α == α' then
      return (.app f x, .bool)
    else if α ⊑ α' then
      let ⟨«f!», f!_spec⟩ ← loosen "app!" f (α.fun .bool) (α'.fun .bool)
      declareConst «f!» (α'.fun .bool)
      addSpec «f!» f!_spec
      return (.app (.var «f!») x, .bool)
    else if α' ⊑ α then
      let ⟨x!, x!_spec⟩ ← loosen "app!" x α' α
      declareConst x! α
      addSpec x! x!_spec
      return (.app f (.var x!), .bool)
    else throw s!"encodeTerm:app: Failed to unify {α} with {α'}"
  | (f, .fun τ (.option σ)), (x, ξ) => do
    -- dbg_trace "castApp: f : {f} : {τ} -> Option {σ}, x : {x} : {ξ}"
    if τ == ξ then
      return (.the (.app f x), σ)
    else if τ ⊑ ξ then
      let ⟨«f!», f!_spec⟩ ← loosen "app!" f (τ.fun (.option σ)) (ξ.fun (.option σ))
      declareConst «f!» (ξ.fun (.option σ))
      addSpec «f!» f!_spec
      return (.the (.app (.var «f!») x), σ)
    else if ξ ⊑ τ then
      let ⟨x!, x!_spec⟩ ← loosen "app!" x ξ τ
      declareConst x! τ
      addSpec x! x!_spec
      return (.the (.app f (.var x!)), σ)
    else throw s!"encodeTerm:app: Failed to unify {τ} with {ξ}"
  | (_, τ), _ => throw s!"encodeTerm:app: Expected a function, got {τ}"

def castMembership : Term × SMTType → Term × SMTType → Encoder (Term × SMTType) := λ ⟨x, α⟩ ⟨S, τ⟩ =>
  match τ with
  | .fun α' .bool => do
    if α == α' then
    /-
      x : α    S : α -> bool
      ----------------------
      x ∈ S    ↪    S x
    -/
      return (.app S x, .bool)
    else if α ⊑ α' then do
    /-
      x : α    S : α' -> bool    α ⊑ α'
      ---------------------------------
      x ∈ S    ↪    x!_spec ⇒ S x!
    -/
      let ⟨x!, x!_spec⟩ ← loosen "mem!" x α α'
      declareConst x! α'
      return (x!_spec ∧ˢ .app S (.var x!), .bool)
    else if α' ⊑ α then do
    /-
      x : α    S : α' -> bool    α' ⊑ α
      ---------------------------------
      x ∈ S    ↪    S!_spec ⇒ S! x
    -/
      let ⟨S!, S!_spec⟩ ← loosen "mem!" S (.fun α' .bool) (.fun α .bool)
      declareConst S! (.fun α .bool)
      return (S!_spec ∧ˢ .app (.var S!) x, .bool)
    else throw s!"castMembership:1: Failed to unify {α} with {α'}"
  | .fun α' (.option β') => do
    match α with
    | .pair α β => do
      if α == α' then
        if β == β' then
        /-
          x : α × β    S : α -> Option β
          -------------------------------------
          x ∈ S    ↪    S (fst x) = some (snd x)
        -/
          return (.eq (.app S (.fst x)) (.some (.snd x)), .bool)
        else if β ⊑ β' then
        /-
          x : α × β    S : α -> Option β'    β ⊑ β'
          -------------------------------------------
          x ∈ S    ↪    y!_spec ⇒ S (fst x) = some y!
        -/
          let ⟨y!, y!_spec⟩ ← loosen "mem!" (.snd x) β β'
          declareConst y! β'
          return (.and y!_spec (.eq (.app S (.fst x)) (.some (.var y!))), .bool)
        else if β' ⊑ β then
        /-
          x : α × β    S : α -> Option β'    β' ⊑ β
          -------------------------------------------------
          x ∈ S    ↪    S!_spec ⇒ S! (fst x) = some (snd x)
        -/
          let ⟨S!, S!_spec⟩ ← loosen "mem!" S (.fun α (.option β')) (.fun α (.option β))
          declareConst S! (.fun α (.option β))
          return (.and S!_spec (.eq (.app (.var S!) (.fst x)) (.some (.snd x))), .bool)
        else throw s!"castMembership:2: Failed to unify {β} with {β'}"
      else if α ⊑ α' then
        if β == β' then
        /-
          x : α × β    S : α' -> Option β    α ⊑ α'
          -------------------------------------------
          x ∈ S    ↪    x!_spec ⇒ S x! = some (snd x)
        -/
          let ⟨x!, x!_spec⟩ ← loosen "mem!" (.fst x) α α'
          declareConst x! α'
          return (.and x!_spec (.eq (.app S (.var x!)) (.some (.snd x))), .bool)
        else if β ⊑ β' then
        /-
          x : α × β    S : α' -> Option β'    α ⊑ α'    β ⊑ β'
          ----------------------------------------------------
          x ∈ S    ↪    x!_spec ⇒ S (fst x!) = some (snd x!)
        -/
          let ⟨x!, x!_spec⟩ ← loosen "mem!" x (.pair α β) (.pair α' β')
          declareConst x! (.pair α' β')
          return (x!_spec ∧ˢ (.app S (.fst (.var x!)) =ˢ .some (.snd (.var x!))), .bool)
        else if β' ⊑ β then
        /-
          x : α × β    S : α' -> Option β'    α ⊑ α'    β' ⊑ β
          ------------------------------------------------------
          x ∈ S    ↪    x!_spec ∧ S!_spec ⇒ S! (fst x!) = some (snd x)
        -/
          let ⟨x!, x!_spec⟩ ← loosen "mem!" (.fst x) α α'
          declareConst x! α'
          let ⟨S!, S!_spec⟩ ← loosen "mem!" S (.fun α' (.option β')) (.fun α' (.option β))
          declareConst S! (.fun α' (.option β))
          return (x!_spec ∧ˢ S!_spec ∧ˢ (.app (.var S!) (.var x!) =ˢ .some (.snd x)), .bool)
        else throw s!"castMembership:3: Failed to unify {β} with {β'}"
      else if α' ⊑ α then
        if β == β' then
        /-
          x : α × β    S : α' -> Option β    α' ⊑ α
          -------------------------------------------------
          x ∈ S    ↪    S!_spec ∧ S! (fst x) = some (snd x)
        -/
          let ⟨S!, S!_spec⟩ ← loosen "mem!" S (.fun α' (.option β)) (.fun α (.option β))
          declareConst S! (.fun α (.option β))
          return (S!_spec ∧ˢ (.app (.var S!) (.fst x) =ˢ .some (.snd x)), .bool)
        else if β ⊑ β' then
        /-
          x : α × β    S : α' -> Option β'    α' ⊑ α    β ⊑ β'
          ------------------------------------------------------
          x ∈ S    ↪    y!_spec ∧ S!_spec ⇒ S! (fst x) = some y!
        -/
          let ⟨y!, y!_spec⟩ ← loosen "mem!" (.snd x) β β'
          declareConst y! β'
          let ⟨S!, S!_spec⟩ ← loosen "mem!" S (.fun α' (.option β')) (.fun α (.option β'))
          declareConst S! (.fun α (.option β'))
          return (y!_spec ∧ˢ S!_spec ∧ˢ (.app (.var S!) (.fst x) =ˢ .some (.var y!)), .bool)
        else if β' ⊑ β then
        /-
          x : α × β    S : α' -> Option β'    α' ⊑ α    β' ⊑ β
          ------------------------------------------------------
          x ∈ S    ↪    S!_spec ⇒ S! (fst x) = some (snd x)
        -/
          let ⟨S!, S!_spec⟩ ← loosen "mem!" S (.fun α' (.option β')) (.fun α (.option β))
          declareConst S! (.fun α (.option β))
          return (S!_spec ∧ˢ (.app (.var S!) (.fst x) =ˢ .some (.snd x)), .bool)
        else throw s!"castMembership:4: Failed to unify {β} with {β'}"
      else throw s!"castMembership:5: Failed to unify {α} with {α'}"
    | _ => throw s!"castMembership: Expected a pair type, got {α}"
  | _ => throw s!"encodeTerm:mem:6: Failed to unify {α} with {τ}"

def castUnion_aux_rel_rel : Term × SMTType × SMTType → Term × SMTType × SMTType → Encoder (Term × SMTType) := λ ⟨S, α, β⟩ ⟨T, α', β'⟩ => do
  if α == α' then
      if β == β' then
      /-
        S : α × β -> bool    T : α × β -> bool
        --------------------------------------
        S ∪ T    ↪    λ z. S z ∨ T z
      -/
        let z ← freshVar (.pair α β)
        return (.lambda [z] [.pair α β] (.or (.app S (.var z)) (.app T (.var z))),
          .fun (.pair α β) .bool)
      else if β ⊑ β' then
      /-
        S : α × β -> bool    T : α × β' -> bool    β ⊑ β'
        ------------------------------------------------------------
        S ∪ T    ↪    λ z. S z ∨ (∃ v!, v!_spec ∧ T (pair (fst z) v!))
      -/
        let z ← freshVar (.pair α β)
        let ⟨sndz!, sndz!_spec⟩ ← loosen "union!" (.snd (.var z)) β β'
        return (.lambda [z] [.pair α β] (.or
          (.app S (.var z))
          (.exists [sndz!] [β'] (.and sndz!_spec (.app T (.pair (.fst (.var z)) (.var sndz!)))))),
          .fun (.pair α β) .bool)
      else if β' ⊑ β then
      /-
        S : α × β -> bool    T : α × β' -> bool    β' ⊑ β
        ---------------------------------------------------
        S ∪ T    ↪    λ z. (∃ v!, v!_spec ∧ S (pair (fst z) v!)) ∨ T z
      -/
        let z ← freshVar (.pair α β')
        let ⟨sndz!, sndz!_spec⟩ ← loosen "union!" (.snd (.var z)) β' β
        return (.lambda [z] [.pair α β'] (.or
          (.exists [sndz!] [β] (.and sndz!_spec (.app S (.pair (.fst (.var z)) (.var sndz!)))))
          (.app T (.var z))),
          .fun (.pair α β') .bool)
      else throw s!"castUnion: Failed to unify {β} with {β'}"
    else if α ⊑ α' then
      if β == β' then
      /-
        S : α × β -> bool    T : α' × β -> bool    α ⊑ α'
        ------------------------------------------------------------
        S ∪ T    ↪    λ z. S z ∨ (∃ u!, u!_spec ∧ T (pair u! (snd z))
      -/
        let z ← freshVar (.pair α β)
        let ⟨fstz!, fstz!_spec⟩ ← loosen "union!" (.fst (.var z)) α α'
        return (.lambda [z] [.pair α β] (.or
          (.app S (.var z))
          (.exists [fstz!] [α'] (.and fstz!_spec (.app T (.pair (.var fstz!) (.snd (.var z))))))),
          .fun (.pair α β) .bool)
      else if β ⊑ β' then
      /-
        S : α × β -> bool    T : α' × β' -> bool    α ⊑ α'    β ⊑ β'
        ----------------------------------------------------------------
        S ∪ T    ↪    λ z. S z ∨ (∃ z!, z!_spec ∧ T z!)
      -/
        let z ← freshVar (.pair α β)
        let ⟨z!, z!_spec⟩ ← loosen "union!" (.var z) (.pair α β) (.pair α' β')
        return (.lambda [z] [.pair α β] (.or
          (.app S (.var z))
          (.exists [z!] [.pair α' β'] (.and z!_spec (.app T (.var z!))))),
          .fun (.pair α β) .bool)
      else if β' ⊑ β then
      /-
        S : α × β -> bool    T : α' × β' -> bool    α ⊑ α'    β' ⊑ β
        ----------------------------------------------------------------
        S ∪ T    ↪    λ z. (∃ u!, u!_spec ∧ S (pair u! (snd z))) ∨ (∃ v!, v!_spec ∧ T (pair (fst z) v!))
      -/
        let z ← freshVar (.pair α β')
        let ⟨u!, u!_spec⟩ ← loosen "union!" (.fst (.var z)) α α'
        let ⟨v!, v!_spec⟩ ← loosen "union!" (.snd (.var z)) β' β
        return (.lambda [z] [.pair α β'] (.or
          (.exists [u!] [α'] (.and u!_spec (.app S (.pair (.var u!) (.snd (.var z))))))
          (.exists [v!] [β] (.and v!_spec (.app T (.pair (.fst (.var z)) (.var v!)))))),
          .fun (.pair α β') .bool)
      else throw s!"castUnion: Failed to unify {β} with {β'}"
    else if α' ⊑ α then
      if β == β' then
      /-
        S : α × β -> bool    T : α' × β -> bool    α' ⊑ α
        ------------------------------------------------------------
        S ∪ T    ↪    λ z. (∃ u!, u!_spec ∧ S (pair u! (snd z))) ∨ T z
      -/
        let z ← freshVar (.pair α' β)
        let ⟨u!, u!_spec⟩ ← loosen "union!" (.fst (.var z)) α' α
        return (.lambda [z] [.pair α' β] (.or
          (.exists [u!] [α] (.and u!_spec (.app S (.pair (.var u!) (.snd (.var z))))))
          (.app T (.var z))),
          .fun (.pair α' β) .bool)
      else if β ⊑ β' then
      /-
        S : α × β -> bool    T : α' × β' -> bool    α' ⊑ α    β ⊑ β'
        --------------------------------------------------------------
        S ∪ T    ↪    λ z. (∃ u!, u!_spec ∧ S (pair u! (snd z))) ∨ (∃ v!, v!_spec ∧ T (pair (fst z) v!)
      -/
        let z ← freshVar (.pair α' β)
        let ⟨u!, u!_spec⟩ ← loosen "union!" (.fst (.var z)) α' α
        let ⟨v!, v!_spec⟩ ← loosen "union!" (.snd (.var z)) β β'
        return (.lambda [z] [.pair α' β] (.or
          (.exists [u!] [α] (.and u!_spec (.app S (.pair (.var u!) (.snd (.var z))))))
          (.exists [v!] [β'] (.and v!_spec (.app T (.pair (.fst (.var z)) (.var v!)))))),
          .fun (.pair α' β) .bool)
      else if β' ⊑ β then
      /-
        S : α × β -> bool    T : α' × β' -> bool    α' ⊑ α    β' ⊑ β
        --------------------------------------------------------------
        S ∪ T    ↪    λ z. (∃ z!, z!_spec ∧ S z!) ∨ T z
      -/
        let z ← freshVar (.pair α' β')
        let ⟨z!, z!_spec⟩ ← loosen "union!" (.var z) (.pair α' β') (.pair α β)
        return (.lambda [z] [.pair α' β'] (.or
          (.exists [z!] [.pair α β] (.and z!_spec (.app S (.var z!))))
          (.app T (.var z))),
          .fun (.pair α' β') .bool)
      else throw s!"castUnion: Failed to unify {β} with {β'}"
    else throw s!"castUnion: Failed to unify {α} with {α'}"

def castUnion_aux_set_set : Term × SMTType → Term × SMTType → Encoder (Term × SMTType) := λ ⟨S, α⟩ ⟨T, α'⟩ => do
  if α == α' then
    /-
      S : α -> bool    T : α -> bool
      ------------------------------
      S ∪ T    ↪    λ x. S x ∨ T x
    -/
      let z ← freshVar α
      return (.lambda [z] [α] (.or (.app S (.var z)) (.app T (.var z))), .fun α .bool)
    else if α ⊑ α' then
    /-
      S : α -> bool    T : α' -> bool    α ⊑ α'
      -------------------------------------------
      S ∪ T    ↪    λ x. S x ∨ (∃ x!, x!_spec ∧ T x!)
    -/
      let x ← freshVar α
      let ⟨x!, x!_spec⟩ ← loosen "union!" (.var x) α α'
      return (.lambda [x] [α] (.or (.app S (.var x)) (.exists [x!] [α'] (.and x!_spec (.app T (.var x!))))), .fun α .bool)
    else if α' ⊑ α then
    /-
      S : α -> bool    T : α' -> bool    α' ⊑ α
      -------------------------------------------
      S ∪ T    ↪    λ x. (∃ x!, x!_spec ∧ S x!) ∨ T x
    -/
      let x ← freshVar α'
      let ⟨x!, x!_spec⟩ ← loosen "union!" (.var x) α' α
      return (.lambda [x] [α'] (.or (.exists [x!] [α] (.and x!_spec (.app S (.var x)))) (.app T (.var x))), .fun α' .bool)
    else throw s!"castUnion: Failed to unify {α} with {α'}"

def castUnion_aux_fun_fun : Term × SMTType × SMTType → Term × SMTType × SMTType → Encoder (Term × SMTType) := λ ⟨S, α, β⟩ ⟨T, α', β'⟩ => do
/-
    safe encoding: cast back to relation, I don't want to
    generate a new PO stating that domains are disjoint.
  -/
  if α == α' then
    if β == β' then
    /-
      S : α -> Option β    T : α -> Option β
      ----------------------------------------------------------------------------
      S ∪ T    ↪    λ z : α × β. the (S (fst z)) = snd z ∨ the (T (fst z)) = snd z
    -/
      let z ← freshVar (.pair α β)
      return (.lambda [z] [.pair α β] (.or (.eq (.the (.app S (.fst (.var z)))) (.snd (.var z))) (.eq (.the (.app T (.fst (.var z)))) (.snd (.var z)))), .fun (.pair α β) .bool)
    else if β ⊑ β' then
    /-
      S : α -> Option β    T : α -> Option β'    β ⊑ β'
      ----------------------------------------------------------------------------
      S ∪ T    ↪    λ z : α × β'. the (S (fst z)) = snd z ∨ ∃ sndz!, sndz!_spec ∧ the (T (fst z)) = sndz!
    -/
      let z ← freshVar (.pair α β')
      let ⟨sndz!, sndz!_spec⟩ ← loosen "union!" (.snd (.var z)) β β'
      return (.lambda [z] [.pair α β'] (.or
        (.eq (.the (.app S (.fst (.var z)))) (.snd (.var z)))
        (.exists [sndz!] [β'] (.and sndz!_spec (.eq (.the (.app T (.fst (.var z)))) (.var sndz!))))),
        .fun (.pair α β') .bool)
    else if β' ⊑ β then
    /-
      S : α -> Option β    T : α -> Option β'    β' ⊑ β
      ----------------------------------------------------------------------------
      S ∪ T    ↪    λ z : α × β. (∃ sndz!, sndz!_spec ∧ the (S (fst z)) = sndz!) ∨ the (T (fst z)) = snd z
    -/
      let z ← freshVar (.pair α β)
      let ⟨sndz!, sndz!_spec⟩ ← loosen "union!" (.fst (.var z)) β β'
      return (.lambda [z] [.pair α β] (.or
        (.exists [sndz!] [β'] (.and sndz!_spec (.eq (.the (.app S (.fst (.var z)))) (.var sndz!))))
        (.eq (.the (.app T (.fst (.var z)))) (.snd (.var z)))),
        .fun (.pair α β) .bool)
    else throw s!"castUnion: Failed to unify {β} with {β'}"
  else if α ⊑ α' then
    if β == β' then
    /-
      S : α -> Option β    T : α' -> Option β    α ⊑ α'
      ----------------------------------------------------------------------------------------------------
      S ∪ T    ↪    λ z : α × β. the (S (fst z)) = snd z ∨ (∃ fstz!, fstz!_spec ∧ the (T (fstz!)) = snd z)
    -/
      let z ← freshVar (.pair α β)
      let ⟨fstz!, fstz!_spec⟩ ← loosen "union!" (.fst (.var z)) α α'
      return (.lambda [z] [.pair α β] (.or
        (.eq (.the (.app S (.fst (.var z)))) (.snd (.var z)))
        (.exists [fstz!] [α'] (.and fstz!_spec (.eq (.the (.app T (.var fstz!))) (.snd (.var z)))))),
        .fun (.pair α β) .bool)
    else if β ⊑ β' then
    /-
      NOTE: First solution:
      S : α -> Option β    T : α' -> Option β'    α ⊑ α'    β ⊑ β'
      ---------------------------------------------------------------------------------------------------
      S ∪ T    ↪    λ z : α × β. the (S (fst z)) = snd z ∨ (∃ z!, z!_spec ∧ the (T (fst z!)) = snd z!)
    -/
      let z ← freshVar (.pair α β)
      let ⟨z!, z!_spec⟩ ← loosen "union!" (.var z) (.pair α β) (.pair α' β')
      return (.lambda [z] [.pair α β] (.or
        (.eq (.the (.app S (.fst (.var z)))) (.snd (.var z)))
        (.exists [z!] [.pair α' β'] (.and z!_spec (.eq (.the (.app T (.fst (.var z!)))) (.snd (.var z!)))))),
        .fun (.pair α β) .bool)
      /-
        NOTE: Second solution:
        S : α -> Option β    T : α' -> Option β'    α ⊑ α'    β ⊑ β'
        ---------------------------------------------------------------------------------------------------
        S ∪ T    ↪    λ z : α' × β'. (∃ S!, S!_spec ∧ the (S! (fst z)) = snd z) ∨ the (T (fst z)) = snd z
      -/
      -- let z ← freshVar (.pair α' β')
      -- let ⟨S!, S!_spec⟩ ← loosen S (.fun α (.option β)) (.fun α' (.option β))
      -- return (.lambda [z] [.pair α' β'] (.or
      --   (.exists [S!] [.fun α' (.option β)] (.and S!_spec (.eq (.the (.app (.var S!) (.fst (.var z)))) (.snd (.var z)))))
      --   (.eq (.the (.app T (.fst (.var z)))) (.snd (.var z)))),
      --   .fun (.pair α' β') .bool)
    else if β' ⊑ β then
    /-
      NOTE: a choice on what terms are loosened and the output type is made again here, as above
      S : α -> Option β    T : α' -> Option β'    α ⊑ α'    β' ⊑ β
      ---------------------------------------------------------------------------------------------------
      S ∪ T    ↪    λ u : α, v : β'. (∃ v!, v!_spec ∧ the (S u) = v!) ∨ (∃ u!, u!_spec ∧ the (T u!) = v)
    -/
      let z ← freshVar (.pair α' β)
      let ⟨u!, u!_spec⟩ ← loosen "union!" (.fst (.var z)) α α'
      let ⟨v!, v!_spec⟩ ← loosen "union!" (.snd (.var z)) β' β
      return (.lambda [z] [.pair α β'] (.or
          (.exists [v!] [β] (.and v!_spec (.eq (.the (.app S (.fst (.var z)))) (.var v!))))
          (.exists [u!] [α'] (.and u!_spec (.eq (.the (.app T (.var u!))) (.snd (.var z)))))),
        .fun (.pair α β') .bool)
    else throw s!"castUnion: Failed to unify {β} with {β'}"
  else if α' ⊑ α then do
    if β == β' then
    /-
      S : α -> Option β    T : α' -> Option β    α' ⊑ α
      -----------------------------------------------------------------------------------------------------
      S ∪ T    ↪    λ z : α' × β. (∃ fstz!, fstz!_spec ∧ the (S (fstz!)) = snd z) ∨ the (T (fst z)) = snd z
    -/
      let z ← freshVar (.pair α' β)
      let ⟨fstz!, fstz!_spec⟩ ← loosen "union!" (.fst (.var z)) α' α
      return (.lambda [z] [.pair α' β] (.or
        (.exists [fstz!] [α] (.and fstz!_spec (.eq (.the (.app S (.var fstz!))) (.snd (.var z)))))
        (.eq (.the (.app T (.fst (.var z)))) (.snd (.var z)))), .fun (.pair α' β) .bool)
    else if β ⊑ β' then
    /-
      S : α -> Option β    T : α' -> Option β'    α' ⊑ α    β ⊑ β'
      --------------------------------------------------------------------------------------------------
      S ∪ T    ↪    λ u : α', v : β. (∃ v!, v!_spec ∧ the (S u) = v!) ∨ (∃ u!, u!_spec ∧ the (T u!) = v)
    -/
      let z ← freshVar (.pair α' β)
      let ⟨u!, u!_spec⟩ ← loosen "union!" (.fst (.var z)) α' α
      let ⟨v!, v!_spec⟩ ← loosen "union!" (.snd (.var z)) β β'
      return (.lambda [z] [.pair α' β] (.or
        (.exists [v!] [β] (.and v!_spec (.eq (.the (.app S (.fst (.var z)))) (.var v!))))
        (.exists [u!] [α] (.and u!_spec (.eq (.the (.app T (.var u!))) (.snd (.var z)))))), .fun (.pair α' β) .bool)
    else if β' ⊑ β then
    /-
      S : α -> Option β    T : α' -> Option β'    α' ⊑ α    β' ⊑ β
      -------------------------------------------------------------------------------------------------
      S ∪ T    ↪    λ z : α' × β'. (∃ z!, z!_spec ∧ the (S (fst z!)) = snd z) ∨ the (T (fst z)) = snd z
    -/
      let z ← freshVar (.pair α' β')
      let ⟨z!, z!_spec⟩ ← loosen "union!" (.var z) (.pair α' β') (.pair α β)
      return (.lambda [z] [.pair α' β'] (.or
        (.exists [z!] [.pair α β] (.and z!_spec (.eq (.the (.app S (.fst (.var z!)))) (.snd (.var z)))))
        (.eq (.the (.app T (.fst (.var z)))) (.snd (.var z)))), .fun (.pair α' β') .bool)
    else throw s!"castUnion: Failed to unify {β} with {β'}"
  else throw s!"castUnion: Failed to unify {α} with {α'}"

def castUnion_aux_fun_rel : Term × SMTType × SMTType → Term × SMTType × SMTType → Encoder (Term × SMTType) := λ ⟨S, α, β⟩ ⟨T, α', β'⟩ => do
  if α == α' then
    if β == β' then
    /-
      S : α -> Option β    T : α × β -> bool
      ------------------------------------------------
      S ∪ T    ↪    λ z. the (S (fst z)) = snd z ∨ T z
    -/
      let z ← freshVar (.pair α β)
      return (.lambda [z] [.pair α β] (.or (.eq (.the (.app S (.fst (.var z)))) (.snd (.var z))) (.app T (.var z))), .fun (.pair α β) .bool)
    else if β ⊑ β' then
    /-
      S : α -> Option β    T : α × β' -> bool    β ⊑ β'
      -----------------------------------------------------------------------------------------
      S ∪ T    ↪    λ z. the (S (fst z)) = snd z ∨ (∃ sndz!, sndz!_spec ∧ T (pair (fst z) sndz!))
    -/
      let z ← freshVar (.pair α β)
      let ⟨sndz!, sndz!_spec⟩ ← loosen "union!" (.snd (.var z)) β β'
      return (.lambda [z] [.pair α β] (.or
        (.eq (.the (.app S (.fst (.var z)))) (.snd (.var z)))
        (.exists [sndz!] [β'] (.and sndz!_spec (.app T (.pair (.fst (.var z)) (.var sndz!)))))),
        .fun (.pair α β) .bool)
    else if β' ⊑ β then
    /-
      S : α -> Option β    T : α × β' -> bool    β' ⊑ β
      ------------------------------------------------------------------------
      S ∪ T    ↪    λ z. (∃ sndz!, sndz!_spec ∧ the (S (fst z)) = sndz!) ∨ T z
    -/
      let z ← freshVar (.pair α β')
      let ⟨sndz!, sndz!_spec⟩ ← loosen "union!" (.snd (.var z)) β' β
      return (.lambda [z] [.pair α β'] (.or
        (.exists [sndz!] [β] (.and sndz!_spec (.eq (.the (.app S (.fst (.var z)))) (.var sndz!))))
        (.app T (.var z))),
        .fun (.pair α β') .bool)
    else throw s!"castUnion: Failed to unify {β} with {β'}"
  else if α ⊑ α' then
    if β == β' then
    /-
      S : α -> Option β    T : α' × β -> bool    α ⊑ α'
      ------------------------------------------------------------------------------------------
      S ∪ T    ↪    λ z. the (S (fst z)) = snd z ∨ (∃ fstz!, fstz!_spec ∧ T (pair fstz! (snd z))
    -/
      let z ← freshVar (.pair α β)
      let ⟨fstz!, fstz!_spec⟩ ← loosen "union!" (.fst (.var z)) α α'
      return (.lambda [z] [.pair α β] (.or
        (.eq (.the (.app S (.fst (.var z)))) (.snd (.var z)))
        (.exists [fstz!] [α'] (.and fstz!_spec (.app T (.pair (.var fstz!) (.snd (.var z))))))), .fun (.pair α β) .bool)
    else if β ⊑ β' then
    /-
      S : α -> Option β    T : α' × β' -> bool    α ⊑ α'    β ⊑ β'
      ------------------------------------------------------------------
      S ∪ T    ↪    λ z. the (S (fst z)) = snd z ∨ (∃ z!, z!_spec ∧ T z!
    -/
      let z ← freshVar (.pair α β)
      let ⟨z!, z!_spec⟩ ← loosen "union!" (.var z) (.pair α β) (.pair α' β')
      return (.lambda [z] [.pair α β] (.or
        (.eq (.the (.app S (.fst (.var z)))) (.snd (.var z)))
        (.exists [z!] [.pair α' β'] (.and z!_spec (.app T (.var z!))))), .fun (.pair α β) .bool)
    else if β' ⊑ β then
    /-
      S : α -> Option β    T : α' × β' -> bool    α ⊑ α'    β' ⊑ β
      ----------------------------------------------------------------------------------------------------------------
      S ∪ T    ↪    λ z. (∃ fstz!, fstz!_spec ∧ the (S (fstz!)) = snd z) ∨ (∃ sndz!, sndz!_spec ∧ T (pair fst z sndz!)
    -/
      let z ← freshVar (.pair α β')
      let ⟨fstz!, fstz!_spec⟩ ← loosen "union!" (.fst (.var z)) α α'
      let ⟨sndz!, sndz!_spec⟩ ← loosen "union!" (.snd (.var z)) β' β
      return (.lambda [z] [.pair α β'] (.or
        (.exists [fstz!] [α'] (.and fstz!_spec (.eq (.the (.app S (.var fstz!))) (.snd (.var z)))))
        (.exists [sndz!] [β] (.and sndz!_spec (.app T (.pair (.fst (.var z)) (.var sndz!)))))),
        .fun (.pair α β') .bool)
    else throw s!"castUnion: Failed to unify {β} with {β'}"
  else if α' ⊑ α then
    if β == β' then
    /-
      S : α -> Option β    T : α' × β -> bool    α' ⊑ α
      ------------------------------------------------------------------------
      S ∪ T    ↪    λ z. (∃ fstz!, fstz!_spec ∧ the (S (fstz!)) = snd z) ∨ T z
    -/
      let z ← freshVar (.pair α' β)
      let ⟨fstz!, fstz!_spec⟩ ← loosen "union!" (.fst (.var z)) α' α
      return (.lambda [z] [.pair α' β] (.or
        (.exists [fstz!] [α] (.and fstz!_spec (.eq (.the (.app S (.var fstz!))) (.snd (.var z)))))
        (.app T (.var z))), .fun (.pair α' β) .bool)
    else if β ⊑ β' then
    /-
      S : α -> Option β    T : α' × β' -> bool    α' ⊑ α    β ⊑ β'
      ----------------------------------------------------------------------------------------------------------------
      S ∪ T    ↪    λ z. (∃ fstz!, fstz!_spec ∧ the (S (fstz!)) = snd z) ∨ (∃ sndz!, sndz!_spec ∧ T (pair fstz! sndz!)
    -/
      let z ← freshVar (.pair α' β)
      let ⟨fstz!, fstz!_spec⟩ ← loosen "union!" (.fst (.var z)) α' α
      let ⟨sndz!, sndz!_spec⟩ ← loosen "union!" (.snd (.var z)) β β'
      return (.lambda [z] [.pair α' β] (.or
        (.exists [fstz!] [α] (.and fstz!_spec (.eq (.the (.app S (.var fstz!))) (.snd (.var z)))))
        (.exists [sndz!] [β'] (.and sndz!_spec (.app T (.pair (.var fstz!) (.var sndz!)))))),
        .fun (.pair α' β) .bool)
    else if β' ⊑ β then
    /-
      S : α -> Option β    T : α' × β' -> bool    α' ⊑ α    β' ⊑ β
      -------------------------------------------------------------------
      S ∪ T    ↪    λ z. (∃ z!, z!_spec ∧ the (S (fst z!)) = snd z) ∨ T z
    -/
      let z ← freshVar (.pair α' β')
      let ⟨z!, z!_spec⟩ ← loosen "union!" (.var z) (.pair α' β') (.pair α β)
      return (.lambda [z] [.pair α' β'] (.or
        (.exists [z!] [.pair α β] (.and z!_spec (.eq (.the (.app S (.fst (.var z!)))) (.snd (.var z)))))
        (.app T (.var z))), .fun (.pair α' β') .bool)
    else throw s!"castUnion: Failed to unify {β} with {β'}"
  else throw s!"castUnion: Failed to unify {α} with {α'}"

-- set_option trace.profiler true in
def castUnion : Term × SMTType → Term × SMTType → Encoder (Term × SMTType) := λ ⟨S, α⟩ ⟨T, β⟩ =>
  match α, β with
  | SMTType.fun (.pair α β) .bool, SMTType.fun (.pair α' β') .bool => castUnion_aux_rel_rel (S, α, β) (T, α', β')
  | SMTType.fun α .bool, SMTType.fun α' .bool => castUnion_aux_set_set (S, α) (T, α')
  | SMTType.fun α (.option β), SMTType.fun α' (.option β') => castUnion_aux_fun_fun (S, α, β) (T, α', β')
  | SMTType.fun α (.option β), SMTType.fun (.pair α' β') .bool => castUnion_aux_fun_rel (S, α, β) (T, α', β')
  | SMTType.fun (.pair α β) .bool, SMTType.fun α' (.option β') => castUnion_aux_fun_rel (T, α', β') (S, α, β)
  | _, _ => throw s!"castUnion: Not implemented yet for types {α} and {β}"

def castInter_aux_rel_rel : Term × SMTType × SMTType → Term × SMTType × SMTType → Encoder (Term × SMTType) := λ ⟨S, α, β⟩ ⟨T, α', β'⟩ => do
  if α == α' then
    if β == β' then
    /-
      S : α × β -> bool    T : α × β -> bool
      --------------------------------------
      S ∩ T    ↪    λ z. S z ∧ T z
    -/
      let z ← freshVar (.pair α β)
      return (.lambda [z] [.pair α β] (.and (.app S (.var z)) (.app T (.var z))), .fun (.pair α β) .bool)
    else if β ⊑ β' then
    /-
      S : α × β -> bool    T : α × β' -> bool    β ⊑ β'
      ------------------------------------------------------------
      S ∩ T    ↪    λ z. S z ∧ (∃ v!, v!_spec ∧ T (pair (fst z) v!))
    -/
      let z ← freshVar (.pair α β)
      let ⟨sndz!, sndz!_spec⟩ ← loosen "inter!" (.snd (.var z)) β β'
      return (.lambda [z] [.pair α β] (.and
        (.app S (.var z))
        (.exists [sndz!] [β'] (.and sndz!_spec (.app T (.pair (.fst (.var z)) (.var sndz!)))))),
        .fun (.pair α β) .bool)
    else if β' ⊑ β then
    /-
      S : α × β -> bool    T : α × β' -> bool    β' ⊑ β
      ------------------------------------------------------------
      S ∩ T    ↪    λ z. (∃ v!, v!_spec ∧ S (pair (fst z) v!)) ∧ T z
    -/
      let z ← freshVar (.pair α β')
      let ⟨sndz!, sndz!_spec⟩ ← loosen "inter!" (.snd (.var z)) β' β
      return (.lambda [z] [.pair α β'] (.and
        (.exists [sndz!] [β] (.and sndz!_spec (.app S (.pair (.fst (.var z)) (.var sndz!)))))
        (.app T (.var z))),
        .fun (.pair α β') .bool)
    else throw s!"castInter: Cannot unify {β} with {β'}"
  else if α ⊑ α' then
    if β == β' then
    /-
      S : α × β -> bool    T : α' × β -> bool    α ⊑ α'
      ------------------------------------------------------------
      S ∩ T    ↪    λ z. S z ∧ (∃ z!, z!_spec ∧ T z!)
    -/
      let z ← freshVar (.pair α β)
      let ⟨fstz!, fstz!_spec⟩ ← loosen "inter!" (.fst (.var z)) α α'
      return (.lambda [z] [.pair α β] (.and
        (.app S (.var z))
        (.exists [fstz!] [α'] (.and fstz!_spec (.app T (.pair (.var fstz!) (.snd (.var z))))))),
        .fun (.pair α β) .bool)
    else if β ⊑ β' then
    /-
      S : α × β -> bool    T : α' × β' -> bool    α ⊑ α'    β ⊑ β'
      ------------------------------------------------------------
      S ∩ T    ↪    λ z. S z ∧ (∃ z!, z!_spec ∧ T z!)
    -/
      let z ← freshVar (.pair α β)
      let ⟨z!, z!_spec⟩ ← loosen "inter!" (.var z) (.pair α β) (.pair α' β')
      return (.lambda [z] [.pair α β] (.and
        (.app S (.var z))
        (.exists [z!] [.pair α' β'] (.and z!_spec (.app T (.var z!))))),
        .fun (.pair α β) .bool)
    else if β' ⊑ β then
    /-
      S : α × β -> bool    T : α' × β' -> bool    α ⊑ α'    β' ⊑ β
      ------------------------------------------------------------------------------------
      S ∩ T    ↪    λ z. (∃ u!, u!_spec ∧ S (u!, snd z)) ∧ (∃ v!, v!_spec ∧ T (fst z, v!))
    -/
      let z ← freshVar (.pair α β')
      let ⟨fstz!, fstz!_spec⟩ ← loosen "inter!" (.fst (.var z)) α α'
      let ⟨sndz!, sndz!_spec⟩ ← loosen "inter!" (.snd (.var z)) β' β
      return (.lambda [z] [.pair α β'] (.and
        (.exists [sndz!] [β] (.and sndz!_spec (.app S (.pair (.fst (.var z)) (.var sndz!)))))
        (.exists [fstz!] [α'] (.and fstz!_spec (.app T (.pair (.var fstz!) (.snd (.var z))))))),
        .fun (.pair α β') .bool)
    else throw s!"castInter: Cannot unify {β} with {β'}"
  else if α' ⊑ α then
    if β == β' then
    /-
      S : α × β -> bool    T : α' × β -> bool    α' ⊑ α
      ------------------------------------------------------------
      S ∩ T    ↪    λ z. (∃ z!, z!_spec ∧ S z!) ∧ T z
    -/
      let z ← freshVar (.pair α' β)
      let ⟨fstz!, fstz!_spec⟩ ← loosen "inter!" (.fst (.var z)) α' α
      return (.lambda [z] [.pair α' β] (.and
        (.exists [fstz!] [α] (.and fstz!_spec (.app S (.pair (.var fstz!) (.snd (.var z))))))
        (.app T (.var z))),
        .fun (.pair α' β) .bool)
    else if β ⊑ β' then
    /-
      S : α × β -> bool    T : α' × β' -> bool    α' ⊑ α    β ⊑ β'
      ------------------------------------------------------------
      S ∩ T    ↪    λ z. (∃ u!, u!_spec ∧ S (u!, snd z)) ∧ (∃ v!, v!_spec ∧ T (fst z, v!))
    -/
      let z ← freshVar (.pair α' β)
      let ⟨fstz!, fstz!_spec⟩ ← loosen "inter!" (.fst (.var z)) α' α
      let ⟨sndz!, sndz!_spec⟩ ← loosen "inter!" (.snd (.var z)) β β'
      return (.lambda [z] [.pair α' β] (.and
        (.exists [fstz!] [α] (.and fstz!_spec (.app S (.pair (.var fstz!) (.snd (.var z))))))
        (.exists [sndz!] [β'] (.and sndz!_spec (.app T (.pair (.fst (.var z)) (.var sndz!)))))),
        .fun (.pair α' β) .bool)
    else if β' ⊑ β then
    /-
      S : α × β -> bool    T : α' × β -> bool    α' ⊑ α    β' ⊑ β
      ------------------------------------------------------------
      S ∩ T    ↪    λ z. (∃ z!, z!_spec ∧ S z!) ∧ T z
    -/
      let z ← freshVar (.pair α' β')
      let ⟨z!, z!_spec⟩ ← loosen "inter!" (.var z) (.pair α' β') (.pair α β)
      return (.lambda [z] [.pair α' β'] (.and
        (.exists [z!] [.pair α β] (.and z!_spec (.app S (.var z!))))
        (.app T (.var z))),
        .fun (.pair α' β') .bool)
    else throw s!"castInter: Cannot unify {β} with {β'}"
  else throw s!"castInter: Cannot unify {α} with {α'}"

def castInter_aux_set_set : Term × SMTType → Term × SMTType → Encoder (Term × SMTType) := λ ⟨S, α⟩ ⟨T, α'⟩ => do
  if α == α' then
  /-
    S : α -> bool    T : α -> bool
    ------------------------------
    S ∩ T    ↪    λ z. S z ∧ T z
  -/
    let z ← freshVar α
    return (.lambda [z] [α] (.and (.app S (.var z)) (.app T (.var z))), .fun α .bool)
  else if α ⊑ α' then
  /-
    S : α -> bool    T : α' -> bool    α ⊑ α'
    -------------------------------------------
    S ∩ T    ↪    λ z. S z ∧ (∃ z!, z!_spec ∧ T z!)
  -/
    let z ← freshVar α
    let ⟨z!, z!_spec⟩ ← loosen "inter!" (.var z) α α'
    return (.lambda [z] [α] (.and (.app S (.var z)) (.exists [z!] [α'] (.and z!_spec (.app T (.var z!))))), .fun α .bool)
  else if α' ⊑ α then
  /-
    S : α -> bool    T : α' -> bool    α' ⊑ α
    -------------------------------------------
    S ∩ T    ↪    λ z. (∃ z!, z!_spec ∧ S z!) ∧ T z
  -/
    let z ← freshVar α'
    let ⟨z!, z!_spec⟩ ← loosen "inter!" (.var z) α' α
    return (.lambda [z] [α'] (.and (.exists [z!] [α] (.and z!_spec (.app S (.var z)))) (.app T (.var z))), .fun α' .bool)
  else throw s!"castInter_aux_set_set: Cannot unify {α} with {α'}"

def castInter_aux_fun_fun : Term × SMTType × SMTType → Term × SMTType × SMTType → Encoder (Term × SMTType) := λ ⟨S, α, β⟩ ⟨T, α', β'⟩ => do
  if α == α' then
    if β == β' then
    /-
      S : α -> Option β    T : α -> Option β
      ------------------------------------------------
      S ∩ T    ↪    λ z. if (S z) = (T z) then S z else none
    -/
      let z ← freshVar α
      return (.lambda [z] [α] (.ite (.eq (.app S (.var z)) (.app T (.var z))) (.app S (.var z)) (none$β)), .fun α (.option β))
    else if β ⊑ β' then
    /-
      NOTE: we can either loosen S directly, or S z only since z is bound in the lambda
      S : α -> Option β    T : α -> Option β'    β ⊑ β'
      ------------------------------------------------------------
      S ∩ T    ↪    λ z. if (∃ S!. S!_spec ∧ S! z = T z) then S z else none
    -/
      let ⟨S!, S!_spec⟩ ← loosen "inter!" S (.fun α (.option β)) (.fun α (.option β'))
      declareConst S! (SMTType.fun α (.option β))
      let z ← freshVar α
      return (.lambda [z] [α] (.ite (.and S!_spec (.eq (.app (.var S!) (.var z)) (.app T (.var z)))) (.app S (.var z)) (none$β)), .fun α (.option β))
    else if β' ⊑ β then
    /-
      NOTE: same remark as above
      S : α -> Option β    T : α -> Option β'    β' ⊑ β
      ------------------------------------------------------------
      S ∩ T    ↪    λ z. if (∃ T!. T!_spec ∧ S z = T! z) then S z else none
    -/
      let ⟨T!, T!_spec⟩ ← loosen "inter!" T (.fun α (.option β')) (.fun α (.option β))
      declareConst T! (SMTType.fun α (.option β))
      let z ← freshVar α
      return (.lambda [z] [α] (.ite
        (.and T!_spec (.eq (.app S (.var z)) (.app (.var T!) (.var z))))
        (.app T (.var z))
        (none$β)),
        .fun α (.option β'))
    else throw s!"castInter_aux_fun_fun: Cannot unify {β} with {β'}"
  else if α ⊑ α' then
    if β == β' then
    /-
      S : α -> Option β    T : α' -> Option β    α ⊑ α'
      ---------------------------------------------------------------------
      S ∩ T    ↪    λ z. if (∃ z!. z!_spec ∧ S z = T z!) then S z else none
    -/
      let z ← freshVar α
      let ⟨z!, z!_spec⟩ ← loosen "inter!" (.var z) α α'
      return (.lambda [z] [α] (.ite
        (.exists [z!] [α'] (.and z!_spec (.eq (.app S (.var z)) (.app T (.var z!)))))
        (.app S (.var z))
        (none$β)),
        .fun α (.option β))
    else if β ⊑ β' then
    /-
      S : α -> Option β    T : α' -> Option β'    α ⊑ α'    β ⊑ β'
      ------------------------------------------------------------------------------ where p! loosens (z, S z)
      S ∩ T    ↪    λ z. if (∃ p!. p!_spec ∧ snd p! = T (fst p!)) then S z else none
    -/
      let z ← freshVar α
      let ⟨p!, p!_spec⟩ ← loosen "inter!" (.pair (.var z) (.the (.app S (.var z)))) (.pair α β) (.pair α' β')
      let z! : Term := .fst (.var p!)
      let Sz! : Term := .snd (.var p!)
      return (.lambda [z] [α] (.ite
        (.exists [p!] [.pair α' β'] (.and p!_spec (.eq Sz! (.app T z!))))
        (.app S (.var z))
        (none$β)),
        .fun α (.option β))
    else if β' ⊑ β then
    /-
      S : α -> Option β    T : α' -> Option β'    α ⊑ α'    β' ⊑ β
      --------------------------------------------------------------------------------
      S ∩ T    ↪    λ z. if (∃ z!. z!_spec ∧ T!_spec ∧ S z = T! z!) then S z else none
    -/
      let ⟨T!, T!_spec⟩ ← loosen "inter!" T (.fun α' (.option β')) (.fun α' (.option β))
      declareConst T! (SMTType.fun α' (.option β))
      let z ← freshVar α
      let ⟨z!, z!_spec⟩ ← loosen "inter!" (.var z) α α'
      return (.lambda [z] [α] (.ite
        (.exists [z!] [α'] (.and z!_spec (.and T!_spec (.eq (.app S (.var z)) (.app (.var T!) (.var z!))))))
        (.app S (.var z))
        (none$β)),
        .fun α (.option β))
    else throw s!"castInter_aux_fun_fun: Cannot unify {β} with {β'}"
  else if α' ⊑ α then
    if β == β' then
    /-
      S : α -> Option β    T : α' -> Option β    α' ⊑ α
      ----------------------------------------------------------------------
      S ∩ T    ↪    λ z. if (∃ z!. z!_spec ∧ S z! = T z) then T z else none
    -/
      let z ← freshVar α'
      let ⟨z!, z!_spec⟩ ← loosen "inter!" (.var z) α' α
      return (.lambda [z] [α'] (.ite
        (.exists [z!] [α] (.and z!_spec (.eq (.app S (.var z!)) (.app T (.var z)))))
        (.app T (.var z))
        (none$β)),
        .fun α' (.option β))
    else if β ⊑ β' then
    /-
      NOTE: we get the mgt on the rhs in this case and the lgt on the lhs
      S : α -> Option β    T : α' -> Option β'    α' ⊑ α    β ⊑ β'
      --------------------------------------------------------------------------------
      S ∩ T    ↪    λ z. if (∃ z!. z!_spec ∧ S!_spec ∧ S! z! = T z) then T z else none
    -/
      let ⟨S!, S!_spec⟩ ← loosen "inter!" S (.fun α (.option β)) (.fun α (.option β'))
      declareConst S! (SMTType.fun α (.option β'))
      let z ← freshVar α'
      let ⟨z!, z!_spec⟩ ← loosen "inter!" (.var z) α' α
      return (.lambda [z] [α'] (.ite
        (.exists [z!] [α] (.and z!_spec (.and S!_spec (.eq (.app (.var S!) (.var z!)) (.app T (.var z))))))
        (.app T (.var z))
        (none$β')),
        .fun α' (.option β'))
    else if β' ⊑ β then
    /-
      S : α -> Option β    T : α' -> Option β'    α' ⊑ α    β' ⊑ β
      --------------------------------------------------------------------------------
      S ∩ T    ↪    λ z. if (∃ z!. z!_spec ∧ T!_spec ∧ S z = T! z!) then T z else none
    -/
      let z ← freshVar α'
      let ⟨p!, p!_spec⟩ ← loosen "inter!" (.pair (.var z) (.the (.app T (.var z)))) (.pair α' β') (.pair α β)
      let z! : Term := .fst (.var p!)
      let Tz! : Term := .snd (.var p!)
      return (.lambda [z] [α'] (.ite
        (.exists [p!] [.pair α β] (.and p!_spec (.eq Tz! (.app S z!))))
        (.app T (.var z))
        (none$β')),
        .fun α' (.option β'))
    else throw s!"castInter_aux_fun_fun: Cannot unify {β} with {β'}"
  else throw s!"castInter_aux_fun_fun: Cannot unify {α} with {α'}"

def castInter_aux_fun_rel : Term × SMTType × SMTType → Term × SMTType × SMTType → Encoder (Term × SMTType) := λ ⟨S, α, β⟩ ⟨T, α', β'⟩ => do
  if α == α' then
    if β == β' then
    /-
      S : α -> Option β    T : α × β -> bool
      ------------------------------------------------
      S ∩ T    ↪    λ z. if T (pair z (S z)) then S z else none
    -/
      let z ← freshVar α
      return (.lambda [z] [α] (.ite (.app T (.pair (.var z) (.the (.app S (.var z))))) (.app S (.var z)) (none$β)), .fun α (.option β))
    else if β ⊑ β' then
    /-
      S : α -> Option β    T : α × β' -> bool    β ⊑ β'
      ------------------------------------------------------------------------ where v! loosens S z
      S ∩ T    ↪    λ z. if (∃ v!, v!_spec ∧ T (pair z v!)) then S z else none
    -/
      let z ← freshVar α
      let ⟨sndz!, sndz!_spec⟩ ← loosen "inter!" (.the (.app S (.var z))) β β'
      return (.lambda [z] [α] (.ite
        (.exists [sndz!] [β'] (.and sndz!_spec (.app T (.pair (.var z) (.var sndz!)))))
        (.app S (.var z))
        (none$β)),
        .fun α (.option β))
    else if β' ⊑ β then
    /-
      NOTE: we have the choice between
        - loosening T directly: preserves the functional structure, we get the mgt
        - loosening S z: we get a relation, and the lgt
      S : α -> Option β    T : α × β' -> bool    β' ⊑ β
      -----------------------------------------------------------------------
      S ∩ T    ↪    λ z. if (T!_spec ∧ T! (.pair z (S z))) then S z else none
    -/
      let ⟨T!, T!_spec⟩ ← loosen "inter!" T (.fun (.pair α β') .bool) (.fun (.pair α β) .bool)
      declareConst T! (SMTType.fun (.pair α β) .bool)
      let z ← freshVar α
      return (.lambda [z] [α] (.ite
        (.and T!_spec (.app (.var T!) (.pair (.var z) (.the (.app S (.var z))))))
        (.app S (.var z))
        (none$β)),
        .fun α (.option β))
    else throw s!"castInter_aux_fun_rel: Cannot unify {β} with {β'}"
  else if α ⊑ α' then
    if β == β' then
    /-
      S : α -> Option β    T : α' × β -> bool    α ⊑ α'
      ---------------------------------------------------------------
      S ∩ T    ↪    λ z. if (∃ z!. z!_spec ∧ T (z!, S z)) then S z else none
    -/
      let z ← freshVar α
      let ⟨z!, z!_spec⟩ ← loosen "inter!" (.var z) α α'
      return (.lambda [z] [α] (.ite
        (.exists [z!] [α'] (.and z!_spec (.app T (.pair (.var z!) (.the (.app S (.var z)))))))
        (.app S (.var z))
        (none$β)),
        .fun α (.option β))
    else if β ⊑ β' then
    /-
      S : α -> Option β    T : α' × β' -> bool    α ⊑ α'    β ⊑ β'
      --------------------------------------------------------------- where z! loosens pair z (S z)
      S ∩ T    ↪    λ z. if (∃ z!. z!_spec ∧ T z!) then S z else none
    -/
      let z ← freshVar α
      let ⟨z!, z!_spec⟩ ← loosen "inter!" (.pair (.var z) (.the (.app S (.var z)))) (.pair α β) (.pair α' β')
      return (.lambda [z] [α] (.ite
        (.exists [z!] [.pair α' β'] (.and z!_spec (.app T (.var z!))))
        (.app S (.var z))
        (none$β)),
        .fun α (.option β))
    else if β' ⊑ β then
    /-
      S : α -> Option β    T : α' × β' -> bool   α ⊑ α'    β' ⊑ β
      ---------------------------------------------------------------------------------------------
      S ∩ T    ↪    λ z. if (∃ z!. z!_spec ∧ T!_spec ∧ T! (pair z! (the (S z)))) then S z else none
    -/
      let ⟨T!, T!_spec⟩ ← loosen "inter!" T (.fun (.pair α' β') .bool) (.fun (.pair α' β) .bool)
      declareConst T! (SMTType.fun (.pair α' β) .bool)
      let z ← freshVar α
      let ⟨z!, z!_spec⟩ ← loosen "inter!" (.var z) α α'
      return (.lambda [z] [α] (.ite
        (.exists [z!] [α'] (.and z!_spec (.and T!_spec (.app (.var T!) (.pair (.var z!) (.the (.app S (.var z))))))))
        (.app S (.var z))
        (none$β)),
        .fun α (.option β))
    else throw s!"castInter_aux_fun_fun: Cannot unify {β} with {β'}"
  else if α' ⊑ α then
    if β == β' then
    /-
      NOTE: we have the choice between
        - loosening T directly: preserves the functional structure, we get the mgt
        - loosening T z: we get a relation, and the lgt
      S : α -> Option β    T : α' × β -> bool    α' ⊑ α
      ----------------------------------------------------------------------
      S ∩ T    ↪    λ z. if (T!_spec ∧ T! (pair z (S z))) then S z else none
    -/
      let ⟨T!, T!_spec⟩ ← loosen "inter!" T (.fun (.pair α' β) .bool) (.fun (.pair α β) .bool)
      declareConst T! (SMTType.fun (.pair α β) .bool)
      let z ← freshVar α
      return (.lambda [z] [α] (.ite
        (.and T!_spec (.app (.var T!) (.pair (.var z) (.the (.app S (.var z))))))
        (.app S (.var z))
        (none$β)),
        .fun α (.option β))
    else if β ⊑ β' then
    /-
      NOTE: this is an intricate case that requires a lot of loosening (bad for performance)
      S : α -> Option β    T : α' × β' -> bool    α' ⊑ α    β ⊑ β'
      ---------------------------------------------------------------
      S ∩ T    ↪    λ z. if (∃ z!. z!_spec ∧ T z!) then S z else none
    -/
      let ⟨T!, T!_spec⟩ ← loosen "inter!" T (.fun (.pair α' β') .bool) (.fun (.pair α β') .bool)
      declareConst T! (SMTType.fun (.pair α β') .bool)
      let ⟨S!, S!_spec⟩ ← loosen "inter!" S (.fun α (.option β)) (.fun α (.option β'))
      declareConst S! (SMTType.fun α (.option β'))
      let z ← freshVar α
      return (.lambda [z] [α] (.ite
        (.and S!_spec (.and T!_spec (.app (.var T!) (.pair (.var z) (.the (.app (.var S!) (.var z)))))))
        (.app S (.var z))
        (none$β)),
        .fun α (.option β))
    else if β' ⊑ β then
    /-
      NOTE: we get the mgt
      S : α -> Option β    T : α' × β' -> bool    α' ⊑ α    β' ⊑ β
      ----------------------------------------------------------------------
      S ∩ T    ↪    λ z. if (∃ z!. z!_spec ∧ T!_spec ∧ S z = T! z!) then T z else none
    -/
      let ⟨T!, T!_spec⟩ ← loosen "inter!" T (.fun (.pair α' β') .bool) (.fun (.pair α β) .bool)
      declareConst T! (SMTType.fun (.pair α β) .bool)
      let z ← freshVar α
      return (.lambda [z] [α] (.ite
        (.and T!_spec (.app (.var T!) (.pair (.var z) (.the (.app S (.var z))))))
        (.app S (.var z))
        (none$β)),
        .fun α (.option β))
    else throw s!"castInter_aux_fun_fun: Cannot unify {β} with {β'}"
  else throw s!"castInter_aux_fun_fun: Cannot unify {α} with {α'}"

def castInter : Term × SMTType → Term × SMTType → Encoder (Term × SMTType) := λ ⟨S, α⟩ ⟨T, β⟩ => do
  match α, β with
  | .fun (.pair α β) .bool, .fun (.pair α' β') .bool => castInter_aux_rel_rel (S, α, β) (T, α', β')
  | .fun α .bool, .fun α' .bool => castInter_aux_set_set (S, α) (T, α')
  | .fun α (.option β), .fun α' (.option β') => castInter_aux_fun_fun (S, α, β) (T, α', β')
  | .fun α (.option β), .fun (.pair α' β') .bool => castInter_aux_fun_rel (S, α, β) (T, α', β')
  | .fun (.pair α β) .bool, .fun α' (.option β') => castInter_aux_fun_rel (T, α', β') (S, α, β)
  | _, _ => throw "castInter: Not implemented yet"
