import Encoder.Simplifier
import Encoder.Loosening

open Batteries SMT

def B.Term.vars (t : B.Term) : List B.𝒱 :=
  fv t ∪ bv t

def B.SimpleGoal.vars (g : B.SimpleGoal) : List B.𝒱 :=
  (g.hyps.map B.Term.vars).flatten ++ g.goal.vars

def B.ProofObligation.vars (po : B.ProofObligation) : List B.𝒱 :=
  (po.defs.map B.Term.vars).flatten ++
  (po.hyps.map B.Term.vars).flatten ++
  (po.goals.map B.SimpleGoal.vars).flatten

def B.Env.initialUsedVars (E : B.Env) : List B.𝒱 := Id.run do
  let mut used := E.context.keys
  used := E.flags ++ used
  for ⟨v, d⟩ in E.defs.entries do
    used := v :: d.vars ++ used
  for ⟨_, hs⟩ in E.hypotheses do
    used := (hs.map B.Term.vars).flatten ++ used
  for ds in E.distinct do
    used := (ds.map B.Term.vars).flatten ++ used
  used := (E.finite.map B.Term.vars).flatten ++ used
  used := (E.po.map B.ProofObligation.vars).flatten ++ used
  return used

def encodeTerm : B.Term → B.Env → Encoder (SMT.Term × SMTType)
  | .var v, E => do
    match (←get).types.lookup v with
    | none => throw s!"encodeTerm:var: Unknown variable {v} in SMT context"
    | some τ => do
      return (.var v, τ)
      -- let .some τ' := E.context.lookup v | return (.var v, τ) --FIXME: hack?
      --   -- throw s!"encodeTerm:var: Missing type for {v} in B context"
      -- if τ = τ'.toSMTType then
      --   return (.var v, τ)
      -- else
      --   throw s!"encodeTerm:var: Type mismatch for {v}: expected {τ}, got {τ'.toSMTType}"
  | .int n, _ => return (.int n, .int)
  | .bool b, _ => return (.bool b, .bool)
  -- | .imp x y, E => do
  --   let ⟨x', .bool⟩ ← encodeTerm x E | throw s!"encodeTerm:imp: Expected a boolean, got {← encodeTerm x E}"
  --   let ⟨y', .bool⟩ ← encodeTerm y E | throw s!"encodeTerm:imp: Expected a boolean, got {← encodeTerm y E}"
  --   return (.imp x' y', .bool)
  -- | .or x y, E => do
  --   let ⟨x', .bool⟩ ← encodeTerm x E | throw s!"encodeTerm:or: Expected a boolean, got {← encodeTerm x E}"
  --   let ⟨y', .bool⟩ ← encodeTerm y E | throw s!"encodeTerm:or: Expected a boolean, got {← encodeTerm y E}"
  --   return (.or x' y', .bool)
  | .and x y, E => do
    let ⟨x', .bool⟩ ← encodeTerm x E | throw s!"encodeTerm:and: Expected a boolean, got {← encodeTerm x E}"
    let ⟨y', .bool⟩ ← encodeTerm y E | throw s!"encodeTerm:and: Expected a boolean, got {← encodeTerm y E}"
    return (.and x' y', .bool)
  | .le x y, E => do
    return (.le (← encodeTerm x E).fst (← encodeTerm y E).fst, .bool)
  | .maplet x y, E => do
    let ⟨x', α⟩ ← encodeTerm x E
    let ⟨y', β⟩ ← encodeTerm y E
    return (.pair x' y', .pair α β)
  | .add x y, E => do
    let ⟨x', .int⟩ ← encodeTerm x E | throw s!"encodeTerm:add: Expected an integer, got {← encodeTerm x E}"
    let ⟨y', .int⟩ ← encodeTerm y E | throw s!"encodeTerm:add: Expected an integer, got {← encodeTerm y E}"
    return (.add x' y', .int)
  | .sub x y, E => do
    let ⟨x', .int⟩ ← encodeTerm x E | throw s!"encodeTerm:sub: Expected an integer, got {← encodeTerm x E}"
    let ⟨y', .int⟩ ← encodeTerm y E | throw s!"encodeTerm:sub: Expected an integer, got {← encodeTerm y E}"
    return (.sub x' y', .int)
  | .mul x y, E => do
    let ⟨x', .int⟩ ← encodeTerm x E | throw s!"encodeTerm:mul: Expected an integer, got {← encodeTerm x E}"
    let ⟨y', .int⟩ ← encodeTerm y E | throw s!"encodeTerm:mul: Expected an integer, got {← encodeTerm y E}"
    return (.mul x' y', .int)
  | .not x, E => do
    let ⟨x', .bool⟩ ← encodeTerm x E | throw s!"encodeTerm:not: Expected a boolean, got {← encodeTerm x E}"
    return (.not x', .bool)
  | .eq A B, E => do
    castEq (← encodeTerm A E) (← encodeTerm B E)
  | .ℤ, _ => do
    let ctx := (←get).types
    let v ← freshVar .int
    modify λ e => { e with types := ctx } -- rollback context but keep freshvarsc incremented
    return (.lambda [v] [.int] (.bool true), .fun .int .bool)
  | .𝔹, _ => do
    let ctx := (←get).types
    let v ← freshVar .bool
    modify λ e => { e with types := ctx } -- rollback context but keep freshvarsc incremented
    return (.lambda [v] [.bool] (.bool true), .fun .bool .bool)
  | .mem x S, E => do
    castMembership (← encodeTerm x E) (← encodeTerm S E)
  | .pow S, E => do
    let ⟨S', τS⟩ ← encodeTerm S E
    match τS with
    | .fun α .bool => do -- `S` is a set
      let ctx := (←get).types
      let x ← freshVar α
      let ℰ ← freshVar <| .fun α .bool
      modify λ e => { e with types := ctx } -- rollback context but keep freshvarsc incremented
      return (.lambda [ℰ] [.fun α .bool] (.forall [x] [α] (.imp (.app (.var ℰ) (.var x)) (.app S' (.var x)))), .fun (.fun α .bool) .bool)
    | .fun α (.option β) => do -- `S` is a function
      -- `𝒫(S) = { f : α +-> β | ∀ x y, f(x) = y ⇒ S(x) = y}`
      let ctx := (←get).types
      let x ← freshVar α
      let y ← freshVar β
      let f ← freshVar <| α.fun β.option
      modify λ e => { e with types := ctx } -- rollback context but keep freshvarsc incremented
      return (.lambda [f] [α.fun β.option] (.forall [x, y] [α, β] (.imp
        (.eq (.app (.var f) (.var x)) (.var y))
        (.eq (.app S' (.var x)) (.var y)))), .fun (α.fun β.option) .bool)
    | _ => throw s!"encodeTerm:pow: Expected a set or a function, got {τS}"
  | .cprod A B, E => do
    let ⟨A', .fun α .bool⟩ ← encodeTerm A E | throw s!"encodeTerm:cprod: Expected a set, got {← encodeTerm A E}"
    let ⟨B', .fun β .bool⟩ ← encodeTerm B E | throw s!"encodeTerm:cprod: Expected a set, got {← encodeTerm B E}"
    let p ← freshVar (.pair α β); let a ← freshVar α; let b ← freshVar β
    -- λ p:α×β.∃ a:α,b:β. a ∈ A ∧ b ∈ B ∧ p = a ↦ b
    return (.lambda [p] [.pair α β] (.exists [a, b] [α, β] (.and (.app A' (.var a)) (.and (.app B' (.var b)) (.eq (.var p) (.pair (.var a) (.var b)))))),
      .fun (.pair α β) .bool)
  | .union S T, E => do
    castUnion (← encodeTerm S E) (← encodeTerm T E)
  | .inter S T, E => do
    castInter (← encodeTerm S E) (← encodeTerm T E)
  -- | .card S, E => _
  | .app f x, E => do
    castApp (← encodeTerm f E) (← encodeTerm x E)
  | .collect vs D P, E => do
    /- two cases : `D` is either a set or a function -/
    let ⟨D', τD⟩ ← encodeTerm D E
    match τD with
    | .fun α (.option β) => do
      -- `D` is a function
      -- {x, y ∈ D | P} = λ x. if P[y ↦ D(x)] then some (D(x)) else none
      let αs := α.fromProdl <| vs.length - 2
      unless αs.length == vs.length - 1 do
        throw s!"encodeTerm:collect: Expected {vs.length - 1} types, got {αs.length}"
      for ⟨v, ξ⟩ in vs.zip (αs.concat β) do
        modify λ e => { e with types := e.types.insert v ξ }
      let ⟨P', .bool⟩ ← encodeTerm P E | throw s!"encodeTerm:collect: Expected a boolean, got {(← encodeTerm P E).2}"
      let xs ← freshVarList αs
      let ⟨Dxs, _⟩ ← castApp (D', α.fun β.option) (xs.map .var |>.toPairl, αs.toProdl)
      let P' := substList vs ((xs.map .var).concat Dxs) P'
      -- Erase bound vars from context (they were temporarily added for P encoding)
      for v in vs do SMT.eraseFromContext v
      return (.lambda xs αs (.ite P' (.some Dxs) (none$ β)), αs.toProdl.fun β.option)
    | .fun τ .bool => do
      -- `D` is a set
      let τs := τ.fromProdl <| vs.length - 1
      for ⟨v, ξ⟩ in vs.zip τs do addToContext v ξ
      let ⟨P', .bool⟩ ← encodeTerm P E | throw s!"encodeTerm:collect: Expected a boolean, got {(← encodeTerm P E).2}"
      let z ← freshVar τ
      let P' := substList vs (toDestPair vs (.var z)) P'
      -- Erase bound vars and lambda-bound var from context
      for v in vs do SMT.eraseFromContext v
      SMT.eraseFromContext z
      return (.lambda [z] [τ] (.ite (.app D' (.var z)) P' (.bool false)), .fun τ .bool)
    | _ => throw s!"encodeTerm:collect: Expected a set or a function, got {τD}"
  | .lambda vs D P, E => do
    /- Encode `λ vs ∈ D. P` (B type `(τ ×ᴮ β).set`) as the SMT relation
       `{xy : τ × β | xy.π₁ ∈ D ∧ xy.π₂ = P[xy.π₁/vs]}`, i.e. the graph of the
       partial function. The resulting SMT type is `.fun (.pair τ β) .bool`,
       matching `(τ ×ᴮ β).set.toSMTType`.

       `D` must have SMT type `.fun τ .bool` (a set / characteristic function),
       guaranteed by `B.Typing.lambda`'s requirement that `D : .set τ`. -/
    let ⟨D', τD⟩ ← encodeTerm D E
    match τD with
    | .fun τ .bool => do
      -- `D` is a set of tuples with arity `vs.length`
      let τs := τ.fromProdl <| vs.length - 1
      for ⟨v, ξ⟩ in vs.zip τs do addToContext v ξ
      let ⟨P', γ⟩ ← encodeTerm P E
      -- Single bound variable `xy : τ × γ` representing the input-output pair
      let xy ← freshVar (.pair τ γ)
      -- Destructure `xy.fst` (type `τ`) into the individual vs components
      let Px := substList vs (toDestPair vs (.fst (.var xy))) P'
      let x_mem_D' := .app D' (.fst (.var xy))
      for v in vs do SMT.eraseFromContext v
      SMT.eraseFromContext xy
      return (.lambda [xy] [.pair τ γ]
        (.and x_mem_D' (.eq (.snd (.var xy)) Px)),
        .fun (.pair τ γ) .bool)
    | _ => throw s!"encodeTerm:lambda: Expected a set (.fun τ .bool), got {τD}"
  | .pfun A B, E => do
    /-
    A ⇸ B = { R ∈ 𝒫(A × B) | R is a partial function }
    Encoded as: λ R : (α × β) → bool.
      (∀ x : α, y : β. R(⟨x,y⟩) ⇒ A(x) ∧ B(y)) ∧
      (∀ x : α, y : β, y' : β. R(⟨x,y⟩) ∧ R(⟨x,y'⟩) ⇒ y = y')
    -/
    let ⟨A', .fun α .bool⟩ ← encodeTerm A E | throw "encodeTerm:pfun: Expected a set for domain"
    let ⟨B', .fun β .bool⟩ ← encodeTerm B E | throw "encodeTerm:pfun: Expected a set for codomain"
    let R ← freshVar (.fun (.pair α β) .bool)
    let x ← freshVar α
    let y ← freshVar β
    let y' ← freshVar β
    return (.lambda [R] [.fun (.pair α β) .bool] (.and
      -- (1) R ⊆ A × B: ∀ x y. R(⟨x,y⟩) ⇒ A(x) ∧ B(y)
      (.forall [x, y] [α, β] (.imp (.app (.var R) (.pair (.var x) (.var y)))
        (.and (.app A' (.var x)) (.app B' (.var y)))))
      -- (2) R is functional: ∀ x y y'. R(⟨x,y⟩) ∧ R(⟨x,y'⟩) ⇒ y = y'
      (.forall [x, y, y'] [α, β, β] (.imp
        (.and (.app (.var R) (.pair (.var x) (.var y)))
              (.app (.var R) (.pair (.var x) (.var y'))))
        (.eq (.var y) (.var y'))))
    ), .fun (.fun (.pair α β) .bool) .bool)
  -- | .min S, E => _
  -- | .max S, E => _
  | .all vs D P, E => do
    let ⟨D', τD⟩ ← encodeTerm D E
    match τD with
    | .fun τ .bool =>
      let tmp_τs := τ.fromProdl <| vs.length - 1

      if hlen : vs.length = tmp_τs.length then
        let τs : List SMTType ← tmp_τs.mapFinIdxM fun i τ hi ↦
          if vs[i] ∈ E.flags then
            match τ with
            | .fun (.pair α β) .bool => return .fun α (.option β)
            | .fun α (.option β) => return .fun α (.option β)
            | ξ => throw s!"encodeTerm:all: Unsupported flag type {vs[i]} : {ξ}"
          else return τ

        for ⟨v, τ⟩ in vs.zip τs do addToContext v τ

        let ⟨P', .bool⟩ ← encodeTerm P E | throw s!"encodeTerm:all: Expected a boolean, got {← encodeTerm P E}"
        let zs ← freshVarList τs
        let P' := substList vs (zs.map .var) P'
        let τ' := τs.toProdl
        let (z_mem_D', .bool) ← castMembership (zs.map .var |>.toPairl, τ') (D', .fun τ .bool) | throw s!"encodeTerm:all: Failed to cast {zs} ∈ {D'}"

        -- Erase bound vars and forall-bound vars from context
        for v in vs do SMT.eraseFromContext v
        for v in zs do SMT.eraseFromContext v
        return (.forall zs τs (.imp z_mem_D' P'), .bool)
      else throw s!"encodeTerm:all: number of variables {vs.length} does not match number of gathered types {tmp_τs.length}"
    | .fun α (.option β) =>
      let τs := (α.pair β).fromProdl <| vs.length - 1
      unless τs.length == vs.length do
        throw s!"encodeTerm:all: Expected {vs.length - 1} types, got {τs.length}"

      for ⟨v, ξ⟩ in vs.zip τs do addToContext v ξ

      let xs ← freshVarList τs

      let ⟨P', .bool⟩ ← encodeTerm P E | throw s!"encodeTerm:all: Expected a boolean, got {← encodeTerm P E}"
      let P' := substList vs (xs.map .var) P'

      let ⟨xsy_mem_D, _⟩ ← castMembership (xs.map .var |>.toPairl, τs.toProdl) (D', .fun α (.option β))

      -- Erase bound vars and forall-bound vars from context
      for v in vs do SMT.eraseFromContext v
      for v in xs do SMT.eraseFromContext v

      return (.forall xs τs (xsy_mem_D ⇒ˢ P'), .bool)
    | _ => throw s!"encodeTerm:all: Expected a set or a function, got {← encodeTerm D E}"
  | t, _ => throw s!"Unsupported term {t}"

def encodeTypeContext (e : B.Env) : Encoder Unit := do
  for ⟨v, τ⟩ in e.context.entries do
    if v ∈ e.flags then
      match τ with
      | .set (.prod α β) => modify λ e =>
        { e with types := e.types.insert v <| .fun (α.toSMTType) (.option β.toSMTType) }
      | ξ => throw s!"Unsupported flag type {v} : {ξ}"
    else
      modify λ e => { e with types := e.types.insert v τ.toSMTType }

def encodeDefs (E : B.Env) : Encoder Unit := do
  let rec aux : List ((_ : B.𝒱) × B.Term) → List SMT.𝒱 → Encoder (List SMT.𝒱)
    | .nil, vs => return vs
    | .cons ⟨v, dv⟩ defs, vs => do
      let .some τ := (←get).types.lookup v | throw s!"encodeDefs: missing type for {v}"
      let ⟨t, _⟩ ← encodeTerm dv E
      /-
        NOTE: Using define_fun instead of define_const because cvc5 doesn't
        support define_const for function types.
      -/
      modify (λ e => { e with env := { e.env with declarations := e.env.declarations.concat <| Instr.define_fun v .unit τ t } })
      aux defs (v :: vs)
  let declared ← aux E.defs.entries []
  let e ← get
  let Γ : TypeContext := e.types.filter (λ k _ => k ∉ declared)
  -- for ⟨v, τ⟩ in e.types do if v ∉ declared then Γ := Γ.cons v τ
  let decl := Γ.entries.map (λ ⟨v, τ⟩ => Instr.declare_const v τ)
  let mut ass := []
  for ⟨_, d⟩ in E.hypotheses do
    ass := ass ++ (← d.mapM (encodeTerm · E))
  modify λ e => { e with env := { e.env with
    asserts := match e.env.asserts with
    | .asserts as => .asserts <| as.concat <| Stages.instr <| ass.map (Instr.assert ∘ Prod.fst)
    | _ => panic! "encodeDefs: malformed assert in environment"
    declarations := decl.reverse ++ e.env.declarations }}

def encodeDistinctFinite (E : B.Env) : Encoder Unit := do
  let ds ← E.distinct.mapM λ ds => Term.distinct <$> ds.mapM (λ t => Prod.fst <$> (encodeTerm t E))
  let fs ← E.finite.mapM λ fin => (Prod.fst <$> encodeTerm fin E)
  modify λ e => { e with env := { e.env with
    asserts := match e.env.asserts with
    | .asserts as => .asserts <| as.concat (Stages.instr <| (ds ++ fs).map Instr.assert)
    | _ => panic! "encodeDefs: malformed assert in environment" }}

def encodeSimpleGoal (g : B.SimpleGoal) (E : B.Env) : Encoder <| Stages := do
  let lh ← g.hyps.mapM (encodeTerm · E)
  let g ← encodeTerm g.goal E
  return .instr <| (lh.map Prod.fst).concat g.1 |>.map Instr.assert |>.concat .check_sat

def B.SimpleGoal.negate (sg : SimpleGoal) : SimpleGoal :=
  { sg with goal := .not sg.goal }

def B.ProofObligation.negateGoals (po : ProofObligation) : ProofObligation :=
  { po with goals := po.goals.map (·.negate)}

def encodeProofObligation (φ : B.ProofObligation) (E : B.Env) : Encoder Stages := do
  let defs ← (φ.defs.mapM ((Instr.assert ∘ Prod.fst) <$> encodeTerm · E))
  let globalHyps : Chunk ← (φ.hyps.mapM ((Instr.assert ∘ Prod.fst) <$> encodeTerm · E))
  let goals : List Stages ← φ.negateGoals.goals.mapM (encodeSimpleGoal · E)
  -- let goals : List Stages ← φ.goals.mapM (encodeSimpleGoal · E)
  return Stages.asserts <| (.instr <| defs ++ globalHyps) :: goals.map (fun s => Stages.asserts [s])

def encodeProofObligations (E : B.Env) : Encoder Unit := do
  let rec aux : List B.ProofObligation → Encoder Unit
    | [] => pure ()
    | φ::φs => do
      let po ← encodeProofObligation φ E
      modify (λ e =>
        match e.env.asserts with
        | .asserts as => { e with env := { e.env with asserts := .asserts <| as.concat po }}
        | _ => panic! "Malformed environment"
        )
      aux φs
  aux E.po
def encode (e : B.Env) : Encoder Unit := do
  modify λ st => { st with env := { st.env with
    freshvarsc := e.freshvarsc
    usedVars := e.initialUsedVars } }
  encodeTypeContext e *> encodeDefs e *> encodeDistinctFinite e *> encodeProofObligations e

def EncoderState.toSMTFile : Encoder String := do
  let env := (← get).env.simplify
  return toString <| Stages.asserts [.instr env.declarations, env.asserts]

def encodePOG (pogpath : System.FilePath) (show_encoding := false): IO String := do
  let pog ← readPOG pogpath |>.propagateError
  let ⟨(), st⟩ ← POGtoB pog |>.run ∅ |>.run |>.propagateError
  -- dbg_trace st.env
  let st' ← match encode st.env |>.run ∅ with
    | .ok ⟨(), st'⟩ => pure st'
    | .error e => throw <| IO.userError e
  -- dbg_trace st'.types.entries
  let r ← match EncoderState.toSMTFile |>.run st' with
    | .ok ⟨r, _⟩ => pure r
    | .error e => throw <| IO.userError e
  if show_encoding then
    IO.println r
  return r

-- #eval encodePOG (".."/".."/"benchmark"/"dataset-pog"/"0002"/"00028.pog") >>= cvc5 (timeout := 1000) >>= IO.println
-- #eval MCH2POG "Test/Test.mch" >>= encodePOG (show_encoding := true) >>= cvc5 >>= IO.println
-- #eval encodePOG ("Test"/"Eval.pog") (show_encoding := true) >>= cvc5 >>= IO.println

-- 0010_00006
-- 0015/00132: malformed pog (s89 = s89_1)

-- (Pair (Pair _ (-> Int (Option Int))) _)
-- (Pair (Pair _ (-> (Pair Int Int) Bool)) _)
