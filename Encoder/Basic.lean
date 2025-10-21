import POGReader
import SMT.Extra
import Extra.Utils

open Batteries SMT

def B.BType.toSMTType : B.BType → SMTType
  | .int => .int
  | .bool => .bool
  | .set α => .fun (α.toSMTType) .bool
  | .prod α β => .pair (α.toSMTType) (β.toSMTType)

structure EncoderState where
  env : SMT.Env
  types : SMT.TypeContext
  deriving Inhabited

instance : EmptyCollection EncoderState where
  emptyCollection := { env := {}, types := ∅ }

instance : ToString EncoderState where
  toString st := s!"⟪env:\n{st.env}"
    --++"\ncontext:\n{st.types}"
    ++"⟫"

abbrev Encoder := StateT EncoderState (Except String)

def SMT.incrementFreshVarC : Encoder Nat :=
  modifyGet λ st => (st.env.freshvarsc, { st with env.freshvarsc := st.env.freshvarsc + 1 } )

def SMT.freshVar (τ : SMTType) (name := "x") : Encoder SMT.𝒱 := do
  let v : SMT.𝒱 := s!"{name}{←incrementFreshVarC}"
  if v ∈ (←get).types.keys then
    throw s!"SMT.freshVar: variable {v} already in context"
  else
    modifyGet λ st => (v, { st with types := st.types.insert v τ })

def SMT.freshVarList : List SMTType → Encoder (List 𝒱)
  | [] => return []
  | τ::τs => .cons <$> freshVar τ <*> freshVarList τs

def SMT.defineFun (v : 𝒱) (τ σ : SMTType) (d : Term) : Encoder Unit :=
  modify λ e => { e with env := { e.env with declarations := e.env.declarations.concat <| .define_fun v τ σ d }}

def SMT.declareConst (v : 𝒱) (τ : SMTType) : Encoder Unit :=
  modify λ e => { e with env := { e.env with declarations := e.env.declarations.concat <| .declare_const v τ }}

def SMT.addToContext (v : 𝒱) (τ : SMTType) : Encoder Unit :=
  modify λ e => { e with types := e.types.insert v τ }

partial def addInstr : Stages → Chunk → Stages
  | .instr is, as => .instr <| as ++ is --NOTE: is the order correct?
  | .asserts as, as' =>
    if h : as.attach.isEmpty then .asserts [.instr as']
    else
      let as_ := as.dropLast
      let a := as.getLast (Ne.symm (ne_of_apply_ne (·.attach.isEmpty) (h <| id <| Eq.symm ·)))
      .asserts <| as_ ++ [addInstr a as'] --NOTE: is the order correct?

def SMT.addAssertAux : Stages → Chunk → Stages
  | .instr is, ck => .instr <| is ++ ck
  | .asserts [], ck => .asserts [.instr ck]
  | .asserts (as::ass), ck => .asserts <| (addAssertAux as ck) :: ass

def SMT.addAssert (t : Term) : Encoder Unit := do
  match (←get).env.asserts with
  | .instr _ => throw "SMT.addAssert: malformed asserts, cannot add assert here"
  | .asserts ass => modify λ e => { e with env := { e.env with asserts := addAssertAux (.asserts ass) [.assert t] }}

def SMT.addSpec (x! : 𝒱) (x!_spec : Term) : Encoder Unit := do
  defineFun s!"{x!}_spec" .unit .bool x!_spec
  addAssert <| .var s!"{x!}_spec"

def SMT.addAssert' (t : Term) : Encoder Unit := do
  let ass := (←get).env.asserts
  modify λ e => { e with env := { e.env with asserts := go t ass}}
  where go (t : Term) : Stages → Stages
    | .instr is => .instr <| is.concat <| .assert t
    | .asserts [] => .asserts [.instr [.assert t]]
    | .asserts [x] => .asserts [go t x]
    | .asserts (as :: ass) =>
      letI butLast := List.dropLast (as::ass)
      letI last := (as::ass).getLast (List.cons_ne_nil as ass)
      .asserts (butLast.concat (go t last))
  termination_by s => s
    decreasing_by (
      · decreasing_trivial
      · simp only [Stages.asserts.sizeOf_spec, List.cons.sizeOf_spec, gt_iff_lt]
        induction ass with
        | nil => simp +arith
        | cons a ass ih =>
          dsimp
          cases ass with
          | nil => simp +arith
          | cons as' ass =>
            simp +arith at ih
            simp +arith
            trans
            · exact ih
            · simp+arith
    )

def SMT.Term.getType : Term → Encoder SMTType
  | .var v => return (←get).types.lookup v |>.get!
  | .int _ => return .int
  | .bool _
  | .forall _ _ _| .exists _ _ _ | .eq _ _ | .and _ _ | .or _ _| .not _ | .imp _ _ | .le _ _ | .distinct _ => return .bool
  | .app f x => do
    match (← f.getType), (← x.getType) with
    | .fun σ τ, ξ => if σ == ξ then return τ else throw s!"Expected {σ}, got {ξ}"
    | α, β => throw s!"Cannot apply {α} to {β}"
  | .lambda vs τs t => do
    if h_len : vs.length = τs.length then
      let st ← get
      modify fun σ ↦ {σ with types := σ.types.update vs τs h_len}
      match τs, (← t.getType) with
      | [], _ => throw "SMT.Term.getType:lambda: Empty type list"
      | [τ], σ =>
        modify fun _ ↦ st
        return .fun τ σ
      | τ₁::τ₂::τs, σ =>
        let τ := (τ₁::τ₂::τs).dropLast.foldr (init := (τ₁::τ₂::τs).getLast (List.cons_ne_nil _ _)) (.pair · ·)
        modify fun _ ↦ st
        return .fun τ σ
    else throw "SMT.Term.getType:lambda: Type list length mismatch"
  | .as _ τ => return τ
  | .some t => return (← t.getType).option
  | .the t => do
    let .option τ ← t.getType | throw s!"SMT.Term.getType: Expected option type, got {(← t.getType)}"
    return τ
  | .none => return .option .unit -- TODO: this is a hack
  | .pair t₁ t₂ => do
    return (← t₁.getType).pair (← t₂.getType)
  | .fst t => do
    match (← t.getType) with
    | .pair α _ => return α
    | τ => throw s!"SMT.Term.getType: Expected pair, got {τ}"
  | .snd t => do
    match (← t.getType) with
    | .pair _ β => return β
    | τ => throw s!"SMT.Term.getType: Expected pair, got {τ}"
  | .add _ _ | .sub _ _ | .mul _ _ => return .int
  | .ite _ t _ => t.getType -- TODO: could check if both branches have the same types

def SMT.SMTType.fromProdl : SMTType → Nat → List SMTType
  | .pair α β, n+1 => α.fromProdl n |>.concat β
  | .pair α β, 0 => [.pair α β]
  | τ, _ => [τ]

theorem SMT.SMTType.fromProdl_length (τ : SMT.SMTType) (n : Nat) : (τ.fromProdl n).length <= n + 1 := by
  induction τ generalizing n with
  | pair α β αih =>
    cases n with
    | zero =>
      rw [SMT.SMTType.fromProdl]
      simp only [List.length_singleton, Nat.zero_add, Nat.le_refl]
    | succ n =>
      rw [SMT.SMTType.fromProdl]
      simp +arith [αih]
  | _ =>
    unfold SMT.SMTType.fromProdl
    simp only [List.length_singleton, Nat.le_add_left]

partial def List.toProdl (xs : List SMTType) : SMTType :=
  aux xs.reverse
where aux : List SMTType → SMTType
  | [x] => x
  | x::xs => .pair (aux xs) x
  | _ => panic! "SMT.Term.toProdl: Empty list"

partial def List.toProdr (xs : List SMTType) : SMTType :=
  match xs.reverse with
  | [x] => x
  | x::xs => .pair x xs.toProdr
  | _ => panic! "SMT.Term.toProdr: Empty list"

partial def List.currify (xs : List SMTType) : SMTType :=
  match xs with
  | [x] => x
  | x::xs => .fun x xs.currify
  | _ => panic! "SMT.Term.toProdl: Empty list"

def SMT.SMTType.fromCurry : SMTType → List SMTType
  | .fun α β => α::β.fromCurry
  | τ => [τ]

partial def List.toPairl (xs : List Term) : Term :=
  match xs with
  | [x] => x
  | x::xs =>
    let last := (x::xs).getLast (cons_ne_nil x xs)
    let xs' := (x::xs).dropLast
    .pair (toPairl xs') last
  | _ => panic! "SMT.Term.toPairl: Empty list"

def gatherPairsl : Term → List Term
  | .pair x y => gatherPairsl x |>.concat y
  | x => [x]

def toDestPair (vs : List 𝒱) (z : Term) (acc : List Term := []) (d : Term := z) : List Term :=
  match vs with
  | [] => acc
  | [_] => z :: acc
  | _ :: xs => toDestPair xs (.fst d) (.snd d :: acc) (.fst d)
