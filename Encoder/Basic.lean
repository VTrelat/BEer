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

def SMT.foldMaxLen (xs : List SMT.𝒱) : Nat :=
  xs.foldl (fun n s => max n s.length) 0

def SMT.superFresh (xs : List SMT.𝒱) : SMT.𝒱 :=
  String.mk (List.replicate (SMT.foldMaxLen xs + 1) 'x')

theorem SMT.le_foldMaxLen (acc : Nat) (xs : List SMT.𝒱) :
    acc ≤ xs.foldl (fun n t => max n t.length) acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons a as ih =>
    simp
    exact Nat.le_trans (Nat.le_max_left _ _) (ih (acc := max acc a.length))

theorem SMT.length_le_foldMaxLenAux (acc : Nat) (xs : List SMT.𝒱) (s : SMT.𝒱) (hs : s ∈ xs) :
    s.length ≤ xs.foldl (fun n t => max n t.length) acc := by
  induction xs generalizing acc with
  | nil => cases hs
  | cons a as ih =>
    simp at hs ⊢
    cases hs with
    | inl hsa =>
      subst hsa
      exact Nat.le_trans (Nat.le_max_right acc s.length) (SMT.le_foldMaxLen (acc := max acc s.length) as)
    | inr hmem =>
      exact ih (acc := max acc a.length) hmem

theorem SMT.length_le_foldMaxLen (xs : List SMT.𝒱) (s : SMT.𝒱) (hs : s ∈ xs) :
    s.length ≤ SMT.foldMaxLen xs := by
  simpa [SMT.foldMaxLen] using SMT.length_le_foldMaxLenAux 0 xs s hs

theorem SMT.superFresh_not_mem (xs : List SMT.𝒱) : SMT.superFresh xs ∉ xs := by
  intro hs
  have hle : (SMT.superFresh xs).length ≤ SMT.foldMaxLen xs :=
    SMT.length_le_foldMaxLen xs (SMT.superFresh xs) hs
  have hgt : SMT.foldMaxLen xs < (SMT.superFresh xs).length := by
    simp [SMT.superFresh, SMT.foldMaxLen]
  exact Nat.not_lt_of_ge hle hgt

def SMT.freshVar (τ : SMTType) (name := "x") : Encoder SMT.𝒱 := do
  let mut n ← incrementFreshVarC
  let mut v₀ : SMT.𝒱 := s!"{name}{n}"
  modifyGet λ st =>
    let used := st.env.usedVars ++ st.types.keys
    let v := if v₀ ∈ used then SMT.superFresh used else v₀
    (v, { st with
      env := { st.env with usedVars := v :: st.env.usedVars }
      types := st.types.insert v τ })

def SMT.freshVarList : List SMTType → Encoder (List 𝒱)
  | [] => return []
  | τ::τs => .cons <$> freshVar τ <*> freshVarList τs

def SMT.defineFun (v : 𝒱) (τ σ : SMTType) (d : Term) : Encoder Unit :=
  modify λ e => { e with env := { e.env with declarations := e.env.declarations.concat <| .define_fun v τ σ d }}

def SMT.declareConst (v : 𝒱) (τ : SMTType) : Encoder Unit :=
  modify λ e => { e with env := { e.env with declarations := e.env.declarations.concat <| .declare_const v τ }}

def SMT.addToContext (v : 𝒱) (τ : SMTType) : Encoder Unit :=
  modify λ e => { e with types := e.types.insert v τ, env.usedVars := v :: e.env.usedVars }

def SMT.eraseFromContext (v : 𝒱) : Encoder Unit :=
  modify λ e => { e with types := e.types.erase v }

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

/-- Build a left-associated product type from a list, reading the list in reverse.
Empty input returns a default `.unit`; this case is unreachable for all encoder
call sites (which pass non-empty lists via typing invariants), but making the
function total is necessary for the correctness proof. -/
def List.toProdl.aux : List SMTType → SMTType
  | [] => .unit
  | [x] => x
  | x::xs => .pair (List.toProdl.aux xs) x

def List.toProdl (xs : List SMTType) : SMTType := List.toProdl.aux xs.reverse

/-- Build a right-associated product type. -/
def List.toProdr.aux : List SMTType → SMTType
  | [] => .unit
  | [x] => x
  | x::xs => .pair x (List.toProdr.aux xs)

def List.toProdr (xs : List SMTType) : SMTType := List.toProdr.aux xs.reverse

/-- Curry a list of SMT types into a single function type. -/
def List.currify : List SMTType → SMTType
  | [] => .unit
  | [x] => x
  | x::xs => .fun x (List.currify xs)

def SMT.SMTType.fromCurry : SMTType → List SMTType
  | .fun α β => α::β.fromCurry
  | τ => [τ]

/-- Build a left-associated pair term from a list, reading the list in reverse.
Empty input returns a default boolean-false term; this case is unreachable for
all encoder call sites. -/
def List.toPairl.aux : List Term → Term
  | [] => .bool false
  | [x] => x
  | x::xs => .pair (List.toPairl.aux xs) x

def List.toPairl (xs : List Term) : Term := List.toPairl.aux xs.reverse

def gatherPairsl : Term → List Term
  | .pair x y => gatherPairsl x |>.concat y
  | x => [x]

def toDestPair (vs : List 𝒱) (z : Term) (acc : List Term := []) (d : Term := z) : List Term :=
  match vs with
  | [] => acc
  | [_] => z :: acc
  | _ :: xs => toDestPair xs (.fst d) (.snd d :: acc) (.fst d)
