import POGReader
import SMT.Extra
import Extra.Utils

open Batteries SMT

def B.BType.toSMTType : B.BType → SMTType
  | .int => .int
  | .bool => .bool
  | .set α => .fun (α.toSMTType) .bool
  | .prod α β => .pair (α.toSMTType) (β.toSMTType)

/-- A constant standing for the value of an operator that SMT-LIB cannot
express directly — `card`, `min`, `max`, `finite`.  Rather than declaring a
higher-order symbol and quantifying over sets (which cvc5 cannot instantiate at
a λ-term), the encoder introduces one constant per *occurrence* and asserts the
defining properties for that occurrence only, keeping everything first order.

`set` is the encoded argument and `τ` its element type; sites are matched on
`set` so that two occurrences of the same B expression share one constant. -/
structure Site where
  op : String
  set : SMT.Term
  τ : SMT.SMTType
  name : SMT.𝒱
  deriving Inhabited

structure EncoderState where
  env : SMT.Env
  types : SMT.TypeContext
  /-- Sites introduced so far, most recent first.  Cleared between proof
  obligations, since their defining assertions live inside the PO's
  `(push 1) … (pop 1)`. -/
  sites : List Site := []
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

/-- A name not used anywhere yet.

`usedVars` holds the names the `.pog` brought in, and is never added to: the
monotone counter already keeps generated names apart from each other, since
`freshvarsc` is consumed once per call and no two calls can therefore produce the
same `name ++ n`.  What is left to avoid is a clash with a source name, which is
what the retry below does.

Inserting each generated name back into the set is what the encoder used to do,
and it dominated the runtime — the set is shared, so every insert copied the
whole thing.  Removing it took a 15 s file to 1.4 s. -/
partial def SMT.freshVar (τ : SMTType) (name := "x") : Encoder SMT.𝒱 := do
  let rec fresh : Encoder SMT.𝒱 := do
    let n ← incrementFreshVarC
    let v : SMT.𝒱 := s!"{name}{n}"
    if (← get).env.usedVars.contains v then fresh else return v
  let v ← fresh
  -- Destructured rather than updated with `{ st with … }`: keeping `st` alive
  -- across the update leaves the table shared, and the insert then clones it.
  modify fun ⟨env, types, sites⟩ => ⟨env, types.insert v τ, sites⟩
  return v

def SMT.freshVarList : List SMTType → Encoder (List 𝒱)
  | [] => return []
  | τ::τs => .cons <$> freshVar τ <*> freshVarList τs

def SMT.defineFun (v : 𝒱) (τ σ : SMTType) (d : Term) : Encoder Unit :=
  modify λ e => { e with env := { e.env with declarations := e.env.declarations.push <| .define_fun v τ σ d }}

def SMT.declareConst (v : 𝒱) (τ : SMTType) : Encoder Unit :=
  modify λ e => { e with env := { e.env with declarations := e.env.declarations.push <| .declare_const v τ }}

def SMT.addToContext (v : 𝒱) (τ : SMTType) : Encoder Unit :=
  modify fun ⟨env, types, sites⟩ => ⟨env, types.insert v τ, sites⟩

def SMT.eraseFromContext (v : 𝒱) : Encoder Unit :=
  modify fun ⟨env, types, sites⟩ => ⟨env, types.erase v, sites⟩

/-- Remember the types that `vs` shadow, so a binder can be undone.

Binder names come straight from the `.pog`, and Atelier B numbers fresh names
per scope, so a binder routinely collides with a global.  Leaving its type
behind meant every later use of the global was encoded at the binder's type
while its declaration kept the original — the two set representations then
disagreed and the emitted file was ill-typed. -/
def SMT.saveShadowed (vs : List 𝒱) : Encoder (List (𝒱 × Option SMTType)) := do
  let Γ := (← get).types
  return vs.map fun v => (v, Γ[v]?)

def SMT.restoreShadowed (saved : List (𝒱 × Option SMTType)) : Encoder Unit := do
  for (v, old) in saved do
    match old with
    | some τ => addToContext v τ
    | none => eraseFromContext v

/-- Hide the sites a binder would capture, returning them so the caller can put
them back.

A site memoises its constant on the *term* its argument encoded to, and terms
carry no scope.  Since a binder name routinely collides with a global (see
`saveShadowed`), an outer site recorded against a term mentioning that name stays
visible inside the body, where the name now denotes the binder — at the other set
representation, in general.  Linking a new site against it then puts both
readings of the name in one formula, and the substitution that closes the body
rewrites them to the same variable: the graph use and the partial-function use
end up on the same symbol, and the file no longer typechecks.

The sites hidden here are only a memo table, so dropping them costs sharing and
cross-site facts, never soundness. -/
def SMT.hideCapturedSites (vs : List 𝒱) : Encoder (List Site) := do
  let (captured, kept) := (← get).sites.partition fun s => (fv s.set).any (· ∈ vs)
  modify fun e => { e with sites := kept }
  return captured

/-- Undo `hideCapturedSites`.  The hidden sites are older than anything the body
recorded, so they go back at the end. -/
def SMT.restoreSites (hidden : List Site) : Encoder Unit :=
  modify fun e => { e with sites := e.sites ++ hidden }

/-- The constant already standing for `op` applied to `S`, if any. -/
def SMT.findSite (op : String) (S : Term) : Encoder (Option 𝒱) := do
  return (← get).sites.find? (fun s => s.op == op && s.set == S) |>.map (·.name)

/-- How many earlier sites a new one is related to.

Relating every pair is quadratic in the number of sites, and a machine with many
enumerated SETS clauses easily produces a few hundred `finite` sites — the
resulting specifications dwarf the proof obligation itself.  Only the most
recent sites are linked, which costs provable facts but never soundness: the
axioms left out are ones the solver simply never learns. -/
def SMT.maxSiteLinks : Nat := 8

/-- The sites recorded for `op` at element type `τ`, most recent first and
capped at `maxSiteLinks`; used to relate a new constant to the ones already
introduced (e.g. `S ⊆ T → |S| ≤ |T|`). -/
def SMT.sitesOf (op : String) (τ : SMTType) : Encoder (List Site) := do
  return (← get).sites.filter (fun s => s.op == op && s.τ == τ) |>.take maxSiteLinks

def SMT.recordSite (s : Site) : Encoder Unit :=
  modify λ e => { e with sites := s :: e.sites }

def SMT.clearSites : Encoder Unit :=
  modify λ e => { e with sites := [] }

partial def addInstr : Stages → Chunk → Stages
  | .instr is, as => .instr <| as ++ is --NOTE: is the order correct?
  | .asserts as, as' =>
    if h : as.attach.isEmpty then .asserts [.instr as']
    else
      let as_ := as.dropLast
      let a := as.getLast (Ne.symm (ne_of_apply_ne (·.attach.isEmpty) (h <| id <| Eq.symm ·)))
      .asserts <| as_ ++ [addInstr a as'] --NOTE: is the order correct?

/-- Define a helper's specification and assert it.

The assertion is emitted next to the definition rather than into the assert
tree, so that a helper's `declare-const`, `define-fun` and `assert` form one
contiguous run of instructions.  Callers that need to relocate a helper — the
quantifier cases, which re-scope it inside the binder, and
`encodeProofObligation`, which moves it inside the obligation's `push` — then
move or drop the three together.  Splitting them across the two lists used to
leave the assertion behind, referring to a definition that had been reverted or
rewritten. -/
def SMT.addSpec (x! : 𝒱) (x!_spec : Term) : Encoder Unit := do
  defineFun s!"{x!}_spec" .unit .bool x!_spec
  modify λ e => { e with env := { e.env with
    declarations := e.env.declarations.push <| .assert (.var s!"{x!}_spec") }}

/-- Declare a cast helper and assert its defining specification.  Keeping the
pair as one encoder operation lets quantifier encoding collect and re-scope
both declarations together. -/
def SMT.declareConstWithSpec (x! : 𝒱) (τ : SMTType)
    (x!_spec : Term) : Encoder Unit := do
  declareConst x! τ
  addSpec x! x!_spec

def SMT.Term.getType : Term → Encoder SMTType
  | .var v => return (←get).types.get? v |>.get!
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
  | .builtin _ τ _ => return τ
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
