import SMT.Environment

/-!
# Type checking the emitted SMT

The encoder keeps a B set in either of two representations — a characteristic
predicate `α → Bool` or a partial function `α → Option β` — and the loosening
layer is what converts between them.  When a conversion is missed the encoder
still produces a file; the mismatch only shows up as a solver type error, far
from the code responsible, and only if anyone runs a solver at all.

This pass closes that gap: it re-derives the type of every emitted term against
the declarations actually written out, and reports applications whose argument
does not match the function's domain.  It is deliberately *partial* — anything
it cannot infer is silently accepted — because a false alarm would reject a good
file, which is worse than the leak it is guarding against.
-/

namespace SMT

/-- Binders in scope, innermost first, layered over the declarations.

Extending the declaration map itself would copy it at every binder — it is still
referenced by the enclosing call, so the insert cannot happen in place — and that
made checking a large file cost more than encoding it.  Nesting depth is small,
so a scan of the layer is cheaper than any map. -/
abbrev Locals := List (𝒱 × SMTType)

private def lookup (Γ : TypeContext) (L : Locals) (v : 𝒱) : Option SMTType :=
  match L.find? (·.1 == v) with
  | some (_, τ) => some τ
  | none => Γ[v]?

/-- Best-effort type of an emitted term.  `none` means "cannot tell". -/
partial def infer (Γ : TypeContext) (L : Locals) : Term → Option SMTType
  | .var v => lookup Γ L v
  | .int _ | .add .. | .sub .. | .mul .. => some .int
  | .bool _ | .forall .. | .exists .. | .eq .. | .and .. | .or .. | .not _
  | .imp .. | .le .. | .distinct _ => some .bool
  | .as _ τ => some τ
  | .builtin _ τ _ => some τ
  | .none => none
  | .some t => (infer Γ L t).map .option
  | .the t => match infer Γ L t with
    | some (.option τ) => some τ
    | _ => none
  | .pair a b => match infer Γ L a, infer Γ L b with
    | some α, some β => some (.pair α β)
    | _, _ => none
  | .fst t => match infer Γ L t with
    | some (.pair α _) => some α
    | _ => none
  | .snd t => match infer Γ L t with
    | some (.pair _ β) => some β
    | _ => none
  | .ite _ t e => (infer Γ L t).orElse fun _ => infer Γ L e
  | .app f _ => match infer Γ L f with
    | some (.fun _ τ) => some τ
    | _ => none
  -- Only the single-binder form is inferred.  A multi-binder λ is curried by
  -- the solver but the encoder treats its domain as a tuple in places, and
  -- guessing wrong here would manufacture false alarms.
  | .lambda [v] [τ] t => (infer Γ ((v, τ) :: L) t).map (SMTType.fun τ)
  | .lambda .. => none

/-- Push a binder list onto the local layer, ignoring a malformed one.  Innermost
first, so `lookup`'s first hit is the one in scope. -/
private def bind (L : Locals) (vs : List 𝒱) (τs : List SMTType) : Locals :=
  (vs.zip τs).reverse ++ L

/-- Applications in `t` whose argument type contradicts the function's domain. -/
partial def mismatches (Γ : TypeContext) (L : Locals) (t : Term) : List String :=
  match t with
  | .app f x =>
    let here := match infer Γ L f, infer Γ L x with
      | some (.fun σ _), some ξ =>
        if σ == ξ then []
        else [s!"applied a function of domain {σ} to an argument of type {ξ}: " ++
              (Term.toString f).take 70 ++ " @ " ++ (Term.toString x).take 60]
      | _, _ => []
    here ++ mismatches Γ L f ++ mismatches Γ L x
  | .lambda vs τs b | .forall vs τs b | .exists vs τs b => mismatches Γ (bind L vs τs) b
  | .eq a b | .and a b | .or a b | .imp a b | .le a b | .pair a b
  | .add a b | .sub a b | .mul a b => mismatches Γ L a ++ mismatches Γ L b
  | .not a | .some a | .the a | .fst a | .snd a | .as a _ => mismatches Γ L a
  | .ite c a b => mismatches Γ L c ++ mismatches Γ L a ++ mismatches Γ L b
  | .distinct ts | .builtin _ _ ts => ts.attach.flatMap (fun ⟨u, _⟩ => mismatches Γ L u)
  | .var _ | .int _ | .bool _ | .none => []

/-- Record what an instruction declares, and report what it asserts. -/
private def step (Γ : TypeContext) : Instr → TypeContext × List String
  | .declare_const v τ => (Γ.insert v τ, [])
  | .define_fun v _ τ t => (Γ.insert v τ, mismatches Γ [] t)
  | .define_const v τ t => (Γ.insert v τ, mismatches Γ [] t)
  | .assert t => (Γ, mismatches Γ [] t)
  | _ => (Γ, [])

private def chunk (Γ : TypeContext) (is : Chunk) : TypeContext × List String :=
  is.foldl (fun (Δ, acc) i => let (Δ', p) := step Δ i; (Δ', acc ++ p)) (Γ, [])

/-- Walk the assert tree.  A nested stage sees the enclosing declarations but
does not export its own, matching `push`/`pop`. -/
private partial def stages (Γ : TypeContext) : Stages → TypeContext × List String
  | .instr is => chunk Γ is
  | .asserts ss =>
    ss.attach.foldl (fun (Δ, acc) ⟨s, _⟩ => let (Δ', p) := stages Δ s; (Δ', acc ++ p)) (Γ, [])

/-- Representation mismatches in an environment about to be written out. -/
def Env.mismatches (E : Env) : List String :=
  let (Γ, p) := chunk ∅ E.declarations.toList
  p ++ (stages Γ E.asserts).2

end SMT
