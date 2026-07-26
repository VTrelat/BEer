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

/-- Best-effort type of an emitted term.  `none` means "cannot tell". -/
partial def infer (Γ : TypeContext) : Term → Option SMTType
  | .var v => Γ[v]?
  | .int _ | .add .. | .sub .. | .mul .. => some .int
  | .bool _ | .forall .. | .exists .. | .eq .. | .and .. | .or .. | .not _
  | .imp .. | .le .. | .distinct _ => some .bool
  | .as _ τ => some τ
  | .builtin _ τ _ => some τ
  | .none => none
  | .some t => (infer Γ t).map .option
  | .the t => match infer Γ t with
    | some (.option τ) => some τ
    | _ => none
  | .pair a b => match infer Γ a, infer Γ b with
    | some α, some β => some (.pair α β)
    | _, _ => none
  | .fst t => match infer Γ t with
    | some (.pair α _) => some α
    | _ => none
  | .snd t => match infer Γ t with
    | some (.pair _ β) => some β
    | _ => none
  | .ite _ t e => (infer Γ t).orElse fun _ => infer Γ e
  | .app f _ => match infer Γ f with
    | some (.fun _ τ) => some τ
    | _ => none
  -- Only the single-binder form is inferred.  A multi-binder λ is curried by
  -- the solver but the encoder treats its domain as a tuple in places, and
  -- guessing wrong here would manufacture false alarms.
  | .lambda [v] [τ] t => (infer (Γ.insert v τ) t).map (SMTType.fun τ)
  | .lambda .. => none

/-- Extend `Γ` with a binder list, ignoring a malformed one. -/
private def bind (Γ : TypeContext) (vs : List 𝒱) (τs : List SMTType) : TypeContext :=
  (vs.zip τs).foldl (fun Δ (v, τ) => Δ.insert v τ) Γ

/-- Applications in `t` whose argument type contradicts the function's domain. -/
partial def mismatches (Γ : TypeContext) (t : Term) : List String :=
  match t with
  | .app f x =>
    let here := match infer Γ f, infer Γ x with
      | some (.fun σ _), some ξ =>
        if σ == ξ then []
        else [s!"applied a function of domain {σ} to an argument of type {ξ}: " ++
              (Term.toString f).take 70 ++ " @ " ++ (Term.toString x).take 60]
      | _, _ => []
    here ++ mismatches Γ f ++ mismatches Γ x
  | .lambda vs τs b | .forall vs τs b | .exists vs τs b => mismatches (bind Γ vs τs) b
  | .eq a b | .and a b | .or a b | .imp a b | .le a b | .pair a b
  | .add a b | .sub a b | .mul a b => mismatches Γ a ++ mismatches Γ b
  | .not a | .some a | .the a | .fst a | .snd a | .as a _ => mismatches Γ a
  | .ite c a b => mismatches Γ c ++ mismatches Γ a ++ mismatches Γ b
  | .distinct ts | .builtin _ _ ts => ts.attach.flatMap (fun ⟨u, _⟩ => mismatches Γ u)
  | .var _ | .int _ | .bool _ | .none => []

/-- Record what an instruction declares, and report what it asserts. -/
private def step (Γ : TypeContext) : Instr → TypeContext × List String
  | .declare_const v τ => (Γ.insert v τ, [])
  | .define_fun v _ τ t => (Γ.insert v τ, mismatches Γ t)
  | .define_const v τ t => (Γ.insert v τ, mismatches Γ t)
  | .assert t => (Γ, mismatches Γ t)
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
