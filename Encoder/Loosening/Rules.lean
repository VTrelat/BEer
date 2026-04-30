import Encoder.Basic
import Encoder.Loosening.Castable

open SMT

/- TODO: Define `loosenAux_proofs` and `loosenAux_impl` where:
- `loosenAux_impl`: contains the optimized `refl`-cases optimizations
- `loosenAux_prf `: does not contain the optimized `refl`-cases optimizations to simplify proofs and reduce the number of cases
-/

def defaultSpecM (name : String) : SMTType → Term → Encoder Term
  | .int, t => pure (t =ˢ .int 0)
  | .bool, t => pure (t =ˢ .bool false)
  | .unit, _ => pure (.bool true)
  | .option α, t => pure (t =ˢ none$α)
  | .pair α β, t => do
      let hfst ← defaultSpecM s!"{name}_fst" α (.fst t)
      let hsnd ← defaultSpecM s!"{name}_snd" β (.snd t)
      pure (hfst ∧ˢ hsnd)
  | .fun α β, t => do
      let x ← SMT.freshVar α s!"{name}_arg"
      let body ← defaultSpecM s!"{name}_body" β (.app t (.var x))
      pure (.forall [x] [α] body)

def loosenAux_prf (name : String) {α β : SMTType} (c : α ~> β) (x : Term) : Encoder (𝒱 × Term) := do
  let x! ← SMT.freshVar β name
  match c with
  | @castPath.graph α β α' β' c_α c_β =>
    let z ← SMT.freshVar (.pair α β) s!"{x!}_funGraph"
    let ⟨z!, z!_spec⟩ ← loosenAux_prf s!"{name}_funGraph_pair" (c_α.pair c_β) (.var z)
    return ⟨x!,
      .var x! =ˢ
        (.lambda [z!] [α'.pair β']
          (.exists [z] [.pair α β]
            (((.app x (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)))
    ⟩
  | @castPath.chpred α α' c_α =>
    let z ← SMT.freshVar α s!"{x!}_charPred"
    let ⟨z!, z!_spec⟩ ← loosenAux_prf s!"{name}_char_pred" c_α (.var z)
    return ⟨x!, .var x! =ˢ (.lambda [z!] [α'] (.exists [z] [α] ((.app x (.var z)) ∧ˢ z!_spec)))⟩
  | @castPath.opt α α' c_α =>
    match _hx : x with
    | .none   => return ⟨x!, .var x! =ˢ none$α'⟩
    | .some x =>
      let ⟨the_x!, the_x!_spec⟩ ← loosenAux_prf s!"{name}_opt_opt" c_α x
      return ⟨x!,
        .exists [the_x!] [α'] ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec)
      ⟩
    | x       =>
      let ⟨the_x!, the_x!_spec⟩ ← loosenAux_prf s!"{name}_opt_opt" c_α (.the x)
      return ⟨x!,
        .ite (x =ˢ none$α) (.var x! =ˢ none$α')
          (.exists [the_x!] [α'] ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec))
      ⟩
  | @castPath.pair α β α' β' c_α c_β =>
    let ⟨fst!, fst!_spec⟩ ← loosenAux_prf s!"{name}_pair_fst" c_α (.fst x)
    let ⟨snd!, snd!_spec⟩ ← loosenAux_prf s!"{name}_pair_snd" c_β (.snd x)
    return ⟨x!,
      .exists [fst!, snd!] [α', β'] ((.var x! =ˢ .pair (.var fst!) (.var snd!)) ∧ˢ (fst!_spec ∧ˢ snd!_spec))
    ⟩
  | .refl _ => return ⟨x!, .var x! =ˢ x⟩
  | @castPath.fun α β α' β' _ c_α c_β =>
    let a ← SMT.freshVar α s!"{x!}_funFun_src_arg"
    let ⟨a!, a!_spec⟩ ← loosenAux_prf s!"{name}_funFun_arg" c_α (.var a)
    let b ← SMT.freshVar β s!"{x!}_funFun_src_ret"
    let ⟨b!, b!_spec⟩ ← loosenAux_prf s!"{name}_funFun_ret" c_β (.var b)
    let hdefault ← defaultSpecM s!"{name}_funFun_default" β' (.app (.var x!) (.var a!))
    return ⟨x!,
      .forall [a!] [α'] (
        .ite (.exists [a] [α] a!_spec)
          (.forall [b!] [β']
            (((.app (.var x!) (.var a!)) =ˢ (.var b!)) =ˢ
              (.exists [a, b] [α, β]
                (((.app x (.var a)) =ˢ (.var b)) ∧ˢ (a!_spec ∧ˢ b!_spec)))))
          hdefault)
    ⟩

def loosenAux_impl (name : String) {α β : SMTType} (c : α ~> β) (x : Term) : Encoder (𝒱 × Term) := do
  let x! ← SMT.freshVar β name
  match c with
  | @castPath.graph α β α' β' c_α c_β =>
    let z ← SMT.freshVar (.pair α β) s!"{x!}_funGraph"
    let ⟨z!, z!_spec⟩ ← loosenAux_impl s!"{name}_funGraph_pair" (c_α.pair c_β) (.var z)
    return ⟨x!,
      .var x! =ˢ
        (.lambda [z!] [α'.pair β']
          (.exists [z] [.pair α β]
            (((.app x (.fst (.var z))) =ˢ .some (.snd (.var z))) ∧ˢ z!_spec)))
    ⟩
  | @castPath.chpred α α' c_α =>
    match c_α with
    | .refl _ => return ⟨x!, .var x! =ˢ x⟩
    | c_α =>
      let z ← SMT.freshVar α s!"{x!}_charPred"
      let ⟨z!, z!_spec⟩ ← loosenAux_impl s!"{name}_char_pred" c_α (.var z)
      return ⟨x!, .var x! =ˢ (.lambda [z!] [α'] (.exists [z] [α] ((.app x (.var z)) ∧ˢ z!_spec)))⟩
  | @castPath.opt α α' c_α =>
    match c_α with
    | .refl _ => return ⟨x!, .var x! =ˢ x⟩
    | c_α =>
      match _hx : x with
      | .none   => return ⟨x!, .var x! =ˢ none$α'⟩
      | .some x =>
        let ⟨the_x!, the_x!_spec⟩ ← loosenAux_impl s!"{name}_opt_opt" c_α x
        return ⟨x!, (.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec⟩
      | x       =>
        let ⟨the_x!, the_x!_spec⟩ ← loosenAux_impl s!"{name}_opt_opt" c_α (.the x)
        return ⟨x!, .ite (x =ˢ none$α) (.var x! =ˢ none$α') ((.var x! =ˢ .some (.var the_x!)) ∧ˢ the_x!_spec)⟩
  | @castPath.pair α β α' β' c_α c_β =>
    match c_α, c_β with
    | .refl _, .refl _ => return ⟨x!, .var x! =ˢ x⟩
    | .refl _, c_β =>
      let ⟨snd!, snd!_spec⟩ ← loosenAux_impl s!"{name}_pair_refl_snd" c_β (.snd x)
      return ⟨x!, .exists [snd!] [β'] ((.var x! =ˢ .pair (.fst x) (.var snd!)) ∧ˢ snd!_spec)⟩
    | c_α, .refl _ =>
      let ⟨fst!, fst!_spec⟩ ← loosenAux_impl s!"{name}_pair_fst_refl" c_α (.fst x)
      return ⟨x!, .exists [fst!] [α'] ((.var x! =ˢ .pair (.var fst!) (.snd x)) ∧ˢ fst!_spec)⟩
    | c_α, c_β =>
      let ⟨fst!, fst!_spec⟩ ← loosenAux_impl s!"{name}_pair_fst" c_α (.fst x)
      let ⟨snd!, snd!_spec⟩ ← loosenAux_impl s!"{name}_pair_snd" c_β (.snd x)
      return ⟨x!,
        .exists [fst!, snd!] [α', β'] ((.var x! =ˢ .pair (.var fst!) (.var snd!)) ∧ˢ (fst!_spec ∧ˢ snd!_spec))
      ⟩
  | .refl _ => return ⟨x!, .var x! =ˢ x⟩
  | @castPath.fun α β α' β' _ c_α c_β =>
    let a ← SMT.freshVar α s!"{x!}_funFun_src_arg"
    let ⟨a!, a!_spec⟩ ← loosenAux_impl s!"{name}_funFun_arg" c_α (.var a)
    let b ← SMT.freshVar β s!"{x!}_funFun_src_ret"
    let ⟨b!, b!_spec⟩ ← loosenAux_impl s!"{name}_funFun_ret" c_β (.var b)
    let hdefault ← defaultSpecM s!"{name}_funFun_default" β' (.app (.var x!) (.var a!))
    return ⟨x!,
      .forall [a!] [α'] (
        .ite (.exists [a] [α] a!_spec)
          (.forall [b!] [β']
            (((.app (.var x!) (.var a!)) =ˢ (.var b!)) =ˢ
              (.exists [a, b] [α, β]
                (((.app x (.var a)) =ˢ (.var b)) ∧ˢ (a!_spec ∧ˢ b!_spec)))))
          hdefault)
    ⟩

/--
If `Γ ⊢ˢ x : α` for some `Γ` (often the local context) and if `α ⊑ β`,
`loosen name x α β` returns `(x!, x!_spec)` where `Γ ⊢ˢ x! : β` and
`⟦x!_spec⟧ˢ = ⊤ᶻ ↔ ⟦x⟧ˢ = ⟦var x!⟧ˢ`

**Note**: This version uses the proof-oriented version of the loosening rules.
For an optimized version, change for `loosenAux_impl`.
-/
def loosen (name : String) (x : Term) (α β : SMTType) : Encoder (𝒱 × Term) := do
  if h : α ⊑ β then loosenAux_prf name (castable?.toCastPath h) x
  else throw s!"loosen: Cannot loosen {α} to {β}"
