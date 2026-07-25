import B.Simplifier
import POGReader.Builtins

open Lean

def String.toBinaryOp : String → B.BType → B.Term → B.Term → Decoder B.Term
  -- comparison operators
  | ":", _ => pure ∘₂ .mem
  | "/:", _ => pure ∘₂ (.not ∘₂ .mem)
  | "<:", .bool => fun S T ↦ .All S fun x ↦ return x ∈ᴮ T
  | "/<:", _ => pure ∘₂ (.not ∘₂ (.mem · ∘ .pow))
  | "<<:", _ => fun S T ↦ do
      let sub ← .All S fun x ↦ return x ∈ᴮ T
      return sub ∧ᴮ ¬ᴮ (S =ᴮ T)
  | "/<<:", _ => fun S T ↦ do
      let sub ← .All S fun x ↦ return x ∈ᴮ T
      return ¬ᴮ (sub ∧ᴮ ¬ᴮ (S =ᴮ T))
  | "=", _ => pure ∘₂ .eq
  | "/=", _ => pure ∘₂ (.not ∘₂ .eq)
  | ">=r", _ | ">=f", _ | ">=i", _ => pure ∘₂ (flip .le)
  | ">r", _ | ">f", _ | ">i", _ => pure ∘₂ (.not ∘₂ .le)
  | "<=r", _ | "<=f", _ | "<=i", _ => pure ∘₂ .le
  | "<r", _ | "<f", _ | "<i", _ => pure ∘₂ (.not ∘₂ flip .le)
  -- binary exp operators
  -- | "," => throw "Not implemented"
  | "*", _ | "*i", _ | "*r", _ | "*f", _ => pure ∘₂ .mul
  -- | "**" => throw "Not implemented"
  -- A literal exponent unfolds into repeated multiplication, which solvers
  -- handle much better than the axiomatised `bpow`; symbolic exponents fall
  -- back to the real exponentiation operator.
  | "**i", _ | "**r", _ => fun x y => do
      match y with
      | .int n => return x.expLit n
      | _ => return x ^ᴮ y
  | "*s", _ => pure ∘₂ .cprod
  -- | "**r" => throw "Not implemented"
  | "+", _ | "+i", _ | "+r", _ | "+f", _ => pure ∘₂ .add
  -- | "-" => throw "Not implemented"
  | "-i", _ => pure ∘₂ .sub
  | "-r", _ => pure ∘₂ .sub
  | "-f", _ => pure ∘₂ .sub
  | "-s", _ => λ A B => do
      let v := s!"x{← incrementFreshVarC}"
      return .collect [v] A (¬ᴮ ((.var v) ∈ᴮ B))
  -- | "->" => throw "Not implemented"
  | "..", .set .int => λ a b => do
      let v := s!"x{← incrementFreshVarC}"
      return .collect [v] .ℤ ((a ≤ᴮ (.var v)) ∧ᴮ ((.var v) ≤ᴮ b))
  | "/", _ | "/i", _ | "/r", _ | "/f", _ => pure ∘₂ .div
  | "mod", _ => pure ∘₂ .mod
  | "/\\", _ => pure ∘₂ .inter
  | "/|\\", _ => B.Term.seqTake
  | "\\|/", _ => B.Term.seqDrop
  | "^", _ => B.Term.seqConcat
  | "<-", _ => B.Term.seqAppend
  | "->", _ => B.Term.seqPrepend
  | ";", τ => fun R S ↦ do
      let .set (.prod α γ) := τ | throw s!"; operator expects a relation, got type {τ}"
      let .set (.prod _ β) ← R.getType
        | throw s!"; operator expects a relation on the left, got type {← R.getType}"
      B.Term.compose α β γ R S
  | "<+", τ => fun S T ↦ do
      let .set (.prod α β) := τ | throw s!"<+ operator should have type `set (α × β)`, got {τ}"
      B.Term.overload α β S T
  | "<->", ξ => fun S T ↦ do
      let .set (.set (.prod τ σ)) := ξ | throw s!"<-> operator expects a relation, got type {ξ}"
      return 𝒫ᴮ (S ⨯ᴮ T)
  -- | "<-" => throw "Not implemented"
  | "<<|", τ =>
      fun F R ↦ do
      let .set (.prod α β) := τ | throw s!"<<| operator expects a relation, got type {τ}"
      let x ← freshVar α
      let y ← freshVar β
      return .collect [x, y] (α.toTerm ⨯ᴮ β.toTerm) (.var x ↦ᴮ .var y ∈ᴮ R ∧ᴮ ¬ᴮ(.var x ∈ᴮ F))
  | "<|", τ => fun F R ↦ do
      let .set (.prod α β) := τ | throw s!"<| operator expects a relation, got type {τ}"
      let x ← freshVar α
      let y ← freshVar β
      return .collect [x, y] (α.toTerm ⨯ᴮ β.toTerm) (.var x ↦ᴮ .var y ∈ᴮ R ∧ᴮ .var x ∈ᴮ F)
  | "+->", ξ => fun S T ↦ do
    let ⟨τ, σ⟩ ← ξ.getFunctionType
    return S.pfun T
  | "+->>", ξ => fun S T ↦ do
      let ⟨τ, σ⟩ ← ξ.getFunctionType
      .Collect (S ⇸ᴮ T) (B.Term.surj τ σ ·)
  | "-->", ξ => fun S T ↦ do
      let ⟨τ, σ⟩ ← ξ.getFunctionType
      .Collect (S ⇸ᴮ T) (B.Term.tot_on S σ ·)
  | "-->>", ξ => fun S T ↦ do
      let ⟨τ, σ⟩ ← ξ.getFunctionType
      .Collect (S ⇸ᴮ T) (λ f => .and <$> (B.Term.tot τ σ f) <*> (B.Term.surj τ σ f))
  | ">+>", ξ => fun S T ↦ do
    let ⟨τ, _⟩ ← ξ.getFunctionType
    .Collect (S ⇸ᴮ T) (B.Term.inj τ ·)
  | ">->", ξ => fun S T ↦ do
    let ⟨τ, σ⟩ ← ξ.getFunctionType
    .Collect (S ⇸ᴮ T) (λ f => .and <$> (B.Term.tot τ σ f) <*> (B.Term.inj τ f))
  | ">+>>", ξ => fun S T ↦ do
    let ⟨τ, σ⟩ ← ξ.getFunctionType
    .Collect (S ⇸ᴮ T) (B.Term.bij τ σ ·)
  | ">->>", ξ => fun S T ↦ do
    let ⟨τ, σ⟩ ← ξ.getFunctionType
    .Collect (S ⇸ᴮ T) (λ f => .and <$> (.and <$>
      (B.Term.tot τ σ f) <*>
      (B.Term.inj_on S f)) <*>
      (B.Term.surj_on S σ f))
  | "><", τ => fun E F => do
    let .set (.prod α (.prod β γ)) := τ | throw s!">< operator should have type `set (α × (β × γ))`, got {τ}"
    let x := s!"x{← incrementFreshVarC}"
    let yz := s!"y{← incrementFreshVarC}"
    let y := s!"y{← incrementFreshVarC}"
    let z := s!"z{← incrementFreshVarC}"
    return .collect [x, yz] (α.toTerm ⨯ᴮ (β.toTerm ⨯ᴮ γ.toTerm)) (
      .exists [y, z] (β.toTerm ⨯ᴮ γ.toTerm) (
        (.var yz =ᴮ .var y ↦ᴮ .var z) ∧ᴮ
        (.var x ↦ᴮ .var y ∈ᴮ E) ∧ᴮ
        (.var x ↦ᴮ .var z ∈ᴮ F)))
  -- | "||" => throw "Not implemented"
  | "\\/", _ => pure ∘₂ .union
  | "|->", _ => pure ∘₂ .maplet
  | "|>", τ => fun S T ↦ do
      let .set (.prod _ _) := τ | throw s!"<| operator expects a relation, got type {τ}"
      S ▷ T
  | "|>>", τ => fun S T ↦ do
      let .set (.prod _ _) := τ | throw s!"<<| operator expects a relation, got type {τ}"
      S ⩥ T
  | "[", τ =>
    -- if R ⊆ A ⨯ B then R[E] = { y ∈ B | ∃ x ∈ E, (x, y) ∈ R }
    fun R E ↦ do
      let .set α := τ | throw s!"[ operator expects a set, got type {τ}"
      .Collect α.toTerm fun y ↦ .Exists E fun x ↦ return (x ↦ᴮ y ∈ᴮ R)
  | "(", _ => pure ∘₂ .app
  -- | "<'" => throw "Not implemented"
  | "prj1", τ => fun E F => do
    let .set (.prod (.prod α _) α') := τ | throw s!"prj1 operator should have type `set (α × β × α)`, got {τ}"
    unless α = α' do
      throw s!"prj1 operator should have type `set (α × β × α)`, got {τ}"
    let x := s!"x{← incrementFreshVarC}"
    let y := s!"y{← incrementFreshVarC}"
    let z := s!"z{← incrementFreshVarC}"
    return .collect [x, y, z] (E ⨯ᴮ F ⨯ᴮ E) (.var z =ᴮ .var x)
  | "prj2", τ => λ E F => do
      let .set (.prod (.prod α _) α') := τ | throw s!"prj2 operator should have type `set (α × β × α)`, got {τ}"
      unless α = α' do
        throw s!"prj2 operator should have type `set (α × β × α)`, got {τ}"
      let x := s!"x{← incrementFreshVarC}"
      let y := s!"y{← incrementFreshVarC}"
      let z := s!"z{← incrementFreshVarC}"
      return .collect [x, y, z] (E ⨯ᴮ F ⨯ᴮ E) (.var z =ᴮ .var y)
  -- `iterate(R, n)` is `R` composed with itself `n` times.  A literal count is
  -- unfolded into compositions, which solvers handle far better; a symbolic one
  -- falls back to the primitive, encoded as a relation indexed by an integer.
  | "iterate", τ => fun R n => do
    let .set (.prod α α') := τ
      | throw s!"iterate operator expects a homogeneous relation, got type {τ}"
    unless α = α' do
      throw s!"iterate operator expects a homogeneous relation, got type {τ}"
    let .int k := n | return .iterate R n
    if k < 0 then throw s!"Cannot iterate a negative number of times ({k})"
    if k > 16 then throw s!"Refusing to unfold iterate {k} times"
    if k = 0 then
      let x ← freshVar α
      return .lambda [x] α.toTerm (.var x)
    else
      let mut acc := R
      for _ in [1:k.toNat] do
        acc ← B.Term.compose α α α acc R
      return acc
  -- | "const" => throw "Not implemented"
  -- | "rank" => throw "Not implemented"
  -- | "father" => throw "Not implemented"
  -- | "subtree" => throw "Not implemented"
  -- | "arity" => throw "Not implemented"
  -- binary pred operators
  | "=>", _ => pure ∘₂ .imp
  | "<=>", _ => pure ∘₂ .iff
  | s, τ => λ _ _ => throw s!"Unknown binary operator {s} : {τ}"

def String.toUnaryOp : String → B.BType → B.Term → Decoder B.Term
  | "not", _ => pure ∘ .not
  | "max", _ => pure ∘ .max
  | "imax", _ => pure ∘ .max
  -- | "rmax" => throw "Unary operator not implemented"
  | "min", _ => pure ∘ .min
  | "imin", _ => pure ∘ .min
  -- | "rmin" => throw "Unary operator not implemented"
  | "card", .int => pure ∘ .card
  | "dom", .set τ => λ S => do
    let .set (.prod _ σ) ← S.getType | unreachable!
    B.Term.dom τ σ S
  | "ran", .set σ => λ S => do
    let .set (.prod τ _) ← S.getType | unreachable!
    B.Term.ran τ σ S
  | "POW", τ => fun S => do
    let .set (.set _) := τ | throw s!"POW operator expects a set, got type {τ}"
    return S.pow
  | "POW1", τ => fun S => do
    let .set (.set τ') := τ | throw s!"POW1 operator expects a set, got type {τ}"
    .Collect S.pow fun s => .Exists τ'.toTerm fun x => return x ∈ᴮ s
  | "FIN", .set (.set τ) => λ S => do .Collect (𝒫ᴮ S) (B.Term.mkFinite τ ·)
  | "FIN1", .set (.set τ) => λ S => do
    .Collect (𝒫ᴮ S) (fun x => do
      let emp ← B.Term.emptyset τ
      let fin ← (x.mkFinite τ)
      return fin ∧ᴮ ¬ᴮ(x =ᴮ emp))
  | "union", τ => fun S => do
    let .set τ' := τ | throw s!"union operator expects a set, got type {τ}"
    .Collect τ'.toTerm fun x => .Exists S fun y => return x ∈ᴮ y
  | "inter", τ => fun S => do
    let .set τ' := τ | throw s!"union operator expects a set, got type {τ}"
    .Collect τ'.toTerm fun x => .All S fun y => return x ∈ᴮ y
  | "seq", τ => λ S => do
    let .set (.set (.prod _ _)) := τ | throw s!"seq operator expects a set(set(prod α β)), got type {τ}"
    S.seq
  | "seq1", τ => fun S =>
    S.seq1
  | "iseq", τ => λ S => do
    let .set (.set (.prod _ _)) := τ | throw s!"iseq operator expects a set(set(prod α β)), got type {τ}"
    S.iseq
  | "iseq1", τ => fun S =>
    S.iseq1
  -- | "-" => throw "Unary operator not implemented"
  | "-i", _ => fun S => return .int 0 -ᴮ S
  -- | "-r" => throw "Unary operator not implemented"
  | "~", τ => fun R => do
    let .set (.prod β α) := τ | throw s!"~ operator expects a relation, got type {τ}"
    let x ← freshVar α
    let y ← freshVar β
    return .collect [y, x] (β.toTerm ⨯ᴮ α.toTerm) (.var x ↦ᴮ .var y ∈ᴮ R)
  | "size", τ => fun S => do
    unless τ == .int do throw s!"size operator expects a type int, got {τ}"
    let .set (.prod .int α) ← S.getType | throw s!"size operator expects a sequence."
    B.Term.card <$> (S.dom .int α)
  | "perm", τ => fun S => do
    let .set _ := τ | throw s!"perm operator expects a set, got type {τ}"
    S.perm
  | "first", _ => B.Term.seqFirst
  | "last", _ => B.Term.seqLast
  | "tail", _ => B.Term.seqTail
  | "front", _ => B.Term.seqFront
  | "rev", _ => B.Term.seqRev
  | "id", τ => fun S => do
    let .set (.prod α α') := τ | throw s!"id operator expects a set (prod α α), got type {τ}"
    unless α = α' do throw s!"id operator expects a set (prod α α), got type {τ}"
    let x ← freshVar α
    /- NOTE: `id` is encoded as a function since it is a bijection
    by definition, although it is defined as a relation. -/
    -- let y := s!"x{← incrementFreshVarC}"
    -- return .collect [x, y] (S ⨯ᴮ S) (.var x =ᴮ .var y)
    return .lambda [x] S (.var x)
  | "closure", _ => pure ∘ (.closure true)
  | "closure1", _ => pure ∘ (.closure false)
  -- | "tail" => throw "Unary operator not implemented"
  -- | "front" => throw "Unary operator not implemented"
  -- | "rev" => throw "Unary operator not implemented"
  -- | "conc" => throw "Unary operator not implemented"
  -- | "succ" => throw "Unary operator not implemented"
  -- | "pred" => throw "Unary operator not implemented"
  | "rel", τ => fun f => do
    let .set (.prod α β) := τ | throw s!"rel operator expects a relation, got type {τ}"
    B.Term.toRelation α β f
  | "fnc", τ => fun r => do
    let .set (.prod α (.set β)) := τ
      | throw s!"fnc operator expects a set-valued function, got type {τ}"
    B.Term.toFunction α β r
  -- | "real" => throw "Unary operator not implemented"
  -- | "floor" => throw "Unary operator not implemented"
  -- | "ceiling" => throw "Unary operator not implemented"
  -- | "tree" => throw "Unary operator not implemented"
  -- | "btree" => throw "Unary operator not implemented"
  -- | "top" => throw "Unary operator not implemented"
  -- | "sons" => throw "Unary operator not implemented"
  -- | "prefix" => throw "Unary operator not implemented"
  -- | "postfix" => throw "Unary operator not implemented"
  -- | "sizet" => throw "Unary operator not implemented"
  -- | "mirror" => throw "Unary operator not implemented"
  -- | "left" => throw "Unary operator not implemented"
  -- | "right" => throw "Unary operator not implemented"
  -- | "infix" => throw "Unary operator not implemented"
  -- | "bin" => throw "Unary operator not implemented"
  | s, τ => λ _ => throw s!"Unsupported unary operator {s} with type {τ}"

-- set_option maxHeartbeats 220000 in
def decodeTerm : Xml.Element → Decoder B.Term
  | ⟨"Id", a, _⟩ => do
    match (a.get! "value") with
    | "MAXINT" => return .MAXINT
    | "MININT" => return .MININT
    | "BOOL" => return .𝔹
    | "INTEGER" => return .ℤ
    | "NATURAL" => .Collect .ℤ (pure ∘ ((.int 0) ≤ᴮ ·))
    | "NAT" => .Collect .ℤ (pure ∘ (λ v => (.int 0 ≤ᴮ v) ∧ᴮ (v ≤ᴮ .MAXINT)))
    | "INT" => .Collect .ℤ (pure ∘ (λ v => (.MININT ≤ᴮ v) ∧ᴮ (v ≤ᴮ .MAXINT)))
    | s =>
      /-
        `x<i>` is used for naming fresh variables. We need to account for potential name clashes
        from the POG file.
      -/
      if String.Pos.Raw.get! s 0 == 'x' then
        if let some n := s.drop 1 |>.toNat? then
          modify λ st => { st with env.freshvarsc := max n st.env.freshvarsc }
      let typref := (a.get! "typref").toNat!
      let τ := (← get).types[typref]!
      let v := s ++ (match a.get? "suffix" with | some s => "_" ++ s | none => "")
      addToContext v τ
      pure <| .var v
  | ⟨"Exp_Comparison",a,c⟩ | ⟨"Binary_Exp",a,c⟩ | ⟨"Binary_Pred",a,c⟩ => do
    let typemap := (←get).types
    let op := (a.get! "op").toBinaryOp <| match (a.get? "typref") with
      | none => .bool
      | some τ =>
        typemap[τ.toNat!]!
    let ts ← c.attach.filterMapM (λ | ⟨.Element e, _⟩ => some <$> decodeTerm e | _ => pure none)
    match h : ts.size with
    | 2 =>
      let out := op ts[0] ts[1]
      -- special case for x = λ_._ or x ∈ _ ⇸ _ or x = y with x in flags
      match ← out with
      | .eq (.var x) (.lambda _ _ _) => modify λ st => { st with env := { st.env with flags := st.env.flags.insert x}}
      | .mem (.var x) (.pfun _ _) => modify λ st => { st with env := { st.env with flags := st.env.flags.insert x}}
      | .mem (.var x) (.collect _ (.pfun _ _) _) => modify λ st => { st with env := { st.env with flags := st.env.flags.insert x}}
      | .eq (.var x) (.var y) =>
        let flags := (←get).env.flags
        if x ∈ flags then modify λ st => { st with env := { st.env with flags := flags.insert y}}
        else if y ∈ flags then modify λ st => { st with env := { st.env with flags := flags.insert x}}
        else do pure ()
      | _ => pure ()
      out
    | n => throw s!"Expected 2 terms, got {n}"
  | ⟨"Unary_Pred",a,c⟩ | ⟨"Unary_Exp",a,c⟩=> do
    let typemap := (←get).types
    let op := (a.get! "op").toUnaryOp <| match a.get? "typref" with
      | none => .bool
      | some n => typemap[n.toNat!]!
    let ts ← c.attach.filterMapM (λ | ⟨.Element e, _⟩ => some <$> decodeTerm e | _ => pure none)
    match h : ts.size with
    | 1 => op ts[0]
    | n => throw s!"Expected 1 term, got {n}"
  | ⟨"EmptySet", a, _⟩ | ⟨"EmptySeq", a, _⟩ => do
    let τ : B.BType := (← get).types[(a.get! "typref").toNat!]!
    let .set α := τ | throw s!"EmptySet type is expected to be a set, got {τ}"
    B.Term.emptyset α
  | ⟨"Integer_Literal", a, _⟩ => do
    let n := (a.get! "value").toInt!
    pure <| .int n
  | ⟨"Boolean_Literal", a, _⟩ => do
    match a.get! "value" with
      | "TRUE" => pure <| .bool true
      | "FALSE" => pure <| .bool false
      | s => throw s!"Invalid boolean literal {s}"
  | ⟨"Set", _, c⟩ => do
      match h : c.size with
      | 2 =>
        let ⟨.Element ⟨"Id", a, c'⟩, _⟩ := c.attach[0]'(by rw[Array.size_attach, h]; exact Nat.zero_lt_two) | unreachable!
        let ⟨.Element ⟨"Enumerated_Values", _a₁, values⟩, _⟩ := c.attach[1]'(by rw[Array.size_attach, h]; exact Nat.one_lt_two) | unreachable!
        let n ← decodeTerm ⟨"Id", a, c'⟩
        let .set τ := (← get).types[(a.get! "typref").toNat!]! | unreachable!
        let x := s!"x{← incrementFreshVarC}"
        if h : values.size = 0 then
          return n
        else
          let ⟨.Element e, _⟩ := values.attach[0]'(by rw[Array.size_attach]; exact Nat.zero_lt_of_ne_zero h) | unreachable!
          let e' ← decodeTerm e
          let mut disj := (.var x) =ᴮ e'
          let mut distinct : List B.Term := [e']
          for val in values.attach[1:] do
            match val with
            | ⟨.Element e@⟨"Id", _a₂, _c₂⟩, _⟩ =>
              let e' ← decodeTerm e
              disj := disj ∨ᴮ ((.var x) =ᴮ e')
              distinct := distinct.concat e'
            | _ => throw "Invalid Set element"
          let fin ← B.Term.mkFinite τ n
          modify λ st => { st with env := { st.env with
            distinct := st.env.distinct.concat distinct
            finite := st.env.finite.concat fin
          }}
          return (n =ᴮ (.collect [x] τ.toTerm disj))
      | 1 =>
        let ⟨.Element e@⟨"Id", a, c'⟩, _⟩ := c.attach[0]'(by rw [Array.size_attach, h]; exact Nat.zero_lt_one) | unreachable!
        let E ← decodeTerm e
        let τE : B.BType := (← get).types[(a.get! "typref").toNat!]!
        let .set τ := τE | throw s!"Set type is expected to be a set, got {τE}"
        let «∅» ← B.Term.emptyset τ
        let finE ← B.Term.mkFinite τ E
        let hyps := (← get).env.hypotheses
        let sets_hyps := hyps.find? .sets |>.get! |>.concat (¬ᴮ (E =ᴮ «∅»))
        modify fun st ↦ { st with env.hypotheses := hyps.replace .sets sets_hyps } --, env.finite := st.env.finite.concat finE }
        return E
      | _ => throw "Invalid entity in Set"
  | ⟨"Quantified_Pred", a, c⟩ => do
    let quantifier ← getQuantifier (a.get! "type")
    match h : c.size with
    | 2 =>
      let ⟨.Element ⟨"Variables", _a₁, vars⟩, _⟩ := c.attach[0]'(by rw [Array.size_attach, h]; exact Nat.zero_lt_two) | unreachable!
      let ⟨.Element ⟨"Body", _a₂, c'⟩, _⟩ := c.attach[1]'(by rw [Array.size_attach, h]; exact Nat.one_lt_two) | unreachable!
      if h' : c'.size = 1 then
        let ⟨.Element body, _⟩ := c'.attach[0]'(by rw [Array.size_attach, h']; exact Nat.zero_lt_one) | unreachable!
        let vs ← vars.attach.foldlM (λ
          | acc, ⟨.Element e, _⟩ => do
            let .var v ← decodeTerm e | unreachable!
            return acc.concat v
          | acc, _ => return acc) []
        let Γ := (← get).env.context
        let dom := vs.map (λ v => Γ.find? v |>.get! |>.toTerm)
        let body ← decodeTerm body
        return quantifier vs (dom.tail!.foldl (· ⨯ᴮ ·) dom.head!) body
      else throw "Invalid entity in Quantified_Pred"
    | _ => throw "Invalid entity in Quantified_Pred"
  | ⟨"Quantified_Exp", a, c⟩ => do
    let typemap := (← get).types
    let τ : B.BType := match a.get? "typref" with
      | none => .bool
      | some n => typemap[n.toNat!]!
    let quantifier ← getExpQuantifier (a.get! "type") τ
    match h : c.size with
    | 3 =>
      let ⟨.Element ⟨"Variables", _a₁, vars⟩, _⟩ := c.attach[0]'(by rw [Array.size_attach, h]; exact Nat.zero_lt_succ 2) | unreachable!
      let ⟨.Element ⟨"Pred", _a₂, c'⟩, _⟩ := c.attach[1]'(by rw [Array.size_attach, h]; exact Nat.one_lt_succ_succ 1) | unreachable!
      if h' : c'.size = 1 then
        let ⟨.Element ⟨"Body", _a₃, c''⟩, _⟩ := c.attach[2]'(by rw [Array.size_attach, h]; exact Nat.lt_add_one 2) | unreachable!
        let ⟨.Element pred, _⟩ := c'.attach[0]'(by rw [Array.size_attach, h']; exact Nat.zero_lt_one) | unreachable!
        if h'' : c''.size = 1 then
          let ⟨.Element body, _⟩ := c''.attach[0]'(by rw [Array.size_attach, h'']; exact Nat.zero_lt_one) | unreachable!
          let vs : List B.𝒱 ← vars.attach.foldlM (λ
            | acc, ⟨.Element e, _⟩ => do
              let .var v ← decodeTerm e | throw s!"Invalid variable {e} in Quantified_Exp"
              return acc.concat v
            | acc, _ => return acc) []
          let Γ := (← get).env.context
          let vtyps := vs.map (λ v => Γ.find? v |>.get!)
          let vs' ← freshVarList vtyps
          let doms : List B.Term := vtyps.map (·.toTerm)
          let P ← decodeTerm pred
          let foldedDom :=
            .collect vs' (doms.tail.foldl (· ⨯ᴮ ·) doms.head!) <| B.substList vs (vs'.map .var) P
          let body ← decodeTerm body
          quantifier vs foldedDom body
        else throw "Invalid entity in Quantified_Exp"
      else throw "Invalid entity in Quantified_Exp"
    | _ => throw "Invalid entity in Quantified_Exp"
  | ⟨"Quantified_Set", a, c⟩ => do
    let .set τ := (← get).types[(a.get! "typref").toNat!]! | unreachable!
    match h : c.size with
    | 2 =>
      let ⟨.Element ⟨"Variables", _a₁, vars⟩, _⟩ := c.attach[0]'(by rw [Array.size_attach, h]; exact Nat.zero_lt_two) | unreachable!
      let ⟨.Element ⟨"Body", _a₂, c'⟩, _⟩ := c.attach[1]'(by rw [Array.size_attach, h]; exact Nat.one_lt_two) | unreachable!
      if h' : c'.size = 1 then
        let ⟨.Element body, _⟩ := c'.attach[0]'(by rw [Array.size_attach, h']; exact Nat.zero_lt_one) | unreachable!
        let body ← decodeTerm body
        match h : vars.size with
        | 0 => throw "Empty Quantified_Set"
        | _ =>
          let vs ← vars.attach.foldlM (λ
            | acc, ⟨.Element e, _⟩ => do
              let .var v ← decodeTerm e | unreachable!
              return acc.concat v
            | acc, _ => return acc) []
          let Γ := (← get).env.context
          let dom := vs.map (λ v => Γ.find? v |>.get! |>.toTerm)
          return .collect vs (dom.tail!.foldl (· ⨯ᴮ ·) dom.head!) body
      else throw "Invalid entity in Quantified_Set"
    | _ => throw "Invalid entity in Quantified_Set"
  | ⟨"Nary_Pred", a, c⟩ => do
    let ⟨op, default⟩ ← match (a.get! "op") with
      | "&" => pure (B.Term.and, B.Term.bool true)
      | "or" => pure (B.Term.or, B.Term.bool false)
      | s => throw s!"Unknown Nary_Pred operator {s}"
    if h : c.size > 0 then
      let ⟨.Element c₀, _⟩ := c.attach[0]'(by rw [Array.size_attach]; exact h) | unreachable!
      c.attach[1:].foldlM
        (λ acc e => match acc, e with
          | acc, ⟨.Element e, _⟩ => do
            return op acc (←decodeTerm e)
          | acc, _ => return acc)
        (←decodeTerm c₀)
    else return default
  | ⟨"Nary_Exp", a, c⟩ => do
    let v := s!"x{← incrementFreshVarC}"
    let .set τ := (← get).types[(a.get! "typref").toNat!]! | unreachable!
    if h : c.size > 0 then
      let ⟨.Element c₀, _⟩ := c.attach[0]'(by rw [Array.size_attach]; exact h) | unreachable!
      match (a.get! "op") with
        | "{" => .collect [v] τ.toTerm <$> (c.attach[1:].foldlM (λ acc e => match acc, e with
          | acc, ⟨.Element e, _⟩ => do
            return acc ∨ᴮ (.var v =ᴮ (←decodeTerm e))
          | acc, _ => return acc) (.var v =ᴮ (←decodeTerm c₀)))
        -- `[e₁, …, eₙ]` is the sequence `{1 ↦ e₁, …, n ↦ eₙ}`; `τ` is already
        -- the pair type `int × σ`, so the same comprehension shape applies.
        | "[" =>
          -- `[e₁, …, eₙ]` is the sequence `{1 ↦ e₁, …, n ↦ eₙ}`; `τ` is already
          -- the pair type `int × σ`, so the same comprehension shape applies.
          .collect [v] τ.toTerm <$> Prod.snd <$> (c.attach[1:].foldlM (λ acc e => match acc, e with
          | (i, acc), ⟨.Element e, _⟩ => do
            return (i + 1, acc ∨ᴮ (.var v =ᴮ (.int (i + 1) ↦ᴮ (←decodeTerm e))))
          | acc, _ => return acc) ((1 : Int), .var v =ᴮ (.int 1 ↦ᴮ (←decodeTerm c₀))))
        | s => throw s!"Unknown Nary_Exp operator {s}"
    else throw "Empty Nary_Exp"
  | ⟨"Boolean_Exp", _, c⟩ => do
    if h : c.size = 1 then
      let ⟨.Element e, _⟩ := c.attach[0]'(by rw [Array.size_attach, h]; exact Nat.zero_lt_one) | unreachable!
      decodeTerm e
    else throw s!"Boolean_Exp expects exactly one argument"
  | ⟨n,_,_⟩ => throw s!"{n} not implemented"
termination_by e => e
decreasing_by
  all_goals simp_wf
  · apply Nat.lt_trans (m := sizeOf <| Xml.Content.Element _) (by decreasing_trivial) (by decreasing_trivial)
  · apply Nat.lt_trans (m := sizeOf <| Xml.Content.Element _) (by decreasing_trivial) (by decreasing_trivial)
  · apply Nat.lt_trans (m := sizeOf <| Xml.Content.Element _) (by decreasing_trivial) (by decreasing_trivial)
  · apply Nat.lt_trans (m := sizeOf <| Xml.Content.Element _) (by decreasing_trivial) (by decreasing_trivial)
  · apply Nat.lt_trans (m := sizeOf <| Xml.Content.Element _) (by decreasing_trivial) (by decreasing_trivial)
  · calc
      _ < sizeOf (Xml.Content.Element (Xml.Element.Element "Id" a c')) := by decreasing_trivial
      _ < sizeOf c := by decreasing_trivial
      _ < _ := by decreasing_trivial
  · calc
      _ < sizeOf (Xml.Content.Element e) := by decreasing_trivial
      _ < sizeOf values := by decreasing_trivial
      _ < sizeOf (Xml.Element.Element "Enumerated_Values" _a₁ values) := by decreasing_trivial
      _ < sizeOf (Xml.Content.Element (Xml.Element.Element "Enumerated_Values" _a₁ values)) := by decreasing_trivial
      _ < sizeOf c := by decreasing_trivial
      _ < _ := by decreasing_trivial
  · subst e
    calc
      _ < sizeOf (Xml.Content.Element (Xml.Element.Element "Id" _a₂ _c₂)) := by decreasing_trivial
      _ < sizeOf values := by decreasing_trivial
      _ < sizeOf (Xml.Element.Element "Enumerated_Values" _a₁ values) := by decreasing_trivial
      _ < sizeOf (Xml.Content.Element (Xml.Element.Element "Enumerated_Values" _a₁ values)) := by decreasing_trivial
      _ < sizeOf c := by decreasing_trivial
      _ < _ := by decreasing_trivial
  · subst e
    calc
      _ < sizeOf (Xml.Content.Element (Xml.Element.Element "Id" a c')) := by decreasing_trivial
      _ < sizeOf c := by decreasing_trivial
      _ < _ := by decreasing_trivial
  · calc
      _ < sizeOf (Xml.Content.Element e) := by decreasing_trivial
      _ < sizeOf vars := by decreasing_trivial
      _ < sizeOf (Xml.Element.Element "Variables" _a₁ vars) := by decreasing_trivial
      _ < sizeOf (Xml.Content.Element (Xml.Element.Element "Variables" _a₁ vars)) := by decreasing_trivial
      _ < sizeOf c := by decreasing_trivial
      _ < _ := by decreasing_trivial
  · calc
      _ < sizeOf (Xml.Content.Element body) := by decreasing_trivial
      _ < sizeOf c' := by decreasing_trivial
      _ < sizeOf (Xml.Element.Element "Body" _a₂ c') := by decreasing_trivial
      _ < sizeOf (Xml.Content.Element (Xml.Element.Element "Body" _a₂ c')) := by decreasing_trivial
      _ < sizeOf c := by decreasing_trivial
      _ < _ := by decreasing_trivial
  · calc
      _ < sizeOf (Xml.Content.Element e) := by decreasing_trivial
      _ < sizeOf vars := by decreasing_trivial
      _ < sizeOf (Xml.Element.Element "Variables" _a₁ vars) := by decreasing_trivial
      _ < sizeOf (Xml.Content.Element (Xml.Element.Element "Variables" _a₁ vars)) := by decreasing_trivial
      _ < sizeOf c := by decreasing_trivial
      _ < _ := by decreasing_trivial
  · calc
      _ < sizeOf (Xml.Content.Element pred) := by decreasing_trivial
      _ < sizeOf c' := by decreasing_trivial
      _ < sizeOf (Xml.Element.Element "Pred" _a₂ c') := by decreasing_trivial
      _ < sizeOf (Xml.Content.Element (Xml.Element.Element "Pred" _a₂ c')) := by decreasing_trivial
      _ < sizeOf c := by decreasing_trivial
      _ < _ := by decreasing_trivial
  · calc
      _ < sizeOf (Xml.Content.Element body) := by decreasing_trivial
      _ < sizeOf c'' := by decreasing_trivial
      _ < sizeOf (Xml.Element.Element "Body" _a₃ c'') := by decreasing_trivial
      _ < sizeOf (Xml.Content.Element (Xml.Element.Element "Body" _a₃ c'')) := by decreasing_trivial
      _ < sizeOf c := by decreasing_trivial
      _ < _ := by decreasing_trivial
  · calc
      _ < sizeOf (Xml.Content.Element body) := by decreasing_trivial
      _ < sizeOf c' := by decreasing_trivial
      _ < sizeOf (Xml.Element.Element "Body" _a₂ c') := by decreasing_trivial
      _ < sizeOf (Xml.Content.Element (Xml.Element.Element "Body" _a₂ c')) := by decreasing_trivial
      _ < sizeOf c := by decreasing_trivial
      _ < _ := by decreasing_trivial
  · calc
      _ < sizeOf (Xml.Content.Element _) := by decreasing_trivial
      _ < sizeOf _ := by decreasing_trivial
      _ < sizeOf (Xml.Element.Element _ _a₂ _) := by decreasing_trivial
      _ < sizeOf (Xml.Content.Element (Xml.Element.Element _ _ _)) := by decreasing_trivial
      _ < sizeOf _ := by decreasing_trivial
      _ < _ := by decreasing_trivial
  · apply Nat.lt_trans (m := sizeOf <| Xml.Content.Element _) (by decreasing_trivial) (by decreasing_trivial)
  · apply Nat.lt_trans (m := sizeOf <| Xml.Content.Element _) (by decreasing_trivial) (by decreasing_trivial)
  · apply Nat.lt_trans (m := sizeOf <| Xml.Content.Element _) (by decreasing_trivial) (by decreasing_trivial)
  · calc
      _ < sizeOf (Xml.Content.Element e) := by decreasing_trivial
      _ < sizeOf c := by decreasing_trivial
      _ < _ := by decreasing_trivial
  · apply Nat.lt_trans (m := sizeOf <| Xml.Content.Element _) (by decreasing_trivial) (by decreasing_trivial)
  -- `Boolean_Exp`
  · apply Nat.lt_trans (m := sizeOf <| Xml.Content.Element _) (by decreasing_trivial) (by decreasing_trivial)

def decodeDefineField (c : Array Xml.Content) : Decoder (List B.Term × B.TypeContext) := do
    let mut invs := []; let mut binds : B.TypeContext := ∅
    for d in c do
      match d with
      | .Element ⟨n, a, c⟩ => do
        let inv ← decodeTerm ⟨n, a, c⟩
        -- add definitions/invariants to the context
        unless n = "Set" ∧ c.size = 1 do
          invs := invs.concat inv
        match inv with
        | .mem (.var v) _ =>
          let env := (← get).env
          match env.context.find? v with
          | some τ => binds := binds.insert v τ
          | none => throw s!"Variable {v} not found in context"
        | _ => continue
      | _ => continue
    return (invs, binds)

def decodeDefine : String → Array Xml.Content → Decoder Unit
  | "B definitions", _ => pure () -- default env already contains B definitions
  | s, c => match s.toDefinitionType with
    | some d => do
      let ⟨invs, binds⟩ ← decodeDefineField c
      modify λ st =>
        { st with
          env := { st.env with
            hypotheses := st.env.hypotheses.replace d ((st.env.hypotheses.find? d |>.get!) ++ invs),
            context := binds.foldl (λ acc k v => acc.insert k v) st.env.context
          }
        }
    | none => throw s!"Invalid definition clause {s}"

def decodeType : Xml.Content → Decoder B.BType
  | .Element ⟨"Id",a,_⟩ =>
    match (a.get! "value") with
    | "BOOL" => return .bool
    | "INTEGER" => return .int
    | _ =>
      -- case of the name of an abstract set...
      return .int
  | .Element ⟨"Unary_Exp",a,c⟩ =>
    match a.get! "op" with
    | "POW" =>
      match h : c.size with
      | 1 => .set <$> decodeType c[0]
      | n => throw s!"POW expects 1 argument, {n} were given"
    | o => throw s!"Invalid unary operator {o} in Type"
  | .Element ⟨"Binary_Exp",a,c⟩ =>
    match a.get! "op" with
    | "*" =>
      match h : c.size with
      | 2 => .prod <$> (decodeType c[0]) <*> (decodeType c[1])
      | n => throw s!"* expects 2 arguments, {n} were given"
    | o => throw s!"Invalid binary operator {o} in Type"
  -- Records are deliberately out of scope on this branch.
  | .Element ⟨"Struct", _, _⟩ => throw "decodeType: records are not supported"
  | _ => throw "Invalid content in Type element"

def removeEmptyDeep (c : Array Xml.Content) : Array Xml.Content :=
  c.attach.filterMap (λ
    | ⟨.Element ⟨n,a,c⟩, _⟩ => some <| .Element ⟨n,a,removeEmptyDeep c⟩
    | _ => none
  )
termination_by c
decreasing_by
  all_goals simp_wf
  · rename_i c' mem_c'
    calc
      sizeOf c < sizeOf (Xml.Content.Element (Xml.Element.Element n a c)) := by decreasing_trivial
      _ < sizeOf c' := Array.sizeOf_lt_of_mem mem_c'

def decodeTypeInfos (c : Array Xml.Content) : Decoder Unit :=
  for typ in c do
    match typ with
    | .Element ⟨"Type",a,c⟩ => do
      let id := (a.get! "id").toNat!
      -- check that `id` is exactly the next type to be added
      match id == (← get).types.size, h : c.size with
      | true, 1 => do
        let τ ← decodeType c[0]
        modify λ st => { st with types := st.types.push τ}
      | true, n => throw s!"Type element expects 1 argument, {n} were given"
      | false, _ => throw s!"Invalid Type id \"{id}\" in TypeInfos (should be \"{(← get).types.size}\")"
    | .Element ⟨e,_,_⟩ => throw s!"Invalid Type element {e} in TypeInfos"
    | _ => continue

def decodeGoal (c : Array Xml.Content) (lh : Array B.Term) : Decoder B.SimpleGoal := do
  let mut hs := []
  let mut g : B.Term := .bool true
  for e in c do
    match e with
    | .Element ⟨"Tag", _, _⟩ | .Element ⟨"Proof_State", _, _⟩ => continue
    | .Element ⟨"Ref_Hyp", a, _⟩ =>
      let n := (a.get! "num").toNat! - 1 -- local hyps are 1-indexed
      match lh[n]? with
      | none => throw s!"Invalid Local_Hyp index {n+1}"
      | some lhₙ => hs := hs.concat <| lhₙ
    | .Element ⟨"Goal", _, #[.Element e]⟩ => g ← decodeTerm e
    | e => throw s!"Invalid Goal element {e}"
  return { hyps := hs, goal := g }

def decodeProofObligationElement (c : Array Xml.Content) : Decoder B.ProofObligation := do
  let mut po : B.ProofObligation := {}
  let mut lh : Array B.Term := #[]
  for e in c do
    match e with
    | .Element ⟨"Tag", _, _⟩ => continue
    | .Element ⟨"Definition", a, _⟩ =>
      if a.get! "name" != "B definitions" then
        let d := (← get).env.hypotheses.find? ((a.get! "name").toDefinitionType |>.get!) |>.get!
        po := { po with defs := po.defs ++ d }
      else continue
    | .Element ⟨"Hypothesis", _, #[.Element e]⟩ =>
      po := { po with hyps := po.hyps ++ [← decodeTerm e] }
    | .Element ⟨"Local_Hyp", a, #[.Element e]⟩ =>
      lh := lh.push (← decodeTerm e)
      let i := (a.get! "num").toNat!
      if lh.size != i then throw s!"Invalid Local_Hyp index {i}"
    | .Element ⟨"Simple_Goal", _, c⟩ => do
      let sg ← decodeGoal c lh
      po := { po with goals := po.goals.concat sg }
    | _ => throw "Invalid Proof_Obligation element"
  return po

def decodeProofObligation (c : Array Xml.Content) : Decoder Unit := do
  -- Snapshot global context/flags before decoding this PO so PO-local
  -- additions can be isolated. Atelier B reuses fresh names (e.g. `s392`)
  -- across POs with potentially different types — keeping them in the
  -- global env would cause spurious type conflicts.
  let ctxBefore := (← get).env.context
  let flagsBefore := (← get).env.flags
  let po ← decodeProofObligationElement c
  let stAfter := (← get)
  -- Compute PO-local additions: keys in ctxAfter not in ctxBefore.
  let beforeKeys : Std.HashSet B.𝒱 := Std.HashSet.ofList ctxBefore.keys
  let localCtx : B.TypeContext :=
    stAfter.env.context.entries.foldl
      (fun acc ⟨k, τ⟩ => if beforeKeys.contains k then acc else acc.insert k τ)
      ∅
  let localFlags : List B.𝒱 := stAfter.env.flags.filter (· ∉ flagsBefore)
  let po_simp : B.ProofObligation :=
    { po with
      goals := po.goals.map (λ sg => { sg with goal := sg.goal.simplify })
      localContext := localCtx
      localFlags := localFlags }
  -- Restore the global env to its pre-PO state, then record the PO.
  modify λ st => { st with env := { st.env with
    context := ctxBefore
    flags := flagsBefore
    po := st.env.po.concat po_simp } }

def readPOG (path : System.FilePath) : IO <| Except String Xml.Element := Xml.parse <$> IO.FS.readFile path

def POGtoB : Xml.Element → Decoder Unit
  -- remove the root Xml.Element "Proof_Obligations"
  | ⟨_, _, content⟩ => do
    let data := removeEmptyDeep content
    for c in data do
      /-
        NOTE: the order of the POs is important. Unfortunately, the ordering defined above
        with the dedup does not guarantee that the POs are in the same order as in the XML file.
        We need to implememt three different functions to filter out TypeInfos, Define and
        Proof_Obligation elements, and apply in that order the decoding functions.
      -/
      match c with
      | .Element ⟨"TypeInfos", _, c⟩ => decodeTypeInfos c
      | _ => continue

    for c in data do
      match c with
      | .Element ⟨"Define", a, c⟩ => decodeDefine (a.get! "name") c
      | _ => continue
    for c in data do
      match c with
      | .Element ⟨"Proof_Obligation", _, c⟩ =>
        modify λ st => { st with env := { st.env with hypotheses := st.env.hypotheses.mapVal (λ _ => (·.map (·.simplify))) } }
        decodeProofObligation c
      | _ => continue

-- #eval do
--   let pog ← readPOG ("Test"/"Test.pog") |>.propagateError
--   let ⟨_, st⟩ ← POGtoB pog |>.run ∅ |>.propagateError
--   return st
