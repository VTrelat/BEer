import POGReader.Basic

open B

def Decoder.Collect (D : Term) (P : Term → Decoder Term) : Decoder Term := do
  let x := s!"x{← incrementFreshVarC}"
  .collect [x] D <$> (P <| .var x)

abbrev B.Term.Natural : Decoder Term :=
  .Collect .ℤ <| fun x => return .int 0 ≤ᴮ x

def Decoder.All (D : Term) (P : Term → Decoder Term) : Decoder Term := do
  let x := s!"x{← incrementFreshVarC}"
  .all [x] D <$> (P <| .var x)

def Decoder.Exists (D : Term) (P : Term → Decoder Term) : Decoder Term := do
  let x := s!"x{← incrementFreshVarC}"
  .exists [x] D <$> (P <| .var x)

def B.Term.domRestriction (F R : Term) : Decoder Term := do
  let x := s!"x{← incrementFreshVarC}"
  let y := s!"y{← incrementFreshVarC}"
  return .collect [x, y] R (.var x ↦ᴮ .var y ∈ᴮ R ∧ᴮ .var x ∈ᴮ F)
infix:90 "◁" => B.Term.domRestriction

/-- `F ⩤ R` — drop the pairs of `R` whose *domain* element lies in `F`. -/
def B.Term.domSubtraction (F R : Term) : Decoder Term := do
  let x := s!"x{← incrementFreshVarC}"
  let y := s!"y{← incrementFreshVarC}"
  return .collect [x, y] R (.var x ↦ᴮ .var y ∈ᴮ R ∧ᴮ ¬ᴮ(.var x ∈ᴮ F))
infix:90 "⩤" => B.Term.domSubtraction

def B.Term.ranRestriction (R F : Term) : Decoder Term := do
  let x := s!"x{← incrementFreshVarC}"
  let y := s!"y{← incrementFreshVarC}"
  return .collect [x, y] R (.var x ↦ᴮ .var y ∈ᴮ R ∧ᴮ .var y ∈ᴮ F)
infix:90 "▷" => B.Term.ranRestriction

/-- `R ⩥ F` — drop the pairs of `R` whose *range* element lies in `F`. -/
def B.Term.ranSubtraction (R F : Term) : Decoder Term := do
  let x := s!"x{← incrementFreshVarC}"
  let y := s!"y{← incrementFreshVarC}"
  return .collect [x, y] R (.var x ↦ᴮ .var y ∈ᴮ R ∧ᴮ ¬ᴮ(.var y ∈ᴮ F))
infix:90 "⩥" => B.Term.ranSubtraction

def B.Term.overload (τ σ : BType) (Q R : Term) : Decoder Term := do
  let x ← freshVar τ
  let y ←  freshVar σ
  let domR := Term.dom R
  return .collect [x, y] (τ.toTerm ⨯ᴮ σ.toTerm)
    (((.var x ↦ᴮ .var y ∈ᴮ Q) ∧ᴮ ¬ᴮ(.var x ∈ᴮ domR)) ∨ᴮ (.var x ↦ᴮ .var y ∈ᴮ R))

def B.Term.tot_on (D : Term) (σ : BType) (f : Term) : Decoder Term := do
  .All D <| λ x => .Exists σ.toTerm <| fun y => return (x ↦ᴮ y) ∈ᴮ f

def B.Term.tot (τ σ : BType) (f : Term) : Decoder Term := do
  return .eq τ.toTerm (.dom f)

def B.Term.tfun (A B : Term) : Decoder Term :=
  .Collect (A ⇸ᴮ B) fun f => .All A fun x => .Exists B fun y => return (x ↦ᴮ y) ∈ᴮ f
infixl:90 " →ᴮ " => B.Term.tfun

def B.Term.inj_on (D f : Term) : Decoder Term :=
  .All D <| fun x => .All D <| fun y => return ((@ᴮ f) x =ᴮ (@ᴮ f) y) ⇒ᴮ (x =ᴮ y)
def B.Term.inj (τ : B.BType) (f : Term) : Decoder Term := inj_on τ.toTerm f

def B.Term.injpfun (A B : Term) : Decoder Term :=
  .Collect (A ⇸ᴮ B) fun f =>
    .All A fun x₁ =>
      .All A fun x₂ =>
        .All B fun y =>
          return (x₁ ↦ᴮ y ∈ᴮ f) ∧ᴮ (x₂ ↦ᴮ y ∈ᴮ f) ⇒ᴮ x₁ =ᴮ x₂
infixl:90 " ⤔ᴮ " => B.Term.injpfun

def B.Term.surjpfun (A B : Term) : Decoder Term :=
  .Collect (A ⇸ᴮ B) fun f => .All B fun y => .Exists A fun x => return x ↦ᴮ y ∈ᴮ f
infixl:90 " ⤀ᴮ " => B.Term.surjpfun

def B.Term.injtfun (A B : Term) : Decoder Term := do
  let tfun ← A →ᴮ B
  .Collect tfun fun f =>
    .All A fun x =>
      .All A fun y =>
          return (@ᴮ f) x =ᴮ (@ᴮ f) y ⇒ᴮ x =ᴮ y
infixl:90 " ↣ᴮ " => B.Term.injtfun

def B.Term.surjtfun (A B : Term) : Decoder Term := do
  let tfun ← A →ᴮ B
  .Collect tfun fun f => .All B fun y => .Exists A fun x => return x ↦ᴮ y ∈ᴮ f
infixl:90 " ↠ᴮ " => B.Term.surjtfun

def B.Term.surj_on (D : Term) (σ : BType) (f : Term) : Decoder Term :=
  .All σ.toTerm <| fun y => .Exists D <| fun x => return x ↦ᴮ y ∈ᴮ f
def B.Term.surj (τ σ : BType) (f : Term) : Decoder Term := surj_on τ.toTerm σ f

def B.Term.bij_on (D : Term) (σ : BType) (f : Term) : Decoder Term :=
  .and <$> Term.inj_on D f <*> Term.surj_on D σ f
def B.Term.bij (τ σ : BType) (f : Term) : Decoder Term := bij_on τ.toTerm σ f

def B.Term.emptyset (τ : BType) : Decoder Term :=
  .Collect τ.toTerm <| fun _ => return (.bool .false)

/-- `finite(S)`.

The B-Book definition is `∃ N, ∃ f ∈ S ⇸ ℤ. f injective on S ∧ dom f = S ∧
∀ x ∈ S. 0 ≤ f(x) ≤ N`, i.e. a quantifier alternation over a function space per
occurrence — and every enumerated SETS clause emits one.  `beer-lite` uses the
primitive `Term.finite` instead, which the encoder turns into a constant closed
under subsets. -/
def B.Term.mkFinite (_τ : BType) (S : Term) : Decoder Term := return .finite S

def B.Term.range (i j : Term) : Decoder Term := .Collect .ℤ <| λ k => pure <| Term.and (i ≤ᴮ k) (k ≤ᴮ j)

infixr:90 "..ᴮ" => Term.range

/--
`τ` is supposed to be the type of `E`
-/
def B.Term.seq (E : Term) : Decoder Term := do
  let Nat ← Term.Natural
  .Collect (Nat ⇸ᴮ E) fun f => .Exists Nat fun n => do
    let ℐ ← .int 1 ..ᴮ n
    let tfun ← ℐ →ᴮ E
    return (f ∈ᴮ tfun)

def B.Term.seq1 (E : Term) : Decoder Term := do
  let Nat ← Term.Natural
  .Collect (Nat ⇸ᴮ E) fun f => .Exists Nat fun n => do
    let ℐ ← .int 1 ..ᴮ n
    let tfun ← ℐ →ᴮ E
    let x := s!"x{← incrementFreshVarC}"
    let y := s!"y{← incrementFreshVarC}"
    return (f ∈ᴮ tfun ∧ᴮ .exists [x, y] (Nat ⨯ᴮ E) ((.app f (.var x)) =ᴮ .var y))

def B.Term.iseq (E : Term) : Decoder Term := do
  let Nat ← Term.Natural
  let S ← seq E
  let Inj ← Nat ⤔ᴮ E
  return S ∩ᴮ Inj

def B.Term.iseq1 (E : Term) : Decoder Term := do
  let Nat ← Term.Natural
  let S ← seq1 E
  let Inj ← Nat ⤔ᴮ E
  return S ∩ᴮ Inj

def B.Term.perm (E : Term) : Decoder Term := do
  let Nat ← Term.Natural
  let S ← iseq E
  let Surj ← Nat ⤀ᴮ E
  return S ∩ᴮ Surj

/-! ## Relations -/

/-- `R ; S`, forward relational composition. `β` is the type joining the two
relations, which the caller reads off `R`'s type. -/
def B.Term.compose (α β γ : BType) (R S : Term) : Decoder Term := do
  let x ← freshVar α
  let z ← freshVar γ
  let y ← freshVar β
  return .collect [x, z] (α.toTerm ⨯ᴮ γ.toTerm)
    (.exists [y] β.toTerm ((.var x ↦ᴮ .var y ∈ᴮ R) ∧ᴮ (.var y ↦ᴮ .var z ∈ᴮ S)))

/-- `p || q` — parallel product: `{(a, c) ↦ (b, d) | a ↦ b ∈ p ∧ c ↦ d ∈ q}`.

Not to be confused with the direct product `><`, which pairs two relations
sharing a source rather than running them side by side. -/
def B.Term.parallel (α β γ δ : BType) (p q : Term) : Decoder Term := do
  let ac ← freshVar (α ×ᴮ γ)
  let bd ← freshVar (β ×ᴮ δ)
  let a ← freshVar α; let c ← freshVar γ
  let b ← freshVar β; let d ← freshVar δ
  return .collect [ac, bd] ((α.toTerm ⨯ᴮ γ.toTerm) ⨯ᴮ (β.toTerm ⨯ᴮ δ.toTerm))
    (.exists [a, c] (α.toTerm ⨯ᴮ γ.toTerm)
      (.exists [b, d] (β.toTerm ⨯ᴮ δ.toTerm)
        (((.var ac =ᴮ .var a ↦ᴮ .var c) ∧ᴮ (.var bd =ᴮ .var b ↦ᴮ .var d)) ∧ᴮ
         ((.var a ↦ᴮ .var b ∈ᴮ p) ∧ᴮ (.var c ↦ᴮ .var d ∈ᴮ q)))))

/-- `rel(f)` — the relation `{x ↦ y | y ∈ f(x)}` of a set-valued function.

Atelier B also allows `rel` on a genuine relation `A ↔ POW(B)`, which would need
an existential over `POW(B)` — a higher-order quantifier. Only the functional
reading is produced here. -/
def B.Term.toRelation (α β : BType) (f : Term) : Decoder Term := do
  let x ← freshVar α
  let y ← freshVar β
  return .collect [x, y] (α.toTerm ⨯ᴮ β.toTerm) (.var y ∈ᴮ (@ᴮ f) (.var x))

/-- `fnc(r)` — the set-valued function `λ x ∈ dom r. r[{x}]` of a relation. -/
def B.Term.toFunction (α β : BType) (r : Term) : Decoder Term := do
  let d := Term.dom r
  let x ← freshVar α
  let y ← freshVar β
  return .lambda [x] d (.collect [y] β.toTerm (.var x ↦ᴮ .var y ∈ᴮ r))

/-! ## Sequences

A B sequence over `E` is a function `1‥n → E`, i.e. a set of `int × E` pairs, so
every operator below is a set comprehension over such pairs.  `size` is `card`
of the domain, which the encoder now handles natively. -/

/-- Element type of a sequence, read off its B type. -/
def B.Term.seqElem (s : Term) : Decoder BType := do
  match ← s.getType with
  | .set (.prod .int σ) => return σ
  | τ => throw s!"Expected a sequence, got type {τ}"

def B.Term.size (_σ : BType) (s : Term) : Decoder Term := return .card (.dom s)

/-- Comprehension `{ i ↦ y ∈ ℤ × σ | P i y }`, the shape shared by every
sequence-building operator. -/
private def B.Term.seqBuild (σ : BType) (P : Term → Term → Decoder Term) : Decoder Term := do
  let i ← freshVar .int
  let y ← freshVar σ
  .collect [i, y] (.ℤ ⨯ᴮ σ.toTerm) <$> P (.var i) (.var y)

/-- `first(s) = s(1)`. -/
def B.Term.seqFirst (s : Term) : Decoder Term := return (@ᴮ s) (.int 1)

/-- `last(s) = s(size(s))`. -/
def B.Term.seqLast (s : Term) : Decoder Term := do
  return (@ᴮ s) (← s.size (← s.seqElem))

/-- `front(s)` — all but the last element. -/
def B.Term.seqFront (s : Term) : Decoder Term := do
  let σ ← s.seqElem
  let n ← s.size σ
  seqBuild σ fun i y => return (i ↦ᴮ y ∈ᴮ s) ∧ᴮ (i ≤ᴮ (n -ᴮ .int 1))

/-- `tail(s)` — all but the first element, re-indexed from 1. -/
def B.Term.seqTail (s : Term) : Decoder Term := do
  let σ ← s.seqElem
  seqBuild σ fun i y => return (.int 1 ≤ᴮ i) ∧ᴮ ((i +ᴮ .int 1) ↦ᴮ y ∈ᴮ s)

/-- `rev(s)` — the reversed sequence. -/
def B.Term.seqRev (s : Term) : Decoder Term := do
  let σ ← s.seqElem
  let n ← s.size σ
  seqBuild σ fun i y =>
    return ((.int 1 ≤ᴮ i) ∧ᴮ (i ≤ᴮ n)) ∧ᴮ (((n -ᴮ i) +ᴮ .int 1) ↦ᴮ y ∈ᴮ s)

/-- `s ^ t` — concatenation. -/
def B.Term.seqConcat (s t : Term) : Decoder Term := do
  let σ ← s.seqElem
  let n ← s.size σ
  seqBuild σ fun i y =>
    return (i ↦ᴮ y ∈ᴮ s) ∨ᴮ ((n ≤ᴮ (i -ᴮ .int 1)) ∧ᴮ ((i -ᴮ n) ↦ᴮ y ∈ᴮ t))

/-- `s <- e` — append `e` at the end. -/
def B.Term.seqAppend (s e : Term) : Decoder Term := do
  let σ ← s.seqElem
  let n ← s.size σ
  seqBuild σ fun i y =>
    return (i ↦ᴮ y ∈ᴮ s) ∨ᴮ ((i =ᴮ (n +ᴮ .int 1)) ∧ᴮ (y =ᴮ e))

/-- `e -> s` — insert `e` in front. -/
def B.Term.seqPrepend (e s : Term) : Decoder Term := do
  let σ ← s.seqElem
  seqBuild σ fun i y =>
    return ((i =ᴮ .int 1) ∧ᴮ (y =ᴮ e)) ∨ᴮ ((.int 2 ≤ᴮ i) ∧ᴮ ((i -ᴮ .int 1) ↦ᴮ y ∈ᴮ s))

/-- `s /|\ n` — the first `n` elements. -/
def B.Term.seqTake (s n : Term) : Decoder Term := do
  let σ ← s.seqElem
  seqBuild σ fun i y => return (i ↦ᴮ y ∈ᴮ s) ∧ᴮ (i ≤ᴮ n)

/-- `s \|/ n` — everything after the first `n` elements, re-indexed from 1. -/
def B.Term.seqDrop (s n : Term) : Decoder Term := do
  let σ ← s.seqElem
  seqBuild σ fun i y => return (.int 1 ≤ᴮ i) ∧ᴮ ((i +ᴮ n) ↦ᴮ y ∈ᴮ s)
