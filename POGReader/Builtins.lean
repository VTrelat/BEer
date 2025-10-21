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

def B.Term.domSubtraction (F R : Term) : Decoder Term := do
  let x := s!"x{← incrementFreshVarC}"
  let y := s!"y{← incrementFreshVarC}"
  return .collect [x, y] R (.var x ↦ᴮ .var y ∈ᴮ R ∧ᴮ ¬ᴮ(.var y ∈ᴮ F))
infix:90 "⩤" => B.Term.domSubtraction

def B.Term.ranRestriction (R F : Term) : Decoder Term := do
  let x := s!"x{← incrementFreshVarC}"
  let y := s!"y{← incrementFreshVarC}"
  return .collect [x, y] R (.var x ↦ᴮ .var y ∈ᴮ R ∧ᴮ .var y ∈ᴮ F)
infix:90 "▷" => B.Term.ranRestriction

def B.Term.ranSubtraction (R F : Term) : Decoder Term := do
  let x := s!"x{← incrementFreshVarC}"
  let y := s!"y{← incrementFreshVarC}"
  return .collect [x, y] R (.var x ↦ᴮ .var y ∈ᴮ R ∧ᴮ ¬ᴮ(.var x ∈ᴮ F))
infix:90 "⩥" => B.Term.ranSubtraction

def B.Term.dom (τ σ : BType) (f : Term) : Decoder Term := do
  .Collect τ.toTerm <| λ x => .Exists σ.toTerm <| fun y => return (x ↦ᴮ y) ∈ᴮ f

def B.Term.ran (τ σ : BType) (f : Term) : Decoder Term := do
  .Collect σ.toTerm <| λ y => .Exists τ.toTerm <| fun x => return (x ↦ᴮ y) ∈ᴮ f

def B.Term.overload (τ σ : BType) (Q R : Term) : Decoder Term := do
  let x ← freshVar τ
  let y ←  freshVar σ
  let domR ← R.dom τ σ
  return .collect [x, y] (τ.toTerm ⨯ᴮ σ.toTerm)
    (((.var x ↦ᴮ .var y ∈ᴮ Q) ∧ᴮ ¬ᴮ(.var x ∈ᴮ domR)) ∨ᴮ (.var x ↦ᴮ .var y ∈ᴮ R))

def B.Term.tot_on (D : Term) (σ : BType) (f : Term) : Decoder Term := do
  .All D <| λ x => .Exists σ.toTerm <| fun y => return (x ↦ᴮ y) ∈ᴮ f

def B.Term.tot (τ σ : BType) (f : Term) : Decoder Term := do
  .eq τ.toTerm <$> (B.Term.dom τ σ f)

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

def B.Term.finite (τ : BType) (S : Term) : Decoder Term := do
  let N := s!"x{← incrementFreshVarC}"
  let f := s!"x{← incrementFreshVarC}"
  let x := s!"x{← incrementFreshVarC}"
  let y := s!"x{← incrementFreshVarC}"
  addFunctionFlag f
  return .exists [N] .ℤ (.exists [f] (S ⇸ᴮ .ℤ) (((← inj_on S (.var f)) ∧ᴮ (S =ᴮ (← dom τ .int (.var f)))) ∧ᴮ (.all [x, y] (S⨯ᴮ.ℤ) (.imp ((.var x) ↦ᴮ (.var y) ∈ᴮ (.var f)) ((.int 0 ≤ᴮ .var y) ∧ᴮ (.var y ≤ᴮ .var N))))))
  -- TODO: exists could be factorized
  -- ∃ N ∈ ℤ, ∃ f ∈ S ⇸ ℤ, inj f ∧ S = dom f ∧ ∀ x ∈ S, 0 <= f x ∧ f x <= N
  -- FIXME: There was a confusion between `inj` and `inj_on`, check if the same happens with surj, etc, elsewhere...

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
