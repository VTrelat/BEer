namespace SMT

inductive SMTType where
  | bool
  | int
  | unit
  | «fun» (arg ret : SMTType)
  | option (τ : SMTType)
  | pair (α β : SMTType)
  deriving Inhabited, DecidableEq

abbrev SMTType.rel (α β : SMTType) : SMTType := (α.pair β).fun .bool

instance : LawfulBEq SMTType where
  eq_of_beq := by
    intro a b h
    induction a generalizing b <;> (cases b <;> try trivial) <;> (
      rw [beq_iff_eq] at h
      injections; subst_eqs
      rfl)
  rfl := by
    intro a
    cases a <;>
    first
    | rfl
    | exact ReflBEq.rfl

def SMTType.toString : SMTType → String
  | .bool => "Bool"
  | .int => "Int"
  | .unit => "()"
  | .fun arg ret => s!"(-> {arg.toString} {ret.toString})"
  | .option τ => s!"(Option {toString τ})"
  | .pair α β => s!"(Pair {toString α} {toString β})"

instance : ToString SMTType := ⟨SMTType.toString⟩

abbrev 𝒱 := String

inductive Term where
  -- atomic terms
  | var (v : 𝒱)
  | int (n : Int)
  | bool (b : Bool)
  | app (f : Term) (x : Term)
  -- binders
  | lambda (v : List 𝒱) (τs : List SMTType) (t : Term)
  | forall (v : List 𝒱) (τs : List SMTType) (t : Term)
  | exists (v : List 𝒱) (τs : List SMTType) (t : Term)
  | as (t : Term) (τ : SMTType)
  -- logic
  | eq (t₁ t₂ : Term)
  | and (t₁ t₂ : Term)
  | or (t₁ t₂ : Term)
  | not (t : Term)
  | imp (t₁ t₂ : Term)
  | ite (c t e : Term)
  -- constructors
  | some (t : Term) | the (t : Term) | none
  | pair (t₁ t₂ : Term) | fst (t : Term) | snd (t : Term)
  | distinct (ts : List Term)
  -- arithmetic
  | le (t₁ t₂ : Term)
  | add (t₁ t₂ : Term)
  | sub (t₁ t₂ : Term)
  | mul (t₁ t₂ : Term)
  deriving Inhabited, BEq

@[induction_eliminator]
def Term.rec'.{u} {motive : Term → Sort u} (t : Term)
  (var : (v : 𝒱) → motive (Term.var v)) (int : (n : Int) → motive (Term.int n))
  (bool : (b : Bool) → motive (Term.bool b)) (app : (f x : Term) → motive f → motive x → motive (f.app x))
  (lambda : (v : List 𝒱) → (τs : List SMTType) → (t : Term) → motive t → motive (Term.lambda v τs t))
  («forall» : (v : List 𝒱) → (τs : List SMTType) → (t : Term) → motive t → motive (Term.forall v τs t))
  («exists» : (v : List 𝒱) → (τs : List SMTType) → (t : Term) → motive t → motive (Term.exists v τs t))
  (as : (t : Term) → (τ : SMTType) → motive t → motive (t.as τ))
  (eq : (t₁ t₂ : Term) → motive t₁ → motive t₂ → motive (t₁.eq t₂))
  (and : (t₁ t₂ : Term) → motive t₁ → motive t₂ → motive (t₁.and t₂))
  (or : (t₁ t₂ : Term) → motive t₁ → motive t₂ → motive (t₁.or t₂))
  (not : (t : Term) → motive t → motive t.not)
  (imp : (t₁ t₂ : Term) → motive t₁ → motive t₂ → motive (t₁.imp t₂))
  (ite : (c t e : Term) → motive c → motive t → motive e → motive (c.ite t e))
  (some : (t : Term) → motive t → motive t.some) (the : (t : Term) → motive t → motive t.the)
  (none : motive Term.none) (pair : (t₁ t₂ : Term) → motive t₁ → motive t₂ → motive (t₁.pair t₂))
  (fst : (t : Term) → motive t → motive t.fst) (snd : (t : Term) → motive t → motive t.snd)
  (distinct : (ts : List Term) → (∀ t ∈ ts, motive t) → motive (Term.distinct ts))
  (le : (t₁ t₂ : Term) → motive t₁ → motive t₂ → motive (t₁.le t₂))
  (add : (t₁ t₂ : Term) → motive t₁ → motive t₂ → motive (t₁.add t₂))
  (sub : (t₁ t₂ : Term) → motive t₁ → motive t₂ → motive (t₁.sub t₂))
  (mul : (t₁ t₂ : Term) → motive t₁ → motive t₂ → motive (t₁.mul t₂)) : motive t :=
  match t with
  | .var v => var v
  | .bool b => bool b
  | .int n => int n
  | .mul x y => mul x y (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul) (rec' y var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .sub x y => sub x y (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul) (rec' y var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .add x y => add x y (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul) (rec' y var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .le x y => le x y (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul) (rec' y var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .snd x => snd x (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .fst x => fst x (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .pair x y => pair x y (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul) (rec' y var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .none => none
  | .the x => the x (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .some x => some x (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .ite c x y => ite c x y (rec' c var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul) (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul) (rec' y var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .imp x y => imp x y (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul) (rec' y var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .not x => not x (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .or x y => or x y (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul) (rec' y var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .and x y => and x y (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul) (rec' y var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .eq x y => eq x y (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul) (rec' y var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .as x τ => as x τ (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .exists vs D P => «exists» vs D P (rec' P var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .forall vs D P => «forall» vs D P (rec' P var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .lambda vs D P => lambda vs D P (rec' P var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | .app f x => app f x (rec' f var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul) (rec' x var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul)
  | @Term.distinct ts =>
    distinct ts fun t _ ↦ t.rec' var int bool app lambda «forall» «exists» as eq and or not imp ite some the none pair fst snd distinct le add sub mul



def noneCast : SMTType → Term := λ τ => .as .none (.option τ)
prefix:50 "none$" => noneCast

prefix:70 "λˢ " => Term.lambda
infixl:60 " ∧ˢ " => Term.and
infixl:40 " =ˢ " => Term.eq
infixl:50 " ⇒ˢ " => Term.imp
infixl:40 " ≤ˢ " => Term.le
prefix:80 "¬ˢ" => Term.not
prefix:20 "@ˢ" => Term.app
infixl:45 " ∨ˢ " => Term.or
infixl:70 " +ˢ " => Term.add
infixl:70 " -ˢ " => Term.sub
infixl:75 " *ˢ " => Term.mul

def toSMTArgList (vs : List <| 𝒱 × SMTType) :=
  vs.map (λ ⟨v, τ⟩ => s!"({v} {τ.toString})") |>.intersperse " " |>.foldl (·++·) ""

def Term.toString : Term → String
  | .var v => v
  | .int n => if n < 0 then s!"(- {-n})" else ToString.toString n
  | .bool b => ToString.toString b
  | .app (.lambda v τ t) x => s!"(@ {(Term.lambda v τ t).toString} {x.toString})"
  | .app (.var v) x => s!"({v} {x.toString})"
  | .app f x => s!"(@ {f.toString} {x.toString})"
  | .forall vs τs t => s!"(forall ({toSMTArgList <| vs.zip τs}) {Term.toString t})"
  | .lambda vs τs t => s!"(lambda ({toSMTArgList <| vs.zip τs}) {Term.toString t})"
  | .exists vs τs t => s!"(exists ({toSMTArgList <| vs.zip τs}) {Term.toString t})"
  | .as t τ => s!"(as {Term.toString t} {SMTType.toString τ})"
  | .eq t₁ t₂ => s!"(= {Term.toString t₁} {Term.toString t₂})"
  | .and t₁ t₂ => s!"(and "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .or t₁ t₂ => s!"(or "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .not t => s!"(not "++ Term.toString t ++")"
  | .imp t₁ t₂ => s!"(=> "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .le t₁ t₂ => s!"(<= "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .some t => s!"(some "++ Term.toString t ++")"
  | .none => "none"
  | .the t => s!"(the "++ Term.toString t ++")"
  | .pair t₁ t₂ => s!"(pair "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .fst t => s!"(fst "++ Term.toString t ++")"
  | .snd t => s!"(snd "++ Term.toString t ++")"
  | .add t₁ t₂ => s!"(+ "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .sub t₁ t₂ => s!"(- "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .mul t₁ t₂ => s!"(* "++ Term.toString t₁++" "++ Term.toString t₂ ++")"
  | .ite c t e => s!"(ite "++ Term.toString c++" "++ Term.toString t++" "++ Term.toString e ++")"
  | .distinct ts =>
    let ds := ts.attach.map (λ ⟨t, _⟩ => Term.toString t) |>.intersperse " " |>.foldl (·++·) ""
    s!"(distinct {ds})"

instance : ToString Term := ⟨Term.toString⟩

def fv : Term → List 𝒱
  | .var v => [v]
  | .int _ => []
  | .bool _ => []
  | .app f x => fv f ++ fv x
  | .lambda vs _ t | .forall vs _ t | .exists vs _ t => List.removeAll (fv t) vs
  | .as t _ => fv t
  | .eq t₁ t₂ => fv t₁ ++ fv t₂
  | .and t₁ t₂ => fv t₁ ++ fv t₂
  | .or t₁ t₂ => fv t₁ ++ fv t₂
  | .not t => fv t
  | .imp t₁ t₂ => fv t₁ ++ fv t₂
  | .le t₁ t₂ => fv t₁ ++ fv t₂
  | .some t => fv t
  | .none => []
  | .the t => fv t
  | .pair t₁ t₂ => fv t₁ ++ fv t₂
  | .fst t => fv t
  | .snd t => fv t
  | .add t₁ t₂ => fv t₁ ++ fv t₂
  | .sub t₁ t₂ => fv t₁ ++ fv t₂
  | .mul t₁ t₂ => fv t₁ ++ fv t₂
  | .ite c t e => fv c ++ fv t ++ fv e
  | .distinct ts => ts.attach.map (λ ⟨x, _⟩ => fv x) |>.flatten

def bv : Term → List 𝒱
  | .var _ => []
  | .int _ => []
  | .bool _ => []
  | .app f x => bv f ++ bv x
  | .lambda vs _ t | .forall vs _ t | .exists vs _ t => vs ++ bv t
  | .as t _ => bv t
  | .eq t₁ t₂ => bv t₁ ++ bv t₂
  | .and t₁ t₂ => bv t₁ ++ bv t₂
  | .or t₁ t₂ => bv t₁ ++ bv t₂
  | .not t => bv t
  | .imp t₁ t₂ => bv t₁ ++ bv t₂
  | .le t₁ t₂ => bv t₁ ++ bv t₂
  | .some t => bv t
  | .none => []
  | .the t => bv t
  | .pair t₁ t₂ => bv t₁ ++ bv t₂
  | .fst t => bv t
  | .snd t => bv t
  | .add t₁ t₂ => bv t₁ ++ bv t₂
  | .sub t₁ t₂ => bv t₁ ++ bv t₂
  | .mul t₁ t₂ => bv t₁ ++ bv t₂
  | .ite c t e => bv c ++ bv t ++ bv e
  | .distinct ts => ts.attach.map (λ ⟨x, _⟩ => bv x) |>.flatten

theorem fv.mem_var {v} : v ∈ fv (Term.var v) := by rw [fv, List.mem_singleton]
theorem fv.mem_int {x n} : ¬ x ∈ fv (Term.int n) := by
  unfold fv
  exact List.not_mem_nil
theorem fv.mem_bool {x b} : ¬ x ∈ fv (Term.bool b) := by
  unfold fv
  exact List.not_mem_nil
theorem fv.mem_add {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x +ˢ y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_sub {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x -ˢ y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_mul {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x *ˢ y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_and {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x ∧ˢ y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_or {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x ∨ˢ y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_imp {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x ⇒ˢ y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_le {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x ≤ˢ y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_eq {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x =ˢ y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_not {v x} : v ∈ fv x → v ∈ fv (¬ˢ x) := by
  rw [fv]
  exact id
theorem fv.mem_forall {v vs τs P} : v ∈ (fv P) ∧ v ∉ vs → v ∈ fv (.forall vs τs P) := by
  rw [fv]
  rintro ⟨_, _⟩
  apply List.mem_filter.mpr
  and_intros
  · assumption
  · rwa [List.elem_eq_mem, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
theorem fv.mem_lambda {v vs τs P} : v ∈ (fv P) ∧ v ∉ vs → v ∈ fv (.lambda vs τs P) := by
  rw [fv]
  rintro ⟨_, _⟩
  apply List.mem_filter.mpr
  and_intros
  · assumption
  · rwa [List.elem_eq_mem, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
theorem fv.mem_exists {v vs τs P} : v ∈ (fv P) ∧ v ∉ vs → v ∈ fv (.exists vs τs P) := by
  rw [fv]
  rintro ⟨_, _⟩
  apply List.mem_filter.mpr
  and_intros
  · assumption
  · rwa [List.elem_eq_mem, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
theorem fv.mem_app {v f x} : v ∈ fv f ∨ v ∈ fv x → v ∈ fv ((@ˢ f) x) := by
  rw [fv, List.mem_append]
  exact id
theorem fv.mem_as {v x τ} : v ∈ fv x → v ∈ fv (.as x τ) := by
  rw [fv]
  exact id
theorem fv.mem_some {v x} : v ∈ fv x → v ∈ fv (.some x) := by
  rw [fv]
  exact id
theorem fv.mem_none {v} : ¬ v ∈ fv (.none) := by
  rw [fv]
  exact List.not_mem_nil
theorem fv.mem_the {v x} : v ∈ fv x → v ∈ fv (.the x) := by
  rw [fv]
  exact id
theorem fv.mem_pair {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x.pair y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_fst {v x} : v ∈ fv x → v ∈ fv (x.fst) := by
  rw [fv]
  exact id
theorem fv.mem_snd {v x} : v ∈ fv x → v ∈ fv (x.snd) := by
  rw [fv]
  exact id
theorem fv.mem_ite {v c t e} : v ∈ fv c ∨ v ∈ fv t ∨ v ∈ fv e → v ∈ fv (.ite c t e) := by
  rw [fv, List.mem_append]
  rintro (h | h | h)
  · exact Or.inl <| List.mem_append_left (fv t) h
  · exact Or.inl <| List.mem_append_right (fv c) h
  · exact Or.inr h
theorem fv.mem_distinct {v ts} (t : { x // x ∈ ts }) : v ∈ fv t → v ∈ fv (.distinct ts) := by
  intro hv
  rw [fv]
  apply List.mem_flatten_of_mem _ hv
  exact List.mem_map.mpr ⟨t, List.mem_attach ts t, rfl⟩
