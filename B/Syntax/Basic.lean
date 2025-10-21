namespace B

abbrev 𝒱 := String

inductive Term where
  -- basic terms
  | var (v : 𝒱)
  | int (n : Int)
  | bool (b : Bool)
  -- pairs
  | maplet (x y : Term)
  -- arithmetic
  | add (x y : Term)
  | sub (x y : Term)
  | mul (x y : Term)
  | le (x y : Term)
  -- logic
  | and (x y : Term)
  | not (x : Term)
  | eq (x y : Term)
  -- sets
  -- basic sets
  | ℤ
  | 𝔹
  -- set operations
  | mem (x : Term) (S : Term)
  | collect (vs : List 𝒱) (D P : Term)
  | pow (S : Term)
  | cprod (S T : Term)
  | union (S T : Term)
  | inter (S T : Term)
  | card (S : Term)
  -- functions
  | app (f x : Term)
  | lambda (vs : List 𝒱) (D P : Term)
  | pfun (A B : Term)
  -- | tfun (A B : Term)
  | min (S : Term) -- could be extended to minᵢ, minᵣ, etc.
  | max (S : Term)
  -- quantifiers
  | all (vs : List 𝒱) (D P : Term)
  deriving DecidableEq, Inhabited

infixl:65 " ↦ᴮ " => Term.maplet
infixl:70 " +ᴮ " => Term.add
infixl:70 " -ᴮ " => Term.sub
infixl:75 " *ᴮ " => Term.mul
infixl:45 " ∧ᴮ " => Term.and
prefix:80 " ¬ᴮ " => Term.not
infixl:40 " =ᴮ " => Term.eq
infixl:40 " ≤ᴮ " => Term.le
infixl:65 " ∈ᴮ " => Term.mem
prefix:70 " 𝒫ᴮ " => Term.pow
infixl:75 " ⨯ᴮ " => Term.cprod
infixl:80 " ∪ᴮ " => Term.union
infixl:85 " ∩ᴮ " => Term.inter
prefix:20 "@ᴮ" => Term.app
infixl:90 " ⇸ᴮ " => Term.pfun
notation:90 "|" S "|ᴮ" => Term.card S

def fv : Term → List 𝒱
  | .var v => [v]
  | .int _ => []
  | .bool _ => []
  | .maplet x y | .add x y | .sub x y | .mul x y | .and x y | .le x y | .eq x y => fv x ++ fv y
  | .not x => fv x
  | .ℤ => []
  | .𝔹 => []
  | .mem x S => fv x ++ fv S
  | .collect vs D P | .all vs D P | .lambda vs D P => fv D ++ List.removeAll (fv P) vs
  | .pow S => fv S
  | .cprod S T => fv S ++ fv T
  | .union S T => fv S ++ fv T
  | .inter S T => fv S ++ fv T
  | .pfun A B => fv A ++ fv B
  | .app f x => fv f ++ fv x
  | .card S => fv S
  | .min S => fv S
  | .max S => fv S

theorem fv.mem_var {v} : v ∈ fv (Term.var v) := by rw [fv, List.mem_singleton]
theorem fv.mem_int {x n} : ¬ x ∈ fv (Term.int n) := List.count_eq_zero.mp rfl
theorem fv.mem_bool {x b} : ¬ x ∈ fv (Term.bool b) := List.count_eq_zero.mp rfl
theorem fv.mem_maplet {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x ↦ᴮ y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_add {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x +ᴮ y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_sub {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x -ᴮ y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_mul {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x *ᴮ y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_and {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x ∧ᴮ y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_le {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x ≤ᴮ y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_eq {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x =ᴮ y) := by
  rw [fv, List.mem_append]
  rintro (h | h)
  · exact Or.inl h
  · exact Or.inr h
theorem fv.mem_not {v x} : v ∈ fv x → v ∈ fv (¬ᴮ x) := id
theorem fv.mem_ℤ {v} : ¬ v ∈ fv .ℤ := List.count_eq_zero.mp rfl
theorem fv.mem_𝔹 {v} : ¬ v ∈ fv .𝔹 := List.count_eq_zero.mp rfl
theorem fv.mem_mem {v x y} : v ∈ fv x ∨ v ∈ fv y → v ∈ fv (x ∈ᴮ y) := by
  rw [fv, List.mem_append]
  exact id
theorem fv.mem_collect {v vs D P} : v ∈ fv D ∨ (v ∈ (fv P) ∧ v ∉ vs) → v ∈ fv (.collect vs D P) := by
  rw [fv, List.mem_append]
  rintro (_ | ⟨_, _⟩)
  · left; assumption
  · right
    apply List.mem_filter.mpr
    and_intros
    · assumption
    · rwa [List.elem_eq_mem, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
theorem fv.mem_all {v vs D P} : v ∈ fv D ∨ (v ∈ (fv P) ∧ v ∉ vs) → v ∈ fv (.all vs D P) := by
  rw [fv, List.mem_append]
  rintro (_ | ⟨_, _⟩)
  · left; assumption
  · right
    apply List.mem_filter.mpr
    and_intros
    · assumption
    · rwa [List.elem_eq_mem, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
theorem fv.mem_lambda {v vs D P} : v ∈ fv D ∨ (v ∈ (fv P) ∧ v ∉ vs) → v ∈ fv (.lambda vs D P) := by
  rw [fv, List.mem_append]
  rintro (_ | ⟨_, _⟩)
  · left; assumption
  · right
    apply List.mem_filter.mpr
    and_intros
    · assumption
    · rwa [List.elem_eq_mem, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
theorem fv.mem_pow {v S} : v ∈ fv S → v ∈ fv (.pow S) := id
theorem fv.mem_cprod {v S T} : v ∈ fv S ∨ v ∈ fv T → v ∈ fv (S ⨯ᴮ T) := by
  rw [fv, List.mem_append]
  exact id
theorem fv.mem_union {v S T} : v ∈ fv S ∨ v ∈ fv T → v ∈ fv (S ∪ᴮ T) := by
  rw [fv, List.mem_append]
  exact id
theorem fv.mem_inter {v S T} : v ∈ fv S ∨ v ∈ fv T → v ∈ fv (S ∩ᴮ T) := by
  rw [fv, List.mem_append]
  exact id
theorem fv.mem_card {v S} : v ∈ fv S → v ∈ fv (|S|ᴮ) := id
theorem fv.mem_app {v f x} : v ∈ fv f ∨ v ∈ fv x → v ∈ fv ((@ᴮ f) x) := by
  rw [fv, List.mem_append]
  exact id
theorem fv.mem_min {v S} : v ∈ fv S → v ∈ fv (.min S) := id
theorem fv.mem_max {v S} : v ∈ fv S → v ∈ fv (.max S) := id
theorem fv.mem_pfun {v A B} : v ∈ fv A ∨ v ∈ fv B → v ∈ fv (A ⇸ᴮ B) := by
  rw [fv, List.mem_append]
  exact id

abbrev MAXINT : Int := 2147483647
abbrev MININT : Int := -2147483647
-- #eval (Term.and (.all "x" .ℤ (.var "P")) (Term.all "x" .ℤ (.var "Q")))
-- #eval (Term.all "x" .ℤ (.all "y" .ℤ (.all "z" .ℤ (.mem (.maplet (.maplet (.var "x") (.var "y")) (.var "z")) (.cprod (.cprod .ℤ .ℤ) .ℤ)))))
-- #eval (Term.all "x" .ℤ (.all "y" .ℤ (.all "z" .ℤ (.mem (.maplet (.var "x") (.maplet (.var "y") (.var "z"))) (.cprod .ℤ (.cprod .ℤ .ℤ))))))
-- #eval (Term.all "x" .ℤ (.all "y" .ℤ (.mem (.add (.var "x") (.var "y")) (.collect "y" .ℤ (.eq (.var "y") (.int 0))))))

-- #eval (Term.neq (.var "x") (.mem (.var "y") (.var "S")))
-- #eval (Term.mem (.neq (.var "x") (.var "y")) (.var "S"))
-- #eval (Term.or (.var "P") (.or (.var "Q") (.var "R")))

-- ¬ ¬ P
-- #eval (¬ᴮ (¬ᴮ (.var "P")))
end B
