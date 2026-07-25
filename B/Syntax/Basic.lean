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
  -- `div` truncates towards zero and `mod` is the matching remainder, as in
  -- Atelier B; `exp` is exponentiation with a possibly symbolic exponent.
  | div (x y : Term)
  | mod (x y : Term)
  | exp (x y : Term)
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
  | finite (S : Term)
  -- Transitive closure of a homogeneous relation; `refl` selects the
  -- reflexive-transitive closure (`closure`) over the transitive one
  -- (`closure1`).
  | closure (refl : Bool) (R : Term)
  -- Sum (`isSum`) or product over the values of an integer-valued function,
  -- i.e. Atelier B's `iSIGMA` / `iPI`.
  | fold (isSum : Bool) (f : Term)
  -- `iterate(R, n)`: `R` composed with itself `n` times, for a symbolic `n`
  -- (a literal count is unfolded into compositions by the POG reader).
  | iterate (R n : Term)
  -- `conc(ss)`: the sequences in `ss` concatenated in order.  `R` is the
  -- result type as a term (`BType.toTerm`), carried so that typing `conc` does
  -- not have to recurse through `ss`, which can be arbitrarily deep.
  | conc (R ss : Term)
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
infixl:75 " /ᴮ " => Term.div
infixl:75 " %ᴮ " => Term.mod
infixl:80 " ^ᴮ " => Term.exp
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
  | .maplet x y | .add x y | .sub x y | .mul x y | .and x y | .le x y | .eq x y
  | .div x y | .mod x y | .exp x y => fv x ++ fv y
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
  | .finite S => fv S
  | .closure _ R => fv R
  | .fold _ f => fv f
  | .conc R ss => fv R ++ fv ss
  | .iterate R n => fv R ++ fv n
  | .min S => fv S
  | .max S => fv S

def bv : Term → List 𝒱
  | .var _ | .int _ | .bool _ | .ℤ | .𝔹 => []
  | .maplet x y | .add x y | .sub x y | .mul x y | .and x y | .le x y | .eq x y
  | .div x y | .mod x y | .exp x y => bv x ++ bv y
  | .not x => bv x
  | .mem x S => bv x ++ bv S
  | .collect vs D P | .all vs D P | .lambda vs D P => vs ++ bv D ++ bv P
  | .cprod S T | .union S T | .inter S T => bv S ++ bv T
  | .pfun A B => bv A ++ bv B
  | .app f x => bv f ++ bv x
  | .card S | .finite S | .min S | .max S | .pow S | .closure _ S | .fold _ S => bv S
  | .conc R ss => bv R ++ bv ss
  | .iterate R n => bv R ++ bv n

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
