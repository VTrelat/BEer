import B.Inference
open Batteries

namespace B

-- t[x := e]
def subst (x : 𝒱) (e t : Term) : Term :=
  match t with
  | .var v => if v = x then e else t
  | .𝔹
  | .ℤ
  | .int _
  | .bool _ => t
  | .pfun A B => .pfun (subst x e A) (subst x e B)
  | .app f a => .app (subst x e f) (subst x e a)
  | .inter A B => .inter (subst x e A) (subst x e B)
  | .union A B => .union (subst x e A) (subst x e B)
  | .cprod A B => .cprod (subst x e A) (subst x e B)
  | .pow A => .pow (subst x e A)
  | .mem a S => .mem (subst x e a) (subst x e S)
  | .eq p q => .eq (subst x e p) (subst x e q)
  | .not p => .not (subst x e p)
  | .and p q => .and (subst x e p) (subst x e q)
  | .mul a b => .mul (subst x e a) (subst x e b)
  | .add a b => .add (subst x e a) (subst x e b)
  | .sub a b => .sub (subst x e a) (subst x e b)
  | .div a b => .div (subst x e a) (subst x e b)
  | .mod a b => .mod (subst x e a) (subst x e b)
  | .exp a b => .exp (subst x e a) (subst x e b)
  | .maplet a b => .maplet (subst x e a) (subst x e b)
  | .le a b => .le (subst x e a) (subst x e b)
  | .min S => .min (subst x e S)
  | .max S => .max (subst x e S)
  | .card S => .card (subst x e S)
  | .finite S => .finite (subst x e S)
  | .closure r R => .closure r (subst x e R)
  | .fold s f => .fold s (subst x e f)
  | .collect vs D P =>
    if x ∈ vs then .collect vs (subst x e D) P else .collect vs (subst x e D) (subst x e P)
  | .lambda vs D P =>
    if x ∈ vs then .lambda vs (subst x e D) P else .lambda vs (subst x e D) (subst x e P)
  | .all vs D P =>
    if x ∈ vs then .all vs (subst x e D) P else .all vs (subst x e D) (subst x e P)

notation t:max "[" x " := " e:min "]" => subst x e t

-- t[xs[i] ← es[i]] for all i
def substList (xs : List 𝒱) (es : List Term) (t : Term) : Term :=
  match xs, es with
  | x :: xs, e :: es => substList xs es (subst x e t)
  | _, _ => t

notation t "[" xs " := " es "]" => substList xs es t

def gatherMapletsl : Term → List Term
  | .maplet x y => gatherMapletsl x |>.concat y
  | x => [x]

def gatherMapletsl' (x : Term) (n: Nat) : List Term :=
  match n with
  | 0 => []
  | 1 => [x]
  | n+1 =>
    match x with
    | .maplet x y => gatherMapletsl' x n |>.concat y
    | x => [x]

def gatherMapletsr : Term → List Term
  | .maplet x y => x :: gatherMapletsr y
  | x => [x]

def simplifier_aux_add : Term → Term → Term
  | .int 0, p => p
  | p, .int 0 => p
  | .int n, .int m => .int (n + m)
  | .add x (.int a), .int b => Term.add x (.int (a + b))
  | p, q => .add p q
def simplifier_aux_mul : Term → Term → Term
  | .int 0, _ => .int 0
  | _, .int 0 => .int 0
  | .int 1, p => p
  | p, .int 1 => p
  | .int n, .int m => .int (n * m)
  | .mul x (.int a), .int b => Term.mul x (.int (a * b))
  | p, q => .mul p q
def simplifier_aux_mem : Term → Term → Term
  | x, .collect vs D P =>
    if fv x ∩ fv P = [] then
      let xs := gatherMapletsl x
      if xs.length = vs.length ∧ (∀ v ∈ vs, v ∉ fv P) then
        if vs.length = 1 then (x ∈ᴮ D) ∧ᴮ subst (vs.head!) x P
        else (x ∈ᴮ D) ∧ᴮ substList vs xs P
      else Term.mem x (Term.collect vs D P)
    else Term.mem x (Term.collect vs D P)
  | .maplet x y, .lambda vs D P =>
    let xs := gatherMapletsl' x vs.length
    if xs.length == vs.length ∧ (∀ v ∈ vs, v ∉ fv P) ∧ (∀ v ∈ vs, ∀ y ∈ xs, v ∉ fv y) then
      substList vs xs P =ᴮ y
    else Term.app (Term.lambda vs D P) x =ᴮ y
  | x, S => .mem x S
def simplifier_aux_exists : List 𝒱 → Term → Term → Term
  | _, .collect _ _ (.bool false), _ => .bool false
  | v::vs, .collect xs D' P', Q => .exists (v::vs) D' (((vs.foldl (λ acc v' => .maplet acc (.var v')) (.var v)) ∈ᴮ (Term.collect xs D' P')) ∧ᴮ Q)
  | v, D, P => .exists v D P
def simplifier_aux_all : List 𝒱 → Term → Term → Term
  | v::vs, .collect xs D P, Q =>
    if (v::vs ++ xs).Nodup ∧ (∀ x ∈ v::vs ++ xs, x ∉ fv D) ∧ (∀ x ∈ v::vs, x ∉ fv P) then
      if P = .bool false then .bool true
      else
        .all (v::vs) D (((vs.foldl (λ acc v' => .maplet acc (.var v')) (.var v)) ∈ᴮ (Term.collect xs D P)) ⇒ᴮ Q)
    else .all (v::vs) (.collect xs D P) Q
  | vs, D, P => .all vs D P
def simplifier_aux_not : Term → Term
  | .bool true => .bool false
  | .bool false => .bool true
  | .not p => p
  | p => .not p
def simplifier_aux_and : Term → Term → Term
  | .bool false, _ => .bool false
  | _, .bool false => .bool false
  | .bool true, p => p
  | p, .bool true => p
  | p, q => .and p q
def simplifier_aux_eq : Term → Term → Term
  | .var v', .var v => if v == v' then .bool true else Term.eq (.var v') (.var v)
  | e, .var v => (.var v) =ᴮ e
  | p, .bool true | .bool true, p => p
  | p, .bool false | .bool false, p => ¬ᴮ p
  | p, q => if p == q then .bool true else p =ᴮ q
def simplifier_aux_collect : List 𝒱 → Term → Term → Term
  | _, D, .bool true => D
  | v, D, P => .collect v D P


def simplifier : Term → Term
  | Term.add p q => simplifier_aux_add (simplifier p) (simplifier q)
  | Term.mul p q => simplifier_aux_mul (simplifier p) (simplifier q)
  | Term.mem x S => simplifier_aux_mem (simplifier x) (simplifier S)
  -- | Term.exists vs D P => simplifier_aux_exists vs (simplifier D) (simplifier P)
  | Term.all vs D P => simplifier_aux_all vs (simplifier D) (simplifier P)
  -- | Term.imp p q => .imp (simplifier p) (simplifier q)
  -- | Term.or (.bool false) p | .or p (.bool false) => p
  -- | Term.or (.bool true) _ | .or _ (.bool true) => .bool true
  -- | Term.or p q => .or (simplifier p) (simplifier q)
  | Term.not p => simplifier_aux_not (simplifier p)
  | Term.and p q => simplifier_aux_and (simplifier p) (simplifier q)
  | Term.le x y => .le (simplifier x) (simplifier y)
  | Term.eq p q => simplifier_aux_eq (simplifier p) (simplifier q)
  | Term.collect v D P => simplifier_aux_collect v (simplifier D) (simplifier P)
  | Term.pfun A B => .pfun (simplifier A) (simplifier B)
  | Term.inter A B => .inter (simplifier A) (simplifier B)
  | Term.lambda vs D P => .lambda vs (simplifier D) (simplifier P)
  | Term.app f x => .app (simplifier f) (simplifier x)
  | Term.max S => .max (simplifier S)
  | Term.min S => .min (simplifier S)
  | Term.card S => .card (simplifier S)
  | Term.finite S => .finite (simplifier S)
  | Term.closure r R => .closure r (simplifier R)
  | Term.fold s f => .fold s (simplifier f)
  | Term.div x y => .div (simplifier x) (simplifier y)
  | Term.mod x y => .mod (simplifier x) (simplifier y)
  | Term.exp x y => .exp (simplifier x) (simplifier y)
  | Term.union S T => .union (simplifier S) (simplifier T)
  | Term.cprod S T => .cprod (simplifier S) (simplifier T)
  | Term.pow S => .pow (simplifier S)
  | Term.𝔹 => Term.𝔹
  | Term.ℤ => Term.ℤ
  | Term.sub x y => .sub (simplifier x) (simplifier y)
  | Term.maplet x y => .maplet (simplifier x) (simplifier y)
  | Term.bool b => Term.bool b
  | Term.int n => Term.int n
  | Term.var v => Term.var v
  -- TODO: simplifier subst like x = a ∧ ...? Easily done within solvers

partial def Term.simplify (t : Term) : Term := simplifier_aux t (simplifier t)
  where simplifier_aux (t t' : Term) : Term := if t == t' then t else simplifier_aux t' (simplifier t')

def BType2SMTType : B.BType → SMT.SMTType
  | .int => .int
  | .bool => .bool
  | .set β => .fun (BType2SMTType β) .bool
  | β ×ᴮ γ => .pair (BType2SMTType β) (BType2SMTType γ)

end B
