import Encoder.Basic

namespace SMT

def subst (x : 𝒱) (t e : Term) : Term :=
  match e with
  | Term.var v => if v = x then t else e
  | Term.mul a b => .mul (subst x t a) (subst x t b)
  | Term.add a b => .add (subst x t a) (subst x t b)
  | Term.sub a b => .sub (subst x t a) (subst x t b)
  | Term.le a b => .le (subst x t a) (subst x t b)
  | Term.pair a b => .pair (subst x t a) (subst x t b)
  | Term.some a => .some (subst x t a)
  | Term.imp a b => .imp (subst x t a) (subst x t b)
  | Term.not a => .not (subst x t a)
  | Term.or a b => .or (subst x t a) (subst x t b)
  | Term.and a b => .and (subst x t a) (subst x t b)
  | Term.eq a b => .eq (subst x t a) (subst x t b)
  | Term.forall vs τs body => if x ∈ vs then .forall vs τs body else .forall vs τs (subst x t body)
  | Term.exists vs τs body => if x ∈ vs then .exists vs τs body else .exists vs τs (subst x t body)
  | Term.lambda vs τs body => if x ∈ vs then .lambda vs τs body else .lambda vs τs (subst x t body)
  | Term.app f a => .app (subst x t f) (subst x t a)
  | Term.distinct ts => .distinct (ts.attach.map (λ ⟨e, _⟩ => subst x t e))
  | Term.snd p => .snd (subst x t p)
  | Term.fst p => .fst (subst x t p)
  | Term.none => .none
  | Term.the e => .the (subst x t e)
  | Term.ite c ct cf => .ite (subst x t c) (subst x t ct) (subst x t cf)
  | Term.as a τ => .as (subst x t a) τ
  | Term.bool b => .bool b
  | Term.int n => .int n


-- e[xs[i] ← ts[i]] for all i
def substList (xs : List 𝒱) (ts : List Term) (e : Term) : Term :=
  match xs, ts with
  | x :: xs, t :: ts => substList xs ts (subst x t e)
  | _, _ => e

partial def simplifier : Term → Term
  | Term.app (.var "NATURAL") x => .le (.int 0) x
  | Term.app (.var "NATURAL1") x => .le (.int 1) x
  | Term.app (.var "NAT") x => .and (.le (.int 0) x) (.le x (.int B.MAXINT))
  | Term.app (.var "INTEGER") _ => .bool true
  | Term.app (.var "INT") x => .and (.le (.int B.MININT) x) (.le x (.int B.MAXINT))
  | Term.app (.var "BOOL") _ => .bool true
  | Term.app (.lambda [v] [_] e) x => subst v x e
  | Term.app (.lambda (v::vs) (_::τs) e) x => .lambda vs τs (subst v x e)
  | Term.app f x => .app (simplifier f) (simplifier x)
  | Term.mul a b => .mul (simplifier a) (simplifier b)
  | Term.add (.int x) (.int y) => .int (x+y)
  | Term.add a b => .add (simplifier a) (simplifier b)
  | Term.le a b => bif a == b then .bool true else .le (simplifier a) (simplifier b)
  | Term.fst (.pair a b) => simplifier a
  | Term.snd (.pair a b) => simplifier b
  | Term.fst t => .fst (simplifier t)
  | Term.snd t => .snd (simplifier t)
  | Term.pair (.fst x) (.snd x') =>
    let simpx := simplifier x
    let simpx' := simplifier x'
    if simpx == simpx' then simpx else .pair simpx.fst simpx'.snd
  | Term.pair a b => .pair (simplifier a) (simplifier b)
  | Term.some (.the a) => (simplifier a)
  | Term.some a => .some (simplifier a)
  | Term.the (.some t) => simplifier t
  | Term.the t => .the (simplifier t)
  | Term.imp (.bool true) p => p
  | Term.imp (.bool false) _ | .imp _ (.bool true) => .bool true
  | Term.imp p q => .imp (simplifier p) (simplifier q)
  | Term.or (.bool false) p | .or p (.bool false) => p
  | Term.or (.bool true) _ | .or _ (.bool true) => .bool true
  | Term.or (.not p) q => .imp p q
  | Term.or (.exists vs τs p) q => .imp (.forall vs τs (.not p)) q
  | Term.or p q => .or (simplifier p) (simplifier q)
  | Term.not (.not p) => p
  | Term.not (.forall vs τs (.not p)) => .exists vs τs p
  | Term.not (.forall vs τs (.imp p q)) => .exists vs τs (.and p (.not q))
  | Term.not (.exists vs τs p) => .forall vs τs (.not p)
  -- | Term.not (.imp p q) => .and p (.not q)
  | Term.not (.bool b) => .bool !b
  | Term.not (.and p q) => .or (.not p) (.not q)
  | Term.not (.or p q) => .and (.not p) (.not q)
  | Term.not p => .not (simplifier p)
  | Term.and (.bool false) _ | .and _ (.bool false) => .bool false
  | Term.and (.bool true) p | .and p (.bool true) => p
  | Term.and a b => .and (simplifier a) (simplifier b)
  | Term.eq (.pair x y) (.pair u v) => .and (.eq x u) (.eq y v)
  | Term.eq (.bool true) p | .eq p (.bool true) => p
  | Term.eq (.bool false) p | .eq p (.bool false) => .not p
  | Term.eq a b => if a == b then .bool true else .eq (simplifier a) (simplifier b)
  | Term.exists _ _ (.bool b) => .bool b
  | Term.exists vs τs e => .exists vs τs (simplifier e)
  | Term.forall _ _ (.bool b) => .bool b
  | Term.forall vs τs e => .forall vs τs (simplifier e)
  | Term.lambda vs τs e => .lambda vs τs (simplifier e)
  | Term.ite (.bool true) t _ | .ite (.bool false) _ t => t
  | Term.ite c t e => .ite (simplifier c) (simplifier t) (simplifier e)
  | Term.sub a b => .sub (simplifier a) (simplifier b)
  | Term.distinct [] => .bool true
  | Term.distinct [_] => .bool true
  | Term.distinct ts => .distinct (ts.map simplifier)
  | Term.none => .none
  | Term.as e τ => .as e τ
  | Term.bool b => .bool b
  | Term.int n => .int n
  | Term.var v => .var v

partial def simplify_aux (t : Term) : Term := simplifier_aux t <| simplifier t
  where simplifier_aux (t t' : Term) : Term := if t == t' then t else simplifier_aux t' <| simplifier t'

def simplify (i : Instr) : Instr :=
  match i with
  | .assert t => .assert <| simplify_aux t
  | .define_const v τ i => .define_const v τ <| simplify_aux i
  | .define_fun v τ σ i => .define_fun v τ σ <| simplify_aux i
  | _ => i

def simpAsserts : Stages → Stages
  | .instr is => .instr <| is.map simplify
  | .asserts as => .asserts <| as.attach.map (λ ⟨a, _⟩ => simpAsserts a)

nonrec def Env.simplify (E : Env) : Env :=
  -- dbg_trace "{E.declarations[0]!} ---> {simplify E.declarations[0]!}"
  { E with
    declarations := E.declarations.map simplify
    asserts := simpAsserts E.asserts
  }

end SMT
