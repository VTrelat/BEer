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
  | .maplet a b => .maplet (subst x e a) (subst x e b)
  | .le a b => .le (subst x e a) (subst x e b)
  | .min S => .min (subst x e S)
  | .max S => .max (subst x e S)
  | .card S => .card (subst x e S)
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

theorem substList_nil {xs : List 𝒱} {t : Term} : substList xs [] t = t := by
  cases xs <;> rfl

namespace Term
def WF : Term → Prop
  | .ℤ
  | .𝔹
  | var _
  | int _
  | bool _ => True
  | min x
  | max x
  | pow x
  | card x
  | not x => x.WF
  | add x y
  | sub x y
  | mul x y
  | le x y
  | and x y
  | eq x y
  | mem x y
  | cprod x y
  | union x y
  | inter x y
  | app x y
  | pfun x y
  | maplet x y => x.WF ∧ y.WF
  | lambda vs D P
  | collect vs D P
  | all vs D P =>
    D.WF ∧
    P.WF ∧
    vs.Nodup ∧
    ∀ v ∈ vs, v ∉ fv D

end Term

def gatherMapletsl : Term → List Term
  | .maplet x y => gatherMapletsl x |>.concat y
  | x => [x]

theorem gatherMapletsl_ne_nil {x : Term} : gatherMapletsl x ≠ [] := by
  induction x with
  | maplet x y x_ih y_ih =>
    rw [gatherMapletsl, List.ne_nil_iff_length_pos, List.length_concat]
    apply Nat.zero_lt_succ
  | _ =>
    rw [gatherMapletsl]
    · apply List.cons_ne_nil
    · rintro _ _ ⟨⟩

def gatherMapletsl' (x : Term) (n: Nat) : List Term :=
  match n with
  | 0 => []
  | 1 => [x]
  | n+1 =>
    match x with
    | .maplet x y => gatherMapletsl' x n |>.concat y
    | x => [x]

theorem gatherMapletsl'_eq_gatherMapletsl {x : Term} :
  gatherMapletsl' x (gatherMapletsl x).length = gatherMapletsl x := by
  induction x with
  | maplet x y x_ih y_ih =>
    rw [gatherMapletsl, List.length_concat, gatherMapletsl']
    · rw [x_ih]
    · intro contr
      nomatch gatherMapletsl_ne_nil (List.length_eq_zero_iff.mp contr)
  | _ =>
    unfold gatherMapletsl
    rw [List.length_singleton, gatherMapletsl']

def gatherMapletsr : Term → List Term
  | .maplet x y => x :: gatherMapletsr y
  | x => [x]

def Term.isCanonical : Term → Prop
  | .ℤ | .𝔹 => True
  | .cprod S T => S.isCanonical ∧ T.isCanonical
  | _ => False

def Term.isCanonical.decidable : (t : Term) → Decidable (t.isCanonical)
  | .cprod S T =>
    let _ := Term.isCanonical.decidable S
    let _ := Term.isCanonical.decidable T
    inferInstanceAs (Decidable (_ ∧ _))
  | .ℤ | .𝔹 => inferInstanceAs (Decidable True)
  | .var _ | .int _ | .bool _ | .maplet ..
  | .add .. | .sub .. | .mul .. | .le ..
  | .and .. | .not _ | .eq ..
  | .mem .. | .collect .. | .pow _ | .union .. | .inter .. | .card _
  | .app .. | .lambda .. | .pfun ..
  | .min _ | .max _ | .all .. => inferInstanceAs (Decidable False)

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

section Theorems

theorem simplifier_aux_add.fv {x y : Term}:
  fv (simplifier_aux_add x y) ⊆ fv x ++ fv y := by
  unfold simplifier_aux_add
  split <;> simp [B.fv]
theorem simplifier_aux_mul.fv {x y : Term}:
  fv (simplifier_aux_mul x y) ⊆ fv x ++ fv y := by
  unfold simplifier_aux_mul
  split <;> simp [B.fv]
theorem simplifier_aux_and.fv {x y : Term}:
  fv (simplifier_aux_and x y) ⊆ fv x ++ fv y := by
  unfold simplifier_aux_and
  split <;> simp [B.fv]
theorem simplifier_aux_eq.fv {x y : Term}:
  fv (simplifier_aux_eq x y) ⊆ fv x ++ fv y := by
  unfold simplifier_aux_eq
  split <;> try simp [B.fv]
  repeat
    split_ifs
    intro z hz
    · nomatch hz
    · rw [B.fv]
      exact fun _ => id
theorem simplifier_aux_not.fv {x : Term}:
  fv (simplifier_aux_not x) ⊆ fv x := by
  unfold simplifier_aux_not
  split <;> simp [B.fv]

theorem gatherMapletsl_cons {x} (h : 1 < (gatherMapletsl x).length) : ∃ a b, x = a ↦ᴮ b := by
  induction x with
  | maplet x y _ _ => exists x, y
  | _ =>
    rw [gatherMapletsl, List.length_singleton] at h
    · nomatch h
    · rintro _ _ ⟨⟩

theorem not_mem_fv_subst {x : 𝒱} {t e : Term} (h : x ∉ fv t) : subst x e t = t := by
  induction t with
  | var =>
    rw [subst]
    rw [fv, List.mem_singleton, ←ne_eq, ne_comm] at h
    split_ifs <;> trivial
  | int
  | bool
  | «ℤ»
  | 𝔹 => rfl
  | card _ ih
  | min _ ih
  | max _ ih =>
    rw [subst]
    congr
    exact ih h
  | not x ih
  | pow x ih =>
    rw [fv] at h
    rw [subst, ih h]
  | maplet a b a_ih b_ih
  | add a b a_ih b_ih
  | sub a b a_ih b_ih
  | mul a b a_ih b_ih
  | le a b a_ih b_ih
  | and a b a_ih b_ih
  | eq a b a_ih b_ih
  | mem a b a_ih b_ih
  | cprod a b a_ih b_ih
  | union a b a_ih b_ih
  | inter a b a_ih b_ih
  | app a b a_ih b_ih
  | pfun a b a_ih b_ih =>
    rw [fv, List.mem_append, not_or] at h
    rw [subst, a_ih h.1, b_ih h.2]
  | collect vs D P D_ih P_ih
  | lambda vs D P D_ih P_ih
  | all vs D P D_ih P_ih =>
    rw [subst]
    rw [fv, List.mem_append, not_or, List.mem_removeAll_iff, not_and_or, not_not] at h
    split_ifs with h'
    · rw [D_ih h.1]
    · rw [D_ih h.1, P_ih (Or.resolve_right h.2 h')]

theorem not_mem_fv_substList {xs : List 𝒱} {ts : List Term} {e : Term} (h : ∀ x ∈ xs, x ∉ fv e) : substList xs ts e = e := by
  induction xs, ts using List.induction₂' with
  | nil_nil => rfl
  | nil_cons y ys => rfl
  | cons_nil x xs => rfl
  | cons_cons x xs y ys ih =>
    rw [substList, not_mem_fv_subst (h _ List.mem_cons_self)]
    apply ih fun v hv => h _ (List.mem_cons_of_mem x hv)

theorem subst_fv {v : 𝒱} {e t : Term} (h : v ∉ fv e) :
  v ∉ fv (subst v e t) := by
  induction t with
  | var w =>
    rw [subst]
    split_ifs with h''
    · assumption
    · rw [fv, List.mem_singleton]
      exact (h'' <| ·.symm)
  | int
  | bool
  | «ℤ»
  | 𝔹 =>
    rw [subst, fv]
    exact List.not_mem_nil
  | maplet x y x_ih y_ih
  | add x y x_ih y_ih
  | sub x y x_ih y_ih
  | mul x y x_ih y_ih
  | le x y x_ih y_ih
  | and x y x_ih y_ih
  | mem x y x_ih y_ih
  | eq x y x_ih y_ih
  | cprod x y x_ih y_ih
  | union x y x_ih y_ih
  | inter x y x_ih y_ih
  | app x y x_ih y_ih
  | pfun x y x_ih y_ih =>
    rw [subst, fv, List.mem_append, not_or]
    exact ⟨x_ih, y_ih⟩
  | pow x ih
  | min x ih
  | max x ih
  | card x ih
  | not x ih => exact ih
  | lambda vs D P D_ih P_ih
  | all vs D P D_ih P_ih
  | collect vs D P D_ih P_ih =>
    unfold subst
    split_ifs with h''
    · rw [fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or]
      and_intros
      · exact D_ih
      · right
        push_neg
        exact h''
    · rw [fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or]
      and_intros
      · exact D_ih
      · left
        apply P_ih

theorem not_mem_fv_substList_gatherMapletsl {x : Term} {vs : List 𝒱} {P : Term} (hP : ∀ v ∈ vs, v ∉ fv P) (h : (gatherMapletsl x).length = vs.length)
  ⦃z : 𝒱⦄ (hz : z ∈ B.fv (substList vs (gatherMapletsl x) P)) : z ∈ B.fv P ∧ z ∉ vs := by
  induction x generalizing vs with
  | maplet x y x_ih y_ih =>
    rw [gatherMapletsl, List.length_concat] at h
    obtain ⟨v, vs, rfl⟩ := List.length_pos_iff_exists_cons.mp (h ▸ Nat.succ_eq_add_one _ ▸ Nat.zero_lt_succ (gatherMapletsl x).length)
    obtain ⟨x', xs', x'_xs'_def⟩ := List.length_pos_iff_exists_cons (l := (gatherMapletsl x).concat y).mp (List.length_concat ▸ Nat.zero_lt_succ (gatherMapletsl x).length)
    rw [gatherMapletsl, x'_xs'_def, substList,
      not_mem_fv_subst (hP _ List.mem_cons_self),
      not_mem_fv_substList (fun w hw => hP _ (List.mem_cons_of_mem _ hw))] at hz
    exact ⟨hz, (hP z · hz)⟩
  | _ =>
    rw [gatherMapletsl] at h hz
    · rw [List.length_singleton] at h
      rw [eq_comm, List.length_eq_one_iff] at h
      obtain ⟨v', rfl⟩ := h
      rw [substList, substList] at hz
      · rw [not_mem_fv_subst (hP _ (List.mem_singleton.mpr rfl))] at hz
        exact ⟨hz, (hP z · hz)⟩
      · intros; contradiction
    all_goals (intros; contradiction)

theorem subst_subst {v v' e e' t} (h : v ≠ v') (hv : v ∉ fv e') (hv' : v' ∉ fv e) : subst v e (subst v' e' t) = subst v' e' (subst v e t) := by
  induction t with
  | var x =>
    simp_rw [subst]
    split_ifs with h₁ h₂
    · subst x
      nomatch h h₂.symm
    · subst h₁
      rw [subst]
      split_ifs with h₁
      · exact not_mem_fv_subst hv
      · contradiction
    · subst x
      rw [subst]
      split_ifs
      · symm
        exact (not_mem_fv_subst hv')
      · contradiction
    · simp_rw [subst]
      split_ifs
      rfl
  | «ℤ»
  | 𝔹
  | int
  | bool => rfl
  | add
  | sub
  | mul
  | le
  | and
  | not
  | eq
  | mem
  | pow
  | cprod
  | union
  | inter
  | card
  | app
  | pfun
  | min
  | max
  | maplet =>
    simp_rw [subst]
    congr
  | all vs D P D_ih P_ih
  | lambda vs D P D_ih P_ih
  | collect vs D P D_ih P_ih =>
    simp_rw [subst]
    split_ifs <;>
    · unfold subst
      split_ifs
      congr

theorem susbtList_cons_subst_assoc {v vs e es t} (hlen : vs.length = es.length) (h : v ∉ vs) (hfv : ∀ a b, (a ∈ vs ∨ a = v) ∧ (b ∈ es ∨ b = e) → a ∉ fv b) : substList (vs.concat v) (es.concat e) t = substList vs es (subst v e t) := by
  induction vs, es, hlen using List.induction₂ generalizing v e t with
  | nil_nil => simp_rw [List.concat_nil, substList]
  | cons_cons vv vs ee es hlen ih =>
    simp_rw [List.concat_cons, substList, ih (e := e) (List.not_mem_of_not_mem_cons h) (by
      rintro a b ⟨ha, hb⟩
      rcases ha with ha | rfl <;> rcases hb with hb | rfl <;> apply hfv
      · exact ⟨Or.inl <| List.mem_cons_of_mem vv ha, Or.inl <| List.mem_cons_of_mem ee hb⟩
      · exact ⟨Or.inl <| List.mem_cons_of_mem vv ha, Or.inr rfl⟩
      · exact ⟨Or.inr rfl, Or.inl <| List.mem_cons_of_mem ee hb⟩
      · exact ⟨Or.inr rfl, Or.inr rfl⟩
    )]
    congr 1
    rw [subst_subst]
    · exact List.ne_of_not_mem_cons h
    · apply hfv
      exact ⟨Or.inr rfl, Or.inl List.mem_cons_self⟩
    · apply hfv
      exact ⟨Or.inl List.mem_cons_self, Or.inr rfl⟩

theorem substList_cons_concat {v vs e es t}
  (nodup : (v :: vs).Nodup)
  (hlen : vs.length = es.length)
  (hfv : ∀ x ∈ v::vs, ∀ y ∈ e::es, x ∉ fv y) :
  substList (v :: vs) (e :: es) t = substList (vs.concat v) (es.concat e) t := by
  induction vs, es, hlen using List.induction₂ generalizing v e t with
  | nil_nil => rw [substList, List.concat_nil, List.concat_nil, substList]
  | cons_cons v' vs e es hlen ih =>
    rw [substList, ih, List.concat_cons, List.concat_cons, substList]
    rw [susbtList_cons_subst_assoc hlen]
    · rw [susbtList_cons_subst_assoc hlen (by simp_rw [List.nodup_cons, List.mem_cons, not_or] at nodup; exact nodup.1.2)]
      · congr 1
        rw [subst_subst]
        · rintro rfl
          rw [List.nodup_cons, List.mem_cons, not_or] at nodup
          nomatch nodup.1.1
        · apply hfv
          · simp_rw [List.mem_cons]
            right
            left
            trivial
          · exact List.mem_cons_self
        · apply hfv
          · exact List.mem_cons_self
          · simp_rw [List.mem_cons]
            right
            left
            trivial
      · rintro a b ⟨ha, hb⟩
        rcases ha with ha | rfl <;> rcases hb with hb | rfl <;> apply hfv <;> simp_rw [List.mem_cons]
        <;> first
            | right; right; assumption
            | left; trivial
    · simp_rw [List.nodup_cons] at nodup
      exact nodup.2.1
    · rintro a b ⟨ha | rfl, hb | rfl⟩ <;>
      · apply hfv <;>
        · first
          | exact List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ ‹_›
          | exact List.mem_cons_of_mem _ (List.mem_cons_self)
    · exact List.Nodup.of_cons nodup
    · intro x hx y hy
      apply hfv <;> exact List.mem_cons_of_mem _ ‹_›

theorem not_mem_fv_substList_gatherMapletsl' {x : Term} {vs : List 𝒱} {P : Term}
  (hP : ∀ v ∈ vs, v ∉ fv P)
  (hx : ∀ v ∈ vs, ∀ y ∈ gatherMapletsl' x vs.length, v ∉ fv y)
  (hvs : vs.Nodup)
  (h : (gatherMapletsl' x vs.length).length = vs.length)
  ⦃z : 𝒱⦄ (hz : z ∈ B.fv (substList vs (gatherMapletsl' x vs.length) P)) : z ∈ B.fv P ∧ z ∉ vs := by
  induction x generalizing vs with
  | maplet x y x_ih y_ih =>
    induction vs with
    | nil =>
      rw [List.length_nil] at h hz
      rw [List.length_eq_zero_iff] at h
      rw [h] at hz
      unfold substList at hz
      exact ⟨hz, List.not_mem_nil⟩
    | cons v vs vs_ih =>
      rw [List.length_cons] at h hz
      rcases eq_or_ne vs [] with rfl | vs_nemp
      · rw [List.length_nil, gatherMapletsl'] at h hz
        unfold substList substList at hz
        rw [not_mem_fv_subst (hP v (List.mem_singleton.mpr rfl))] at hz
        apply And.intro hz
        rw [List.mem_singleton]
        rintro rfl
        nomatch hP z (List.mem_singleton.mpr rfl) hz
      · rw [gatherMapletsl', List.length_concat, Nat.succ_inj] at h
        · rw [gatherMapletsl'] at hz
          · obtain ⟨v', vs', vs'_def⟩ := List.ne_nil_snoc.mp (List.cons_ne_nil v vs)
            have hlen : vs.length = vs'.length := by
                  suffices (v::vs).length = vs'.length + 1 by
                    rwa [List.length_cons, Nat.succ_inj] at this
                  rw [vs'_def, List.length_concat]
            rw [vs'_def, ←substList_cons_concat] at hz
            · unfold substList at hz
              rw [not_mem_fv_subst] at hz
              · rw [vs'_def, List.concat_eq_append, List.mem_append, List.mem_singleton, not_or, ←and_assoc]
                specialize @x_ih vs'
                  (by
                    intros a ha
                    apply hP
                    rw [vs'_def, List.concat_eq_append, List.mem_append]
                    left
                    exact ha)
                  _ _
                  (by rwa [←hlen])
                  (by rwa [←hlen])
                · intro v'' hv'' y' hy'
                  apply hx v''
                  · rw [vs'_def, List.concat_eq_append, List.mem_append]
                    left
                    exact hv''
                  · obtain ⟨a, as, as_def⟩ := by exact List.ne_nil_iff_exists_cons.mp vs_nemp
                    rw [as_def, List.length_cons, List.length_cons]
                    simp only [gatherMapletsl']
                    rw [List.concat_eq_append, List.mem_append]
                    left
                    convert hy'
                    rw [←hlen, as_def, List.length_cons]
                · rw [vs'_def, List.concat_eq_append, List.nodup_append] at hvs
                  exact hvs.1
                · apply And.intro
                  · exact x_ih
                  · rintro ⟨⟩
                    simp_rw [vs'_def, List.concat_eq_append, List.mem_append, List.mem_singleton] at hP
                    nomatch hP z (Or.inr rfl) x_ih.1
              · apply hP
                rw [vs'_def, List.concat_eq_append]
                exact List.mem_concat_self
            · rw [vs'_def, List.concat_eq_append, List.nodup_append] at hvs
              simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, List.mem_cons, or_false, ne_eq, forall_eq, true_and] at hvs
              rw [List.nodup_cons, and_comm]
              exact ⟨hvs.1, (hvs.2 v' · rfl)⟩
            · symm
              rwa [←hlen]
            · obtain ⟨a, as, as_def⟩ := by exact List.ne_nil_iff_exists_cons.mp vs_nemp
              intro w hw u hu
              rw [List.mem_cons] at hw hu
              apply hx w
              · rcases hw with hw | hw <;> simp [vs'_def, hw]
              · rw [as_def, List.length_cons, List.length_cons]
                rcases hu with rfl | hu
                · simp only [gatherMapletsl']
                  rw [List.concat_eq_append, List.mem_append]
                  right
                  exact List.mem_singleton.mpr rfl
                · simp only [gatherMapletsl']
                  rw [List.concat_eq_append, List.mem_append]
                  left
                  convert hu
                  rw [as_def, List.length_cons]
          · intro contr
            rw [List.length_eq_zero_iff] at contr
            nomatch vs_nemp contr
        · intro contr
          rw [List.length_eq_zero_iff] at contr
          nomatch vs_nemp contr
  | _ =>
    induction vs with
    | nil => exact ⟨hz, List.not_mem_nil⟩
    | cons v vs vs_ih =>
      cases vs with
      | nil =>
        rw [List.length_singleton] at hz
        unfold gatherMapletsl' substList substList at hz
        rw [not_mem_fv_subst (List.singleton_disjoint.mp hP)] at hz
        rw [List.mem_singleton]
        exact ⟨hz, List.ne_of_not_mem_cons (hP z · hz)⟩
      | cons v' vs =>
      simp_rw [List.length_cons] at hz
      simp only [gatherMapletsl', substList] at hz
      rw [not_mem_fv_subst (hP _ List.mem_cons_self)] at hz
      and_intros
      · exact hz
      · simp_rw [List.mem_cons, not_or]
        and_intros
        · exact List.ne_of_not_mem_cons (hP z · hz)
        · rintro rfl
          nomatch hP z (List.mem_cons.mpr (Or.inr List.mem_cons_self)) hz
        · intro contr
          nomatch hP z (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr contr)))) hz

theorem simplifier_aux_mem.fv {x y : Term} (hx : x.WF) (hy : y.WF) :
  fv (simplifier_aux_mem x y) ⊆ fv x ++ fv y := by
  unfold simplifier_aux_mem
  split <;> simp [B.fv] <;> split_ifs
  · intro z hz
    simp_rw [B.fv, List.mem_append, List.mem_removeAll_iff] at hz ⊢
    rcases hz with ⟨hz | hz⟩ | hz
    · left
      exact hz
    · right
      left
      exact hz
    · right
      right
      rcases ‹_ ∧ _› with ⟨len_eq, hP⟩
      rename _=1 => hlen
      obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hlen
      dsimp [List.head!] at *
      and_intros
      · rwa [not_mem_fv_subst (hP _ (List.mem_singleton.mpr rfl))] at hz
      · simp_rw [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hP ⊢
        rintro rfl
        rename _ = [] => no_common_fv
        rw [not_mem_fv_subst hP] at hz
        contradiction
  · intro z hz
    simp_rw [B.fv, List.mem_append, List.mem_removeAll_iff] at hz ⊢
    rcases hz with ⟨hz | hz⟩ | hz
    · left
      exact hz
    · right
      left
      exact hz
    · right
      right
      rename ¬_ => h
      obtain ⟨hlen, hP⟩ := ‹_∧_›
      exact not_mem_fv_substList_gatherMapletsl hP hlen hz
  · intro z hz
    simp_rw [B.fv, List.mem_append, List.mem_removeAll_iff] at hz ⊢
    rcases hz with hz | hz | hz
    · left
      exact hz
    · right
      left
      exact hz
    · right
      right
      exact hz
  · exact fun _ => id
  · intro z hz
    simp_rw [B.fv, List.mem_append, List.mem_removeAll_iff] at hz ⊢
    rcases hz with hz | hz
    · obtain ⟨hlen, hP, hgather⟩ := ‹_∧_›
      right
      right
      right
      unfold Term.WF at hx hy
      exact not_mem_fv_substList_gatherMapletsl' hP hgather hy.2.2.1 hlen hz
    · right
      left
      exact hz
  · intro z hz
    simp_rw [B.fv, List.mem_append, List.mem_removeAll_iff] at hz ⊢
    rcases hz with ⟨⟨hz | hz⟩ | hz⟩ | hz
    · right
      right
      left
      exact hz
    · right
      right
      right
      exact hz
    · left
      exact hz
    · right
      left
      exact hz

theorem fv_foldl_maplet {vs : List 𝒱} {t : Term} :
  B.fv (List.foldl (fun acc v' => acc ↦ᴮ Term.var v') t vs) = (fv t) ++ vs := by
  induction vs generalizing t with
  | nil => rw [List.foldl_nil, List.append_nil]
  | cons v' vs ih => rw [List.foldl_cons, ih, B.fv, B.fv, ←List.append_cons]

theorem WF_foldl_maplet {vs : List 𝒱} {t : Term} (ht : t.WF) : (List.foldl (fun acc v' => acc ↦ᴮ Term.var v') t vs).WF := by
  induction vs generalizing t with
  | nil => rwa [List.foldl_nil]
  | cons v vs ih =>
    rw [List.foldl_cons]
    apply ih
    rw [Term.WF, Term.WF]
    exact ⟨ht, trivial⟩

theorem simplifier_aux_all.fv {vs : List 𝒱} {D P : Term} :
  fv (simplifier_aux_all vs D P) ⊆ fv D ++ (fv P).removeAll vs := by
  unfold simplifier_aux_all
  split <;> simp [B.fv]
  intro z hz
  simp_rw [List.mem_append]
  simp_rw [List.mem_removeAll_iff, List.mem_cons] at hz ⊢
  split_ifs at hz with hvs hP
  · subst hP
    rw [B.fv] at hz
    nomatch List.not_mem_nil hz
  · rw [B.fv, List.mem_append] at hz
    rcases hz with hz | hz
    · left
      exact hz
    · unfold B.fv at hz
      simp_rw [B.fv, List.mem_removeAll_iff, List.mem_append, List.mem_removeAll_iff] at hz
      rcases hz with ⟨⟨hz | hz | hz⟩ | hz, z_vs⟩
      · rw [fv_foldl_maplet, B.fv, List.mem_append, List.mem_singleton, ←List.mem_cons] at hz
        nomatch z_vs hz
      · left
        exact hz
      · right
        left
        exact hz
      · right
        right
        rw [List.mem_cons] at z_vs
        exact ⟨hz, z_vs⟩
  · simp_rw [not_and_or, List.nodup_cons, List.nodup_append, not_and_or, not_not] at hvs
    simp_rw [B.fv, List.mem_append, List.mem_removeAll_iff] at hz
    rcases hz with ⟨hD | ⟨hP, zxs⟩⟩ | ⟨hP, zvs⟩
    · left
      exact hD
    · right
      left
      exact ⟨hP, zxs⟩
    · right
      right
      rw [List.mem_cons] at zvs
      exact ⟨hP, zvs⟩

theorem not_mem_fv_simplifier {t : Term} {v : 𝒱} (ht : v ∉ fv t) : v ∉ fv (simplifier t) := by
  induction t with
  | «ℤ»
  | 𝔹
  | var
  | int
  | bool => exact ht
  | le x y x_ih y_ih
  | sub x y x_ih y_ih
  | maplet x y x_ih y_ih =>
    unfold simplifier
    rw [fv, List.mem_append] at ht ⊢
    push_neg at ht ⊢
    exact ⟨x_ih ht.1, y_ih ht.2⟩
  | add x y x_ih y_ih =>
    rw [fv, List.mem_append, not_or] at ht
    unfold simplifier simplifier_aux_add
    split
    · exact y_ih ht.2
    · exact x_ih ht.1
    · exact fv.mem_int
    · rw [fv, List.mem_append, not_or]
      rw [‹simplifier x = _›, fv, List.mem_append, not_or] at x_ih
      exact ⟨x_ih ht.1 |>.1, fv.mem_int⟩
    · rw [fv, List.mem_append, not_or]
      exact And.imp x_ih y_ih ht
  | mul x y x_ih y_ih =>
    unfold simplifier simplifier_aux_mul
    rw [fv, List.mem_append, not_or] at ht
    split <;> try first | exact trivial | exact x_ih ht.1 | exact y_ih ht.2 | exact fv.mem_int
    · rw [fv, List.mem_append, not_or]
      rw [‹simplifier x = _›, fv, List.mem_append, not_or] at x_ih
      exact ⟨x_ih ht.1 |>.1, fv.mem_int⟩
    · rw [fv, List.mem_append, not_or]
      exact And.imp x_ih y_ih ht
  | and x y x_ih y_ih =>
    unfold simplifier simplifier_aux_and
    rw [fv, List.mem_append, not_or] at ht
    split <;> try first | exact trivial | exact x_ih ht.1 | exact y_ih ht.2 | exact fv.mem_bool
    rw [fv, List.mem_append, not_or]
    exact And.imp x_ih y_ih ht
  | not x ih =>
    unfold simplifier simplifier_aux_not
    rw [fv] at ht
    split
    · exact fv.mem_bool
    · exact fv.mem_bool
    · rw [‹simplifier x = _›] at ih
      exact ih ht
    · exact ih ht
  | eq x y x_ih y_ih =>
    unfold simplifier simplifier_aux_eq
    rw [fv, List.mem_append, not_or] at ht
    split <;> try first | exact trivial | exact x_ih ht.1 | exact y_ih ht.2
    · split_ifs
      · exact fv.mem_bool
      · simp_rw [fv, List.mem_append, not_or]
        rw [‹simplifier x = _›, fv] at x_ih
        rw [‹simplifier y = _›, fv] at y_ih
        exact And.imp x_ih y_ih ht
    · simp_rw [fv, List.mem_append, not_or]
      rw [‹simplifier y = _›, fv] at y_ih
      symm
      exact And.imp x_ih y_ih ht
    · split_ifs
      · exact fv.mem_bool
      · rw [fv, List.mem_append, not_or]
        exact And.imp x_ih y_ih ht
  | mem x S x_ih S_ih =>
    unfold simplifier simplifier_aux_mem
    rw [fv, List.mem_append, not_or] at ht
    split
    · specialize S_ih ht.2
      rw [‹simplifier S = _›, fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not] at S_ih
      extract_lets xs
      split_ifs with fv_inter vs_len
      · obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp ‹_ = 1›
        simp_rw [fv, List.mem_append, not_or]
        and_intros
        · exact x_ih ht.1
        · exact S_ih.1
        · rw [List.head!, not_mem_fv_subst]
          rw [List.mem_singleton] at S_ih
          · rcases S_ih.2 with _ | rfl
            · assumption
            · exact vs_len.2 v (List.mem_singleton.mpr rfl)
          · exact vs_len.2 v (List.mem_singleton.mpr rfl)
      · simp_rw [fv, List.mem_append, not_or]
        and_intros
        · exact x_ih ht.1
        · exact S_ih.1
        · rw [not_mem_fv_substList]
          · rcases S_ih.2
            · assumption
            · apply vs_len.2
              assumption
          · exact vs_len.2
      repeat
        · simp_rw [fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not]
          exact ⟨x_ih ht.1, S_ih⟩
    · extract_lets xs
      specialize S_ih ht.2
      rw [‹simplifier S = _›, fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not] at S_ih
      specialize x_ih ht.1
      rw [‹simplifier x = _›, fv, List.mem_append, not_or] at x_ih
      split_ifs with h
      · rw [fv, List.mem_append, not_or, not_mem_fv_substList]
        · rcases S_ih.2
          · and_intros
            · assumption
            · exact x_ih.2
          · and_intros
            · apply h.2.1
              assumption
            · exact x_ih.2
        · exact h.2.1
      · simp_rw [fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not]
        exact ⟨⟨⟨S_ih.1, S_ih.2⟩, x_ih.1⟩, x_ih.2⟩
    · rw [fv, List.mem_append, not_or]
      exact ⟨x_ih ht.1, S_ih ht.2⟩
  | min x ih
  | max x ih
  | card x ih
  | pow x ih =>
    unfold simplifier
    rw [fv] at ht ⊢
    exact ih ht
  | pfun x y x_ih y_ih
  | app x y x_ih y_ih
  | inter x y x_ih y_ih
  | union x y x_ih y_ih
  | cprod x y x_ih y_ih =>
    unfold simplifier
    rw [fv, List.mem_append, not_or] at ht ⊢
    exact And.imp x_ih y_ih ht
  | collect vs D P D_ih P_ih =>
    unfold simplifier simplifier_aux_collect
    rw [fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not] at ht
    split
    · exact D_ih ht.1
    · simp_rw [fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not]
      and_intros
      · exact D_ih ht.1
      · rcases ht.2
        · left
          apply P_ih
          assumption
        · right
          assumption
  | lambda vs D P D_ih P_ih =>
    unfold simplifier
    rw [fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not] at ht ⊢
    and_intros
    · exact D_ih ht.1
    · rcases ht.2
      · left
        apply P_ih
        assumption
      · right
        assumption
  | all vs D P D_ih P_ih =>
    rw [fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not] at ht
    obtain ⟨hD, hv⟩ := ht
    unfold simplifier simplifier_aux_all
    split
    · specialize D_ih hD
      rw [‹simplifier D = _›, fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not] at D_ih
      obtain ⟨hD', hv'⟩ := D_ih
      split_ifs with h_if₁ h_if₂
      · exact fv.mem_bool
      · simp only [fv, fv_foldl_maplet, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not, List.mem_singleton]
        and_intros
        · exact hD'
        · rw [or_iff_not_imp_right]
          intro v_mem_vs
          replace hv := Or.resolve_right hv v_mem_vs
          specialize P_ih hv
          rw [←not_or, ←List.mem_cons]
          and_intros
          · exact v_mem_vs
          · exact hD'
          · exact hv'
          · exact P_ih
      · simp_rw [fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not]
        exact ⟨⟨hD', hv'⟩, Or.imp_left P_ih hv⟩
    · simp_rw [fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not]
      exact ⟨D_ih hD, Or.imp_left P_ih hv⟩

theorem subst_self {t : Term} {v : 𝒱} : t[v := Term.var v] = t := by
  induction t with
  | var v =>
    rw [subst]
    split_ifs <;> (subst_vars; rfl)
  | int
  | bool
  | «ℤ»
  | 𝔹 => rw [subst]
  | maplet x y x_ih y_ih
  | add x y x_ih y_ih
  | sub x y x_ih y_ih
  | mul x y x_ih y_ih
  | le x y x_ih y_ih
  | and x y x_ih y_ih
  | eq x y x_ih y_ih
  | mem x y x_ih y_ih
  | cprod x y x_ih y_ih
  | union x y x_ih y_ih
  | inter x y x_ih y_ih
  | app x y x_ih y_ih
  | pfun x y x_ih y_ih =>
    rw [subst, x_ih, y_ih]
  | pow S ih
  | card S ih
  | min S ih
  | max S ih
  | not x ih =>
    rw [subst, ih]
  | collect vs D P D_ih P_ih
  | all vs D P D_ih P_ih
  | lambda vs D P D_ih P_ih =>
    rw [subst, D_ih, P_ih, ite_self]

theorem substList_self {t : Term} {vs : List 𝒱} : t[vs := vs.map .var] = t := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [List.map_cons, substList, subst_self, ih]

theorem WF_of_simplifier {t : Term} (ht : t.WF) : (simplifier t).WF := by
  stop
  induction t with
  | «ℤ» | 𝔹 | var | int | bool => exact ht
  | maplet x y x_ih y_ih =>
    unfold simplifier
    unfold Term.WF at ht ⊢
    exact ⟨x_ih ht.1, y_ih ht.2⟩
  | add x y x_ih y_ih =>
    unfold simplifier simplifier_aux_add
    rw [Term.WF] at ht
    split <;> try (first | exact x_ih ht.1 | exact y_ih ht.2)
    · rename simplifier x = _ => x_eq
      rw [x_eq] at x_ih
      rw [Term.WF]
      exact trivial
    · rw [‹simplifier x = _›] at x_ih
      specialize x_ih ht.1
      simp only [Term.WF] at x_ih y_ih ⊢
      exact x_ih
  | cprod x y x_ih y_ih
  | union x y x_ih y_ih
  | inter x y x_ih y_ih
  | le x y x_ih y_ih
  | sub x y x_ih y_ih =>
    unfold simplifier
    unfold Term.WF at ht ⊢
    exact ⟨x_ih ht.1, y_ih ht.2⟩
  | mem x S x_ih S_ih =>
    unfold simplifier simplifier_aux_mem
    rw [Term.WF] at ht
    split <;> try rw [‹simplifier S = _›] at S_ih
    · split_ifs with h h'
      specialize S_ih ht.2
      unfold Term.WF at S_ih
      extract_lets xs
      split_ifs with h''
      · simp_rw [Term.WF]
        and_intros
        · exact x_ih ht.1
        · exact S_ih.1
        · obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp h'
          rw [List.head!, not_mem_fv_subst <| h''.2 v (List.mem_singleton.mpr rfl)]
          have := S_ih.2.1 [.var v]
          exact this
      · simp_rw [Term.WF]
        exact ⟨x_ih ht.1, S_ih⟩
      · extract_lets xs
        split_ifs with h''
        · simp_rw [Term.WF]
          and_intros
          · exact x_ih ht.1
          · exact S_ih ht.2 |>.1
          · rw [not_mem_fv_substList h''.2]
            exact S_ih ht.2 |>.2.1
        · simp_rw [Term.WF]
          exact ⟨x_ih ht.1, S_ih ht.2⟩
      · simp_rw [Term.WF]
        exact ⟨x_ih ht.1, S_ih ht.2⟩
    · extract_lets xs
      split_ifs with h
      · rw [not_mem_fv_substList h.2.1]
        exact ⟨S_ih ht.2 |>.2.1, ‹simplifier x = _› ▸ x_ih ht.1 |>.2⟩
      · simp_rw [Term.WF] at S_ih ⊢
        rw [‹simplifier x = _›] at x_ih
        exact ⟨⟨S_ih ht.2, x_ih ht.1 |>.1⟩, x_ih ht.1 |>.2⟩
    · exact ⟨x_ih ht.1, S_ih ht.2⟩
  | eq x y x_ih y_ih =>
    unfold simplifier simplifier_aux_eq
    split <;> try first | exact trivial | exact x_ih ht.1 | exact y_ih ht.2
    · split_ifs <;> trivial
    · exact ⟨trivial, x_ih ht.1⟩
    · split_ifs
      · trivial
      · exact ⟨x_ih ht.1, y_ih ht.2⟩
  | and x y x_ih y_ih =>
    unfold simplifier simplifier_aux_and
    split <;> try first | exact trivial | exact x_ih ht.1 | exact y_ih ht.2
    exact ⟨x_ih ht.1, y_ih ht.2⟩
  | mul x y x_ih y_ih =>
    unfold simplifier simplifier_aux_mul
    split <;> try first | exact trivial | exact x_ih ht.1 | exact y_ih ht.2
    · and_intros
      · rw [‹simplifier x = _›] at x_ih
        exact x_ih ht.1 |>.1
      · trivial
    · exact ⟨x_ih ht.1, y_ih ht.2⟩
  | pfun x y x_ih y_ih
  | app x y x_ih y_ih => exact ⟨x_ih ht.1, y_ih ht.2⟩
  | not x ih =>
    specialize ih ht
    unfold simplifier simplifier_aux_not
    split <;> try first | exact trivial | exact ih
    · rename _ = _ => eq
      rw [eq] at ih
      exact ih
  | min x ih
  | max x ih
  | card x ih
  | pow x ih =>
    unfold simplifier
    unfold Term.WF at ht ⊢
    exact ih ht
  | lambda vs D P D_ih P_ih =>
    unfold simplifier
    and_intros
    · exact D_ih ht.1
    · exact P_ih ht.2.1
    · exact ht.2.2.1
    · exact (not_mem_fv_simplifier <| ht.2.2.2 · ·)
  | collect vs D P D_ih P_ih =>
    unfold simplifier simplifier_aux_collect
    split using xs _ _ _ _ | xs _ _ _ _
    · exact D_ih ht.1
    · unfold Term.WF at ht
      exact ⟨D_ih ht.1, P_ih ht.2.1, ht.2.2.1, (not_mem_fv_simplifier <| ht.2.2.2 · ·)⟩
  | all vs D P D_ih P_ih =>
    unfold simplifier simplifier_aux_all
    split using _ _ _ v vs xs D' P' D_eq | xs _ _ _ _
    · specialize D_ih ht.1
      rw [D_eq] at D_ih
      obtain ⟨_, _, _, _⟩ := D_ih
      obtain ⟨_, _, _, _⟩ := ht
      split_ifs with h_if₁ h_if₂
      · trivial
      · obtain ⟨_, _, _⟩ := h_if₁
        and_intros <;> try assumption
        · exact WF_foldl_maplet trivial
        · apply P_ih
          assumption
        · exact (‹∀ x ∈ _, x ∉ fv D'› · <| List.mem_append_left xs ·)
      · and_intros <;> try assumption
        · apply P_ih
          assumption
        · simp_rw [not_and_or, not_forall, not_not] at h_if₁
          intro x hx
          rw [List.mem_cons] at hx
          simp_rw [fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not]
          rcases h_if₁ with dup | ⟨z, z_vs, hz⟩ | ⟨z, z_vs, hz⟩ <;>
          · rcases hx with rfl | hx
            · have := not_mem_fv_simplifier <| ‹∀ v ∈ _::vs, v ∉ fv D› _ List.mem_cons_self
              rwa [D_eq, fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not] at this
            · have := not_mem_fv_simplifier <| ‹∀ v ∈ _::vs, v ∉ fv D› x (List.mem_cons_of_mem v hx)
              rwa [D_eq, fv, List.mem_append, List.mem_removeAll_iff, not_or, not_and_or, not_not] at this
    · exact ⟨D_ih ht.1, P_ih ht.2.1, ht.2.2.1, (not_mem_fv_simplifier <| ht.2.2.2 · ·)⟩

theorem fv_simplifier {t : Term} (ht : t.WF) : fv (simplifier t) ⊆ fv t := by
  stop
  intro v hv
  induction t with
  | «ℤ»
  | 𝔹
  | var
  | int
  | bool => exact hv
  | maplet x y x_ih y_ih
  | sub x y x_ih y_ih
  | le x y x_ih y_ih
  | cprod x y x_ih y_ih
  | union x y x_ih y_ih
  | inter x y x_ih y_ih
  | app x y x_ih y_ih
  | pfun x y x_ih y_ih  =>
    rw [simplifier] at hv
    rw [fv, List.mem_append] at hv ⊢
    rcases hv with hv | hv
    · left
      exact x_ih ht.1 hv
    · right
      exact y_ih ht.2 hv
  | eq x y x_ih y_ih
  | and x y x_ih y_ih
  | mul x y x_ih y_ih
  | add x y x_ih y_ih =>
    rw [simplifier] at hv
    first
    | apply simplifier_aux_add.fv at hv
    | apply simplifier_aux_mul.fv at hv
    | apply simplifier_aux_and.fv at hv
    | apply simplifier_aux_eq.fv at hv
    rw [List.mem_append] at hv
    rw [fv, List.mem_append]
    rcases hv with hv | hv
    · left
      exact x_ih ht.1 hv
    · right
      exact y_ih ht.2 hv
  | mem x y x_ih y_ih =>
    rw [simplifier] at hv
    rw [Term.WF] at ht
    rw [fv, List.mem_append]
    rcases List.mem_append.mp (List.subset_def.eq ▸ simplifier_aux_mem.fv (WF_of_simplifier ht.1) (WF_of_simplifier ht.2) <| hv) with hv | hv
    · left
      exact x_ih ht.1 hv
    · right
      exact y_ih ht.2 hv
  | not x ih =>
    rw [simplifier] at hv
    apply simplifier_aux_not.fv at hv
    exact ih ht hv
  | collect vs D P D_ih P_ih =>
    rw [simplifier] at hv
    rw [B.fv, List.mem_append]
    unfold simplifier_aux_collect at hv
    split at hv
    · left
      exact D_ih ht.1 hv
    · rw [B.fv, List.mem_append] at hv
      rw [List.mem_removeAll_iff] at hv ⊢
      rcases hv with hv | hv
      · left
        exact D_ih ht.1 hv
      · right
        exact ⟨P_ih ht.2.1 hv.1, hv.2⟩
  | pow S ih | card S ih | min S ih | max S ih =>
    rw [simplifier, fv] at hv
    exact ih ht hv
  | lambda vs D P D_ih P_ih =>
    rw [simplifier] at hv
    rw [fv, List.mem_append] at hv ⊢
    rcases hv with hv | hv
    · left
      exact D_ih ht.1 hv
    · right
      rw [List.mem_removeAll_iff] at hv ⊢
      exact ⟨P_ih ht.2.1 hv.1, hv.2⟩
  | all vs D P D_ih P_ih =>
    rw [simplifier] at hv
    rw [B.fv]
    apply simplifier_aux_all.fv at hv
    rw [List.mem_append, List.mem_removeAll_iff] at hv ⊢
    rcases hv with hv | hv
    · left
      exact D_ih ht.1 hv
    · right
      exact ⟨P_ih ht.2.1 hv.1, hv.2⟩

theorem Typing.reduce_subst_eq_subst_reduce {x : 𝒱} (e : Term) (vs : List 𝒱) (Ds : List Term) (vs_nemp : vs ≠ [])
  (vs_Ds_len : vs.length = Ds.length) :
  (List.reduce (fun x1 x2 => x1 ⨯ᴮ x2) Ds (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff]))[x := e] =
    List.reduce (fun x1 x2 => x1 ⨯ᴮ x2) (List.map (fun Dᵢ => Dᵢ[x := e]) Ds) (by rwa [←List.length_pos_iff, List.length_map, ←vs_Ds_len, List.length_pos_iff]) := by
  obtain ⟨v₀, vs, rfl⟩ := List.ne_nil_iff_exists_cons.mp vs_nemp
  obtain ⟨D₀, Ds, rfl⟩ := List.ne_nil_iff_exists_cons.mp (by rwa [←List.length_pos_iff, ←vs_Ds_len, List.length_pos_iff])
  simp_rw [List.length_cons, Nat.succ_inj] at vs_Ds_len
  induction Ds generalizing D₀ v₀ vs with
  | nil =>
    simp_rw [List.reduce, List.head_cons, List.tail_cons, List.foldl_nil, List.map_cons, List.map_nil]
    rfl
  | cons D₁ Ds ih =>
    simp only [List.length_cons] at vs_Ds_len
    obtain ⟨v₁, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one vs_Ds_len
    simp_rw [List.reduce, List.head_cons, List.tail_cons, List.foldl_cons, List.map_cons,
      List.head_cons, List.tail_cons, List.foldl_cons]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, Nat.add_right_cancel_iff,
      List.reduce, List.head_cons, List.tail_cons, List.map_cons, forall_self_imp,
      forall_const] at ih
    exact ih vs (D₀ ⨯ᴮ D₁) (Nat.succ_inj.mp vs_Ds_len)

end Theorems

end B
