import Encoder.Basic
import Mathlib.Order.CompleteLatticeIntervals
open SMT

inductive castPath : SMTType → SMTType → Sort _ where
  -- push refl to leaves, otherwise it is not unique
  | refl {α} (hα : α = .int ∨ α = .bool ∨ α = .unit) : castPath α α
  | graph {α β α' β'} (pα : castPath α α') (pβ : castPath β β') :
    castPath (α.fun (β.option)) ((α'.pair β').fun .bool)
  | chpred {α α'} (p : castPath α α') :
    castPath (α.fun .bool) (α'.fun .bool)
  | «fun» {α β α' β'} (hβ : β ≠ .bool) (pα : castPath α α') (pβ : castPath β β') :
    castPath (α.fun β) (α'.fun β')
  | pair {α β α' β'} (pα : castPath α α') (pβ : castPath β β') :
    castPath (.pair α β) (.pair α' β')
  | opt {α α'} (hα : castPath α α') :
    castPath (α.option) (α'.option)
infix:70 " ~> " => castPath
infix:70 " ⇝ " => castPath

inductive castable? : SMTType → SMTType → Prop
  | refl {α} (hα : α = .int ∨ α = .bool ∨ α = .unit) : castable? α α
  | graph {α β α' β'} (hα : castable? α α') (hβ : castable? β β') :
    castable? (α.fun (β.option)) ((α'.pair β').fun .bool)
  | «fun» {α β α' β'} (β_ne : β ≠ .bool) (hα : castable? α α') (hβ : castable? β β') :
    castable? (α.fun β) (α'.fun β')
  | pair {α β α' β'} (hα : castable? α α') (hβ : castable? β β') :
    castable? (.pair α β) (.pair α' β')
  | opt {α α'} (hα : castable? α α') :
    castable? (α.option) (α'.option)
  | chpred {α α'} (hα : castable? α α') :
    castable? (α.fun .bool) (α'.fun .bool)
infix:70 " ⊑ " => castable?

theorem castable?.reflexive {α : SMTType} : α ⊑ α := by
  induction α with
  | bool | int | unit => exact .refl (by trivial)
  | «fun» α β α_ih β_ih =>
    cases β with
    | bool => exact castable?.chpred α_ih
    | int | unit | «fun» | option | pair => exact castable?.fun nofun α_ih β_ih
  | option τ ih => exact castable?.opt ih
  | pair α β α_ih β_ih => exact castable?.pair α_ih β_ih

instance : IsRefl SMTType (· ⊑ ·) where
  refl _ := castable?.reflexive

def castPath.reflexive : (α : SMTType) → α ~> α
  | .bool | .int | .unit => castPath.refl (by trivial)
  | .fun α .bool => castPath.chpred (castPath.reflexive α)
  | .fun α .int => castPath.«fun» nofun (castPath.reflexive α) (castPath.refl (by trivial))
  | .fun α .unit => castPath.«fun» nofun (castPath.reflexive α) (castPath.refl (by trivial))
  | .fun α (.pair β δ) => castPath.«fun» nofun (castPath.reflexive α) (castPath.reflexive (β.pair δ))
  | .fun α (.option β) => castPath.«fun» nofun (castPath.reflexive α) (castPath.reflexive β.option)
  | .fun α (.fun β δ) => castPath.«fun» nofun (castPath.reflexive α) (castPath.reflexive (β.fun δ))
  | .option α => castPath.opt (castPath.reflexive α)
  | .pair α β => castPath.pair (castPath.reflexive α) (castPath.reflexive β)

instance {α} : Inhabited (α ~> α) where
  default := castPath.reflexive α

theorem castable?.optE {α β : SMTType} (h : α.option ⊑ β.option) : α ⊑ β := by
  cases h with
  | opt hα => exact hα
  | refl hα => exact reflexive

theorem castable?.pairE {α₁ α₂ β₁ β₂ : SMTType} (h : (.pair α₁ α₂) ⊑ (.pair β₁ β₂)) : α₁ ⊑ β₁ ∧ α₂ ⊑ β₂ := by
  cases h with
  | pair hα hβ => exact ⟨hα, hβ⟩
  | refl hα => exact ⟨reflexive, reflexive⟩

theorem castable?.false_of_pair_self_left {α β} : ¬α.pair β ⊑ α := by
  intro contra
  induction α generalizing β with
  | pair α₁ α₂ α₁_ih α₂_ih =>
    cases contra with
    | pair hα hβ => nomatch α₁_ih hα
  | _ => nomatch contra

theorem castable?.false_of_self_pair_left {α β} : ¬α ⊑ α.pair β := by
  intro contra
  induction α generalizing β with
  | pair α₁ α₂ α₁_ih α₂_ih =>
    cases contra with
    | pair hα hβ => nomatch α₁_ih hα
  | _ => nomatch contra

theorem castable?.false_of_pair_castable_left {α β γ} (h : α ⊑ β) (hα : α ⊑ β.pair γ) : False := by
  induction h generalizing γ with
  | refl => nomatch castable?.false_of_self_pair_left hα
  | pair hα hβ hα_ih hβ_ih =>
    cases hα with
    | pair hα hβ => nomatch hα_ih hα
    | refl => nomatch castable?.false_of_pair_self_left hα
  | _ => nomatch hα

instance {α β} : Decidable (α ⊑ β) :=
  let rec go (α β : SMTType) : Decidable (castable? α β) :=
    match α, β with
    | .bool, .bool => isTrue <| castable?.reflexive
    | .bool, .int | .bool, .unit | .bool, .fun .. | .bool, .pair .. | .bool, .option .. => isFalse nofun
    | .int, .int => isTrue <| castable?.reflexive
    | .int, .bool | .int, .unit | .int, .fun .. | .int, .pair .. | .int, .option .. => isFalse nofun
    | .unit, .unit => isTrue <| castable?.reflexive
    | .unit, .bool | .unit, .int | .unit, .fun .. | .unit, .pair .. | .unit, .option .. => isFalse nofun
    | .fun α₁ β₁, .fun α₂ β₂ =>
      match β₁, α₂ with
      | .option β₁, .pair α₂ α₃ =>
        match go α₁ α₂, go β₁ α₃ with
        | isFalse h, isFalse h' =>
          match β₂ with
          | .bool =>
            match go (α₁.pair β₁) (α₂.pair α₃) with
            | isFalse hα₁ =>
              isFalse fun contra ↦ by
                cases contra with
                | graph => contradiction
                | «fun» _ _ hβ => nomatch hβ
            | isTrue hα₁ =>
              isFalse fun contra ↦ by
                cases hα₁ with
                | pair ch _ => exact h ch
                | refl =>
                  cases contra with
                  | graph hα hβ => contradiction
                  | «fun» β_ne hα hβ => nomatch castable?.false_of_self_pair_left hα
          | .option β₂ =>
            match go α₁ (α₂.pair α₃), go β₁ β₂ with
            | isFalse hα₁, _ =>
              isFalse fun contra ↦ by
                cases contra with
                | «fun» _ contra _ => exact hα₁ contra
                | refl => exact hα₁ castable?.reflexive
            | isTrue hα₁, isFalse hβ₁ =>
              isFalse fun contra ↦ by
                cases contra with
                | «fun» _ _ contra =>
                  cases contra with
                  | opt hα => contradiction
                  | refl => nomatch hβ₁ castable?.reflexive
                | refl => exact hβ₁ castable?.reflexive
            | isTrue hα₁, isTrue hβ₁ =>
              isTrue (castable?.fun nofun hα₁ (castable?.opt hβ₁))
          | .int | .unit | .fun .. | .pair .. => isFalse fun | castable?.fun _ _ hβ => nomatch hβ
        | isFalse h, isTrue h' =>
          match β₂ with
          | .bool =>
            isFalse fun contra ↦ by
              cases contra with
              | graph hα hβ => contradiction
              | «fun» _ hα hβ => nomatch hβ
          | .unit
          | .int
          | .pair ..
          | .fun .. =>
            isFalse fun contra ↦ by
              cases contra with
              | «fun» _ hα hβ => nomatch hβ
          | .option β₂ =>
            match go β₁ β₂ with
            | isFalse hβ₁ =>
              isFalse fun contra ↦ by
                cases contra with
                | «fun» _ hα hβ =>
                  cases hβ
                  · exact hβ₁ castable?.reflexive
                  · contradiction
                | refl => exact hβ₁ castable?.reflexive
            | isTrue hβ₁ =>
              match go α₁ (α₂.pair α₃) with
              | isTrue hα₁ =>
                isTrue (castable?.fun nofun hα₁ (castable?.opt hβ₁))
              | isFalse hα₁ =>
                isFalse fun contra ↦ by
                  cases contra with
                  | «fun» _ hα hβ => exact hα₁ hα
                  | refl => exact hα₁ castable?.reflexive
        | isTrue h, isFalse h' =>
          isFalse fun contra ↦ by
            cases contra with
            | graph hα hβ => nomatch h' hβ
            | «fun» _ hα hβ => nomatch castable?.false_of_pair_castable_left h hα
            | refl => nomatch castable?.false_of_pair_self_left h
        | isTrue h, isTrue h' =>
          match β₂ with
          | .int | .unit | .fun .. | .pair .. =>
            isFalse fun | castable?.fun _ _ hβ => nomatch hβ
          | .option β₂ =>
            match go α₁ (α₂.pair α₃) with
              | isTrue hα₁ =>
                match go β₁ β₂ with
                | isTrue hβ₁ => isTrue (castable?.fun nofun hα₁ (castable?.opt hβ₁))
                | isFalse hβ₁ =>
                  isFalse fun contra ↦ by
                    cases contra with
                    | «fun» _ hα hβ =>
                      cases hβ with
                      | opt hα => exact hβ₁ hα
                      | refl => exact hβ₁ castable?.reflexive
                    | refl => exact hβ₁ castable?.reflexive
              | isFalse hα₁ =>
                isFalse fun contra ↦ by
                  cases contra with
                  | «fun» _ hα hβ => exact hα₁ hα
                  | refl => exact hα₁ castable?.reflexive
          | .bool => isTrue (castable?.graph h h')
      | .option β₁, .int =>
        match α₁ with
        | .bool | .unit | .pair .. | .fun .. | .option .. =>
          isFalse fun | castable?.fun _ hα hβ => nomatch hα
        | .int =>
          match go β₁.option β₂ with
          | isFalse hβ =>
            isFalse fun contra ↦ by
              cases contra with
              | «fun» _ hα hβ =>
                cases hβ with
                | opt hβ' => exact hβ (castable?.opt hβ')
                | refl => exact hβ castable?.reflexive
              | refl => exact hβ castable?.reflexive
          | isTrue hβ => isTrue (castable?.fun nofun (castable?.reflexive) hβ)
      | .option β₁, .unit =>
        match α₁ with
        | .bool | .int | .pair .. | .fun .. | .option .. =>
          isFalse fun | castable?.fun _ hα hβ => nomatch hα
        | .unit =>
          match go β₁.option β₂ with
          | isFalse hβ =>
            isFalse fun contra ↦ by
              cases contra with
              | «fun» _ hα hβ =>
                cases hβ with
                | opt hβ' => exact hβ (castable?.opt hβ')
                | refl => exact hβ castable?.reflexive
              | refl => exact hβ castable?.reflexive
          | isTrue hβ => isTrue (castable?.fun nofun (castable?.reflexive) hβ)
      | .option β₁, .bool =>
        match α₁ with
        | .int | .unit | .pair .. | .fun .. | .option .. =>
          isFalse fun | castable?.fun _ hα hβ => nomatch hα
        | .bool =>
          match go β₁.option β₂ with
          | isFalse hβ =>
            isFalse fun contra ↦ by
              cases contra with
              | «fun» _ hα hβ =>
                cases hβ with
                | opt hβ' => exact hβ (castable?.opt hβ')
                | refl => exact hβ castable?.reflexive
              | refl => exact hβ castable?.reflexive
          | isTrue hβ => isTrue (castable?.fun nofun (castable?.reflexive) hβ)
      | .option β₁, .option α₂ =>
          match go α₁ α₂.option, go β₁.option β₂ with
          | isTrue h, isTrue h' => isTrue (castable?.fun nofun h h')
          | isFalse h, _ =>
            isFalse fun contra ↦ by
              cases contra with
              | «fun» _ hα hβ =>
                cases hα with
                | opt hα' => exact h (castable?.opt hα')
                | refl => exact h castable?.reflexive
              | refl => exact h castable?.reflexive
          | isTrue h, isFalse h' =>
            isFalse fun contra ↦ by
              cases contra with
              | «fun» _ hα hβ =>
                cases hβ with
                | opt hβ' => exact h' (castable?.opt hβ')
                | refl => exact h' castable?.reflexive
              | refl => exact h' castable?.reflexive
      | .option β₁, .fun α₂ α₃ =>
        match go α₁ (α₂.fun α₃), go β₁.option β₂ with
        | isTrue h, isTrue h' => isTrue (castable?.fun nofun h h')
        | isFalse h, _ =>
          isFalse fun contra ↦ by
            cases contra with
            | «fun» _ hα hβ => exact h hα
            | refl => exact h castable?.reflexive
        | isTrue h, isFalse h' =>
          isFalse fun contra ↦ by
            cases contra with
            | «fun» _ hα hβ => exact h' hβ
            | refl => exact h' castable?.reflexive
      | .bool, α₂ =>
        match β₂ with
        | .bool =>
          match go α₁ α₂ with
          | isFalse hα =>
            isFalse fun contra ↦ by
              cases contra with
              | chpred => contradiction
              | «fun» => contradiction
              | refl => exact hα castable?.reflexive
          | isTrue hα => isTrue (castable?.chpred hα)
        | .option .. | .pair .. | .fun .. | .unit | .int =>
          isFalse fun | .fun _ _ hβ => nomatch hβ
      | .int, α₂ =>
        match β₂ with
        | .int =>
          match go α₁ α₂ with
          | isFalse hα =>
            isFalse fun contra ↦ by
              cases contra with
              | «fun» => contradiction
              | refl => exact hα castable?.reflexive
          | isTrue hα => isTrue (castable?.fun nofun hα castable?.reflexive)
        | .option .. | .pair .. | .fun .. | .unit | .bool =>
          isFalse fun | .fun _ _ contra => nomatch contra
      | .unit, α₂ =>
        match β₂ with
        | .unit =>
          match go α₁ α₂ with
          | isFalse hα =>
            isFalse fun contra ↦ by
              cases contra with
              | «fun» => contradiction
              | refl => exact hα castable?.reflexive
          | isTrue hα => isTrue (castable?.fun nofun hα castable?.reflexive)
        | .option .. | .pair .. | .fun .. | .int | .bool =>
          isFalse fun | .fun _ _ contra => nomatch contra
      | .pair β₁₁ β₁₂, α₂ =>
        match β₂ with
        | .pair β₂₁ β₂₂ =>
          match go α₁ α₂, go (β₁₁.pair β₁₂) (β₂₁.pair β₂₂) with
          | isTrue hα, isTrue hβ => isTrue (castable?.fun nofun hα hβ)
          | isFalse hα, _ =>
            isFalse fun contra ↦ by
              cases contra with
              | «fun» hα hβ => contradiction
              | refl => exact hα castable?.reflexive
          | _, isFalse hβ =>
            isFalse fun contra ↦ by
              cases contra with
              | «fun» hα hβ => contradiction
              | refl => exact hβ castable?.reflexive
        | .bool | .int | .unit | .option .. | .fun .. =>
          isFalse fun | .fun _ _ contra => nomatch contra
      | .fun β₁₁ β₁₂, α₂ =>
        match go α₁ α₂, go (β₁₁.fun β₁₂) β₂ with
        | isTrue hα, isTrue hβ =>
          isTrue (castable?.fun nofun hα hβ)
        | isFalse hα, _ =>
          isFalse fun contra ↦ by
            cases contra with
            | «fun» hα hβ => contradiction
            | refl => exact hα castable?.reflexive
        | _, isFalse hβ =>
          isFalse fun contra ↦ by
            cases contra with
            | «fun» hα hβ => contradiction
            | refl => exact hβ castable?.reflexive
    | .fun _ _, .pair _ _
    | .fun _ _, .option _
    | .fun _ _, .unit
    | .fun _ _, .int
    | .fun _ _, .bool => isFalse nofun
    | .pair α₁ β₁, .pair α₂ β₂ =>
      match go α₁ α₂, go β₁ β₂ with
      | isTrue hα, isTrue hβ => isTrue (castable?.pair hα hβ)
      | isFalse hα, _ =>
        isFalse fun contra ↦ by
          cases contra with
          | pair => contradiction
          | refl => exact hα castable?.reflexive
      | _, isFalse hβ =>
        isFalse fun contra ↦ by
          cases contra with
          | pair => contradiction
          | refl => exact hβ castable?.reflexive
    | .pair α₁ β₁, .int
    | .pair α₁ β₁, .bool
    | .pair α₁ β₁, .unit
    | .pair α₁ β₁, .fun ..
    | .pair α₁ β₁, .option .. => isFalse nofun
    | .option α, .option β =>
      match go α β with
      | isTrue h => isTrue (castable?.opt h)
      | isFalse h => isFalse fun contra ↦ by
        cases contra with
        | opt => contradiction
        | refl => exact h castable?.reflexive
    | .option α, .bool
    | .option α, .int
    | .option α, .unit
    | .option α, .fun ..
    | .option α, .pair .. => isFalse nofun
  go α β

theorem castable?.toCastPath.extracted_195 {α₁ β₁ α₂ α₃ : SMTType}
  (hα₁α₂ : α₁ ⊑ α₂ = (false = true))
  (h : α₁.fun β₁.option ⊑ (α₂.pair α₃).fun SMTType.bool) (hpair : α₁.pair β₁ ⊑ α₂.pair α₃ = (false = true)) :
  False := by
  cases h with
  | graph hα hβ =>
    rw [Bool.false_eq_true, eq_iff_iff, iff_false] at hα₁α₂
    contradiction
  | «fun» _ hα hβ => nomatch hβ

def castable?.toCastPath {α β : SMTType} (h : α ⊑ β) : α ~> β :=
  match α, β with
  | .bool, .bool => castPath.reflexive .bool
  | .bool, .int | .bool, .unit | .bool, .fun .. | .bool, .pair .. | .bool, .option .. => nomatch h
  | .int, .int => castPath.reflexive .int
  | .int, .bool | .int, .unit | .int, .fun .. | .int, .pair .. | .int, .option .. => nomatch h
  | .unit, .unit => castPath.reflexive .unit
  | .unit, .bool | .unit, .int | .unit, .fun .. | .unit, .pair .. | .unit, .option .. => nomatch h
  | .fun α₁ β₁, .fun α₂ β₂ =>
    match β₁, α₂ with
    | .option β₁, .pair α₂ α₃ =>
      match hα : decide (α₁ ⊑ α₂), hβ : decide (β₁ ⊑ α₃) with
      | false, false =>
        match β₂ with
        | .bool =>
          match hαβ : decide ((α₁.pair β₁) ⊑ (α₂.pair α₃)) with
          | false => False.elim (by
              simp at *
              cases h with
              | graph contra _=> nomatch hα contra
              | «fun» _ _ contra => nomatch contra)
          | true => False.elim (by
              simp at *
              cases hαβ with
              | pair contra _ => nomatch hα contra
              | refl => nomatch hα .reflexive)
        | .option β₂ =>
          match hα₁ : decide (α₁ ⊑ (α₂.pair α₃)), hβ₁ : decide (β₁ ⊑ β₂) with
          | false, _ => False.elim (by
                simp at *
                cases h with
                | «fun» _ contra => nomatch hα₁ contra
                | refl => nomatch hα₁ .reflexive)
          | true, false => False.elim (by
              simp at *
              cases h with
              | «fun» _ _ contra =>
                cases contra
                · exact hβ₁ .reflexive
                · contradiction
              | refl => exact hβ₁ .reflexive)
          | true, true =>
            castPath.fun nofun (castable?.toCastPath (decide_eq_true_eq.mp hα₁)) (castable?.toCastPath (.opt (decide_eq_true_eq.mp hβ₁)))
        | .int | .unit | .fun .. | .pair .. => False.elim (by cases h with | «fun» _ _ contra => nomatch contra)
      | false, true =>
        match β₂ with
        | .bool => False.elim (by
            simp at *
            cases h with
            | graph contra _ => nomatch hα contra
            | «fun» _ _ contra => nomatch contra)
        | .unit | .int | .pair .. | .fun .. => False.elim (by
            simp at *
            cases h with
            | «fun» _ _ contra => nomatch contra)
        | .option β₂ =>
          match hβ₁ : decide (β₁ ⊑ β₂) with
          | false => False.elim (by
              simp at *
              cases h with
              | «fun» _ hα hβ =>
                cases hβ with
                | opt contra => nomatch hβ₁ contra
                | refl => exact hβ₁ .reflexive
              | refl => exact hβ₁ .reflexive)
          | true =>
            match hα₁ : decide (α₁ ⊑ (α₂.pair α₃)) with
            | true =>
              castPath.fun
                nofun
                (castable?.toCastPath (decide_eq_true_eq.mp hα₁))
                (castable?.toCastPath (.opt (decide_eq_true_eq.mp hβ₁)))
            | false => False.elim (by
                simp at *
                cases h with
                | «fun» _ hα hβ => nomatch hα₁ hα
                | refl => nomatch hα₁ .reflexive)
      | true, false => False.elim (by
          simp at *
          cases h with
          | graph _ contra => nomatch hβ contra
          | «fun» _ contra _ => nomatch castable?.false_of_pair_castable_left hα contra
          | refl => nomatch castable?.false_of_pair_self_left hα
        )
      | true, true =>
        match β₂ with
        | .int | .unit | .fun .. | .pair .. =>
          False.elim (by
            simp at *
            cases h with
            | «fun» _ _ contra => nomatch contra
          )
        | .option β₂ =>
          match hα₁ : decide (α₁ ⊑ (α₂.pair α₃)) with
            | true =>
              match hβ₁ : decide (β₁ ⊑ β₂) with
              | true =>
                castPath.fun
                  nofun
                  (castable?.toCastPath (decide_eq_true_eq.mp hα₁))
                  (castable?.toCastPath (.opt (decide_eq_true_eq.mp hβ₁)))
              | false => False.elim (by
                  simp at *
                  cases h with
                  | «fun» _ hα hβ =>
                    cases hβ with
                    | opt contra => nomatch hβ₁ contra
                    | refl => exact hβ₁ .reflexive
                  | refl => exact hβ₁ .reflexive
                )
            | false =>
              False.elim (by
                simp at *
                cases h with
                | «fun» _ hα hβ => nomatch hα₁ hα
                | refl => nomatch hα₁ .reflexive)
        | .bool =>
          castPath.graph
            (castable?.toCastPath (decide_eq_true_eq.mp hα))
            (castable?.toCastPath (decide_eq_true_eq.mp hβ))
    | .option β₁, .int =>
      match α₁ with
      | .bool | .unit | .pair .. | .fun .. | .option .. =>
        False.elim (by cases h with | «fun» _ contra _ => nomatch contra)
      | .int =>
        match hβ : decide (β₁.option ⊑ β₂) with
        | false => False.elim (by
            simp at *
            cases h with
            | «fun» _ _ contra => nomatch hβ contra
            | refl => exact hβ .reflexive)
        | true =>
          castPath.fun
            nofun
            (castPath.reflexive .int)
            (castable?.toCastPath (decide_eq_true_eq.mp hβ))
    | .option β₁, .unit =>
      match α₁ with
      | .bool | .int | .pair .. | .fun .. | .option .. =>
        False.elim (by cases h with | «fun» _ contra _ => nomatch contra)
      | .unit =>
        match hβ : decide (β₁.option ⊑ β₂) with
        | false => False.elim (by
            simp at *
            cases h with
            | «fun» _ _ contra => nomatch hβ contra
            | refl => exact hβ .reflexive)
        | true =>
          castPath.fun
            nofun
            (castPath.reflexive .unit)
            (castable?.toCastPath (decide_eq_true_eq.mp hβ))
    | .option β₁, .bool =>
      match α₁ with
      | .int | .unit | .pair .. | .fun .. | .option .. =>
        False.elim (by cases h with | «fun» _ contra _ => nomatch contra)
      | .bool =>
        match hβ : decide (β₁.option ⊑ β₂) with
        | false =>
          False.elim (by
            simp at *
            cases h with
            | «fun» _ _ contra => nomatch hβ contra
            | refl => nomatch hβ .reflexive)
        | true =>
          castPath.fun
            nofun
            (castPath.reflexive .bool)
            (castable?.toCastPath (decide_eq_true_eq.mp hβ))
    | .option β₁, .option α₂ =>
        match hα : decide (α₁ ⊑ α₂.option), hβ : decide (β₁.option ⊑ β₂) with
        | true, true =>
          castPath.fun
            nofun
            (castable?.toCastPath (decide_eq_true_eq.mp hα))
            (castable?.toCastPath (decide_eq_true_eq.mp hβ))
        | false, _ => False.elim (by
            simp at *
            cases h with
            | «fun» _ contra _ => nomatch hα contra
            | refl => nomatch hα .reflexive)
        | true, false => False.elim (by
            simp at *
            cases h with
            | «fun» _ _ contra => nomatch hβ contra
            | refl => exact hβ .reflexive)
    | .option β₁, .fun α₂ α₃ =>
      match hα : decide (α₁ ⊑ (α₂.fun α₃)), hβ : decide (β₁.option ⊑ β₂) with
      | true, true =>
        castPath.fun
          nofun
          (castable?.toCastPath (decide_eq_true_eq.mp hα))
          (castable?.toCastPath (decide_eq_true_eq.mp hβ))
      | false, _ => False.elim (by
          simp at *
          cases h with
          | «fun» _ contra _ => nomatch hα contra
          | refl => nomatch hα .reflexive)
      | true, false => False.elim (by
          simp at *
          cases h with
          | «fun» _ _ contra => nomatch hβ contra
          | refl => exact hβ .reflexive)
    | .bool, α₂ =>
      match β₂ with
      | .bool =>
        match hα : decide (α₁ ⊑ α₂) with
        | false => False.elim (by
            simp at *
            cases h with
            | chpred => contradiction
            | «fun» => contradiction
            | refl => nomatch hα .reflexive)
        | true =>
          castPath.chpred (castable?.toCastPath (decide_eq_true_eq.mp hα))
      | .option .. | .pair .. | .fun .. | .unit | .int =>
        False.elim (by cases h with | «fun» _ _ contra => nomatch contra)
    | .int, α₂ =>
      match β₂ with
      | .int =>
        match hα : decide (α₁ ⊑ α₂) with
        | false => False.elim (by
            simp at *
            cases h with
            | «fun» => contradiction
            | refl => nomatch hα .reflexive)
        | true =>
          castPath.fun
            nofun
            (castable?.toCastPath (decide_eq_true_eq.mp hα))
            (castPath.reflexive .int)
      | .option .. | .pair .. | .fun .. | .unit | .bool =>
        False.elim (by cases h with | «fun» _ _ contra => nomatch contra)
    | .unit, α₂ =>
      match β₂ with
      | .unit =>
        match hα : decide (α₁ ⊑ α₂) with
        | false => False.elim (by
            simp at *
            cases h with
            | «fun» => contradiction
            | refl => nomatch hα .reflexive)
        | true =>
          castPath.fun
            nofun
            (castable?.toCastPath (decide_eq_true_eq.mp hα))
            (castPath.reflexive .unit)
      | .option .. | .pair .. | .fun .. | .int | .bool =>
        False.elim (by cases h with | «fun» _ _ contra => nomatch contra)
    | .pair β₁₁ β₁₂, α₂ =>
      match β₂ with
      | .pair β₂₁ β₂₂ =>
        match hα : decide (α₁ ⊑ α₂), hβ : decide ((β₁₁.pair β₁₂) ⊑ (β₂₁.pair β₂₂)) with
        | true, true =>
          castPath.fun
            nofun
            (castable?.toCastPath (decide_eq_true_eq.mp hα))
            (castable?.toCastPath (decide_eq_true_eq.mp hβ))
        | false, _ => False.elim (by
            simp at *
            cases h with
            | «fun» _ contra _ => nomatch hα contra
            | refl => nomatch hα .reflexive)
        | _, false => False.elim (by
            simp at *
            cases h with
            | «fun» _ _ contra => nomatch hβ contra
            | refl => exact hβ .reflexive)
      | .bool | .int | .unit | .option .. | .fun .. =>
        False.elim (by cases h with | «fun» _ _ contra => nomatch contra)
    | .fun β₁₁ β₁₂, α₂ =>
      match hα : decide (α₁ ⊑ α₂), hβ : decide ((β₁₁.fun β₁₂) ⊑ β₂) with
      | true, true =>
        castPath.fun
          nofun
          (castable?.toCastPath (decide_eq_true_eq.mp hα))
          (castable?.toCastPath (decide_eq_true_eq.mp hβ))
      | false, _ => False.elim (by
          simp at *
          cases h with
          | «fun» _ contra _ => nomatch hα contra
          | refl => nomatch hα .reflexive)
      | true, false => False.elim (by
          simp at *
          cases h with
          | «fun» _ _ contra => nomatch hβ contra
          | refl => exact hβ .reflexive)
  | .fun _ _, .pair _ _
  | .fun _ _, .option _
  | .fun _ _, .unit
  | .fun _ _, .int
  | .fun _ _, .bool => False.elim (nomatch h)
  | .pair α₁ β₁, .pair α₂ β₂ =>
    match hα : decide (α₁ ⊑ α₂), hβ : decide (β₁ ⊑ β₂) with
    | true, true =>
      castPath.pair
        (castable?.toCastPath (decide_eq_true_eq.mp hα))
        (castable?.toCastPath (decide_eq_true_eq.mp hβ))
    | false, _ => False.elim (by
        simp at *
        cases h with
        | pair => contradiction
        | refl => nomatch hα .reflexive)
    | _, false => False.elim (by
        simp at *
        cases h with
        | pair => contradiction
        | refl => exact hβ .reflexive)
  | .pair α₁ β₁, .int
  | .pair α₁ β₁, .bool
  | .pair α₁ β₁, .unit
  | .pair α₁ β₁, .fun ..
  | .pair α₁ β₁, .option .. => False.elim (nomatch h)
  | .option α, .option β =>
    match h' : decide (α ⊑ β) with
    | true => castPath.opt (castable?.toCastPath (decide_eq_true_eq.mp h'))
    | false => False.elim (by
      simp at *
      cases h with
      | opt => contradiction
      | refl => exact h' .reflexive
      )
  | .option α, .bool
  | .option α, .int
  | .option α, .unit
  | .option α, .fun ..
  | .option α, .pair .. => False.elim (nomatch h)

theorem castable?_of_castPath {α β : SMTType} : α ~> β → α ⊑ β
  | .graph pα pβ    => castable?.graph (castable?_of_castPath pα) (castable?_of_castPath pβ)
  | .fun β_ne hα hβ => castable?.fun β_ne (castable?_of_castPath hα) (castable?_of_castPath hβ)
  | .chpred hα      => castable?.chpred (castable?_of_castPath hα)
  | .pair hα hβ     => castable?.pair (castable?_of_castPath hα) (castable?_of_castPath hβ)
  | .opt hα         => castable?.opt (castable?_of_castPath hα)
  | .refl h         => castable?.reflexive

theorem castable?_of_fun_bool {α α' β' : SMTType} : (α.fun .bool) ⊑ (α'.fun β') → β' = .bool := by
  rintro (_ | ⟨_, _, hβ⟩ | _ | _ | _ | ⟨hα⟩)
  case «fun» hβ => cases hβ; rfl
  all_goals rfl

theorem castable?.trans {α β γ : SMTType} (h₁ : α ⊑ β) (h₂ : β ⊑ γ) : α ⊑ γ := by
  induction γ generalizing α β with
  | bool | int | unit =>
    cases h₂
    exact h₁
  | pair γ₁ γ₂ γ₁_ih γ₂_ih =>
    cases h₂ with
    | refl => exact h₁
    | @pair β₁ β₂ _ _ hβ₁ hβ₂ =>
      cases h₁ with
      | refl => exact pair hβ₁ hβ₂
      | pair hα₁ hα₂ => exact pair (γ₁_ih hα₁ hβ₁) (γ₂_ih hα₂ hβ₂)
  | «fun» γ₁ γ₂ γ₁_ih γ₂_ih =>
    cases h₂ with
    | refl => exact h₁
    | @graph β₁ β₂ β₁' β₂' hβ₁ hβ₂ =>
      cases h₁ with
      | refl => exact graph hβ₁ hβ₂
      | @«fun» α₁ α₂ α₁' α₂' β_ne hα₁ hα₂ =>
        cases hα₂ with
        | refl =>
          apply graph
          · rcases @γ₁_ih (α₁.pair β₂') (β₁.pair β₂') (pair hα₁ reflexive) (pair hβ₁ reflexive)
            · exact reflexive
            · assumption
          · exact hβ₂
        | @opt δ _ hδ =>
          apply graph
          · rcases @γ₁_ih (α₁.pair β₂') (β₁.pair β₂') (pair hα₁ reflexive) (pair hβ₁ reflexive)
            · exact reflexive
            · assumption
          · rcases @γ₁_ih (β₁'.pair δ) (β₁'.pair β₂) (pair reflexive hδ) (pair reflexive hβ₂)
            · exact reflexive
            · assumption
    | @«fun» β₁ β₂ _ _ β₂_ne hβ₁ hβ₂ =>
      cases h₁ with
      | graph => contradiction
      | @chpred α hα => contradiction
      | refl => exact .fun β₂_ne hβ₁ hβ₂
      | @«fun» α₁ α₂ _ _ β_ne hα₁ hα₂ =>
        exact .fun β_ne (γ₁_ih hα₁ hβ₁) (γ₂_ih hα₂ hβ₂)
    | @chpred β _ hβ =>
      cases h₁ with
      | refl => exact chpred hβ
      | @«fun» α₁ α₂ _ _ α_ne hα₁ hα₂ =>
        exact .fun α_ne (γ₁_ih hα₁ hβ) hα₂
      | chpred hα => exact chpred (γ₁_ih hα hβ)
      | @graph α₁ α₂ α₁' α₂' hα₁ hα₂ =>
        cases hβ with
        | refl => exact graph hα₁ hα₂
        | @pair _ _ γ₁ γ₂ hγ₁ hγ₂ =>
          apply graph <;>
          · rcases @γ₁_ih (α₁.pair α₂) (α₁'.pair α₂') (pair hα₁ hα₂) (pair hγ₁ hγ₂)
            · exact reflexive
            · assumption
  | option γ γ_ih =>
    cases h₂ with
    | refl => exact h₁
    | @opt β _ hβ =>
      cases h₁ with
      | refl => exact opt hβ
      | @opt α _ hα => exact opt (γ_ih hα hβ)

instance : IsTrans SMTType (· ⊑ ·) where
  trans _ _ _ := castable?.trans

theorem castable?.antisymm {α β : SMTType} (h₁ : α ⊑ β) (h₂ : β ⊑ α) : α = β := by
  induction α generalizing β with
  | bool | int | unit => cases h₂; rfl
  | option α ih =>
    cases h₂ with
    | opt hβ =>
      cases h₁ with
      | opt hα =>
        congr
        apply ih <;> assumption
      | refl => rfl
    | refl => rfl
  | pair _ _ ih₁ ih₂ =>
    cases h₂ with
    | pair =>
      cases h₁ with
      | pair =>
        congr
        · apply ih₁ <;> assumption
        · apply ih₂ <;> assumption
      | refl => rfl
    | refl => rfl
  | «fun» _ _ ih₁ ih₂ =>
    cases h₂ with
    | refl => rfl
    | graph => cases h₁; contradiction
    | «fun» β_ne hα hβ =>
      cases h₁ with
      | «fun» =>
        congr
        · apply ih₁ <;> assumption
        · apply ih₂ <;> assumption
      | graph => nomatch hβ
      | chpred => nomatch β_ne
      | refl => rfl
    | chpred =>
      cases h₁ with
      | «fun» => contradiction
      | refl => rfl
      | chpred =>
        congr
        apply ih₁ <;> assumption

instance : Std.Antisymm (· ⊑ ·) where
  antisymm _ _ := castable?.antisymm
instance : IsAntisymm SMTType (· ⊑ ·) where
  antisymm _ _ := castable?.antisymm

def castPath.trans {α β γ : SMTType} (p₁ : α ~> β) (p₂ : β ~> γ) : α ~> γ :=
  castable?.toCastPath <| castable?.trans (castable?_of_castPath p₁) (castable?_of_castPath p₂)
def castPath.antisymm {α β : SMTType} (p₁ : α ~> β) (p₂ : β ~> α) : α = β :=
  castable?.antisymm (castable?_of_castPath p₁) (castable?_of_castPath p₂)

instance : PartialOrder SMTType where
  le := (· ⊑ ·)
  le_refl _ := castable?.reflexive
  le_trans _ _ _ := castable?.trans
  le_antisymm _ _ := castable?.antisymm

namespace SMT.SMTType

/--
Most general type for the `⊑` relation.
-/
def mgf : SMTType → SMTType
  | .bool => .bool
  | .int => .int
  | .unit => .unit
  | .option τ => .option (τ.mgf)
  | .pair α β => .pair (α.mgf) (β.mgf)
  | .fun α (.option β) => ((α.mgf).pair (β.mgf)).fun .bool
  | .fun α β => (α.mgf).fun (β.mgf)

/--
Least general type for the `⊑` relation.
-/
def lgf : SMTType → SMTType
  | .bool => .bool
  | .int => .int
  | .unit => .unit
  | .option τ => .option (τ.lgf)
  | .pair α β => .pair (α.lgf) (β.lgf)
  | .fun (.pair α β) .bool => (α.lgf).fun (β.lgf.option)
  | .fun (.pair α β) .int => (α.lgf.pair β.lgf).fun .int
  | .fun (.pair α β) .unit => (α.lgf.pair β.lgf).fun .unit
  | .fun (.pair α β) (.fun γ δ) => (α.lgf.pair β.lgf).fun (γ.fun δ).lgf
  | .fun (.pair α β) (.pair γ δ) => (α.lgf.pair β.lgf).fun (γ.lgf.pair δ.lgf)
  | .fun (.pair α β) (.option τ) => (α.lgf.pair β.lgf).fun (τ.lgf.option)
  | .fun .bool α => .fun .bool (α.lgf)
  | .fun .int α => .fun .int (α.lgf)
  | .fun .unit α => .fun .unit (α.lgf)
  | .fun (.option τ) α => .fun (τ.lgf.option) (α.lgf)
  | .fun (.fun γ δ) α => .fun (γ.fun δ).lgf (α.lgf)


theorem le_mgf (α : SMTType) : α ⊑ α.mgf := by
  induction α with
  | bool | int | unit => exact castable?.refl (by trivial)
  | option τ ih => exact castable?.opt ih
  | pair α β α_ih β_ih => exact castable?.pair α_ih β_ih
  | «fun» α β α_ih β_ih =>
    unfold mgf
    split <;> try contradiction
    · rename_i α' β' eq
      injection eq
      subst_vars
      apply castable?.graph α_ih
      unfold mgf at β_ih
      exact castable?.optE β_ih
    · rename_i α β contra _
      injections
      subst_vars
      cases β with
      | option τ => nomatch contra τ rfl
      | bool => exact castable?.chpred α_ih
      | int | unit | pair α β | «fun» β₁ β₂ => exact castable?.fun nofun α_ih β_ih

private theorem lgf_of_fun_ne_bool {α β : SMTType} : (α.fun β).lgf ≠ .bool := by
  intro contra
  induction α generalizing β with
  | bool | int | unit | «fun» | option => nomatch contra
  | pair α γ α_ih γ_ih =>
    unfold lgf at contra
    split at contra <;> contradiction

private theorem lgf_of_fun_ne_int {α β : SMTType} : (α.fun β).lgf ≠ .int := by
  intro contra
  induction α generalizing β with
  | bool | int | unit | «fun» | option => nomatch contra
  | pair α γ α_ih γ_ih =>
    unfold lgf at contra
    split at contra <;> contradiction

private theorem lgf_of_fun_ne_unit {α β : SMTType} : (α.fun β).lgf ≠ .unit := by
  intro contra
  induction α generalizing β with
  | bool | int | unit | «fun» | option => nomatch contra
  | pair α γ α_ih γ_ih =>
    unfold lgf at contra
    split at contra <;> contradiction

theorem lgf_le (α : SMTType) : α.lgf ⊑ α := by
  fun_induction lgf <;> try exact castable?.reflexive
  · apply castable?.opt
    assumption
  · apply castable?.pair <;> assumption
  · apply castable?.graph <;> assumption
  · apply castable?.fun (by nofun) ?_ .reflexive
    apply castable?.pair <;> assumption
  · apply castable?.fun (by nofun) ?_ .reflexive
    apply castable?.pair <;> assumption
  · apply castable?.fun
    · exact lgf_of_fun_ne_bool
    · apply castable?.pair <;> assumption
    · assumption
  · apply castable?.fun ?_ ?_ ?_
    · nofun
    · apply castable?.pair <;> assumption
    · apply castable?.pair <;> assumption
  · apply castable?.fun
    · nofun
    · apply castable?.pair <;> assumption
    · apply castable?.opt
      assumption
  · rename_i α α_ih
    cases α with
    | bool | int | unit => exact castable?.reflexive
    | «fun» α β =>
      exact castable?.fun lgf_of_fun_ne_bool .reflexive α_ih
    | option τ | pair α β =>
      exact castable?.fun nofun .reflexive α_ih
  · rename_i α α_ih
    cases α with
    | bool | int | unit => exact castable?.reflexive
    | «fun» α β =>
      exact castable?.fun lgf_of_fun_ne_bool .reflexive α_ih
    | option τ | pair α β =>
      exact castable?.fun nofun .reflexive α_ih
  · rename_i α α_ih
    cases α with
    | bool | int | unit => exact castable?.reflexive
    | «fun» α β =>
      exact castable?.fun lgf_of_fun_ne_bool .reflexive α_ih
    | option τ | pair α β =>
      exact castable?.fun nofun .reflexive α_ih
  · rename_i α _ α_ih
    cases α with
    | bool =>
      apply castable?.chpred (.opt ?_)
      assumption
    | int | unit =>
      apply castable?.fun (by nofun) (.opt ?_) α_ih
      assumption
    | «fun» =>
      apply castable?.fun (lgf_of_fun_ne_bool) (.opt ? _) α_ih
      assumption
    | option | pair =>
      apply castable?.fun (by nofun) (.opt ?_) α_ih
      assumption
  · rename_i α _ α_ih
    cases α with
    | bool =>
      rw [lgf]
      apply castable?.chpred
      assumption
    | int | unit =>
      apply castable?.fun (by nofun) ?_ α_ih
      assumption
    | «fun» =>
      apply castable?.fun (lgf_of_fun_ne_bool) ?_ α_ih
      assumption
    | option | pair =>
      apply castable?.fun (by nofun) ?_ α_ih
      assumption

theorem lgf_le_mgf {α : SMTType} : α.lgf ⊑ α.mgf := castable?.trans (lgf_le α) (le_mgf α)

private theorem lgf_idempotent_of_fun_opt {α β : SMTType} (hα : α.lgf = α) (hβ : β.lgf = β) :
    (α.fun β.option).lgf = α.fun β.option := by
  cases α with
  | bool | int | unit => simp_rw [lgf, hβ]
  | «fun» => simp_rw [lgf, hα, hβ]
  | pair | option =>
    simp_rw [lgf] at hα ⊢
    rw [hα, hβ]

private theorem lgf_idempotent_of_pair_fun {α β γ δ : SMTType}
  (ih₁ : α.lgf = α)
  (ih₂ : β.lgf = β)
  (ih₃ : (γ.fun δ).lgf.lgf = (γ.fun δ).lgf) :
    ((α.pair β).fun (γ.fun δ).lgf).lgf = (α.pair β).fun (γ.fun δ).lgf := by
  rw [lgf.eq_def]
  split
  all_goals
    injections
    try subst_eqs
    try contradiction
    try {
      rename_i eq
      have := lgf_le (γ.fun δ)
      rw [eq] at this
      cases this
    }
  · rename_i eq
    rw [←eq, ih₁, ih₂, ih₃]

private theorem lgf_idempotent_of_fun_fun {γ δ α : SMTType}
  (ih₁ : (γ.fun δ).lgf.lgf = (γ.fun δ).lgf)
  (ih₂ : α.lgf = α) :
    ((γ.fun δ).lgf.fun α).lgf = (γ.fun δ).lgf.fun α := by
  cases h : (γ.fun δ).lgf with
  | bool | int | unit | option τ | pair α β =>
    have := lgf_le (γ.fun δ)
    rw [h] at this
    nomatch this
  | «fun» γ' δ' => rw [lgf, ←h, ih₁, ih₂]

private theorem mgf_idempotent_of_fun {α β : SMTType} (hβ : ∀ (β_1 : SMTType), β = β_1.option → False)
  (ih₁ : α.mgf = α)
  (ih₂ : β.mgf = β) :
    (α.fun β).mgf = α.fun β := by
  induction β with
  | bool | int | unit => simp_rw [mgf, ih₁]
  | «fun» β δ β_ih δ_ih => simp_rw [mgf, ih₁, ih₂]
  | pair β δ β_ih δ_ih => rwa [mgf, ih₁, ih₂]
  | option τ ih => nomatch hβ τ rfl

@[simp]
theorem lgf_idempotent {α : SMTType} : (α.lgf).lgf = α.lgf := by
  fun_induction lgf <;> try rfl
  · rename_i ih
    rw [lgf, ih]
  · rename_i ih₁ ih₂
    rw [lgf, ih₁, ih₂]
  · apply lgf_idempotent_of_fun_opt <;> assumption
  · rename_i ih₁ ih₂
    rw [lgf, ih₁, ih₂]
  · rename_i ih₁ ih₂
    rw [lgf, ih₁, ih₂]
  · apply lgf_idempotent_of_pair_fun <;> assumption
  · rename_i ih₁ ih₂ ih₃ ih₄
    rw [lgf, ih₁, ih₂, ih₃, ih₄]
  · rename_i ih₁ ih₂ ih₃
    rw [lgf, ih₁, ih₂, ih₃]
  · rename_i ih
    rw [lgf, ih]
  · rename_i ih
    rw [lgf, ih]
  · rename_i ih
    rw [lgf, ih]
  · rename_i ih₁ ih₂
    rw [lgf, ih₁, ih₂]
  · apply lgf_idempotent_of_fun_fun <;> assumption

@[simp]
theorem mgf_idempotent {α : SMTType} : (α.mgf).mgf = α.mgf := by
  fun_induction mgf <;> try rfl
  · rename_i ih
    rw [mgf, ih]
  · rename_i ih₁ ih₂
    rw [mgf, ih₁, ih₂]
  · rename_i ih₁ ih₂
    simp_rw [mgf, ih₁, ih₂]
  · rename_i β contra _ _
    apply mgf_idempotent_of_fun
    · intro β' eq
      have := le_mgf β
      rw [eq] at this
      cases this <;> nomatch contra _ rfl
    · assumption
    · assumption

@[mono]
theorem lgf_mono {α β : SMTType} (h : α ⊑ β) : α.lgf ⊑ β.lgf := by
  induction h with
  | refl => exact castable?.reflexive
  | @graph α β α' β' hα hβ hα_ih hβ_ih =>
    rw [lgf]
    rw [lgf.eq_def]
    split <;> (injections; try subst_eqs; try contradiction)
    all_goals
    · cases hα <;>
      · simp_rw [lgf]
        refine castable?.fun nofun hα_ih (castable?.opt hβ_ih)
  | «fun» β_ne hα hβ hα_ih hβ_ih =>
    rw [lgf.eq_def]
    split <;> (injections; try subst_eqs; try contradiction)
    · cases hβ
      cases hα <;>
      · rw [lgf]
        exact castable?.fun β_ne hα_ih hβ_ih
    · cases hβ
      cases hα <;>
      · rw [lgf]
        exact castable?.fun β_ne hα_ih hβ_ih
    · cases hα <;> cases hβ <;>
      · rw [lgf]
        apply castable?.fun ?_ hα_ih hβ_ih
        intro contra
        nomatch contra ▸ lgf_le _
    · cases hβ <;> cases hα <;>
      · rw [lgf]
        exact castable?.fun nofun hα_ih hβ_ih
    · cases hβ <;> cases hα <;>
      · rw [lgf]
        exact castable?.fun nofun hα_ih hβ_ih
    · cases hα
      cases hβ with
      | refl => exact castable?.reflexive
      | chpred | opt | pair | graph | «fun» =>
        rw [lgf]
        apply castable?.fun ?_ hα_ih hβ_ih
        intro contra
        try cases contra ▸ lgf_le _
    · cases hα
      rw [lgf]
      refine castable?.fun ?_ hα_ih hβ_ih
      intro contra
      cases contra ▸ lgf_le _
      contradiction
    · cases hα
      rw [lgf]
      refine castable?.fun ?_ hα_ih hβ_ih
      intro contra
      cases contra ▸ lgf_le _
      contradiction
    · cases hα <;>
      · rw [lgf]
        refine castable?.fun ?_ hα_ih hβ_ih
        intro contra
        cases contra ▸ lgf_le _
        contradiction
    · cases hα <;>
      · rw [lgf]
        refine castable?.fun ?_ hα_ih hβ_ih
        intro contra
        cases contra ▸ lgf_le _
        contradiction
  | pair hα hβ hα_ih hβ_ih => exact castable?.pair hα_ih hβ_ih
  | opt hα ih => exact castable?.opt ih
  | @chpred α α' hα ih =>
    cases α with
    | bool | unit | int =>
      cases hα; exact castable?.reflexive
    | option | «fun» α₁ α₂ =>
      cases hα <;> exact castable?.chpred ih
    | pair α β =>
      cases hα <;>
      · simp_rw [lgf] at ih
        have ⟨h, h'⟩ := castable?.pairE ih
        exact castable?.fun nofun h (castable?.opt h')

@[mono]
theorem mgf_mono {α β : SMTType} (h : α ⊑ β) : α.mgf ⊑ β.mgf := by
  induction h with
  | refl => exact castable?.reflexive
  | pair hα hβ hα_ih hβ_ih => exact castable?.pair hα_ih hβ_ih
  | graph hα hβ hα_ih hβ_ih => exact castable?.chpred (castable?.pair hα_ih hβ_ih)
  | chpred hα ih => exact castable?.chpred ih
  | opt hα ih => exact castable?.opt ih
  | @«fun» α β α' β' β_ne hα hβ hα_ih hβ_ih =>
    cases β with
    | bool => contradiction
    | option =>
      cases hβ <;> exact castable?.chpred (castable?.pair hα_ih (castable?.optE hβ_ih))
    | int | unit =>
      cases hβ; exact castable?.fun β_ne hα_ih hβ_ih
    | pair =>
      cases hβ <;> exact castable?.fun nofun hα_ih hβ_ih
    | «fun» =>
      cases hβ with
      | chpred | graph => exact castable?.fun nofun hα_ih hβ_ih
      | «fun» | refl =>
        apply castable?.fun ?_ hα_ih hβ_ih
        intro contra
        nomatch contra ▸ le_mgf _

@[simp]
theorem mgf_of_lgf {α : SMTType} : α.lgf.mgf = α.mgf := by
  apply castable?.antisymm <| mgf_mono <| lgf_le _
  fun_induction lgf <;> try exact .reflexive
  · apply castable?.opt
    assumption
  · apply castable?.pair <;> assumption
  · simp_rw [mgf]
    apply castable?.chpred (castable?.pair _ _) <;> assumption
  · simp_rw [mgf]
    apply castable?.fun (by nofun) ?_ .reflexive
    apply castable?.pair <;> assumption
  · simp_rw [mgf]
    refine castable?.fun (by nofun) ?_ .reflexive
    apply castable?.pair <;> assumption
  · rw (occs := .pos [2]) [mgf]
    · simp_rw [mgf]
      apply castable?.fun
      · intro contra
        nomatch contra ▸ le_mgf _
      · apply castable?.pair <;> assumption
      · assumption
    · intro _ contra
      nomatch contra ▸ lgf_le _
  · simp_rw [mgf]
    apply castable?.fun (by nofun) <;>
    · apply castable?.pair <;> assumption
  · simp_rw [mgf]
    apply castable?.chpred (castable?.pair _ _)
    · apply castable?.pair <;> assumption
    · assumption
  · rename_i α ih
    cases α with
    | bool | int | unit => exact le_mgf _
    | option τ =>
      exact castable?.chpred <| castable?.pair .reflexive (castable?.optE ih)
    | pair α β =>
      exact castable?.fun nofun .reflexive ih
    | «fun» α₁ α₂ =>
      rw [lgf.eq_def]
      split <;> (injections; try subst_eqs; try contradiction)
      all_goals
        apply castable?.fun ?_ .reflexive ih
        intro contra
        nomatch contra ▸ le_mgf _
  · rename_i α ih
    cases α with
    | bool | int | unit => exact le_mgf _
    | option τ =>
      exact castable?.chpred <| castable?.pair .reflexive (castable?.optE ih)
    | pair α β =>
      exact castable?.fun nofun .reflexive ih
    | «fun» α₁ α₂ =>
      rw [lgf.eq_def]
      split <;> (injections; try subst_eqs; try contradiction)
      all_goals
        apply castable?.fun ?_ .reflexive ih
        intro contra
        nomatch contra ▸ le_mgf _
  · rename_i α ih
    cases α with
    | bool | int | unit => exact le_mgf _
    | option τ =>
      exact castable?.chpred <| castable?.pair .reflexive (castable?.optE ih)
    | pair α β =>
      exact castable?.fun nofun .reflexive ih
    | «fun» α₁ α₂ =>
      rw [lgf.eq_def]
      split <;> (injections; try subst_eqs; try contradiction)
      all_goals
        apply castable?.fun ?_ .reflexive ih
        intro contra
        nomatch contra ▸ le_mgf _
  · rename_i α β ih₁ ih₂
    cases β with
    | bool =>
      exact castable?.chpred <| castable?.opt ih₁
    | int | unit =>
      exact castable?.fun nofun (castable?.opt ih₁) ih₂
    | option τ =>
      exact castable?.chpred <| castable?.pair (castable?.opt ih₁) (castable?.optE ih₂)
    | pair α β =>
      exact castable?.fun nofun (castable?.opt ih₁) ih₂
    | «fun» α₁ α₂ =>
      simp_rw [mgf]
      rw (occs := .pos [2]) [lgf.eq_def]
      split <;> (injections; try subst_eqs; try contradiction)
      all_goals
        exact castable?.fun (fun contra ↦ nomatch contra ▸ le_mgf _) (castable?.opt ih₁) ih₂
  · rename_i α β ih₁ ih₂
    cases β with
    | option τ =>
      exact castable?.chpred <| castable?.pair ih₁ (castable?.optE ih₂)
    | bool => exact castable?.chpred ih₁
    | int | unit | pair α β => exact castable?.fun nofun ih₁ ih₂
    | «fun» β₁ β₂ =>
      simp_rw [mgf]
      rw (occs := .pos [2]) [lgf.eq_def]
      split <;> (injections; try subst_eqs; try contradiction)
      all_goals
        exact castable?.fun (fun contra ↦ nomatch contra ▸ le_mgf _) ih₁ ih₂

@[simp]
theorem lgf_of_mgf {α : SMTType} : α.mgf.lgf = α.lgf := by
  apply castable?.antisymm _ (lgf_mono <| le_mgf α)
  fun_induction lgf <;> try exact .reflexive
  · apply castable?.opt
    assumption
  · apply castable?.pair <;> assumption
  · apply castable?.fun
    · nofun
    · assumption
    · apply castable?.opt
      assumption
  · apply castable?.fun (by nofun) _ .reflexive
    apply castable?.pair <;> assumption
  · apply castable?.fun (by nofun) _ .reflexive
    apply castable?.pair <;> assumption
  · rename_i α β δ γ ih₁ ih₂ ih₃
    simp_rw [mgf]
    rw (occs := .pos [3]) [mgf.eq_def]
    split <;> (injections; try subst_eqs; try contradiction)
    · exact castable?.fun nofun (castable?.pair ih₁ ih₂) ih₃
    · apply castable?.fun
      · intro contra
        nomatch contra ▸ lgf_le _
      · exact castable?.pair ih₁ ih₂
      · rw [←mgf]
        · exact ih₃
        · assumption
  · rename_i α β δ γ ih₁ ih₂ ih₃
    simp_rw [mgf, lgf]
    refine castable?.fun nofun (castable?.pair γ ih₁) (castable?.pair ih₂ ih₃)
  · rename_i α β δ ih₁ ih₂ ih₃
    simp_rw [mgf, lgf]
    refine castable?.fun nofun (castable?.pair ih₁ ih₂) (castable?.opt ih₃)
  · rename_i α ih
    cases α with
    | bool | int | unit => exact castable?.reflexive
    | option | pair => exact castable?.fun nofun .reflexive ih
    | «fun» α₁ α₂ =>
      rw [lgf.eq_def]
      split <;> (injections; try subst_eqs; try contradiction)
      all_goals
        apply castable?.fun ?_ .reflexive ih
        intro contra
        cases castable?.trans (castable?.trans (lgf_mono (contra ▸ lgf_le _)) ih) (lgf_le _)
  · rename_i α ih
    cases α with
    | bool | int | unit => exact castable?.reflexive
    | option | pair => exact castable?.fun nofun .reflexive ih
    | «fun» α₁ α₂ =>
      rw [mgf.eq_def]
      split <;> (injections; try subst_eqs; try contradiction)
      all_goals
        apply castable?.fun ?_ .reflexive ih
        intro contra
        cases castable?.trans (castable?.trans (lgf_mono (contra ▸ lgf_le _)) ih) (lgf_le _)
  · rename_i α ih
    cases α with
    | bool | int | unit => exact castable?.reflexive
    | option | pair => exact castable?.fun nofun .reflexive ih
    | «fun» α₁ α₂ =>
      rw [mgf.eq_def]
      split <;> (injections; try subst_eqs; try contradiction)
      all_goals
        apply castable?.fun ?_ .reflexive ih
        intro contra
        cases castable?.trans (castable?.trans (lgf_mono (contra ▸ lgf_le _)) ih) (lgf_le _)
  · rename_i α β ih₁ ih₂
    rw [mgf.eq_def]
    split <;> (injections; try subst_eqs; try contradiction)
    · exact castable?.fun nofun (castable?.opt ih₁) ih₂
    · cases β with
      | bool => exact castable?.chpred <| castable?.opt ih₁
      | pair | option | int | unit => exact castable?.fun nofun (castable?.opt ih₁) ih₂
      | «fun» =>
        apply castable?.fun _ (castable?.opt ih₁) ih₂
        intro contra
        cases castable?.trans (castable?.trans (lgf_mono (contra ▸ lgf_le _)) ih₂) (lgf_le _)
  · rename_i α β γ ih₁ ih₂
    rw [mgf.eq_def]
    split <;> (injections; try subst_eqs; try contradiction)
    · exact castable?.fun nofun ih₁ ih₂
    · rw [mgf.eq_def]
      split <;> (injections; try subst_eqs; try contradiction)
      · cases γ with
        | bool => exact castable?.chpred ih₁
        | pair | option | int | unit => exact castable?.fun nofun ih₁ ih₂
        | «fun» =>
          apply castable?.fun ?_ ih₁ ih₂
          intro contra
          cases castable?.trans (castable?.trans (lgf_mono (contra ▸ lgf_le _)) ih₂) (lgf_le _)
      · cases γ with
        | bool =>
          apply castable?.chpred
          rw [←mgf]
          · exact ih₁
          · assumption
        | pair | option | int | unit =>
          refine castable?.fun nofun ?_ ih₂
          rw [←mgf]
          · exact ih₁
          · assumption
        | «fun» =>
          apply castable?.fun _ _ ih₂
          · intro contra
            cases castable?.trans (castable?.trans (lgf_mono (contra ▸ lgf_le _)) ih₂) (lgf_le _)
          · rw [←mgf]
            · exact ih₁
            · assumption

theorem lgf_le_iff_le_mgf {α β : SMTType} : α.lgf ⊑ β ↔ α ⊑ β.mgf where
  mp h := castable?.trans (le_mgf α) (mgf_of_lgf ▸ mgf_mono h)
  mpr h := by
    trans
    · exact lgf_of_mgf ▸ lgf_mono h
    · apply lgf_le

theorem castable?.galois : GaloisConnection lgf mgf := @lgf_le_iff_le_mgf

theorem castable?_to_castPath_reflexive {α : SMTType} : castable?.reflexive.toCastPath = castPath.reflexive α := by
  induction α with
  | bool | int | unit => rfl
  | «fun» α β α_ih β_ih =>
    cases β with
    | bool | int | unit =>
      rw [castPath.reflexive, castable?.toCastPath]
      split
      · have := decide_eq_true (@castable?.reflexive α)
        contradiction
      · congr
    | «fun» β δ =>
      rw [castPath.reflexive, castable?.toCastPath]
      split
      · congr
      · have := decide_eq_true (@castable?.reflexive α)
        contradiction
      · have := decide_eq_true (@castable?.reflexive (β.fun δ))
        contradiction
    | option β =>
      cases α with
      | bool | int | unit =>
        rw [castPath.reflexive, castable?.toCastPath]
        split
        · have := decide_eq_true (@castable?.reflexive β.option)
          contradiction
        · congr
      | «fun» α₁ α₂ =>
        rw [castPath.reflexive, castable?.toCastPath]
        split
        · congr
        · have := decide_eq_true (@castable?.reflexive β.option)
          contradiction
        · have := decide_eq_true (@castable?.reflexive β.option)
          contradiction
      | option τ =>
        rw [castPath.reflexive, castable?.toCastPath]
        split
        · congr
        · have := decide_eq_true (@castable?.reflexive τ.option)
          contradiction
        · have := decide_eq_true (@castable?.reflexive τ.option)
          contradiction
      | pair α₁ α₂ =>
        rw [castPath.reflexive, castable?.toCastPath]
        dsimp
        have := decide_eq_true (@castable?.reflexive (α₁.pair α₂))
        have := decide_eq_true (@castable?.reflexive β)
        repeat' split
        all_goals first | contradiction | congr
    | pair α β =>
      rw [castPath.reflexive, castable?.toCastPath]
      split
      · congr
      · have := decide_eq_true (@castable?.reflexive (α.pair β))
        contradiction
      · have := decide_eq_true (@castable?.reflexive (α.pair β))
        contradiction
  | option τ ih =>
    rw [castPath.reflexive, castable?.toCastPath]
    split
    · congr
    · have := decide_eq_true (@castable?.reflexive (τ.option))
      contradiction
  | pair α β α_ih β_ih =>
    rw [castPath.reflexive, castable?.toCastPath]
    split
    · congr
    · have := decide_eq_true (@castable?.reflexive (α.pair β))
      contradiction
    · have := decide_eq_true (@castable?.reflexive (α.pair β))
      contradiction

theorem castable?_to_castPath_graph {α β α' β' : SMTType} (hα : α ⊑ α') (hβ : β ⊑ β') :
    (castable?.graph hα hβ).toCastPath = castPath.graph hα.toCastPath hβ.toCastPath := by
  rw [castable?.toCastPath]
  dsimp
  split using contra | _ | _ <;> try contradiction
  · rw [decide_eq_true hβ] at contra
    nomatch contra
  · rfl

/--
Enumerate all `τ` such that `τ ⊑ upper`.
-/
def lowerSet : SMTType → List SMTType
  | .bool => [.bool]
  | .int => [.int]
  | .unit => [.unit]
  | .option α => (lowerSet α).map .option
  | .pair α β => (lowerSet α).product (lowerSet β) |>.map (fun ⟨τ₁, τ₂⟩ => .pair τ₁ τ₂)
  | .fun α .bool =>
    let chpredTargets := (lowerSet α).map (fun τ => .fun τ .bool)
    match α with
    | .pair α₁ α₂ =>
      let graphSources := (lowerSet α₁).product (lowerSet α₂) |>.map (fun ⟨τ₁, τ₂⟩ => .fun τ₁ (.option τ₂))
      chpredTargets ++ graphSources
    | _ => chpredTargets
  | .fun α β =>
    (lowerSet α).product (lowerSet β) |>.map (fun ⟨τ₁, τ₂⟩ => .fun τ₁ τ₂)

/--
Enumerate all `τ` in the interval `[lo, hi]` for `⊑`.
-/
def interval (lo hi : SMTType) : List SMTType :=
  (lowerSet hi).filter (fun τ => lo ⊑ τ)

/--
Enumerate all possible loosening targets between `α.lgf` and `α.mgf`.
-/
def lattice (α : SMTType) : List SMTType :=
  interval α.lgf α.mgf

/--
Unifies two `SMTType` by loosening as little as possible.
- If they are comparable for `⊑`, returns the greater one.
- Otherwise, tries to compute a least upper bound (join) among common upper bounds.
-/
def join (α β : SMTType) : Option SMTType :=
  if α ⊑ β then return β
  else if β ⊑ α then return α
  else
    let I₁ := interval α α.mgf
    let I₂ := interval β β.mgf
    let candidates := I₁.inter I₂
    candidates.find? (fun τ => candidates.all (fun σ => τ ⊑ σ))

/--
Dual of `join`, unifies two `SMTType` by tightening as little as possible.
- If two types are comparable for `⊑`, returns the smaller one.
- Otherwise, tries to compute a greatest lower bound (meet) among common lower bounds.
-/
def meet (α β : SMTType) : Option SMTType :=
  if α ⊑ β then return α
  else if β ⊑ α then return β
  else
    let L₁ := lowerSet α
    let L₂ := lowerSet β
    let candidates := L₁.inter L₂
    candidates.find? (fun τ => candidates.all (fun σ => σ ⊑ τ))

end SMT.SMTType
