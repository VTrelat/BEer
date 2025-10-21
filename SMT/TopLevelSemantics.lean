import SMT.Semantics
import SMT.PHOAS.SMTPHOAS
import SMT.PHOAS.Environment
import SMT.Environment

namespace SMT

section Abstraction
def Instr.abstract {𝒱} (i : Instr) (ρ : SMT.𝒱 → Option 𝒱) (hρ : ∀ {t}, ∀ v ∈ fv t, (ρ v).isSome = true) : PHOAS.Instr 𝒱 :=
  match i with
  | declare_const (v : SMT.𝒱) (τ : SMTType) => .declare_const (ρ v |>.get (hρ v fv.mem_var )) τ
  | define_fun (v : SMT.𝒱) (τ : SMTType) (σ : SMTType) (t : Term) => .define_fun (ρ v |>.get (hρ v fv.mem_var)) τ σ <| t.abstract ρ hρ
  | define_const (v : SMT.𝒱) (τ : SMTType) (t : Term) => .define_const (ρ v |>.get (hρ v fv.mem_var)) τ <| t.abstract ρ hρ
  | assert (t : Term) => .assert (t.abstract ρ hρ)
  | push (n : Nat) => .push n
  | pop (n : Nat) => .pop n
  | check_sat => .check_sat

def Chunk.abtsract {𝒱} (c : Chunk) (ρ : SMT.𝒱 → Option 𝒱) (hρ : ∀ {t}, ∀ v ∈ fv t, (ρ v).isSome = true) : PHOAS.Chunk 𝒱 :=
  c.map (Instr.abstract · ρ hρ)
def Stages.abstract {𝒱} (s : Stages) (ρ : SMT.𝒱 → Option 𝒱) (hρ : ∀ {t}, ∀ v ∈ fv t, (ρ v).isSome = true) : PHOAS.Stages 𝒱 :=
  match s with
  | instr ck => .instr <| ck.abtsract ρ hρ
  | asserts as => .asserts <| as.map (·.abstract ρ hρ)

end Abstraction
namespace PHOAS

section Denotation

def Chunk.WF {𝒱} [DecidableEq 𝒱] (Γ : TypeContext 𝒱) (is : Chunk 𝒱) := ∀ (i : Instr 𝒱) (_ : i ∈ is),
  match i with
  | .declare_const v τ => Γ v = some τ
  | .define_const v τ e => Γ v = some τ ∧ Γ ⊢ e : τ
  | .define_fun v τ σ e => Γ v = some (τ.fun σ) ∧ Γ ⊢ e : τ.fun σ
  | .assert t => Γ ⊢ t : .bool
  | .push _ | .pop _ | .check_sat => True

noncomputable def Chunk.denote (is : PHOAS.Chunk ZFSet) (Γ : TypeContext ZFSet) (wf : is.WF Γ) : ZFSet.ZFBool :=
  go Γ ⊤ [⊤] ⊤ 0 wf is.attach
where go (Γ : TypeContext ZFSet) (acc : ZFSet.ZFBool) (stack : List ZFSet.ZFBool) (denotation : ZFSet.ZFBool) (level : Nat) {is : Chunk ZFSet} (wf : is.WF Γ) : List { x // x ∈ is } → ZFSet.ZFBool
  | [] => denotation
  | ⟨.assert P, h⟩ :: is =>
    let ℙ := ⟦P⟧ˢ ⟨Γ, .bool, wf _ h⟩
    go Γ (acc ⋀ ℙ) stack denotation level wf is
  | ⟨.push _, _⟩ :: is =>
    go Γ acc (acc :: stack) denotation level wf is
  | ⟨.pop n, _⟩ :: is =>
    if _ : n > level then unreachable! -- maybe useless. If yes, remove `level`
    else go Γ stack.head! stack.tail! denotation (level - n) wf is
  | ⟨.check_sat, _⟩ :: is =>
    go Γ acc stack (denotation ⋀ acc) level wf is
  | ⟨.declare_const .., _⟩ :: is =>
    go Γ acc stack denotation level wf is
  | ⟨.define_const v τ exp, h⟩ :: is =>
    let ℰ := ⟦.var v =ˢ' exp⟧ˢ ⟨Γ, .bool, Typing.eq Γ (.var v) exp τ (Typing.var Γ v τ (wf _ h).1) (wf _ h).2⟩
    go Γ (acc ⋀ ℰ) stack denotation level wf is
  | ⟨.define_fun v τ σ exp, h⟩ :: is =>
    let ℰ := ⟦(PHOAS.Term.var v) =ˢ' exp⟧ˢ ⟨Γ, .bool, Typing.eq Γ (.var v) exp (τ.fun σ) (Typing.var Γ v (τ.fun σ) (wf _ h).1) (wf _ h).2⟩
    go Γ (acc ⋀ ℰ) stack denotation level wf is

def Stages.WF {𝒱} [DecidableEq 𝒱] (Γ : TypeContext 𝒱) : Stages 𝒱 → Prop
  | instr is => is.WF Γ
  | asserts as => ∀ s' ∈ as, s'.WF Γ

noncomputable def Stages.denote (Γ : TypeContext ZFSet) (s : Stages ZFSet) (wf : s.WF Γ) : ZFSet.ZFBool :=
  go Γ s wf ⊤
where go (Γ : TypeContext ZFSet) (s : Stages ZFSet) (wf : s.WF Γ) (acc : ZFSet.ZFBool) : ZFSet.ZFBool :=
  match s with
  | instr is => is.denote Γ (by unfold WF at wf; exact wf)
  | asserts [] => acc
  | asserts ((instr is) :: as) =>
    have wf' : (asserts as).WF Γ := by
      unfold WF at wf ⊢
      intro s' hs'
      exact wf s' (List.mem_cons_of_mem _ hs')
    have wf'' : is.WF Γ := by
      unfold WF at wf
      specialize wf (.instr is) List.mem_cons_self
      unfold WF at wf
      exact wf
    go Γ (asserts as) wf' (is.denote Γ wf'')
  | asserts ((asserts as) :: ass) =>
    have wf' : (asserts as).WF Γ := by
      unfold WF at wf
      specialize wf (asserts as) List.mem_cons_self
      exact wf
    have wf'' : (asserts ass).WF Γ := by
      unfold WF at wf ⊢
      intro s hs
      exact wf s (List.mem_cons_of_mem _ hs)
    (go Γ (asserts as) wf' acc) ⋀ (go Γ (asserts ass) wf'' acc)

end Denotation

end PHOAS

end SMT
