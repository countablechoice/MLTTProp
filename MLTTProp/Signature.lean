class Base (Con : Type 1) where
  Ty : Con → Type 1
  Sub : Con → Con -> Type 0
  Tm : ∀ Γ : Con, Ty Γ → Type 0

  /- Substitution calculus -/
  nil : Con
  snoc : ∀ Γ : Con, Ty Γ → Con
  subTy : ∀ {Γ Δ}, Ty Δ → Sub Γ Δ → Ty Γ
  idSub : ∀ Γ, Sub Γ Γ
  compSub : ∀ {Γ Θ Δ}, Sub Θ Δ → Sub Γ Θ → Sub Γ Δ
  endSub : ∀ {Γ}, Sub Γ nil
  snocSub : ∀ {Γ Δ A} (δ : Sub Γ Δ), Tm Γ (subTy A δ) → Sub Γ (snoc Δ A)
  weaken : ∀ {Γ Δ A}, Sub Γ (snoc Δ A) → Sub Γ Δ
  subX : ∀ {Γ Δ A} (δ : Sub Γ (snoc Δ A)), Tm Γ (subTy A (weaken δ))
  subTm : ∀ {Γ Δ A}, Tm Δ A → ∀ (δ : Sub Γ Δ), Tm Γ (subTy A δ)
  subTyId : ∀ {Γ A}, subTy A (idSub Γ) = A
  subTyComp : ∀ {Γ Θ Δ} {δ : Sub Θ Δ} {ν : Sub Γ Θ} {A},
    subTy A (compSub δ ν) = (subTy (subTy A δ) ν)
  /- :TODO: more rules -/

notation "∅" => Base.nil
notation "(" Γ ", x⦂" A ")" => Base.snoc Γ A
notation:1024 A:1024 "[" ρ "]" => Base.subTy A ρ
notation "(" ρ ", x↦ " t ")" => Base.snocSub ρ t
notation:1024 t:1024 "[" ρ "]" => Base.subTm t ρ

def Base.subTyT {Con} [Base Con] {Γ:Con} {A} (B : Ty (snoc Γ A))
    (u : Tm _ A) : Ty Γ :=
  B[(idSub _, x↦ Eq.symm (subTyId (A:=A)) ▸ u)]

def Base.subTmT {Con} [Base Con] {Γ:Con} {A} {B : Ty (snoc Γ A)}
    (t : Tm _ B) (u : Tm _ A) : Tm Γ (subTyT B u) :=
  t[(idSub _, x↦ Eq.symm (subTyId (A:=A)) ▸ u)]

notation:1024 A:1024 "[x↦ " u "]" => Base.subTyT A u
notation:1024 t:1024 "[x↦ " u "]" => Base.subTmT t u

class PiType (Con : Type 1) [Base Con] where
  Pi : ∀ {Γ : Con} (A : Base.Ty Γ), Base.Ty (Γ, x⦂A) → Base.Ty Γ
  lambda : ∀ {Γ A B}, Base.Tm (Γ, x⦂A) B → Base.Tm Γ (Pi A B)
  apX : ∀ {Γ A B},  Base.Tm Γ (Pi A B) → Base.Tm (Γ, x⦂A) B 
  Piβ : ∀ {Γ A B} (t : Base.Tm (Γ, x⦂A) B), apX (lambda t) = t
  Piη : ∀ {Γ A B} (t : Base.Tm Γ (Pi A B)), (lambda (apX t)) = t
  /- :TODO: more rules -/

class SigmaType (Con : Type 1) [Base Con] where
  Sigma : ∀ {Γ : Con} A, Base.Ty (Γ, x⦂A) → Base.Ty Γ
  pair : ∀ {Γ A B} (u:Base.Tm Γ A),
         Base.Tm Γ B[x↦ u] →
         Base.Tm Γ (Sigma A B)
  proj₀ : ∀ {Γ A B}, Base.Tm Γ (Sigma A B) → Base.Tm Γ A 
  proj₁ : ∀ {Γ A B} (t : Base.Tm Γ (Sigma A B)),
          Base.Tm Γ B[x↦ proj₀ t] 
  Sigmaβ₀ : ∀ {Γ A} {B : Base.Ty (Γ, x⦂A)} (u : Base.Tm Γ A)
            (v : Base.Tm Γ B[x↦ u]),
            proj₀ (pair u v) = u
  Sigmaβ₁ : ∀ {Γ A} {B : Base.Ty (Γ, x⦂A)} (u : Base.Tm Γ A)
            (v : Base.Tm Γ B[x↦ u]),
            Sigmaβ₀ u v ▸ proj₁ (pair u v) = v
  Sigmaη : ∀ {Γ A B} (t : Base.Tm Γ (Sigma A B)), (pair (proj₀ t) (proj₁ t)) = t
  /- :TODO: more rules -/

class BoolType (Con : Type 1) [Base Con] where
  𝔹 : ∀ {Γ : Con}, Base.Ty Γ
  tt : ∀ {Γ : Con}, Base.Tm Γ 𝔹
  ff : ∀ {Γ : Con}, Base.Tm Γ 𝔹
  ifThenElse : ∀ {Γ : Con} {C : Base.Ty (Γ, x⦂𝔹)} (t : Base.Tm Γ 𝔹),
    Base.Tm Γ C[x↦ tt] →
    Base.Tm Γ C[x↦ ff] →
    Base.Tm Γ C[x↦ t]
  Boolβtt : ∀ {Γ} {C : Base.Ty (Γ, x⦂𝔹)}
    (u : Base.Tm Γ C[x↦ tt])
    (v : Base.Tm Γ C[x↦ ff]),
    ifThenElse tt u v = u
  Boolβff : ∀ {Γ} {C : Base.Ty (Γ, x⦂𝔹)}
    (u : Base.Tm Γ C[x↦ tt])
    (v : Base.Tm Γ C[x↦ ff]),
    ifThenElse ff u v = v
  /- :TODO: more rules -/

class PropType (Con : Type 1) [Base Con] where
  PROP : ∀ {Γ : Con}, Base.Ty Γ
  elP : ∀ {Γ}, Base.Tm Γ PROP → Base.Ty Γ
  irr : ∀ {Γ a} {u v : Base.Tm Γ (elP a)}, u = v
  subPROP : ∀ {Γ Δ} {ν : Base.Sub Γ Δ}, PROP[ν] = PROP
  subElP : ∀ {Γ Δ a} {ν : Base.Sub Γ Δ}, (elP a)[ν] = elP (subPROP ▸ a[ν])

  piP : ∀ {Γ} (A : Base.Ty Γ), Base.Tm (Γ, x⦂ A) PROP → Base.Tm Γ PROP
  lambdaP : ∀ {Γ A b}, Base.Tm (Γ, x⦂A) (elP b) → Base.Tm Γ (elP (piP A b))
  apXP : ∀ {Γ A b},  Base.Tm Γ (elP (piP A b)) → Base.Tm (Γ, x⦂A) (elP b) 

  sigmaP : ∀ {Γ} (a : Base.Tm Γ PROP), Base.Tm (Γ, x⦂elP a) PROP → Base.Tm Γ PROP
  pairP : ∀ {Γ a} {b : Base.Tm (Γ, x⦂elP a) PROP} (u : Base.Tm Γ (elP a)),
          Base.Tm Γ (elP (subPROP ▸ (b[x↦ u]))) →
          Base.Tm Γ (elP (sigmaP a b))
  proj₀P : ∀ {Γ a b}, Base.Tm Γ (elP (sigmaP a b)) → Base.Tm Γ (elP a) 
  proj₁P : ∀ {Γ a b} (t : Base.Tm Γ (elP (sigmaP a b))),
           Base.Tm Γ (elP (subPROP ▸ (b[x↦ proj₀P t])))

  top : ∀ {Γ}, Base.Tm Γ PROP
  triv : ∀ {Γ}, Base.Tm Γ (elP top)

  bottom : ∀ {Γ}, Base.Tm Γ PROP
  exfalso : ∀ {Γ} {C : Base.Ty Γ}, Base.Tm Γ (elP bottom) → Base.Tm Γ C
  subBottom : ∀ {Γ Δ} {ν : Base.Sub Γ Δ}, subPROP ▸ bottom[ν] = bottom 
  /- :TODO: more rules -/

notation "⊤" => PropType.top
notation "⊥" => PropType.bottom

structure Sig where
  Con : Type 1
  base : Base Con 
  pi : PiType Con
  sigma: SigmaType Con
  bool : BoolType Con
  prop : PropType Con

attribute [instance] Sig.base
attribute [instance] Sig.pi
attribute [instance] Sig.sigma
attribute [instance] Sig.bool
attribute [instance] Sig.prop
instance : CoeSort Sig (Type 1) where
  coe sig := sig.Con

namespace Example

theorem substSubst {A} {a b c : A} (motive : A -> Type)
    (eq1 : a = b) (eq2 : b = c) (eq3 : a = c) (t : motive a) :
    eq2 ▸ eq1 ▸ t = eq3 ▸ t := by
  revert eq2 eq3
  cases eq1
  simp

theorem substSubstRev {A} {a b : A} (motive : A -> Type)
    (eq1 : a = b) (eq2 : b = a) (t : motive a) :
    eq2 ▸ eq1 ▸ t = t := by
  rw [substSubst]
  rfl

variable {M : Sig}
open Base
open BoolType
open PropType

theorem degenerate (ttisff : tt (Γ:=(∅:M)) = ff) {Γ : M} {A} :
    Tm Γ A := by
  apply exfalso
  rw [← subBottom (ν := endSub)]
  rw [← subElP]
  apply subTm
  let subC (t : Tm (∅:M) 𝔹) : Sub (∅:M) (∅, x⦂𝔹) :=
     (idSub _, x↦ Eq.symm (subTyId (Γ:=(∅:M))) ▸ t)
  let castC {t} : PROP[x↦ t] = PROP := subPROP (ν := subC t)
  let revCastC {t} := Eq.symm (@castC t)
  have ffeq : ⊥ = castC ▸ ifThenElse ff (revCastC ▸ ⊤) (revCastC ▸ ⊥) := by
    rw [Boolβff]
    rw [substSubstRev]
  rw [ffeq]
  apply (Eq.rec (motive := λ (X : M.base.Tm ∅ M.bool.𝔹) _ =>
   (Tm (∅:M)
     (elP (castC ▸ ifThenElse X (revCastC ▸ ⊤) (revCastC ▸ ⊥)))))
   _ ttisff)
  have tteq : ⊤ =
      castC ▸ ifThenElse tt (revCastC ▸ ⊤) (revCastC ▸ ⊥) := by
    rw [Boolβtt]
    rw [substSubstRev]
  rw [← tteq]
  apply triv

end Example
