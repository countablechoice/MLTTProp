import «MLTTProp».Signature

namespace Model

instance base : Base Type where
  Ty Γ := Γ → Type
  Sub Γ Δ := Γ → Δ
  Tm Γ A := ∀ γ : Γ, A γ
  nil := Unit
  snoc Γ A := (γ : Γ) × A γ
  subTy A δ := A ∘ δ
  idSub Γ := id 
  compSub δ ν := δ ∘ ν
  endSub _ := ()
  snocSub δ t γ := ⟨δ γ, t γ⟩ 
  weaken δ γ := (δ γ).1
  subX δ γ := (δ γ).2
  subTm t δ γ := t (δ γ)
  subTyId := by intros; rfl
  subTyComp := by intros; rfl

instance pi : PiType Type where 
  Pi A B γ := ∀ x : (A γ), B ⟨γ, x⟩
  lambda t γ x := t ⟨γ, x⟩
  apX t := λ ⟨γ, x⟩ => t γ x
  Piβ := by intros; rfl
  Piη := by intros; rfl

instance sigma : SigmaType Type where 
  Sigma A B γ := Σ x : (A γ), B ⟨γ, x⟩
  pair u v γ := ⟨u γ, v γ⟩
  proj₀ t γ := (t γ).1
  proj₁ t γ := (t γ).2
  Sigmaβ₀ := by intros; rfl
  Sigmaβ₁ := by intros; rfl
  Sigmaη := by intros; rfl

instance bool : BoolType Type where 
  𝔹 _ := Bool
  tt _ := true
  ff _ := false
  ifThenElse {Γ C} t u v γ := 
    @Bool.casesOn (λ b => C ⟨γ, b⟩) (t γ) (v γ) (u γ)
  Boolβtt := by intros; rfl
  Boolβff := by intros; rfl

instance prop : PropType Type where 
  PROP _ := Prop
  elP a γ := PLift (a γ)
  irr := by 
    intros _ _ _ v
    show (λ γ => ⟨(v γ).1⟩) = v
    rfl
  subPROP := by intros; rfl
  subElP := by intros; rfl
  piP A b γ := ∀ x : (A γ), b ⟨γ, x⟩
  lambdaP t γ := PLift.up (λ x => (t ⟨γ, x⟩).down)
  apXP t := λ ⟨γ, x⟩ => PLift.up ((t γ).down x)
  sigmaP a b γ := ∃ x : (a γ), b ⟨γ, PLift.up x⟩
  pairP u v γ := ⟨(u γ).down, (v γ).down⟩
  proj₀P t γ := PLift.up (t γ).down.1
  proj₁P t γ := PLift.up (t γ).down.2
  top _ := True
  triv _ := PLift.up True.intro
  bottom _ := False
  exfalso t γ := False.elim (t γ).down
  subBottom := by intros; rfl

end Model

def Model : Sig where
  Con := Type
  base := Model.base
  pi := Model.pi
  sigma := Model.sigma
  bool := Model.bool
  prop := Model.prop

#print axioms Model
