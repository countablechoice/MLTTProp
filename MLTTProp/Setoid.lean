import «MLTTProp».Signature

set_option pp.beta true

namespace Setoid

def Con := (U : Type) × Setoid U

structure Ty (Γ : Con) where
  U : Γ.1 → Type
  r : ∀ {γ₀ γ₁}, Γ.2.r γ₀ γ₁ → U γ₀ → U γ₁ → Prop
  reflR : ∀ {γ} (α : U γ), r (Γ.2.iseqv.refl γ) α α
  symmR : ∀ {γ₀ γ₁ γ₀₁} {α₀ : U γ₀} {α₁ : U γ₁},
    r γ₀₁ α₀ α₁ → r (Γ.2.iseqv.symm γ₀₁) α₁ α₀
  transR : ∀ {γ₀ γ₁ γ₂ γ₀₁ γ₁₂} {α₀ : U γ₀} {α₁ : U γ₁} {α₂ : U γ₂},
    r γ₀₁ α₀ α₁ → r γ₁₂ α₁ α₂ → r (Γ.2.iseqv.trans γ₀₁ γ₁₂) α₀ α₂
  coe : ∀ {γ₀ γ₁}, Γ.2.r γ₀ γ₁ → U γ₀ → U γ₁
  coh : ∀ {γ₀ γ₁} (γ₀₁ : Γ.2.r γ₀ γ₁) (α : U γ₀), r γ₀₁ α (coe γ₀₁ α)

namespace Ty

def coeRev (A : Ty Γ) (γ₀₁ : Γ.2.r γ₀ γ₁) (t : A.U γ₁) : A.U γ₀ :=
  A.coe (Γ.2.symm γ₀₁) t

def cohRev (A : Ty Γ) (γ₀₁ : Γ.2.r γ₀ γ₁) (t : A.U γ₁) :
  A.r γ₀₁ (A.coeRev γ₀₁ t) t :=
  A.symmR (A.coh _ t)

end Ty

structure Subst (Γ Δ : Con) where
  F : Γ.1 → Δ.1
  r : ∀ {γ₀ γ₁}, Γ.2.r γ₀ γ₁ → Δ.2.r (F γ₀) (F γ₁)

structure Tm (Γ : _) (A : Ty Γ) where
  F : ∀ γ, A.U γ /- when doing PERs we will likely  need a γ≈γ here -/
  r : ∀ γ₀₁, A.r γ₀₁ (F γ₀) (F γ₁)
  
instance base : Base Con where
  Ty := Ty
  Sub := Subst
  Tm := Tm
  nil := ⟨Unit, { r := λ _ _ => True, iseqv := by constructor<;>(intros;constructor) }⟩
  snoc Γ A := ⟨(γ : Γ.1) × A.U γ, {
     r := λ γ₀ γ₁ => ∃ γ₀₁, A.r γ₀₁ γ₀.2 γ₁.2
     iseqv := by
       constructor
       · intro ⟨γ, _⟩
         exists Γ.2.iseqv.refl γ
         apply A.reflR
       · intro ⟨γ₀, _⟩ ⟨γ₁, _⟩ ⟨γ₀₁, _⟩
         exists Γ.2.iseqv.symm γ₀₁
         apply A.symmR<;>assumption
       · intro ⟨γ₀, _⟩ ⟨γ₁, _⟩ ⟨γ₂, _⟩ ⟨γ₀₁, _⟩ ⟨γ₁₂, _⟩
         exists Γ.2.iseqv.trans γ₀₁ γ₁₂
         apply A.transR<;>assumption
   }⟩
  subTy A δ := {
    U := λ γ => A.U (δ.F γ)
    r := λ γ₀₁ α₀ α₁ => A.r (δ.r γ₀₁) α₀ α₁
    reflR := by
      intros
      apply A.reflR
    symmR := by
      intros
      apply A.symmR;assumption
    transR := by
      intros
      apply A.transR<;>assumption
    coe := λ γ₀₁ α => A.coe (δ.r γ₀₁) α 
    coh := by
      intros
      apply A.coh
  }
  idSub Γ := { F := id, r := id }
  compSub δ ν := { F := δ.F ∘ ν.F, r := δ.r ∘ ν.r }
  endSub := { F := λ _ => (), r := by intros; constructor }
  snocSub δ t := {
    F := λ γ => ⟨δ.F γ, t.F γ⟩ 
    r := by
      intros;simp
      constructor
      apply t.r; assumption
  }
  weaken δ := {
    F := λ γ => (δ.F γ).1
    r := by
      intros _ _ a
      cases δ.r a
      assumption
  }
  subX δ := {
    F := λ γ => (δ.F γ).2
    r := by
      intros _ _ a
      cases δ.r a
      assumption
  }
  subTm t δ := {
    F := λ γ => t.F (δ.F γ)
    r := by
      intros
      apply t.r
  }
  subTyId := by intros; rfl
  subTyComp := by intros; rfl

instance pi : PiType Con where
  Pi {Γ} A B := {
    U := λ γ => { f : ∀ x : (A.U γ), B.U ⟨γ, x⟩ //
           ∀ x₀ x₁ (x₀₁ : A.r (Γ.2.refl γ) x₀ x₁),
           B.r (γ₀:=⟨γ, _⟩) (γ₁:=⟨γ, _⟩) ⟨Γ.2.refl γ, x₀₁⟩ (f x₀) (f x₁) }
    r := λ {γ₀ γ₁} γ₀₁ t₀ t₁ => ∀ x₀ x₁ (x₀₁ : A.r γ₀₁ x₀ x₁),
           B.r (γ₀:=⟨γ₀, _⟩) (γ₁:=⟨γ₁, _⟩) ⟨γ₀₁, x₀₁⟩ (t₀.1 x₀) (t₁.1 x₁)
    reflR := by simp; intro _ ⟨_, _⟩; assumption
    symmR := by
      simp; intro _ _ _ ⟨f, Hf⟩ ⟨g, Hg⟩ t₀₁ x₁ x₀ x₁₀
      simp at *
      apply B.symmR
      apply t₀₁
      apply A.symmR
      assumption
    transR := by
      simp; intro _ _ _ _ _ ⟨f, Hf⟩ ⟨g, Hg⟩ ⟨h, Hh⟩ t₀₁ t₁₂ x₀ x₂ x₀₂
      simp at *
      apply B.transR
      · apply t₀₁
        apply A.coh
      · apply t₁₂
        apply A.transR
        · apply A.symmR
          apply A.coh
        · assumption
    coe := λ {γ₀ γ₁} γ₀₁ t => ⟨
      λ x => B.coe (γ₀:=⟨γ₀, _⟩) ⟨γ₀₁, A.cohRev γ₀₁ x⟩
                (t.1 (A.coeRev γ₀₁ x)),
      by
        intros _ _ x₁₂
        apply B.transR
        · apply B.symmR
          apply B.coh
        · apply (flip B.transR)
          · apply B.coh
          · apply t.2 
            apply A.transR
            · apply A.cohRev
            · apply A.transR
              · apply x₁₂
              · apply A.symmR
                apply A.cohRev
                assumption
            assumption

      ⟩
    coh := by
      simp; intro _ _ γ₀₁ ⟨f, Hf⟩ _ _ x₀₁
      apply B.transR
      · apply Hf
        apply (A.transR x₀₁)
        apply A.symmR
        apply (A.cohRev γ₀₁)
      · apply B.coh
  }
  lambda t := {
    F := λ γ => ⟨λ x => t.1 ⟨γ, x⟩, 
      by intros; apply t.r ⟩
    r := by simp; intros; apply t.r
  }
  apX t := {
    F := λ γx => (t.1 γx.1).1 γx.2
    r := by
      cases t
      simp at *
      rename_i f Hf
      intro ⟨γ₀, x₀⟩ ⟨γ₁, x₁⟩ ⟨γ₀₁, x₀₁⟩
      simp at *
      apply (Hf γ₀₁ x₀ x₁ x₀₁)
  }
  Piβ := by intros; rfl
  Piη := by intros; rfl

instance sigma : SigmaType Con where
  Sigma A B := {
    U := λ γ => Σ x : (A.U γ), B.U ⟨γ, x⟩
    r := λ {γ₀ γ₁} γ₀₁ uv₀ uv₁ => ∃ u₀₁ : A.r γ₀₁ uv₀.1 uv₁.1,
      B.r (γ₀:=⟨γ₀, _⟩) (γ₁:=⟨γ₁, _⟩) ⟨γ₀₁, u₀₁⟩ uv₀.2 uv₁.2
    reflR := by
      intro _ ⟨u, v⟩
      exists (A.reflR u)
      apply B.reflR
    symmR := by
      intro _ _ _ ⟨_, _⟩ ⟨_, _⟩ ⟨u₀₁, v₀₁⟩
      exists (A.symmR u₀₁)
      apply B.symmR;assumption
    transR := by
      intro _ _ _ _ _ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨u₀₁, v₀₁⟩ ⟨u₁₂, v₁₂⟩
      exists (A.transR u₀₁ u₁₂)
      apply B.transR<;>assumption
    coe := λ {γ₀ γ₁} γ₀₁ t => ⟨A.coe γ₀₁ t.1,
      B.coe (γ₀:=⟨γ₀, _⟩) ⟨γ₀₁, A.coh γ₀₁ t.1⟩ t.2⟩
    coh := by
      simp
      intro γ₀ γ₁ γ₀₁ ⟨u, v⟩
      exists (A.coh γ₀₁ u)
      apply (B.coh (γ₀:=⟨γ₀, _⟩) (γ₁:=⟨γ₁, _⟩) ⟨γ₀₁, A.coh _ u⟩ v)
  }
  pair u v := {
    F := λ γ => ⟨u.1 γ, v.1 γ⟩
    r := λ γ₀₁ => ⟨u.r γ₀₁, v.r γ₀₁⟩
  }
  proj₀ t := {
    F := λ γ => (t.1 γ).1
    r := λ γ₀₁ => (t.r γ₀₁).1
  }
  proj₁ {Γ A B} t := {
    F := λ γ => (t.1 γ).2
    r := λ γ₀₁ => (t.r γ₀₁).2
  }
  Sigmaβ₀ := by intros; rfl
  Sigmaβ₁ := by intros; rfl
  Sigmaη := by intros; rfl

def 𝔹 {Γ} : Ty Γ := {
  U := λ _ => Bool
  r := λ _ t₀ t₁ => 
    match t₀, t₁ with
    | true, true => True
    | false, false => True
    | _, _ => False
  reflR := by intro _ t;cases t<;>constructor
  symmR := by intros _ _ _ t₀ t₁ _;cases t₀<;>cases t₁<;>
    first | contradiction | constructor
  transR := by
    intro _ _ _ _ _ t₀ t₁ t₂ _ _
    cases t₀<;>cases t₁<;>cases t₂<;>
    first | contradiction | constructor
  coe := λ _ t => t
  coh := by
    intros
    rename_i t
    simp
    cases t<;>constructor
}

instance bool : BoolType Con where
  𝔹 := 𝔹
  tt := {
    F := λ _ => true
    r := by intros; constructor
  }
  ff := {
    F := λ _ => false
    r := by intros; constructor
  }
  ifThenElse {Γ C} t u v := {
    F := λ γ => @Bool.casesOn (λ b => C.U ⟨γ, b⟩) (t.F γ) (v.F γ) (u.F γ) 
    r := by
      intro γ₀ γ₁ γ₀₁
      generalize t.r γ₀₁ = t₀₁
      revert t₀₁
      show (∀ t₀₁, C.r ⟨_, t₀₁⟩
        (@Bool.casesOn (λ b => C.U ⟨γ₀, b⟩) (t.1 γ₀) (Tm.F v γ₀) (Tm.F u γ₀))
        (@Bool.casesOn (λ b => C.U ⟨γ₁, b⟩) (t.1 γ₁) (Tm.F v γ₁) (Tm.F u γ₁)))
      cases t.1 γ₀<;>cases t.1 γ₁<;>intros<;>try { contradiction }
      · apply v.r; assumption
      · apply u.r; assumption
  }
  Boolβtt := by intros; rfl
  Boolβff := by intros; rfl

instance prop : PropType Con where
  PROP := {
    U := λ _ => Prop
    r := λ _ A B => A ↔ B
    reflR := λ _ => ⟨id, id⟩
    symmR := λ ⟨x₀, x₁⟩ => ⟨x₁, x₀⟩
    transR := λ ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ => ⟨y₀ ∘ x₀, x₁ ∘ y₁⟩
    coe := λ _ x => x
    coh := λ _ _ => ⟨id, id⟩
  }
  elP a := {
    U := λ γ => PLift (a.1 γ)
    r := λ _ _ _ => True
    reflR := λ _ => ⟨⟩
    symmR := λ _ => ⟨⟩
    transR := λ _ _ => ⟨⟩
    coe := λ γ₀₁ ⟨x⟩ => ⟨(a.r γ₀₁).1 x⟩
    coh := λ _ _ => ⟨⟩
  }
  irr := by 
    intros _ _ _ v
    show ⟨λ γ => ⟨(v.F γ).1⟩, v.r⟩ = v
    rfl
  subPROP := by intros; rfl
  subElP := by intros; rfl
  piP A b := {
    F := λ γ => ∀ x : (A.1 γ), b.1 ⟨γ, x⟩
    r := λ {γ₀ γ₁} γ₀₁ => ⟨
      λ f x => (b.r (γ₀:=⟨γ₀,_⟩) (γ₁:=⟨γ₁,_⟩)
        ⟨γ₀₁, A.cohRev γ₀₁ x⟩).1 (f (A.coeRev γ₀₁ x)),
      λ f x => (b.r (γ₀:=⟨γ₀,_⟩) (γ₁:=⟨γ₁,_⟩)
        ⟨γ₀₁, A.coh γ₀₁ x⟩).2 (f (A.coe γ₀₁ x))
      ⟩
  }
  lambdaP t := {
    F := λ γ => PLift.up (λ x => (t.1 ⟨γ, x⟩).down)
    r := by intros; trivial
  }
  apXP t := {
    F := λ ⟨γ, x⟩ => PLift.up ((t.1 γ).down x)
    r := by intros; trivial
  }
  sigmaP a b := {
    F := λ γ => ∃ x : (a.1 γ), b.1 ⟨γ, PLift.up x⟩
    r := λ {γ₀ γ₁} γ₀₁ => ⟨
      λ ⟨x, y⟩ => ⟨(a.r γ₀₁).1 x,
        ((b.r (γ₀:=⟨γ₀,_⟩) (γ₁:=⟨γ₁,_⟩) ⟨γ₀₁, True.intro⟩).1 y)⟩,
      λ ⟨x, y⟩ => ⟨(a.r γ₀₁).2 x,
        ((b.r (γ₀:=⟨γ₀,_⟩) (γ₁:=⟨γ₁,_⟩) ⟨γ₀₁, True.intro⟩).2 y)⟩,
      ⟩
  }
  pairP u v := {
    F := λ γ => ⟨(u.1 γ).down, (v.1 γ).down⟩
    r := by intros; trivial
  }
  proj₀P t := {
    F := λ γ => PLift.up (t.1 γ).down.1
    r := by intros; trivial
  }
  proj₁P t := {
    F := λ γ => PLift.up (t.1 γ).down.2
    r := by intros; trivial
  }
  top := {
    F := λ _ => True
    r := λ _ => ⟨id, id⟩
  }
  triv := {
    F := λ _ => PLift.up True.intro
    r := by intros; trivial
  }
  bottom := {
    F := λ _ => False
    r := λ _ => ⟨id, id⟩
  }
  exfalso t := {
    F := λ γ => False.elim (t.1 γ).down
    r := by
      intro γ₀ _ _
      let X := (t.1 γ₀).down
      cases X
  }
  subBottom := by intros; rfl

end Setoid

def SetoidModel : Sig where
  Con := Setoid.Con
  base := Setoid.base
  pi := Setoid.pi
  sigma := Setoid.sigma
  bool := Setoid.bool
  prop := Setoid.prop

#print axioms SetoidModel
