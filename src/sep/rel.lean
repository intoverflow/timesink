/- Relations between separation algebras
 -
 -/
import .basic

namespace Sep
universes ℓ₁ ℓ₂ ℓ₃ ℓ₄

/- Relations between separation algebras
 -
 -/
def Rel (A₁ : Alg.{ℓ₁}) (A₂ : Alg.{ℓ₂})
  := A₁.τ → Set A₂

def FunRel {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}}
    (f : A₁.τ → A₂.τ)
  : Rel A₁ A₂
 := λ x y, y = f x

def InvFunRel {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}}
    (f : A₁.τ → A₂.τ)
  : Rel A₂ A₁
 := λ y x, y = f x

instance Rel_has_le {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} : has_le (Rel A₁ A₂)
 := { le := λ r₁ r₂, ∀ x, r₁ x ⊆ r₂ x
    }

def Rel.Refl {A : Alg.{ℓ₁}} (r : Rel A A)
  : Prop
 := ∀ x, r x x

def Rel.Trans {A : Alg.{ℓ₁}} (r : Rel A A)
  : Prop
 := ∀ x₁ x₂ x₃, r x₁ x₂ → r x₂ x₃ → r x₁ x₃

def Rel.WellDefined {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {x} {y₁ y₂}
      (R₁ : r x y₁)
      (R₂ : r x y₂)
    , y₁ = y₂

def Rel.Total {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ x, ∃ y, r x y

def Rel.Surj {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ y, ∃ x, r x y

-- An equivalence relation on relations; happens to imply equality but is easier to prove
def RelEq {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r₁ r₂ : Rel A₁ A₂) : Prop
  := ∀ x₁ x₂, r₁ x₁ x₂ ↔ r₂ x₁ x₂

def RelEq.refl {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : RelEq r r
  := λ x₁ x₂, by trivial

def RelEq.symm {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r₁ r₂ : Rel A₁ A₂}
    (H : RelEq r₁ r₂)
  : RelEq r₂ r₁
  := λ x₁ x₂, iff.symm (H _ _)

def RelEq.trans {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r₁ r₂ r₃ : Rel A₁ A₂}
    (H₁₂ : RelEq r₁ r₂) (H₂₃ : RelEq r₂ r₃)
  : RelEq r₁ r₃
  := λ x₁ x₂, iff.trans (H₁₂ _ _) (H₂₃ _ _)

def RelEq.to_eq {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r₁ r₂ : Rel A₁ A₂}
  : RelEq r₁ r₂ → r₁ = r₂
 := begin
      intro H,
      apply funext, intro x₁,
      apply funext, intro x₂,
      apply iff.to_eq,
      apply H
    end


-- The identity relation
def Alg.IdRel (A : Alg.{ℓ₁})
  : Rel A A
 := λ x, eq x

def Rel.Reflexive {A : Alg.{ℓ₁}} (r : Rel A A) : Prop
  := A.IdRel ≤ r

def Rel.Discrete {A : Alg.{ℓ₁}} (r : Rel A A) : Prop
  := r ≤ A.IdRel

-- Composition of relations
def Rel_comp {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {A₃ : Alg.{ℓ₃}}
  : Rel A₂ A₃ → Rel A₁ A₂ → Rel A₁ A₃
:= λ r₂ r₁ x₁ x₃
   , ∃ x₂, r₁ x₁ x₂ ∧ r₂ x₂ x₃

reserve infixr ` ∘ ` : 100
infixr ` ∘ ` := λ {A₁} {A₂} {A₃}
                  (r₂₃ : Rel A₂ A₃) (r₁₂ : Rel A₁ A₂)
                , Rel_comp r₂₃ r₁₂

def Rel_comp.id_l {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}}
    (r : Rel A₁ A₂)
  : Rel_comp A₂.IdRel r = r
 := begin
      apply RelEq.to_eq,
      intros x₀ y₀,
      apply iff.intro,
      { intro H, cases H with y H,
        cases H with R E,
        simp [Alg.IdRel] at E,
        subst E, assumption
      },
      { intro H,
        existsi y₀,
        exact and.intro H rfl
      }
    end

def Rel_comp.id_r {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}}
    (r : Rel A₁ A₂)
  : Rel_comp r A₁.IdRel = r
 := begin
      apply RelEq.to_eq,
      intros x₀ y₀,
      apply iff.intro,
      { intro H,
        cases H with y H,
        cases H with E R,
        simp [Alg.IdRel] at E,
        subst E, assumption
      },
      { intro H,
        existsi x₀,
        exact and.intro rfl H
      }
    end

def Rel_comp.congr {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {A₃ : Alg.{ℓ₃}}
    {s₁ s₂ : Rel A₂ A₃} {r₁ r₂ : Rel A₁ A₂}
    (Es : s₁ = s₂) (Er : r₁ = r₂)
  : s₁ ∘ r₁ = s₂ ∘ r₂
 := begin subst Es, subst Er end

-- Composition is associative
def Rel_comp.assoc {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {A₃ : Alg.{ℓ₃}} {A₄ : Alg.{ℓ₄}}
    {r₃₄ : Rel A₃ A₄} {r₂₃ : Rel A₂ A₃} {r₁₂ : Rel A₁ A₂}
  : ((r₃₄ ∘ r₂₃) ∘ r₁₂) = (r₃₄ ∘ (r₂₃ ∘ r₁₂))
 := RelEq.to_eq
     (λ x₁ x₄
      , iff.intro
          (λ H, begin
                  cases H with x₂ H, cases H with H₁₂ H,
                  cases H with x₃ H, cases H with H₂₃ H₃₄,
                  existsi x₃, refine and.intro _ H₃₄,
                  existsi x₂, exact and.intro H₁₂ H₂₃
                end)
          (λ H, begin
                  cases H with x₃ H, cases H with H H₃₄,
                  cases H with x₂ H, cases H with H₁₂ H₂₃,
                  existsi x₂, apply and.intro H₁₂,
                  existsi x₃, exact and.intro H₂₃ H₃₄
                end))


-- The complement relation
def Rel.Compl {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Rel A₁ A₂
 := λ x y, ¬ r x y

def Rel.Compl.Involutive {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : r.Compl.Compl = r
 := begin
      apply funext, intro x,
      apply funext, intro y,
      simp [Rel.Compl],
      apply iff.to_eq,
      apply iff.intro,
      { intro H₁,
        apply classical.by_contradiction,
        intro H₂,
        exact H₁ H₂
      },
      { intros H₁ H₂,
        exact H₂ H₁
      }
    end


-- The function induced by a relation
def Rel.Fn {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂)
  : Set A₁ → Set A₂
:= λ X, λ y, ∃ x, X x ∧ f x y

def Rel.Fn.show {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {f : Rel A₁ A₂}
    {X : Set A₁} {y} (x) (Hx : x ∈ X) (Hf : f x y)
  : y ∈ f.Fn X
 := exists.intro x (and.intro Hx Hf)

def Rel.Fn.elim {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {f : Rel A₁ A₂}
    {X : Set A₁} {y} (H : y ∈ f.Fn X)
    {P : Prop}
    (C : ∀ {x}, x ∈ X → f x y → P)
  : P
 := begin cases H with x H, exact C H.1 H.2 end

def Rel.Fn.subset {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂)
  : ∀ (X₁ X₂ : Set A₁)
    , X₁ ⊆ X₂ → f.Fn X₁ ⊆ f.Fn X₂
 := λ X₁ X₂ H y Hy
    , begin
        cases Hy with x Hx,
        existsi x,
        exact and.intro (H Hx.1) Hx.2
      end


-- The inverse image of the function induced by a relation
def Rel.FnInv {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Set A₂ → Set A₁
 := λ Y x, (∃ y, y ∈ Y ∧ r x y)

def Rel.FnInv.show {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {f : Rel A₁ A₂}
    {Y : Set A₂} {x} {y} (Hxy : f x y) (Hy : y ∈ Y)
  : x ∈ f.FnInv Y
:= exists.intro y (and.intro Hy Hxy)

def Rel.FnInv.elim {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    {Y : Set A₂} {x} (Hx : x ∈ r.FnInv Y)
    {P : Prop}
  : (∀ y, y ∈ Y → r x y → P)
  → P
 := begin
      intro C,
      { cases Hx with y Hy,
        exact C y Hy.1 Hy.2
      }
    end

def Rel.FnInv.subset {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : ∀ (Y₁ Y₂ : Set A₂)
    , Y₁ ⊆ Y₂ → r.FnInv Y₁ ⊆ r.FnInv Y₂
 := λ Y₁ Y₂ HYY x Hx
    , begin
        apply Rel.FnInv.elim Hx,
        { intros y Hy Rxy,
          apply Rel.FnInv.show Rxy (HYY Hy)
        }
      end

def Rel.FnInv.Empty {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : r.FnInv ∅ = ∅
 := begin
      apply funext, intro x,
      apply iff.to_eq, apply iff.intro,
      { intro H,
        cases H with y H,
        cases H with F Rxy,
        cases F
      },
      { intro H, cases H }
    end

-- The image of the function induced by a relation
def Rel.Im {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Set A₂
 := λ y, ∃ x, r x y

def Rel.FinIm {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Prop
 := ∀ x, ∃ (ys : list A₂.τ), (∀ y, r x y ↔ y ∈ ys)

-- Increasing elements
def Rel.increasing {A : Alg.{ℓ₁}} (r : Rel A A)
  : Set A
 := λ s, ∀ x y, A.join s x y → r x y


-- The proper domain of the function induced by a relation
def Rel.Dom {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Set A₁
 := λ x, ∃ y, r x y

def Rel.IdealDom {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {x₁ x₂ x₃} (Dx₁ : x₁ ∈ r.Dom) (Jx : A₁.join x₁ x₂ x₃)
    , x₃ ∈ r.Dom

def Total.IdealDom {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  (rT : r.Total)
  : r.IdealDom
 := begin intros x₁ x₂ x₃ Dx₁ Jx, apply rT end

def Rel.FnIdealDom {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := r.Dom.Ideal

def Rel.FnIdealDom_iff {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : r.FnIdealDom ↔ r.IdealDom
 := begin
      apply iff.intro,
      { intro rID, exact @rID },
      { intro rID, exact @rID }
    end


-- Fibers
def Rel.Fib {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) (y : A₂.τ)
  : Set A₁
 := λ x, r x y

def Rel.FinFib {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Prop
 := ∀ (y : A₂.τ), ∃ (xs : list A₁.τ), (r.Fib y = λ x, x ∈ xs)


-- The kernel of the function induced by a relation
def Rel.Ker {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Set A₁
 := λ x, ∀ y, ¬ r x y


def Rel.IdealKer {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {x₁ x₃}
    , A₁.Divides x₁ x₃
    → (∀ y₁, ¬ r x₁ y₁)
    → (∀ y₃, ¬ r x₃ y₃)

def Rel.FnIdealKer {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
  := r.Ker.Ideal

def Rel.FnIdealKerl_iff {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : r.FnIdealKer ↔ r.IdealKer
 := begin
      apply iff.intro,
      { intro rLinear,
        intros x₁ x₃ Dx₁x₃ Kx₁ y₃ Rx₃y₃,
        apply Dx₁x₃,
        { intros x₂ Jx,
          apply rLinear Kx₁ Jx,
          assumption
        },
        { intro E, subst E,
          exact Kx₁ _ Rx₃y₃
        }
      },
      { intro rLinear,
        intros x₁ x₂ x₃ Kx₁ Jx y₃ Rx₃y₃,
        refine rLinear _ Kx₁ _ Rx₃y₃,
        intros P C₁ C₂, exact C₁ Jx
      }
    end


def Rel.PrimeKer {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {x₁ x₂ x₃}
    , A₁.join x₁ x₂ x₃
    → (∀ y₃, ¬ r x₃ y₃)
    → (∀ y₁, ¬ r x₁ y₁) ∨ (∀ y₂, ¬ r x₂ y₂)

def Rel.FnPrimeKer {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
  := r.Ker.Prime

def Rel.FnPrimeKer_iff {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : r.FnPrimeKer ↔ r.PrimeKer
 := begin
      apply iff.intro,
      { intro rKP,
        intros x₁ x₂ x₃ Jx Kx₃,
        exact rKP _ _ _ Jx Kx₃
      },
      { intro rKP,
        intros x₁ x₂ x₃ Jx Kx₃,
        exact rKP Jx Kx₃
      }
    end


-- Preservation of ideals, join-closed sets, prime sets, division, etc
def Rel.FnComplSubAlgPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {S : Set A₂} (S_CSA : S.Compl.SubAlg)
    , (r.FnInv S).Compl.SubAlg


def Rel.FnJoinClosedPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {S : Set A₁} (SJC : S.JoinClosed)
    , (r.Fn S).JoinClosed


def Rel.FnWeakIdealPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
  := ∀ {I : Set A₂} (Iideal : I.WeakIdeal)
     , (r.FnInv I).WeakIdeal

def Rel.IdealPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
  := ∀ {x₁ x₂ x₃} {y₁}
     , A₁.join x₁ x₂ x₃ → r x₁ y₁
     → (r x₃ y₁) ∨ (∃ y₂ y₃, r x₃ y₃ ∧ A₂.join y₁ y₂ y₃)

def Rel.FnIdealPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
  := ∀ {I : Set A₂} (Iideal : I.Ideal)
     , (r.FnInv I).Ideal

def Rel.IdealPres_iff {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  : r.FnIdealPres ↔ r.IdealPres
 := begin
      apply iff.intro,
      { intro rIP,
        intros x₁ x₂ x₃ y₁ Jx Rx₁y₁,
        have Q₀ : x₁ ∈ Rel.FnInv r (Alg.GenIdeal₁ A₂ y₁), from
          begin
            existsi y₁,
            apply and.intro,
            {apply GenIdeal₁.mem},
            {assumption}
          end,
        have Q := rIP (@GenIdeal₁.Ideal _ y₁) Q₀ Jx,
        cases Q with y₃ Hy₃,
        cases Hy₃ with Hy₁ Rx₃y₃,
        cases Hy₁ with y₁' Hy₁',
        cases Hy₁' with Dy₁y₃ E,
        subst E,
        apply Dy₁y₃,
        { intros y₂ Jy,
          apply or.inr,
          existsi y₂, existsi y₃,
          apply and.intro,
          repeat { assumption }
        },
        { intro E, subst E,
          exact or.inl Rx₃y₃
        }
      },
      { intro rIP,
        intros I Iideal,
        intros x₁ x₂ x₃ Hx₁ Hx,
        apply Rel.FnInv.elim Hx₁,
        intros y₁ Iy₁ Rx₁y₁,
        cases rIP Hx Rx₁y₁ with Rx₃y₁ Hy,
        { existsi y₁, apply and.intro, repeat {assumption}
        },
        { cases Hy with y₂ Hy, cases Hy with y₃ Hy,
          exact Rel.FnInv.show Hy.1 (Iideal Iy₁ Hy.2)
        }
      }
    end


def Rel.PrimePres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {p : Set A₂} (pPrime : p.Prime)
      {x₁ x₂ x₃} {y₃}
      (Jx : x₃ ∈ A₁.join x₁ x₂)
      (Rx₃y₃ : r x₃ y₃)
      (Py₃ : y₃ ∈ p)
    , (∃ y₁, r x₁ y₁ ∧ y₁ ∈ p) ∨ (∃ y₂, r x₂ y₂ ∧ y₂ ∈ p)

def Rel.FnPrimePres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
  := ∀ {p : Set A₂} (pPrime : p.Prime)
     , (r.FnInv p).Prime

def Rel.PrimePres_iff {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  : r.FnPrimePres ↔ r.PrimePres
 := begin
      apply iff.intro,
      { intro rPP,
        intros p pPrime x₁ x₂ x₃ y₃ Jx Rx₃y₃ Py₃,
        have Px₃ : x₃ ∈ r.FnInv p := Rel.FnInv.show Rx₃y₃ Py₃,
        cases rPP pPrime _ _ _ Jx Px₃ with H H,
        { apply Rel.FnInv.elim H,
          intros y₁ Py₁ Rx₁y₁,
          apply or.inl, existsi y₁,
          apply and.intro, repeat {assumption}
        },
        { apply Rel.FnInv.elim H,
          intros y₂ Py₂ Rx₂y₂,
          apply or.inr, existsi y₂,
          apply and.intro, repeat {assumption}
        }
      },
      { intro rPP,
        intros p pPrime x₁ x₂ x₃ Jx Px₃,
        apply Rel.FnInv.elim Px₃,
        intros y₃ Py₃ Rx₃y₃,
        cases rPP @pPrime Jx Rx₃y₃ Py₃ with H H,
        { cases H with y₁ Hy₁,
          apply or.inl,
          exact Rel.FnInv.show Hy₁.1 Hy₁.2
        },
        { cases H with y₂ Hy₂,
          apply or.inr,
          exact Rel.FnInv.show Hy₂.1 Hy₂.2
        }
      }
    end


def Rel.DivPres_r {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
  := ∀ {x₁ x₃} {y₃}
     , A₁.Divides x₁ x₃
     → r x₃ y₃
     → ∃ y₁, r x₁ y₁ ∧ A₂.Divides y₁ y₃

def DivPres_r.IdealKer {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rDP : r.DivPres_r)
  : r.IdealKer
 := begin
      intros x₁ x₃ Dx₁x₃ Kx₁ y₃ Rx₃y₃,
      cases rDP @Dx₁x₃ Rx₃y₃ with y₁ Hy₁,
      exact Kx₁ _ Hy₁.1
    end

def DivPres_r.GenPrime.Prime {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rDP : r.DivPres_r)
  : ∀ {gen}, (r.FnInv (A₂.GenPrime₁ gen)).Prime
 := begin
      intros y x₁ x₂ x₃ Jx Rx₃,
      apply Rel.FnInv.elim Rx₃,
      intros y₃ Hy₃ Rx₃y₃,
      cases rDP (λ P C₁ C₂, C₁ Jx) Rx₃y₃ with y₁ Hy,
      cases Hy with Rx₁y₁ Dy₁y₃,
      apply or.inl,
      apply Rel.FnInv.show Rx₁y₁,
      existsi y,
      refine and.intro _ rfl,
      apply Divides.trans @Dy₁y₃,
      cases Hy₃ with y' Hy',
      cases Hy' with Hy' E,
      subst E, assumption
    end


def Rel.DivPres_l {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
  := ∀ {x₁ x₃} {y₁}
     , A₁.Divides x₁ x₃
     → r x₁ y₁
     → (r x₃ y₁) ∨ (∃ y₃, r x₃ y₃ ∧ A₂.Divides y₁ y₃)

def DivPres_l.PrimeKer {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rDP : r.DivPres_l)
  : r.PrimeKer
 := begin
      intros x₁ x₃ x₃ Jx Kx₃,
      apply or.inl,
      intros y₁ Rx₁y₁,
      cases rDP (λ P C₁ C₂, C₁ Jx) Rx₁y₁ with Rx₃y₁ Hy,
      { exact Kx₃ _ Rx₃y₁ },
      { cases Hy with y Hy,
        exact Kx₃ _ Hy.1
      }
    end

def Rel.IdealPres_iff' {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  : r.IdealPres ↔ r.DivPres_l
 := begin
      apply iff.intro,
      { intro rIP,
        intros x₁ x₃ y₁ Dx₁x₃ Rx₁y₁,
        apply Dx₁x₃,
        { intros x₂ Jx,
          have Ix₁ : x₁ ∈ r.FnInv (A₂.GenIdeal₁ y₁), from
            begin
              apply Rel.FnInv.show Rx₁y₁,
              apply GenIdeal₁.mem
            end,
          cases rIP Jx Rx₁y₁ with Rx₃y₁ Hy,
          { exact or.inl Rx₃y₁ },
          { apply or.inr,
            cases Hy with y₂ Hy,
            cases Hy with y₃ Hy,
            cases Hy with Rx₃y₃ Jy,
            existsi y₃, apply and.intro Rx₃y₃,
            intros P C₁ C₂, exact C₁ Jy
          }
        },
        { intro E, subst E,
          exact or.inl Rx₁y₁
        }
      },
      { intro rDP,
        intros x₁ x₂ x₃ y₁ Jx Rx₁y₁,
        have Dx₁x₃ : A₁.Divides x₁ x₃ := λ P C₁ C₂, C₁ Jx,
        cases rDP @Dx₁x₃ Rx₁y₁ with Rx₃y₁ Hy₃,
        { exact or.inl Rx₃y₁ },
        { cases Hy₃ with y₃ Hy₃,
          apply Hy₃.2,
          { intros y₂ Jy,
            apply or.inr,
            existsi y₂, existsi y₃,
            exact and.intro Hy₃.1 Jy
          },
          { intro E, subst E,
            exact or.inl Hy₃.1
          }
        }
      }
    end


-- Downwards, (quasi)-upwards, and quasi-closure
def Rel.QuasiClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂) : Prop
 := ∀ {a₁ a₂ a₁₂} {fa₁₂ b₁ b₂ b₁₂}
      (Ha : A₁.join a₁ a₂ a₁₂) (Hfa₁₂ : f a₁₂ fa₁₂)
      (Ha₁b₁ : f a₁ b₁) (Ha₂b₂ : f a₂ b₂) (Hb : A₂.join b₁ b₂ b₁₂)
    , ∃ y a₁₂' b₁' b₂'
      , f a₁ b₁' ∧ f a₂ b₂'
      ∧ A₁.join a₁ a₂ a₁₂' ∧ f a₁₂' y ∧ A₂.join b₁' b₂' y

def Rel.FnQuasiClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂) : Prop
  := ∀ (X₁ X₂ : Set A₁)
     , Set.nonempty (f.Fn (X₁ <*> X₂))
     → Set.nonempty (f.Fn X₁ <*> f.Fn X₂)
     → Set.nonempty (f.Fn (X₁ <*> X₂) ∩ (f.Fn X₁ <*> f.Fn X₂))

-- note that the converse does not appear to be true.
def Rel.QuasiClosed_if {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂)
  : f.FnQuasiClosed → f.QuasiClosed
 := begin
      intros H_qc a₁ a₂ a₁₂ fa₁₂ b₁ b₂ b₁₂ Ha Hfa₁₂ Ha₁b₁ Ha₂b₂ Hb,
      refine exists.elim (H_qc (eq a₁) (eq a₂)
                            (exists.intro fa₁₂
                              (Rel.Fn.show a₁₂ (Alg.Join.show rfl rfl Ha) Hfa₁₂))
                            (exists.intro b₁₂
                              (Alg.Join.show
                                (Rel.Fn.show a₁ rfl Ha₁b₁)
                                (Rel.Fn.show a₂ rfl Ha₂b₂)
                                Hb))) _,
      intros y Hy,
      cases Hy with Hy₁ Hy₂,
      apply Rel.Fn.elim Hy₁, clear Hy₁,
      intros a₁₂' Ha₁₂' Ha₁₂y,
      apply Alg.Join.elim Hy₂, clear Hy₂,
      intros b₁' b₂' Hb₁' Hb₂' HJb,
      apply Rel.Fn.elim Hb₁', clear Hb₁', intros a₁' Ha₁' Hfa₁b₁', have Q : a₁ = a₁' := Ha₁', subst Q,
      apply Rel.Fn.elim Hb₂', clear Hb₂', intros a₂' Ha₂' Hfa₂b₂', have Q : a₂ = a₂' := Ha₂', subst Q,
      apply Alg.Join.elim Ha₁₂',
      intros a₁' a₂' Ha₁' Ha₂' HJa, subst Ha₁', subst Ha₂',
      existsi y, existsi a₁₂', existsi b₁', existsi b₂',
      repeat {try {assumption}, apply and.intro, assumption },
      assumption
    end


def Rel.DownClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂) : Prop
  := ∀ {n₁ n₂} {m₁ m₂ m₃}
     , f n₁ m₁ → f n₂ m₂ → A₂.join m₁ m₂ m₃
     → ∃ n₃, f n₃ m₃ ∧ A₁.join n₁ n₂ n₃

def DownClosed.QuasiClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂)
  : f.DownClosed → f.QuasiClosed
 := λ H a₁ a₂ a₁₂ fa₁₂ b₁ b₂ b₁₂ Ha Hfa₁₂ Ha₁b₁ Ha₂b₂ Hb
    , begin
        apply exists.elim (H Ha₁b₁ Ha₂b₂ Hb),
        intros x Hx, cases Hx with Hx₁ Hx₂,
        existsi b₁₂, existsi x, existsi b₁, existsi b₂,
        repeat {try {assumption}, apply and.intro, assumption },
        assumption
      end

def DownClosed.JoinClosedPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rDC : r.DownClosed)
  : r.FnJoinClosedPres
 := begin
      intros S SJC,
      intros b₁ b₂ b₃ Jb Sb₁ Sb₂,
      apply Rel.Fn.elim Sb₁, intros a₁ Sa₁ Ra₁b₁,
      apply Rel.Fn.elim Sb₂, intros a₂ Sa₂ Ra₂b₂,
      cases rDC Ra₁b₁ Ra₂b₂ Jb with a₃ Ha,
      cases Ha with Ra₃b₃ Ja,
      have Sa₃ : a₃ ∈ S := SJC _ _ _ Ja Sa₁ Sa₂,
      exact Rel.Fn.show _ Sa₃ Ra₃b₃
    end

-- This condition is too strong
def Rel.QuasiDownClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {n₁ n₂ n₃} {m₁ m₂ m₃}
     , r n₁ m₁ → r n₂ m₂ → r n₃ m₃
     → A₂.join m₁ m₂ m₃
     → A₁.join n₁ n₂ n₃

def QuasiDownClosed.DownClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
    (rIM : r.Im.JoinClosed)
    (rDC : r.QuasiDownClosed)
  : r.DownClosed
 := begin
      intros n₁ n₂ m₁ m₂ m₃ Rn₁m₁ Rn₂m₂ Jm,
      have Im₁ : m₁ ∈ r.Im := exists.intro n₁ Rn₁m₁,
      have Im₂ : m₂ ∈ r.Im := exists.intro n₂ Rn₂m₂,
      cases rIM _ _ _ Jm Im₁ Im₂ with n₃ Rn₃m₃,
      existsi n₃, apply and.intro Rn₃m₃,
      exact rDC Rn₁m₁ Rn₂m₂ Rn₃m₃ Jm
    end

def Rel.FnDownClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂) : Prop
  := ∀ (X₁ X₂ : Set A₁)
     , (f.Fn X₁ <*> f.Fn X₂) ⊆ f.Fn (X₁ <*> X₂)

def Rel.DownClosed_iff {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂)
  : f.FnDownClosed ↔ f.DownClosed
 := begin
      apply iff.intro,
      { intros H_dc n₁ n₂ fn₁ fn₂ m₃ Hfn₁ Hfn₂ HJ,
        apply Rel.Fn.elim
          (H_dc (eq n₁) (eq n₂)
                (Alg.Join.show (Rel.Fn.show _ rfl Hfn₁)
                               (Rel.Fn.show _ rfl Hfn₂)
                               HJ)),
        intros fx H' Hfx,
        existsi fx,
        apply and.intro Hfx,
        apply Alg.Join.elim H', clear H',
        intros x₁' x₂' Hx₁' Hx₂' HJ',
        subst Hx₁', subst Hx₂', assumption
      },
      { intros H_dc X₁ X₂ y Hy,
        apply Alg.Join.elim Hy, clear Hy,
        intros y₁ y₂ Hy₁ Hy₂ HJy,
        apply Rel.Fn.elim Hy₁, intros x₁ Hx₁ Hx₁y₁, clear Hy₁,
        apply Rel.Fn.elim Hy₂, intros x₂ Hx₂ Hx₂y₂, clear Hy₂,
        cases (H_dc Hx₁y₁ Hx₂y₂ HJy) with x H', cases H' with Hxy HJx,
        exact Rel.Fn.show x (Alg.Join.show Hx₁ Hx₂ HJx) Hxy
      }
    end


def Rel.UpClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂) : Prop
  := ∀ {m₁ m₂ m₃} {n₃}
     , A₁.join m₁ m₂ m₃ → f m₃ n₃
     → ∃ n₁ n₂, A₂.join n₁ n₂ n₃ ∧ f m₁ n₁ ∧ f m₂ n₂

def UpClosed.QuasiClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  : r.UpClosed → r.QuasiClosed
 := λ H a₁ a₂ a₁₂ fa₁₂ b₁ b₂ b₁₂ Ha Hfa₁₂ Ha₁b₁ Ha₂b₂ Hb
    , begin
        apply exists.elim (H Ha Hfa₁₂),
        intros y₁ Hy,
        cases Hy with y₂ Hy,
        cases Hy with Hy₁ Hy, cases Hy with Hy₂ H₃,
        existsi fa₁₂, existsi a₁₂, existsi y₁, existsi y₂,
        repeat {try {assumption}, apply and.intro, assumption },
        assumption
      end

def UpClosed.IdealPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  (rUC : r.UpClosed)
  (rID : r.IdealDom)
  (rWD : r.WellDefined)
  : r.IdealPres
 := begin
      intros x₁ x₂ x₃ y₁ Jx Rx₁y₁,
      have Dx₁ : x₁ ∈ r.Dom, from begin existsi y₁, assumption end,
      cases rID Dx₁ Jx with y₃ Rx₃y₃,         -- Uses rID
      have Q := rUC Jx Rx₃y₃,                 -- Uses rUC
      cases Q with y₁' Q, cases Q with y₂' Q,
      have E : y₁' = y₁ := rWD Q.2.1 Rx₁y₁,   -- Uses rWD
      subst E,
      apply or.inr,
      existsi y₂', existsi y₃,
      exact and.intro Rx₃y₃ Q.1
    end

def UpClosed.PrimePres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  (rUC : r.UpClosed)
  : r.FnPrimePres
 := begin
      intros p pPrime,
      intros x₁ x₂ x₃ Jx Px₃,
      apply Rel.FnInv.elim Px₃,
      intros y₃ Py₃ Rx₃y₃,
      cases rUC Jx Rx₃y₃ with n₁ Hn,
      cases Hn with n₂ Hn,
      cases pPrime _ _ _ Hn.1 Py₃ with H H,
      { exact or.inl (Rel.FnInv.show Hn.2.1 H) },
      { exact or.inr (Rel.FnInv.show Hn.2.2 H) }
    end

def UpClosed.DivPres_r {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rUC : r.UpClosed)
  : r.DivPres_r
 := begin
      intros x₁ x₃ y₃ Dx₁x₃ Rx₃y₃,
      apply Dx₁x₃,
      { intros x₂ Jx,
        cases rUC Jx Rx₃y₃ with y₁ Hy,
        cases Hy with y₂ Hy,
        existsi y₁,
        apply and.intro Hy.2.1,
        intros P C₁ C₂, exact C₁ Hy.1
      },
      { intro E, subst E,
        existsi y₃,
        apply and.intro Rx₃y₃,
        apply Divides.refl
      }
    end

def UpClosed.IdealKer {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rUC : r.UpClosed)
  : r.IdealKer
 := begin
      apply DivPres_r.IdealKer,
      apply UpClosed.DivPres_r,
      assumption
    end

def Rel.FnUpClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂) : Prop
  := ∀ (X₁ X₂ : Set A₁)
     , f.Fn (X₁ <*> X₂) ⊆ (f.Fn X₁ <*> f.Fn X₂)

def Rel.UpClosed_iff {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂)
  : f.FnUpClosed ↔ f.UpClosed
 := begin
      apply iff.intro,
      { intros H_uc m₁ m₂ m₃ n₃ HJm Hm₃n₃, 
        apply Alg.Join.elim
          (H_uc (eq m₁) (eq m₂)
                (Rel.Fn.show m₃ (Alg.Join.show rfl rfl HJm) Hm₃n₃)),
        intros n₁ n₂ Hn₁ Hn₂ HJn,
        existsi n₁, existsi n₂,
        apply and.intro HJn,
        apply Rel.Fn.elim Hn₁, intros m₁' Hm₁' Hm₁n₁, have Q : m₁ = m₁' := Hm₁', subst Q,
        apply Rel.Fn.elim Hn₂, intros m₂' Hm₂' Hm₂n₂, have Q : m₂ = m₂' := Hm₂', subst Q,
        exact and.intro Hm₁n₁ Hm₂n₂
      },
      { intros H_uc X₁ X₂ y Hy,
        apply Rel.Fn.elim Hy, clear Hy,
        intros x Hx Hxy,
        apply Alg.Join.elim Hx, clear Hx,
        intros x₁ x₂ Hx₁ Hx₂ HJx,
        cases (H_uc HJx Hxy) with y₁ H, cases H with y₂ H,
        exact Alg.Join.show (Rel.Fn.show x₁ Hx₁ H.2.1) (Rel.Fn.show x₂ Hx₂ H.2.2) H.1
      }
    end

def Rel.QuasiUpClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {x₁ x₂ x₃} {y₃}
    , A₁.join x₁ x₂ x₃
    → ¬ x₁ ∈ r.Ker → ¬ x₂ ∈ r.Ker → r x₃ y₃
    → ∃ y₁' y₂', A₂.join y₁' y₂' y₃ ∧ r x₁ y₁' ∧ r x₂ y₂'

def Rel.UpClosed_iff' {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : r.UpClosed ↔ r.IdealKer ∧ r.QuasiUpClosed
 := begin
      apply iff.intro,
      { intro rUC,
        apply and.intro,
        { apply UpClosed.IdealKer,
          assumption
        },
        { intros x₁ x₂ x₃ y₃ Jx Kx₁ Kx₂ Rx₃y₃,
          exact rUC Jx Rx₃y₃
        }
      },
      { intro rH, cases rH with rKI rL,
        intros m₁ m₂ m₃ n₃ Jm Rn₃m₃,
        have Km₁ : ¬ m₁ ∈ r.Ker, from
          begin
            intro H,
            have Q : m₃ ∈ r.Ker := rKI (λ P C₁ C₂, C₁ Jm) @H,
            exact Q _ Rn₃m₃
          end,
        have Km₂ : ¬ m₂ ∈ r.Ker, from
          begin
            intro H,
            have Q : m₃ ∈ r.Ker := rKI (λ P C₁ C₂, C₁ (A₁.comm Jm)) @H,
            exact Q _ Rn₃m₃
          end,
        apply rL Jm Km₁ Km₂ Rn₃m₃
      }
    end


-- DownPrime and UpJoin

def Rel.DownPrime {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Set A₁
 := λ x, ∃ x₂ y₁ y₂ y₃, r x y₁ ∧ r x₂ y₂ ∧ A₂.join y₁ y₂ y₃

def Rel.PreDownPrime {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Set A₂
 := λ y, ∃ y₂ y₃ x₁ x₂, r x₁ y ∧ r x₂ y₂ ∧ A₂.join y y₂ y₃

def PreDownPrime_DownPrime {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  : r.DownPrime = r.FnInv (GenPrime r.PreDownPrime)
 := begin
      apply funext, intro x₁,
      apply iff.to_eq, apply iff.intro,
      { intro H,
        cases H with x₂ H,
        cases H with y₁ H,
        cases H with y₂ H,
        cases H with y₃ H,
        cases H with R₁ H,
        cases H with R₂ Jy,
        existsi y₁,
        refine and.intro _ R₁,
        existsi y₁,
        refine and.intro _ _,
        { intros P C₁ C₂, exact C₂ rfl },
        existsi y₂, existsi y₃,
        existsi x₁, existsi x₂,
        apply and.intro R₁,
        exact and.intro R₂ Jy
      },
      { intro H,
        cases H with y₁ H,
        cases H with H R₁,
        cases H with y₁' H,
        cases H with Dy₁y₁' H,
        cases H with y₂ H,
        cases H with y₃ H,
        cases H with x₁' H,
        cases H with x₂ H,
        cases H with R₁' H,
        cases H with R₂ Jy,
        apply Dy₁y₁' ; clear Dy₁y₁',
        { intros y₁'' Jy',
          apply A₂.assoc (A₂.comm Jy') Jy,
          intro a,
          existsi x₂,
          existsi y₁, existsi y₂, existsi a.x,
          apply and.intro R₁,
          apply and.intro R₂,
          exact a.J₁
        },
        { intro E, subst E,
          existsi x₂,
          existsi y₁, existsi y₂, existsi y₃,
          exact and.intro R₁ (and.intro R₂ Jy),
        }
      }
    end

def FnPrimePres.DownPrime.Prime {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rPP : r.FnPrimePres)
  : r.DownPrime.Prime
 := begin
      rw PreDownPrime_DownPrime,
      apply rPP,
      apply GenPrime.Prime
    end

def UpClosed.DownPrime.Prime {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rUC : r.UpClosed)
  : r.DownPrime.Prime
 := begin
      intros x₁ x₂ x₃ Jx Dx₃,
      cases Dx₃ with x₃' Dx₃,
      cases Dx₃ with y₁ Dx₃,
      cases Dx₃ with y₂ Dx₃,
      cases Dx₃ with y₃ Dx₃,
      cases Dx₃ with Rx₃y₁ Dx₃,
      cases Dx₃ with Rx₃y₂ Jx₃,
      have Q := rUC Jx Rx₃y₁,
      cases Q with y₁₁ Q,
      cases Q with y₁₂ Q,
      cases Q with Jy₁ Q,
      apply or.inl,
      existsi x₂,
      existsi y₁₁, existsi y₁₂, existsi y₁,
      apply and.intro Q.1,
      exact and.intro Q.2 Jy₁
    end


def Rel.UpJoin {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Set A₂
 := λ y, ∃ x₁ x₂ x, r x y ∧ A₁.join x₁ x₂ x

def Rel.PreUpJoin {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Set A₁
 := λ x, ∃ x₁ x₂ y, r x y ∧ A₁.join x₁ x₂ x

def PreUpJoin_UpJoin {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  : r.UpJoin = r.Fn (JoinClosure r.PreUpJoin)
 := begin
      apply funext, intro y,
      apply iff.to_eq, apply iff.intro,
      { intro H,
        cases H with x₁ H,
        cases H with x₂ H,
        cases H with x H,
        cases H with R₃ Jx,
        existsi x,
        refine and.intro _ R₃,
        apply JoinClosure.gen,
        existsi x₁, existsi x₂, existsi y,
        exact and.intro R₃ Jx
      },
      { intro H,
        cases H with x H,
        cases H with H R₃,
        cases H with H H,
        { cases H with x₁ H,
          cases H with x₂ H,
          cases H with y' H,
          cases H with R₃' Jx,
          existsi x₁, existsi x₂, existsi x,
          exact and.intro R₃ Jx
        },
        { existsi x₁, existsi x₂, existsi x,
          apply and.intro R₃,
          assumption
        }
      }
    end

def FnJoinClosedPres.UpJoin.JoinClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rJP : r.FnJoinClosedPres)
  : r.UpJoin.JoinClosed
 := begin
      rw PreUpJoin_UpJoin,
      apply rJP,
      apply JoinClosure.JoinClosed
    end

def DownClosed.UpJoin.JoinClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rDC : r.DownClosed)
  : r.UpJoin.JoinClosed
 := begin
      intros y₁ y₂ y₃ Jy Uy₁ Uy₂,
      cases Uy₁ with x₁₁ Uy₁,
      cases Uy₁ with x₁₂ Uy₁,
      cases Uy₁ with x₁₃ Uy₁,
      cases Uy₁ with Rx₁₃y₁ Uy₁,
      cases Uy₂ with x₂₁ Uy₂,
      cases Uy₂ with x₂₂ Uy₂,
      cases Uy₂ with x₂₃ Uy₂,
      cases Uy₂ with Rx₂₃y₂ Uy₂,
      have Q := rDC Rx₁₃y₁ Rx₂₃y₂ Jy,
      cases Q with x₃₃ Q,
      existsi x₁₃, existsi x₂₃, existsi x₃₃,
      exact Q
    end


def UpJoin_PreDownPrime {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rUC : r.UpClosed)
  : r.UpJoin ⊆ JoinClosure r.PreDownPrime
 := begin
      intros y H,
      cases H with x₁ H,
      cases H with x₂ H,
      cases H with x₃ H,
      cases H with R₃ Jx,
      have Q := rUC Jx R₃,
      cases Q with y₁ Q,
      cases Q with y₂ Q,
      cases Q with Jy Q,
      cases Q with R₁ R₂,
      apply JoinClosure.mul Jy,
      { apply JoinClosure.gen,
        existsi y₂, existsi y,
        existsi x₁, existsi x₂,
        apply and.intro R₁,
        exact and.intro R₂ Jy
      },
      { apply JoinClosure.gen,
        existsi y₁, existsi y,
        existsi x₂, existsi x₁,
        apply and.intro R₂,
        exact and.intro R₁ (A₂.comm Jy)
      }
    end

def DownClosed.DownPrime_PreUpJoin {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rDC : r.DownClosed)
  : r.DownPrime ⊆ GenPrime r.PreUpJoin
 := begin
      intros x₁ H,
      cases H with x₂ H,
      cases H with y₁ H,
      cases H with y₂ H,
      cases H with y₃ H,
      cases H with R₁ H,
      cases H with R₂ Jy,
      have Q := rDC R₁ R₂ Jy,
      cases Q with x₃ Q,
      existsi x₃,
      apply and.intro,
      { intros P C₁ C₂, exact C₁ Q.2 },
      { existsi x₁, existsi x₂, existsi y₃, exact Q }
    end

def UpClosed.DownPrime_PreUpJoin {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rUC : r.UpClosed)
    {x x₂' x₃'}
    (Jx' : A₁.join x x₂' x₃')
    (H : x₃' ∈ r.PreUpJoin)
  : x ∈ r.DownPrime
 := begin
      cases H with x₃ H,
      cases H with x₁ H,
      cases H with y H,
      cases H with R₃ Jx,
      have Q := rUC Jx' R₃,
      cases Q with y₁ Q,
      cases Q with y₂ Q,
      cases Q with Jy Q,
      cases Q with R₁ R₂,
      existsi x₂',
      existsi y₁, existsi y₂, existsi y,
      apply and.intro R₁,
      exact and.intro R₂ Jy
    end

def Flat.DownPrime_PreUpJoin {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rUC : r.UpClosed)
    (rDC : r.DownClosed)
  : r.DownPrime ∪ r.PreUpJoin = GenPrime r.PreUpJoin
 := begin
      apply funext, intro x,
      apply iff.to_eq, apply iff.intro,
      { intro H, cases H with H H,
        { exact DownClosed.DownPrime_PreUpJoin @rDC H },
        { exact GenPrime.mem _ H }
      },
      { intro H, cases H with x' H,
        cases H with Dxx' H,
        apply Dxx',
        { intros x₀ Jx',
          exact or.inl (UpClosed.DownPrime_PreUpJoin @rUC Jx' H)
        },
        { intro E, subst E, exact or.inr H }
      }
    end

def Flat.DownPrime_PreUpJoin.Prime {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rUC : r.UpClosed)
    (rDC : r.DownClosed)
  : (r.DownPrime ∪ r.PreUpJoin).Prime
 := begin
      rw Flat.DownPrime_PreUpJoin @rUC @rDC,
      apply GenPrime.Prime
    end


def Rel.WeakUnitPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ x, A₁.Unit x → ∃ y, r x y ∧ A₂.Unit y

def UpClosed.AlmostUnitPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rUC : r.UpClosed)
    (H : ∃ x y, r x y ∧ A₁.Unit x ∧ A₂.Unit y)
  : r.WeakUnitPres
 := begin
      intros x Hx,
      cases H with x₀ H,
      cases H with y₀ H,
      cases H with R₀ H,
      cases H with Hx₀ Hy₀,
      apply Hx x₀,
      { intros x' Jx,
        have Q := rUC Jx R₀,
        cases Q with y Q,
        cases Q with y' Q,
        cases Q with Jy Q,
        existsi y,
        apply and.intro Q.1,
        have Dyy₀ : A₂.Divides y y₀ := λ P C₁ C₂, C₁ Jy,
        exact Unit.Divides Hy₀ _ Dyy₀
      },
      { intro E, subst E,
        existsi y₀,
        exact and.intro R₀ Hy₀
      }
    end


def Rel.UpUnitPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := r.Fn A₁.LinearUnit ⊆ A₂.LinearUnit

def Rel.IntegralPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {I : Set A₂} (Iintegral : I.Integral)
    , (r.FnInv I).Integral

def UnitPres.IntegralPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  : r.UpUnitPres ↔ r.IntegralPres
 := begin
      apply iff.intro,
      { intro Hr,
        intros I Iintegral,
        intros x Hy Hx,
        cases Hy with y Hy,
        cases Hy with Iy Rxy,
        apply Iintegral y Iy,
        apply Hr,
        existsi x,
        exact and.intro Hx Rxy
      },
      { intro Hr,
        intros y H,
        cases H with x H,
        cases H with Hx Rxy,
        apply @classical.by_contradiction (y ∈ A₂.LinearUnit),
        intro F,
        have Q : @Set.Integral A₂ (eq y), from
          begin
            intros y' Hy',
            have E : y = y' := Hy', subst E,
            exact F
          end,
        have Q' := Hr Q,
        have Q'' : x ∈ Rel.FnInv r (eq y), from
          begin
            existsi y,
            exact and.intro rfl Rxy
          end,
        exact Q' x Q'' Hx
      }
    end
      

def Rel.DownUnitPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := A₂.LinearUnit ⊆ r.Fn A₁.LinearUnit

def Reflexive.DownUnitPres {A : Alg.{ℓ₁}} (r : Rel A A)
    (r_refl : ∀ a, r a a)
  : r.DownUnitPres
 := begin
      intros x Hx,
      existsi x,
      exact and.intro Hx (r_refl x)
    end

def Rel.RationalPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {R : Set A₁} (Rrational : R.Rational)
    , (r.Fn R).Rational

def UnitPres.RationalPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : r.DownUnitPres ↔ r.RationalPres
 := begin
      apply iff.intro,
      { intro Hr,
        intros R Rrational,
        intros x Ux,
        cases Hr Ux with y Hy,
        existsi y,
        refine and.intro _ Hy.2,
        exact Rrational Hy.1
      },
      { intro Hr,
        intros y Hy,
        refine Hr _ Hy,
        intros x Hx,
        exact Hx
      }
    end


def Rel.WeakIdPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ x y, r x y → A₁.WeakIdentity x → A₂.WeakIdentity y

def Rel.FnGenPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {p : Set A₁} (pNG : p.Generating)
    , (r.Fn p).Generating

def Rel.FnNonGenPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {p : Set A₂} (pNG : p.NonGenerating)
    , (r.FnInv p).NonGenerating


-- Local and confined sets
def Rel.Local {A : Alg.{ℓ₁}} (r : Rel A A) (S : Set A)
  : Prop
 := r.Fn S ⊆ S ∪ r.increasing

def Rel.Local.Fn {A : Alg.{ℓ₁}} (S : Set A) (r : Rel A A)
    (r_trans : r.Trans)
  : r.Local (r.Fn S)
 := begin
      intros z H,
      cases H with y H,
      cases H with H Ryz,
      cases H with x H,
      cases H with HSx Rxy,
      apply or.inl,
      existsi x,
      apply and.intro, assumption,
      apply r_trans, repeat { assumption }
    end

def Rel.Local.FnInv {A : Alg.{ℓ₁}} (p : Set A) (r : Rel A A)
    (r_trans : r.Trans)
    (Hp : r.Local p.Compl)
  : r.Local (r.FnInv p).Compl
 := begin
      intros y H, cases H with x H,
      cases H with H Rxy,
      apply or.inl,
      intro F,
      cases F with x' F,
      cases F with Hx' Ryx',
      apply H,
      existsi x',
      apply and.intro Hx',
      apply r_trans,
      repeat { assumption }
    end


def Rel.Confined {A : Alg.{ℓ₁}} (r : Rel A A) (p : Set A)
  : Prop
 := r.FnInv p ⊆ p

def Rel.Confined.Fn {A : Alg.{ℓ₁}} (r : Rel A A) (S : Set A)
    (r_trans : r.Trans)
    (HS : r.Confined S.Compl)
  : r.Confined (r.Fn S).Compl
 := begin
      intros y H,
      cases H with z H,
      cases H with H Ryz,
      intro F,
      cases F with x F,
      cases F with HSx Rxy,
      apply H,
      existsi x,
      apply and.intro HSx,
      apply r_trans, repeat { assumption }
    end

def Rel.Confined.FnInv {A : Alg.{ℓ₁}} (r : Rel A A) (p : Set A)
    (r_trans : r.Trans)
    (Hp : r.Confined p)
  : r.Confined (r.FnInv p)
 := begin
      intros x H,
      cases H with y H,
      cases H with H Rxy,
      cases H with z H,
      cases H with Hpz Ryz,
      existsi z,
      apply and.intro Hpz,
      apply r_trans, repeat { assumption }
    end

def Confined.Local {A : Alg.{ℓ₁}} {p : Set A} {r : Rel A A}
    (Hp : r.Confined p.Compl)
  : r.Local p
 := begin
      intros y H,
      cases H with x H, cases H with Hpx Rxy,
      apply classical.by_contradiction,
      intro F,
      apply Hp ⟨y, and.intro (λ F', F (or.inl F')) Rxy⟩,
      assumption
    end

def Local.Confined {A : Alg.{ℓ₁}} {S : Set A} {r : Rel A A}
    (HS₁ : r.Local S)
    (HS₂ : r.increasing ⊆ S)
  : r.Confined S.Compl
 := begin
      intros x H,
      cases H with y H,
      cases H with HSy Rxy,
      intro F,
      have Q := HS₁ ⟨x, and.intro F Rxy⟩,
      cases Q with Q Q,
      { exact HSy Q },
      { exact HSy (HS₂ Q) }
    end


def Rel.LocallyUpClosed {A : Alg.{ℓ₁}} {B : Alg.{ℓ₂}} (r: Rel A B) (S : Set A)
  : Prop
 := ∀ s x₂ x₃ y₃
      (Hs : s ∈ S)
      (J : A.join s x₂ x₃)
      (R₃ : r x₃ y₃)
    , ∃ n₁ n₂, B.join n₁ n₂ y₃ ∧ r s n₁ ∧ r x₂ n₂

def Rel.LocallyDownClosed {A : Alg.{ℓ₁}} {B : Alg.{ℓ₂}} (r: Rel A B) (S : Set B)
  : Prop
 := ∀ s x₂ x₃ m₁ m₂
      (Hs : s ∈ S)
      (J : B.join s x₂ x₃)
      (R₁ : r m₁ s)
      (R₂ : r m₂ x₂)
    , ∃ m₃, r m₃ x₃ ∧ A.join m₁ m₂ m₃

structure Rel.LocallyFlat {A : Alg.{ℓ₁}} (r : Rel A A) (S : Set A) : Prop
 := (up : r.LocallyUpClosed S)
    (down : r.LocallyDownClosed S)


def LocallyUpClosed.Union {A : Alg.{ℓ₁}} {B : Alg.{ℓ₂}} {r: Rel A B}
    {S₁ S₂ : Set A}
    (H₁ : r.LocallyUpClosed S₁)
    (H₂ : r.LocallyUpClosed S₂)
  : r.LocallyUpClosed (S₁ ∪ S₂)
 := begin
      intros s x₂ x₃ y₃ Hs J R₃,
      cases Hs with Hs Hs,
      { apply H₁, repeat { assumption } },
      { apply H₂, repeat { assumption } }
    end

def LocallyDownClosed.Union {A : Alg.{ℓ₁}} {B : Alg.{ℓ₂}} {r: Rel A B}
    {S₁ S₂ : Set B}
    (H₁ : r.LocallyDownClosed S₁)
    (H₂ : r.LocallyDownClosed S₂)
  : r.LocallyDownClosed (S₁ ∪ S₂)
 := begin
      intros s x₂ x₃ m₁ m₂ Hs J R₁ R₂,
      cases Hs with Hs Hs,
      { apply H₁, repeat { assumption } },
      { apply H₂, repeat { assumption } }
    end

def LocallyFlat.Union {A : Alg.{ℓ₁}} {r: Rel A A}
    {S₁ S₂ : Set A}
    (H₁ : r.LocallyFlat S₁)
    (H₂ : r.LocallyFlat S₂)
  : r.LocallyFlat (S₁ ∪ S₂)
 := { up := LocallyUpClosed.Union H₁.up H₂.up
    , down := LocallyDownClosed.Union H₁.down H₂.down
    }

def LocallyUpClosed.Subset {A : Alg.{ℓ₁}} {B : Alg.{ℓ₂}} {r: Rel A B}
    (S T : Set A)
    (HST : S ⊆ T) (HT : r.LocallyUpClosed T)
  : r.LocallyUpClosed S
 := begin
      intros s x₂ x₃ y₃ Hs J R₃,
      refine HT _ _ _ _ _ J R₃,
      apply HST,
      assumption
    end


def LocallyDownClosed.Subset {A : Alg.{ℓ₁}} {B : Alg.{ℓ₂}} {r: Rel A B}
    (S T : Set B)
    (HST : S ⊆ T) (HT : r.LocallyDownClosed T)
  : r.LocallyDownClosed S
 := begin
      intros s x₂ x₃ m₁ m₂ Hs J R₁ R₂,
      refine HT _ _ _ _ _ _ J R₁ R₂,
      apply HST,
      assumption
    end


def UpClosed.LocallyUpClosed {A : Alg.{ℓ₁}} {B : Alg.{ℓ₂}} {r: Rel A B}
    (rUC : r.UpClosed) (S : Set A)
  : r.LocallyUpClosed S
 := begin
      intros s x₂ x₃ y₃ Hs J R₃,
      exact rUC J R₃
    end

def DownClosed.LocallyDownClosed {A : Alg.{ℓ₁}} {B : Alg.{ℓ₂}} {r: Rel A B}
    (rDC : r.DownClosed) (S : Set B)
  : r.LocallyDownClosed S
 := begin
      intros s x₂ x₃ m₁ m₂ Hs J R₁ R₂,
      exact rDC R₁ R₂ J
    end

-- def Rel.LocallyClosed {A : Alg.{ℓ₁}} (r: Rel A A) (S : Set A)
--   : Prop
--  := r.LocallyUpClosed S ∨ r.LocallyDownClosed S

-- def UpClosed.LocallyClosed {A : Alg.{ℓ₁}} {r: Rel A A}
--     (rUC : r.UpClosed) (S : Set A)
--   : r.LocallyClosed S
--  := or.inl (UpClosed.LocallyUpClosed @rUC S)

-- def DownClosed.LocallyClosed {A : Alg.{ℓ₁}} {r: Rel A A}
--     (rDC : r.DownClosed) (S : Set A)
--   : r.LocallyClosed S
--  := or.inr (DownClosed.LocallyDownClosed @rDC S)


def Rel.Closed {A : Alg.{ℓ₁}} {B : Alg.{ℓ₂}} (r: Rel A B)
  : Prop
 := r.UpClosed ∨ r.DownClosed

def Rel.Flip {A : Alg.{ℓ₁}} {B : Alg.{ℓ₂}}
    (r: Rel A B)
  : Rel B A
 := λ b a, r a b

end Sep
