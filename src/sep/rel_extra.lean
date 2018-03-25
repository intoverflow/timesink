/- Extra stuff about relations
 -
 -/
import .rel

namespace Sep
universes ℓ₁ ℓ₂

-- More ways of writing up/down closed
def Rel.DownClosed' {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ m₃ n₁ n₂
    , (∃ m₁ m₂, r n₁ m₁ ∧ r n₂ m₂ ∧ A₂.join m₁ m₂ m₃)
    → (∃ n₃, r n₃ m₃ ∧ A₁.join n₁ n₂ n₃)

def Rel.UpClosed' {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ n₃ m₁ m₂
    , (∃ m₃, r m₃ n₃ ∧ A₁.join m₁ m₂ m₃)
    → (∃ n₁ n₂, r m₁ n₁ ∧ r m₂ n₂ ∧ A₂.join n₁ n₂ n₃)

def Rel.DownClosed_iff' {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  : r.DownClosed ↔ r.DownClosed'
 := begin
      apply iff.intro,
      { intro rDC,
        intros m₃ n₁ n₂ H,
        cases H with m₁ H,
        cases H with m₂ H,
        cases H with Rn₁m₁ H,
        cases H with Rn₂m₂ Jm,
        exact rDC Rn₁m₁ Rn₂m₂ Jm
      },
      { intro rDC,
        intros n₁ n₂ m₁ m₂ m₃ Rn₁m₁ Rn₂m₂ Jm,
        apply rDC,
        existsi m₁, existsi m₂,
        apply and.intro Rn₁m₁,
        exact and.intro Rn₂m₂ Jm
      }
    end

def Rel.UpClosed_iff'' {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  : r.UpClosed ↔ r.UpClosed'
 := begin
      apply iff.intro,
      { intro rUC,
        intros n₃ m₁ m₂ H,
        cases H with m₃ H,
        cases H with Rm₃n₃ Jm,
        have Q := rUC Jm Rm₃n₃,
        cases Q with n₁ Q,
        cases Q with n₂ Q,
        cases Q with Jn Q,
        cases Q with Rm₁n₁ Rm₂n₂,
        existsi n₁, existsi n₂,
        apply and.intro Rm₁n₁,
        exact and.intro Rm₂n₂ Jn
      },
      { intro rUC,
        intros m₁ m₂ m₃ n₃ Jm Rm₃n₃,
        have Q := rUC n₃ m₁ m₂ begin existsi m₃, exact and.intro Rm₃n₃ Jm end,
        cases Q with n₁ Q,
        cases Q with n₂ Q,
        cases Q with Rm₁n₁ Q,
        cases Q with Rm₂n₂ Jn,
        existsi n₁, existsi n₂,
        apply and.intro Jn,
        exact and.intro Rm₁n₁ Rm₂n₂
      }
    end

structure Rel.Square {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
 := (x₁ x₂ x₃ : A₁.τ)
    (y₁ y₂ y₃ : A₂.τ)
    (R₁ : r x₁ y₁)
    (R₂ : r x₂ y₂)
    (R₃ : r x₃ y₃)
    (Jx : A₁.join x₁ x₂ x₃)
    (Jy : A₂.join y₁ y₂ y₃)

structure Rel.DownSquare {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
 := (x₁ x₂ : A₁.τ)
    (y₁ y₂ y₃ : A₂.τ)
    (R₁ : r x₁ y₁)
    (R₂ : r x₂ y₂)
    (Jy : A₂.join y₁ y₂ y₃)

structure Rel.UpSquare {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
 := (x₁ x₂ x₃ : A₁.τ)
    (y₃ : A₂.τ)
    (R₃ : r x₃ y₃)
    (Jx : A₁.join x₁ x₂ x₃)

def Rel.DownClosedPreImage {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Set A₂
 := λ y, ∃ (s : r.Square), s.y₁ = y

def Rel.UpDom {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Set A₁
 := λ x, ∃ (s : r.Square), s.x₃ = x



def UpDom_UpJoin {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  : r.Fn r.UpDom ⊆ r.UpJoin
 := begin
      intros y H,
      cases H with x H,
      cases H with H Rxy,
      cases H with s E,
      cases s, subst E,
      simp at Rxy,
      existsi x₁, existsi x₂, existsi x₃,
      exact and.intro Rxy Jx
    end

def UpClosed.UpJoin {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rUC : r.UpClosed)
  : r.UpJoin = r.Fn r.UpDom
 := begin
      apply funext, intro y,
      apply iff.to_eq, apply iff.intro,
      { intro H,
        cases H with x₁ H,
        cases H with x₂ H,
        cases H with x₃ H,
        cases H with R₃ Jx,
        have Q := rUC Jx R₃,
        cases Q with y₁ Q,
        cases Q with y₂ Q,
        cases Q with Jy Q,
        cases Q with R₁ R₂,
        existsi x₃,
        refine and.intro _ R₃,
        let ret : r.Square
             := { x₁ := x₁, x₂ := x₂, x₃ := x₃
                , y₁ := y₁, y₂ := y₂, y₃ := y
                , R₁ := R₁, R₂ := R₂, R₃ := R₃
                , Jx := Jx, Jy := Jy
                },
        existsi ret,
        trivial
      },
      { apply UpDom_UpJoin }
    end


def DownIm_DownPrime {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  : r.FnInv r.DownClosedPreImage ⊆ r.DownPrime
 := begin
      intros x H,
      cases H with y H,
      cases H with H Rxy,
      cases H with s E,
      cases s, subst E,
      simp at Rxy,
      existsi x₂, existsi y₁, existsi y₂, existsi y₃,
      apply and.intro Rxy,
      exact and.intro R₂ Jy
    end

def DownClosed.DownPrime {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rDC : r.DownClosed)
  : r.DownPrime = r.FnInv r.DownClosedPreImage
 := begin
      apply funext, intro x,
      apply iff.to_eq, apply iff.intro,
      { intro H,
        cases H with x₂ H,
        cases H with y₁ H,
        cases H with y₂ H,
        cases H with y₃ H,
        cases H with Rxy₁ H,
        cases H with Rx₂y₂ Jy,
        have Q := rDC Rxy₁ Rx₂y₂ Jy,
        cases Q with x₃ Q,
        cases Q with Rx₃y₃ Jx,
        existsi y₁,
        refine and.intro _ Rxy₁,
        let ret : r.Square
              := { x₁ := x, x₂ := x₂, x₃ := x₃
                  , y₁ := y₁, y₂ := y₂, y₃ := y₃
                  , R₁ := Rxy₁, R₂ := Rx₂y₂, R₃ := Rx₃y₃
                  , Jx := Jx, Jy := Jy
                  },
        existsi ret,
        trivial
      },
      { apply DownIm_DownPrime }
    end


noncomputable def DownPrime.DownSquare {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : {x // r.DownPrime x} → r.DownSquare
 := begin
      intro x,
      cases x with x H₁,
      cases classical.indefinite_description _ H₁ with x₂ H₂,
      cases classical.indefinite_description _ H₂ with y₁ H₃,
      cases classical.indefinite_description _ H₃ with y₂ H₄,
      cases classical.indefinite_description _ H₄ with y₃ H,
      clear H₁ H₂ H₃ H₄,
      cases H with R₁ H,
      cases H with R₂ Jy,
      exact { x₁ := x, x₂ := x₂
            , y₁ := y₁, y₂ := y₂, y₃ := y₃
            , R₁ := R₁, R₂ := R₂
            , Jy := Jy
            }
    end

noncomputable def UpJoin.UpSquare {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : {y // r.UpJoin y} → r.UpSquare
 := begin
      intro y,
      cases y with y H₁,
      cases classical.indefinite_description _ H₁ with x₁ H₂,
      cases classical.indefinite_description _ H₂ with x₂ H₃,
      cases classical.indefinite_description _ H₃ with x₃ H,
      clear H₁ H₂ H₃,
      cases H with R₃ Jx,
      exact { x₁ := x₁, x₂ := x₂, x₃ := x₃
            , y₃ := y
            , R₃ := R₃
            , Jx := Jx
            }
    end

noncomputable def UpClosed.Square {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rUC : r.UpClosed)
  : r.UpSquare → r.Square
 := begin
      intro y,
      have Q₁ := rUC y.Jx y.R₃,
      cases classical.indefinite_description _ Q₁ with y₁ Q₂,
      cases classical.indefinite_description _ Q₂ with y₂ H,
      clear Q₁ Q₂,
      cases H with Jy H,
      cases H with R₁ R₂,
      exact { x₁ := y.x₁, x₂ := y.x₂, x₃ := y.x₃
            , y₁ := y₁, y₂ := y₂, y₃ := y.y₃
            , R₁ := R₁, R₂ := R₂, R₃ := y.R₃
            , Jx := y.Jx
            , Jy := Jy
            }
    end

noncomputable def DownClosed.Square {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rDC : r.DownClosed)
  : r.DownSquare → r.Square
 := begin
      intro x,
      have Q := rDC x.R₁ x.R₂ x.Jy,
      cases classical.indefinite_description _ Q with x₃ H,
      clear Q,
      cases H with R₃ Jx,
      exact { x₁ := x.x₁, x₂ := x.x₂, x₃ := x₃
            , y₁ := x.y₁, y₂ := x.y₂, y₃ := x.y₃
            , R₁ := x.R₁, R₂ := x.R₂, R₃ := R₃
            , Jx := Jx
            , Jy := x.Jy
            }
    end

end Sep
