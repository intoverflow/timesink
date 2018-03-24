import .basic
import .prod
import .option

namespace Sep
universes ℓ


namespace Localize

inductive join {A : Alg.{ℓ}} (S : Set A)
  : A.τ → A.τ → A.τ → Prop
| base : ∀ {x₁ x₂ x₃} (J : x₃ ∈ A.join x₁ x₂)
         , join x₁ x₂ x₃
| local_l : ∀ {x₀ x} {q : {s // S s}} (D : A.Divides x₀ q.val)
          , join x₀ x x
| local_r : ∀ {x₀ x} {q : {s // S s}} (D : A.Divides x₀ q.val)
          , join x x₀ x

def join.assoc {A : Alg.{ℓ}} (S : Set A)
  : IsAssoc (join S)
 := begin
      intros x₁ x₂ x₃ x₁₂ x₁₂₃ J₁₂ J₁₂₃ P C,
      cases J₁₂,
      { cases J₁₂₃,
        { apply A.assoc J J_1,
          intro a,
          refine C { x := a.x, J₁ := _, J₂ := _ },
          { apply join.base, exact a.J₁ },
          { apply join.base, exact a.J₂ }
        },
        { have H₁ : A.Divides x₁ q.val
                  := Divides.trans (λ P C₁ C₂, C₁ J) D,
          have H₂ : A.Divides x₂ q.val
                  := Divides.trans (λ P C₁ C₂, C₁ (A.comm J)) D,
          refine C { x := x₃, J₁ := _, J₂ := _ },
          { apply join.local_l @H₂ },
          { apply join.local_l @H₁ }
        },
        { refine C { x := x₂, J₁ := _, J₂ := _ },
          { exact join.local_r D },
          { exact join.base _ J }
        }
      },
      { cases J₁₂₃,
        { refine C { x := x₁₂₃, J₁ := _, J₂ := _ },
          { assumption },
          { exact join.local_l D }
        },
        { refine C { x := x₃, J₁ := _, J₂ := _ },
          { assumption },
          { exact join.local_l D }
        },
        { refine C { x := x₂, J₁ := _, J₂ := _ },
          { exact join.local_r D_1 },
          { assumption }
        }
      },
      { refine C { x := x₃, J₁ := _, J₂ := _ },
        { exact join.local_l D },
        { assumption }
      }
    end

end Localize

def Alg.Localize (A : Alg.{ℓ}) (S : Set A)
  : Alg.{ℓ}
 := { τ := A.τ
    , join := Localize.join S
    , comm := λ x₁ x₂ x₃ J
              , begin
                  cases J,
                  { apply Localize.join.base, apply A.comm, assumption },
                  { apply Localize.join.local_r, assumption },
                  { apply Localize.join.local_l, assumption }
                end
    , assoc := @Localize.join.assoc A S
    }

end Sep
