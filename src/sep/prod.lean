import .basic

namespace Sep
universes ℓ₁ ℓ₂

def Alg.Prod (A : Alg.{ℓ₁}) (B : Alg.{ℓ₂})
  : Alg.{max ℓ₁ ℓ₂}
  := { τ := A.τ × B.τ
     , join := λ x₁ x₂ x₃
               , (x₃.1 ∈ A.join x₁.1 x₂.1) ∧ (x₃.2 ∈ B.join x₁.2 x₂.2)
     , comm := λ x₁ x₂ x₃ J
               , and.intro (A.comm J.1) (B.comm J.2)
     , assoc := λ x₁ x₂ x₃ x₁₂ x₁₂₃ J₁₂ J₁₂₃ P C
                , begin
                    apply A.assoc J₁₂.1 J₁₂₃.1, intro a,
                    apply B.assoc J₁₂.2 J₁₂₃.2, intro b,
                    exact C { x := (a.x, b.x)
                            , J₁ := and.intro a.J₁ b.J₁
                            , J₂ := and.intro a.J₂ b.J₂
                            }
                  end
     }

end Sep
