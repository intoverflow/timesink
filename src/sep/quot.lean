/- Separation algebras
 -
 -/
import .basic

namespace Sep
universe ℓ

-- Quotient by an ideal
def QuotAlg {A' : Type ℓ} (A : Alg A') (I : A.Ideal) : Alg {a // ¬ I.elem a}
 := { join := λ x₁ x₂ x₃, A.join x₁.1 x₂.1 x₃.1
    , comm := λ x₁ x₂ x₃ H, A.comm H
    , assoc := λ x₁ x₂ x₃ x₁x₂ x₁x₂x₃ H₁₂ H₁₂₃
               , begin
                   cases A.assoc H₁₂ H₁₂₃ with x H,
                   refine exists.intro ⟨x, _⟩ H,
                   { intro H',
                     apply x₁x₂x₃.2,
                     apply I.ideal_l H' (A.comm H.2)
                   }
                 end
    }


end Sep
