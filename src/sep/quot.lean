/- Separation algebras
 -
 -/
import .basic

namespace Sep
universe ℓ

-- Quotient by an ideal
def QuotAlg (A : Alg.{ℓ}) {I : Set A} (Iideal : I.Ideal) : Alg
 := { τ := {a // ¬ a ∈ I}
    , join := λ x₁ x₂ x₃, A.join x₁.1 x₂.1 x₃.1
    , comm := λ x₁ x₂ x₃ H, A.comm H
    , assoc₁ := λ x₁ x₂ x₃ x₁x₂ x₁x₂x₃ H₁₂ H₁₂₃
                , A.assoc₁ H₁₂ H₁₂₃
                    (λ a P C, C { x := ⟨ a.x, (λ Q, x₁x₂x₃.2 (Iideal Q (A.comm a.J₂))) ⟩
                                , J₁ := a.J₁
                                , J₂ := a.J₂
                                })
    }


end Sep
