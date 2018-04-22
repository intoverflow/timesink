/- Ordered separation algebras
 -
 -/
import .rel

namespace Sep
universes ℓ₁ ℓ₂ ℓ₃ ℓ₄

/- Relations between separation algebras
 -
 -/
structure OrdAlg : Type.{ℓ₁ + 1}
 := (alg : Alg.{ℓ₁})
    (ord : Rel alg alg)
    (refl : ord.Refl)
    (trans : ord.Trans)

instance OrdAlg_has_le {A : OrdAlg.{ℓ₁}} : has_le A.alg.τ
 := { le := A.ord
    }

structure OrdRel (A : OrdAlg.{ℓ₁}) (B : OrdAlg.{ℓ₂})
 := (rel : Rel A.alg B.alg)
    (incr : ∀ x₁ x₂ y₁ y₂
              (R₁ : rel x₁ y₁) (R₂ : rel x₂ y₂)
              (Lx : x₁ ≤ x₂)
            , y₁ ≤ y₂)

def OrdRel.LocalPres {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}} (r : OrdRel A B)
  : Prop
 := ∀ (p : Set B.alg) (pLocal : B.ord.Local p.Compl)
    , A.ord.Local (r.rel.FnInv p).Compl

end Sep
