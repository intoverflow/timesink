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
    (incr : ∀ x₁ x₂ y₂
              (R₂ : rel x₂ y₂)
              (Lx : x₁ ≤ x₂)
            , ∃ y₁, rel x₁ y₁ ∧ y₁ ≤ y₂)

def OrdRel.ConfinedPres {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}} (r : OrdRel A B)
  : ∀ {p : Set B.alg} (Hp : B.ord.Confined p)
    , A.ord.Confined (r.rel.FnInv p)
 := begin
      intros p Hp,
      intros a₁ H, cases H with a₂ H, cases H with H La,
      cases H with b₂ H, cases H with Hpb₂ R₂,
      have Q := r.incr _ _ _ R₂ La,
      cases Q with b₁ Q, cases Q with R₁ Lb,
      existsi b₁, exact and.intro (Hp ⟨b₂, and.intro Hpb₂ Lb⟩) R₁
    end

def OrdRel.LocalPres {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}} (r : OrdRel A B)
  : Prop
 := ∀ (p : Set B.alg) (pLocal : B.ord.Local p.Compl)
    , A.ord.Local (r.rel.FnInv p).Compl

def idea {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}} (r : OrdRel A B)
  : r.LocalPres
 := begin
      intros p Hp,
      intros a₂ H, cases H with a₁ H, cases H with Hpa₁ La,
      apply or.inl, intro F,
      cases F with b₂ F, cases F with Hpb₂ R₂,
      have Q := r.incr _ _ _ R₂ La,
      cases Q with b₁ Q, cases Q with R₁ Lb,
      apply Hpa₁, existsi b₁,
      refine and.intro _ R₁,
      apply classical.by_contradiction,
      intro F,
      have Q := Hp ⟨b₁, and.intro F Lb⟩,
      cases Q with Q Q,
      { exact Q Hpb₂ },
      { 
      }
    end

end Sep
