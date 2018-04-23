/- Ordered separation algebras
 -
 -/
import .rel

namespace Sep
universes ℓ₁ ℓ₂ ℓ₃ ℓ₄

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

def OrdAlg.IdRel (A : OrdAlg.{ℓ₁}) : OrdRel A A
 := { rel := A.alg.IdRel
    , incr := begin
                intros x₁ x₂ y₂ R₂ Lx,
                existsi x₁,
                apply and.intro rfl,
                cases R₂,
                exact Lx
              end
    }

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

-- def OrdRel.LocalPres {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}} (r : OrdRel A B)
--   : Prop
--  := ∀ (p : Set B.alg) (pLocal : B.ord.Local p.Compl)
--     , A.ord.Local (r.rel.FnInv p).Compl


def OrdRel.LocallyUpClosedPres {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
  : Prop
 := ∀ (p : Set B.alg) (HS : B.ord.LocallyUpClosed p.Compl)
    , A.ord.LocallyUpClosed (r.rel.FnInv p).Compl

def OrdRel.LocallyDownClosedPres {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
  : Prop
 := ∀ (S : Set A.alg) (HS : A.ord.LocallyDownClosed S)
    , B.ord.LocallyDownClosed (r.rel.Fn S)


structure OrdRel.UpClosed {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
  : Prop
 := (ord : ∀ {x₁ x₂ x₃ y₃}
             (Jx : A.alg.join x₁ x₂ x₃)
             (L₃ : x₃ ≤ y₃)
           , ∃ z₁ z₂ z₃, B.alg.join z₁ z₂ z₃ ∧ r.rel x₁ z₁ ∧ r.rel x₂ z₂ ∧ r.rel y₃ z₃)
    (rel : ∀ {x₁ x₂ x₃ y₁ y₂ y₃}
             (Jx : B.alg.join x₁ x₂ x₃)
             (R₁ : r.rel y₁ x₁)
             (R₂ : r.rel y₂ x₂)
             (R₃ : r.rel y₃ x₃)
           , ∃ z₁ z₂, A.alg.join z₁ z₂ y₃ ∧ y₁ ≤ z₁ ∧ y₂ ≤ z₂)

structure OrdRel.DownClosed {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
  : Prop
 := (ord : ∀ {x₁ x₂ x₃ y₁ y₂}
             (Jx : B.alg.join x₁ x₂ x₃)
             (L₁ : y₁ ≤ x₁)
             (L₂ : y₂ ≤ x₂)
           , ∃ z₁ z₂ z₃, A.alg.join z₁ z₂ z₃ ∧ r.rel z₁ y₁ ∧ r.rel z₂ y₂ ∧ r.rel z₃ x₃)
    (rel : ∀ {x₁ x₂ x₃ y₁ y₂ y₃}
             (Jx : A.alg.join x₁ x₂ x₃)
             (R₁ : r.rel x₁ y₁)
             (R₂ : r.rel x₂ y₂)
             (R₃ : r.rel x₃ y₃)
           , ∃ (m₃ : (B.alg).τ), m₃ ≤ y₃ ∧ (B.alg).join y₁ y₂ m₃)

def OrdRel.UpClosed.LocallyUpClosedPres {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    {r : OrdRel A B}
    (rUC : r.UpClosed)
  : r.LocallyUpClosedPres
 := begin
      intros p Hp,
      intros s x₂ x₃ y₃ Hps J L₃,
      have Q := rUC.ord J L₃,
      cases Q with z₁ Q, cases Q with z₂ Q, cases Q with z₃ Q,
      cases Q with Jz Q, cases Q with R₁ Q, cases Q with R₂ R₃,
      exact rUC.rel Jz R₁ R₂ R₃
    end

def OrdRel.DownClosed.LocallyDownClosedPres {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    {r : OrdRel A B}
    (rDC : r.DownClosed)
  : r.LocallyDownClosedPres
 := begin
      intros S HS,
      intros s x₂ x₃ m₁ m₂ HSs J L₁ L₂,
      have Q := rDC.ord J L₁ L₂,
      cases Q with z₁ Q, cases Q with z₂ Q, cases Q with z₃ Q,
      cases Q with Jz Q, cases Q with R₁ Q, cases Q with R₂ R₃,
      exact rDC.rel Jz R₁ R₂ R₃
    end

end Sep
