/- The spectrum of a separation algebra.
 -
 -/
import .ordalg
import .sheaf
import ..top.basic

namespace Sep
universes ℓ ℓ₁ ℓ₂
open Top

structure OrdAlg.Spec (A : OrdAlg.{ℓ}) : Type.{ℓ}
 := (set : Set A.alg)
    (prime : set.Prime)
    (locl : A.ord.FnInv set = set)

def Spec.eq {A : OrdAlg.{ℓ}} (p₁ p₂ : A.Spec)
  : p₁.set = p₂.set → p₁ = p₂
 := begin
      intro E,
      cases p₁ with p₁ H₁,
      cases p₂ with p₂ H₂,
      simp at E,
      subst E
    end

structure OrdAlg.BasicOpen (A : OrdAlg.{ℓ})
  : Type.{ℓ}
 := (set : Set A.alg)
    (locl : A.ord.Fn set ⊆ set)

def BasicOpen.inter {A : OrdAlg.{ℓ}}
    (S₁ S₂ : A.BasicOpen)
  : A.BasicOpen
 := { set := S₁.set ∪ S₂.set
    , locl := begin
                intros y H,
                cases H with x H,
                cases H with HSx Rxy,
                cases HSx with HSx HSx,
                { apply or.inl,
                  apply S₁.locl,
                  existsi x,
                  apply and.intro,
                  repeat { assumption }
                },
                { apply or.inr,
                  apply S₂.locl,
                  existsi x,
                  apply and.intro,
                  repeat { assumption }
                }
              end
    }

instance BasicOpen_has_inter (A : OrdAlg.{ℓ}) : has_inter A.BasicOpen
 := { inter := BasicOpen.inter
    }

def OrdAlg.BasicOpen.Contains {A : OrdAlg.{ℓ}}
    (S : A.BasicOpen) (p : A.Spec)
  : Prop
 := S.set ∩ p.set = ∅

instance BasicOpen_has_mem (A : OrdAlg.{ℓ}) : has_mem A.Spec A.BasicOpen
 := { mem := λ p S, S.Contains p
    }

def BasicOpen.inter.elem {A : OrdAlg.{ℓ}}
    {S₁ S₂ : A.BasicOpen} {p : A.Spec}
  : p ∈ S₁ ∩ S₂ ↔ p ∈ S₁ ∧ p ∈ S₂
 := begin
      apply iff.intro,
      { intro H,
        apply and.intro,
        { apply funext, intro x,
          apply eq.symm, apply iff.to_eq, apply iff.intro,
          { intro F, exact false.elim F },
          { intro F, rw H.symm,
            refine and.intro _ F.2,
            exact or.inl F.1
          }
        },
        { apply funext, intro x,
          apply eq.symm, apply iff.to_eq, apply iff.intro,
          { intro F, exact false.elim F },
          { intro F, rw H.symm,
            refine and.intro _ F.2,
            exact or.inr F.1
          }
        },
      },
      { intro H,
        apply funext, intro x,
        apply eq.symm, apply iff.to_eq, apply iff.intro,
        { intro F, exact false.elim F },
        { intro F,
          cases F with F Fpx,
          cases F with F F,
          { rw H.1.symm, apply and.intro, repeat { assumption } },
          { rw H.2.symm, apply and.intro, repeat { assumption } }
        }
      }
    end

def Nhbd {A : OrdAlg.{ℓ}} (p : A.Spec) : A.BasicOpen
 := { set := p.set.Compl
    , locl := begin
                intros y H F,
                cases H with x₁ H,
                rw p.locl.symm at F,
                cases F with x₂ F,
                apply H.1,
                rw p.locl.symm,
                existsi x₂,
                apply and.intro F.1,
                exact A.trans _ _ _ H.2 F.2
              end
    }

def Nhbd.mem {A : OrdAlg.{ℓ}} {p : A.Spec}
  : p ∈ Nhbd p
 := begin
      apply funext, intro x,
      apply iff.to_eq, apply iff.intro,
      { intro H,
        cases H with H₁ H₂,
        exact H₁ H₂
      },
      { intro H, exact false.elim H }
    end


def OrdAlg.OpenBasis (A : OrdAlg.{ℓ}) : OpenBasis A.Spec
 := { OI := A.BasicOpen
    , Open := OrdAlg.BasicOpen.Contains
    , Cover := begin
                apply funext, intro p,
                apply eq.symm, apply iff.to_eq, apply iff.intro,
                { intro H, constructor },
                { intro H, clear H,
                  refine exists.intro (OrdAlg.BasicOpen.Contains (Nhbd p)) _,
                  refine exists.intro _ Nhbd.mem,
                  existsi (Nhbd p),
                  trivial
                }
               end
    , inter := λ S₁ S₂, S₁ ∩ S₂
    , Ointer := begin
                  intros U₁ U₂,
                  apply funext, intro p,
                  apply iff.to_eq,
                  exact BasicOpen.inter.elem
                end
    }

def OrdAlg.Top (A : OrdAlg.{ℓ}) : Topology A.Spec
  := A.OpenBasis.Topology

def OrdAlg.ZeroPt (A : OrdAlg.{ℓ}) : A.Spec
 := { set := ∅
    , prime := EmptyPrime _
    , locl := Rel.FnInv.Empty _
    }

def ZeroPt.BasisEverywhere {X : OrdAlg.{ℓ}} {S : X.BasicOpen}
  : X.ZeroPt ∈ S
 := begin
      apply funext, intro z,
      apply eq.symm, apply iff.to_eq, apply iff.intro,
      { intro F, exact false.elim F },
      { intro F,
        cases F with F₁ F₂,
        cases F₂
      }
    end

def ZeroPt.Everywhere {X : OrdAlg.{ℓ}} {S : X.BasicOpen}
  : X.ZeroPt ∈ X.Top.Open (eq S)
 := begin
      existsi X.OpenBasis.Open S,
      refine exists.intro _ _,
      { existsi S, exact and.intro rfl rfl
      },
      { apply ZeroPt.BasisEverywhere }
    end

-- def OrdAlg.BigPt (A : OrdAlg.{ℓ}) (AUC : A.ord.UpClosed)
--     (S : Set A.alg)
--     (HS : A.ord.FnInv (JoinClosure S).Compl = (JoinClosure S).Compl)
--   : A.PrimeSpec
--  := { set := (JoinClosure S).Compl
--     , prime := begin
--                 apply Set.JoinClosed.Complement_Prime,
--                 apply JoinClosure.JoinClosed
--               end
--     , locl := HS
--     }

-- def BigPt.In {X : OrdAlg.{ℓ}} {XUC : X.ord.UpClosed} {S : Set X.alg}
--     {HS : X.ord.FnInv (JoinClosure S).Compl = (JoinClosure S).Compl}
--   : X.BigPt @XUC S HS ∈ (OrdAlg.PrimeSpec.Topology X).Open (eq S)
--  := begin
--       existsi (OrdAlg.PrimeSpec.OpenBasis X).Open S,
--       refine exists.intro _ _,
--       { existsi S, exact and.intro rfl rfl },
--       { intros x F,
--         cases F with HSx F,
--         apply F, clear F,
--         apply JoinClosure.gen,
--         assumption
--       }
--     end


end Sep
