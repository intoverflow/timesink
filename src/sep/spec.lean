/- The spectrum of a separation algebra.
 -
 -/
import .ordalg
import .sheaf
import ..top.basic

namespace Sep
universes ℓ ℓ₁ ℓ₂
open Top

structure OrdAlg.Pt (A : OrdAlg.{ℓ}) : Type.{ℓ}
 := (set : Set A.alg)
    (prime : set.Prime)
    (fixed : A.ord.FnInv set = set)
    (non_increasing : A.ord.increasing ∩ set = ∅)

def Pt.eq {A : OrdAlg.{ℓ}} (p₁ p₂ : A.Pt)
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
    (fixed : A.ord.Fn set ⊆ set)
    (increasing : A.ord.increasing ⊆ set)

def BasicOpen.inter {A : OrdAlg.{ℓ}}
    (S₁ S₂ : A.BasicOpen)
  : A.BasicOpen
 := { set := S₁.set ∪ S₂.set
    , fixed := begin
                intros y H,
                cases H with x H,
                cases H with HSx Rxy,
                cases HSx with HSx HSx,
                { apply or.inl,
                  apply S₁.fixed,
                  existsi x,
                  apply and.intro,
                  repeat { assumption }
                },
                { apply or.inr,
                  apply S₂.fixed,
                  existsi x,
                  apply and.intro,
                  repeat { assumption }
                }
              end
    , increasing := λ x H, or.inl (S₁.increasing H)
    }

instance BasicOpen_has_inter (A : OrdAlg.{ℓ}) : has_inter A.BasicOpen
 := { inter := BasicOpen.inter
    }

def OrdAlg.BasicOpen.Contains {A : OrdAlg.{ℓ}}
    (S : A.BasicOpen) (p : A.Pt)
  : Prop
 := S.set ∩ p.set = ∅

instance BasicOpen_has_mem (A : OrdAlg.{ℓ}) : has_mem A.Pt A.BasicOpen
 := { mem := λ p S, S.Contains p
    }

def BasicOpen.inter.elem {A : OrdAlg.{ℓ}}
    {S₁ S₂ : A.BasicOpen} {p : A.Pt}
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

def Nhbd {A : OrdAlg.{ℓ}} (p : A.Pt) : A.BasicOpen
 := { set := p.set.Compl
    , fixed := begin
                intros y H F,
                cases H with x₁ H,
                rw p.fixed.symm at F,
                cases F with x₂ F,
                apply H.1,
                rw p.fixed.symm,
                existsi x₂,
                apply and.intro F.1,
                exact A.trans _ _ _ H.2 F.2
              end
    , increasing := begin
                      intros x H F,
                      apply cast (congr_fun p.non_increasing x),
                      apply and.intro,
                      repeat { assumption }
                    end
    }

def Nhbd.mem {A : OrdAlg.{ℓ}} {p : A.Pt}
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


def OrdAlg.OpenBasis (A : OrdAlg.{ℓ}) : OpenBasis A.Pt
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

def OrdAlg.Top (A : OrdAlg.{ℓ}) : Topology A.Pt
  := A.OpenBasis.Topology

def OrdAlg.ZeroPt (A : OrdAlg.{ℓ}) : A.Pt
 := { set := ∅
    , prime := EmptyPrime _
    , fixed := Rel.FnInv.Empty _
    , non_increasing := begin
                          apply funext, intro x,
                          apply eq.symm, apply iff.to_eq, apply iff.intro,
                          { intro F, exact false.elim F },
                          { intro F, exact F.2 }
                        end
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


def PrimeRel.Map {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
    (rP : r.PrimeRel)
  : Map B.Top A.Top
 := { map
       := λ p
          , { set := r.action.FnInv p.set
            , prime := rP.prime p.prime
            , fixed
                := begin
                    apply funext, intro a₁,
                    apply iff.to_eq, apply iff.intro,
                    { intro H,
                      cases H with a₂ H, cases H with H La₁a₂,
                      cases H with b₃ H, cases H with Hpb₃ H,
                      cases H with b₂ H, cases H with H Lb₂b₃,
                      cases H with x H, cases H with La₂x Rxb₂,
                      rw p.fixed.symm at Hpb₃,
                      cases Hpb₃ with b₄ H, cases H with Hpb₄ Lb₃b₄,
                      refine exists.intro _ (and.intro Hpb₄ _),
                      refine exists.intro _ (and.intro _ (B.trans _ _ _ Lb₂b₃ Lb₃b₄)),
                      refine exists.intro _ (and.intro _ Rxb₂),
                      apply A.trans, repeat { assumption }
                    },
                    { intro H,
                      cases H with b₃ H, cases H with Hpb₂ H,
                      cases H with b₂ H, cases H with H Lb₂b₃,
                      cases H with x H, cases H with La₁x Rxb₂,
                      rw p.fixed.symm at Hpb₂,
                      cases Hpb₂ with b₄ H, cases H with Hpb₄ Lb₃b₄,
                      refine exists.intro _ (and.intro _ La₁x),
                      refine exists.intro _ (and.intro Hpb₄ _),
                      refine exists.intro _ (and.intro _ (B.trans _ _ _ Lb₂b₃ Lb₃b₄)),
                      refine exists.intro _ (and.intro (A.refl _) Rxb₂)
                    }
                  end
            , non_increasing
                := begin
                    apply funext, intro x₁,
                    apply eq.symm, apply iff.to_eq, apply iff.intro,
                    { intro F, exact false.elim F },
                    { intro H, cases H with Hx H,
                      cases H with b₃ H, cases H with Hpb H,
                      cases H with b₂ H, cases H with H Lb,
                      cases H with x₂ H, cases H with Lx Rx₂b₂,
                      rw p.fixed.symm at Hpb,
                      cases Hpb with b₄ H, cases H with Hpb₄ Lb₃b₄,
                      apply cast (congr_fun p.non_increasing b₄),
                      refine and.intro _ Hpb₄,
                      apply rP.increasing,
                      refine exists.intro _ (and.intro Hx _),
                      refine exists.intro _ (and.intro _ (B.trans _ _ _ Lb Lb₃b₄)),
                      refine exists.intro _ (and.intro Lx Rx₂b₂)
                    }
                  end
            }
    , preimage
       := sorry
    }

def JoinRel.Map {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
    (rJ : r.JoinRel)
  : Map A.Top B.Top
 := { map
       := λ p
          , { set := (r.action.Fn p.set.Compl).Compl
            , prime
               := begin
                    apply Set.JoinClosed.Complement_Prime,
                    apply rJ.join,
                    apply Set.Prime.Complement_JoinClosed,
                    exact p.prime
                  end
            , fixed
                := begin
                    apply funext, intro b₂,
                    apply iff.to_eq, apply iff.intro,
                    { intros H F,
                      cases H with b₃ H, cases H with H Lb₂b₃,
                      apply H, clear H,
                      cases F with a₁ H, cases H with Hpa₁ H,
                      cases H with b₁ H, cases H with H Lb₁b₂,
                      cases H with x H, cases H with La₁x Rxb₁,
                      refine exists.intro _ (and.intro Hpa₁ _),
                      refine exists.intro _ (and.intro _ (B.trans _ _ _ Lb₁b₂ Lb₂b₃)),
                      refine exists.intro _ (and.intro La₁x Rxb₁)
                    },
                    { intro H,
                      refine exists.intro _ (and.intro _ (B.refl _)),
                      intro F, apply H, apply F
                    }
                  end
            , non_increasing
                := begin
                    apply funext, intro b,
                    apply eq.symm, apply iff.to_eq, apply iff.intro,
                    { intro F, exact false.elim F },
                    { intro H, cases H with Hb H,
                      apply H, clear H,
                      have H := rJ.increasing Hb, clear Hb,
                      cases H with a H, cases H with Ha Rab,
                      refine exists.intro _ (and.intro _ Rab),
                      intro F,
                      apply cast (congr_fun p.non_increasing a),
                      apply and.intro,
                      repeat { assumption }
                    }
                  end
            }
    , preimage
       := sorry
    }

end Sep
