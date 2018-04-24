/- Affine separation schemes
 -
 -/
import .sheaf
import .spec
import .localization

namespace Sep
universes ℓ ℓ₁ ℓ₂
open Top

def expand_prime {X : OrdAlg.{ℓ}}
    {o : X.Top.OI}
    (u : {u // X.Top.Open u ⊆ X.Top.Open o})
    (q : {p // p ∈ X.Top.Open u})
  : {p // p ∈ X.Top.Open o}
 := { val := q.val
    , property := u.property q.property
    }

def PrimeAlg {X : OrdAlg.{ℓ}} (XC : X.ord.Closed)
    (p : X.Spec)
  : OrdAlg.{ℓ}
 := X.Localize p.set.Compl
      begin
        apply Localization.locl.trans,
        { apply Set.Prime.Complement_JoinClosed,
          apply p.prime
        },
        { cases XC with XUC XDC,
          { apply or.inl,
            refine and.intro _ @XUC,
            apply Confined.Local,
            rw Set.ComplCompl,
            intros x Hx,
            rw p.locl.symm,
            exact Hx
          },
          { exact or.inr @XDC }
        },
        { exact X.refl },
        { exact X.trans }
      end

def BasisAlg {X : OrdAlg.{ℓ}} (XC : X.ord.Closed)
    (S : X.BasicOpen) (SJC : S.set.JoinClosed)
  : OrdAlg.{ℓ}
 := X.Localize S.set
      begin
        apply Localization.locl.trans,
        { exact SJC },
        { cases XC with XUC XDC,
          { apply or.inl,
            refine and.intro _ @XUC,
            intros x H,
            exact or.inl (S.locl H)
          },
          { exact or.inr @XDC }
        },
        { exact X.refl },
        { exact X.trans }
      end

structure Sec {X : OrdAlg.{ℓ}} (XC : X.ord.Closed)
    (o : X.Top.OI)
  : Type.{ℓ}
 := (fn : ∀ (p : {p // p ∈ X.Top.Open o})
          , (PrimeAlg XC p.val).alg.τ)
    (continuous
      : ∀ (p : {p // p ∈ X.Top.Open o})
        , ∃ (u : {u // X.Top.Open u ⊆ X.Top.Open o})
            (a : X.alg.τ)
          , p.val ∈ X.Top.Open u.val
          ∧ (∀ (q : {p // p ∈ X.Top.Open u})
              , fn (expand_prime u q) = a))

def Sec.eq {X : OrdAlg.{ℓ}} {XC : X.ord.Closed}
    {o : X.Top.OI}
    (s₁ s₂ : Sec XC o)
    (E : ∀ (p : {p // p ∈ X.Top.Open o})
         , (s₁.fn p) = (s₂.fn p))
  : s₁ = s₂
 := begin
      cases s₁ with s₁ Hs₁,
      cases s₂ with s₂ Hs₂,
      have E' : s₁ = s₂, from
        begin
          apply funext, intro p, apply E
        end,
      subst E'
    end

def res {X : OrdAlg.{ℓ}} (XC : X.ord.Closed)
    {o u : X.Top.OI}
    (H : X.Top.Open u ⊆ X.Top.Open o)
  : Sec XC o → Sec XC u
 := λ s
    , { fn := λ p, s.fn (expand_prime {val := u, property := H} p)
      , continuous
         := sorry
      }

def SecAlg {X : OrdAlg.{ℓ}} (XC : X.ord.Closed) (o : X.Top.OI)
  : OrdAlg.{ℓ}
 := { alg :=  { τ := Sec XC o
              , join := λ s₁ s₂ s₃
                        , ∀ (p : {p // p ∈ X.Top.Open o})
                          , (PrimeAlg XC p.val).alg.join (s₁.fn p) (s₂.fn p) (s₃.fn p)
              , comm := λ s₁ s₃ s₃ J p, (PrimeAlg XC p.val).alg.comm (J p)
              , assoc
                 := λ s₁ s₂ s₃ s₁₂ s₁₂₃ J₁₂ J₁₂₃ P C
                    , sorry
                    --  , C { x := { fn := λ p, begin end
                    --             , continuous := begin end
                    --             }
                    --      , J₁ := begin end
                    --      , J₂ := begin end
                    --      }
              }
    , ord := λ s₁ s₂
             , (∀ (p : {p // p ∈ X.Top.Open o})
                , (PrimeAlg XC p.val).ord (s₁.fn p) (s₂.fn p))
    , refl := λ s p
              , (PrimeAlg XC p.val).refl (s.fn p)
    , trans := λ s₁ s₂ s₃ L₁₂ L₂₃ p
               , (PrimeAlg XC p.val).trans _ _ _ (L₁₂ p) (L₂₃ p)
    }

def OrdAlg.Struct (X : OrdAlg.{ℓ}) (XC : X.ord.Closed)
  : Sheaf X.Top
 := { Section := SecAlg XC
    , ρ := λ U₁ U₂ H
           , { rel := λ s₁ s₂, s₂ = res XC H s₁
             , incr
               := λ x₁ x₂ y₂ Rxy L₁₂
                  , begin
                      exact sorry
                    end
             }
    , ρ_id
       := λ U H
          , begin
              exact sorry
            end
    , ρ_circ
       := λ U₁ U₂ U₃ H₁₂ H₂₃ H₁₃
          , begin
              exact sorry
            end
    , locl
       := λ U UU Ucover s t E
          , begin
              exact sorry
            end
    , glue
       := λ U UU Ucover loc E
          , begin
              exact sorry
            end
    }

def OrdAlg.BasicOpen.to_section {X : OrdAlg.{ℓ}} (S : X.BasicOpen) (XC : X.ord.Closed)
  : X.alg.τ → Sec XC (eq S)
 := λ a₀
    , { fn := λ p, a₀
        , continuous
            := λ p, exists.intro
                      { val := eq S
                      , property := λ q Hq, Hq
                      }
                      begin
                        existsi a₀,
                        apply and.intro p.property,
                        intro q, trivial
                      end
      }

def OrdAlg.to_section.inj {X : OrdAlg.{ℓ}} (XC : X.ord.Closed)
    (S : X.BasicOpen)
    {x₁ x₂ : X.alg.τ}
    (E : S.to_section XC x₁ = S.to_section XC x₂)
  : x₁ = x₂
 := begin
      have Q₁ := congr_arg (λ (x : Sec XC (eq S)), x.fn) E,
      have Q₂ := congr_fun Q₁ { val := X.ZeroPt
                              , property := ZeroPt.Everywhere
                              },
      exact Q₂
    end

def OrdAlg.to_section.surj {X : OrdAlg.{ℓ}} (XC : X.ord.Closed)
    {S : X.BasicOpen}
    (s : Sec XC (eq S))
  : ∃ x, S.to_section XC x = s
 := begin
      existsi s.fn { val := X.ZeroPt, property := ZeroPt.Everywhere },
      apply Sec.eq,
      intro p,
      have Q := s.continuous p,
      cases Q with U Q, cases Q with a Q,
      cases Q with Hp E,
      have E' := E { val := X.ZeroPt
                   , property
                     := begin
                          cases Hp with V H,
                          cases H with HV HVp,
                          cases HV with V' HV',
                          cases HV' with HV' E,
                          subst E,
                          refine exists.intro _ (exists.intro (exists.intro V' (and.intro HV' rfl)) _),
                          apply ZeroPt.BasisEverywhere
                        end
                   },
      refine eq.trans E' (eq.symm _),
      refine eq.trans _ (E { val := _, property := Hp}),
      cases p with p Hp',
      trivial
    end

def OrdAlg.ToSection {X : OrdAlg.{ℓ}} (XC : X.ord.Closed)
    (S : X.BasicOpen) (SJC : S.set.JoinClosed)
    : OrdRel
        (BasisAlg XC S SJC)
        ((X.Struct XC).Section (eq S))
 := { rel := λ x y, y = S.to_section XC x
    , incr := λ x₁ x₂ y₂ E L₁₂
              , begin
                  subst E,
                  refine exists.intro _ (and.intro rfl _),
                  intro p,
                  cases L₁₂,
                  { apply Localization.locl.base, exact Rxy },
                  { refine Localization.locl.join _ Rx Ry J,
                    intro F,
                    cases p with p Hp,
                    cases Hp with p₀ Hp,
                    cases Hp with Hp' Hp,
                    cases Hp' with oi Hoi,
                    cases Hoi with Hoi E,
                    subst E, cases Hoi,
                    apply cast (congr_fun Hp s),
                    exact and.intro Hs F
                  }
                end
    }

def OrdAlg.FromSection {X : OrdAlg.{ℓ}} (XC : X.ord.Closed)
    (S : X.BasicOpen) (SJC : S.set.JoinClosed)
    : OrdRel
        ((X.Struct XC).Section (eq S))
        (BasisAlg XC S SJC)
 := { rel := λ x y, x = S.to_section XC y
    , incr := λ v₁ v₂ w₂ E L₁₂
              , begin
                  subst E,
                  have Q := OrdAlg.to_section.surj XC v₁,
                  cases Q with w₁ Hw₁,
                  existsi w₁,
                  apply and.intro Hw₁.symm,
                  subst Hw₁,
                  have HS' : X.ord.FnInv S.set.Compl = S.set.Compl, from
                    begin
                      apply funext, intro x,
                      apply iff.to_eq, apply iff.intro,
                      { intros H F,
                        cases H with y H,
                        apply H.1,
                        apply S.locl,
                        existsi x,
                        exact and.intro F H.2
                      },
                      { intro F,
                        existsi x,
                        apply and.intro F,
                        apply X.refl
                      }
                    end,
                  have Q := L₁₂ { val := { set := S.set.Compl
                                         , prime := Set.JoinClosed.Complement_Prime SJC
                                         , locl := HS'
                                         }
                                , property
                                   := begin
                                        refine exists.intro _
                                                (exists.intro
                                                  (exists.intro _ (and.intro rfl rfl))
                                                  _),
                                        apply funext, intro x,
                                        apply eq.symm, apply iff.to_eq, apply iff.intro,
                                        { intro F, exact false.elim F },
                                        { intro H, exact H.2 H.1 }
                                      end
                                },
                  cases Q ; clear Q,
                  { apply Localization.locl.base, exact Rxy
                  },
                  { have Hs' : s ∈ S.set, from
                      begin
                        rw Set.ComplCompl at Hs,
                        assumption
                      end,
                    exact Localization.locl.join Hs' Rx Ry J
                  }
                end
    }


end Sep
