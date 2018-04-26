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

def PrimeAlg {X : OrdAlg.{ℓ}} 
    (p : X.Pt)
  : OrdAlg.{ℓ}
 := X.Localize p.set.Compl
      begin
        apply Set.Prime.Complement_JoinClosed,
        apply p.prime
      end
      begin
        apply Confined.Local,
        rw Set.ComplCompl,
        intros x Hx,
        rw p.fixed.symm,
        exact Hx
      end

def BasisAlg {X : OrdAlg.{ℓ}} 
    (S : X.BasicOpen) (SJC : S.set.JoinClosed)
  : OrdAlg.{ℓ}
 := X.Localize S.set SJC
      begin
        intros x H,
        exact or.inl (S.fixed H)
      end

structure Sec {X : OrdAlg.{ℓ}} (o : X.Top.OI)
  : Type.{ℓ}
 := (fn : ∀ (p : {p // p ∈ X.Top.Open o})
          , (PrimeAlg p.val).alg.τ)
    (continuous
      : ∀ (p : {p // p ∈ X.Top.Open o})
        , ∃ (u : {u // X.Top.Open u ⊆ X.Top.Open o})
            (a : X.alg.τ)
          , p.val ∈ X.Top.Open u.val
          ∧ (∀ (q : {p // p ∈ X.Top.Open u})
              , fn (expand_prime u q) = a))

def Sec.eq {X : OrdAlg.{ℓ}} {o : X.Top.OI}
    (s₁ s₂ : Sec o)
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

def res {X : OrdAlg.{ℓ}} {o u : X.Top.OI}
    (H : X.Top.Open u ⊆ X.Top.Open o)
  : Sec o → Sec u
 := λ s
    , { fn := λ p, s.fn (expand_prime {val := u, property := H} p)
      , continuous
         := sorry
      }

def SecAlg {X : OrdAlg.{ℓ}} (o : X.Top.OI)
  : OrdAlg.{ℓ}
 := { alg :=  { τ := Sec o
              , join := λ s₁ s₂ s₃
                        , ∀ (p : {p // p ∈ X.Top.Open o})
                          , (PrimeAlg p.val).alg.join (s₁.fn p) (s₂.fn p) (s₃.fn p)
              , comm := λ s₁ s₃ s₃ J p, (PrimeAlg p.val).alg.comm (J p)
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
                , (PrimeAlg p.val).ord (s₁.fn p) (s₂.fn p))
    , refl := λ s p
              , (PrimeAlg p.val).refl (s.fn p)
    , trans := λ s₁ s₂ s₃ L₁₂ L₂₃ p
               , (PrimeAlg p.val).trans _ _ _ (L₁₂ p) (L₂₃ p)
    , closed := sorry
    }

def OrdAlg.Struct (X : OrdAlg.{ℓ})
  : Sheaf X.Top
 := { Section := SecAlg
    , Stalk := λ p, true.intro
    , ρ := λ U₁ U₂ H
           , { rel := λ s₁ s₂, s₂ = res H s₁
             , action := sorry
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

def OrdAlg.BasicOpen.to_section {X : OrdAlg.{ℓ}}
    (S : X.BasicOpen) (SJC : S.set.JoinClosed)
  : (BasisAlg S SJC).alg.τ → ((X.Struct).Section (eq S)).alg.τ
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

def OrdAlg.to_section.inj {X : OrdAlg.{ℓ}}
    {S : X.BasicOpen} (SJC : S.set.JoinClosed)
    {x₁ x₂ : X.alg.τ}
    (E : S.to_section SJC x₁ = S.to_section SJC x₂)
  : x₁ = x₂
 := begin
      have Q₁ := congr_arg (λ (x : Sec (eq S)), x.fn) E,
      have Q₂ := congr_fun Q₁ { val := X.ZeroPt
                              , property := ZeroPt.Everywhere
                              },
      exact Q₂
    end

def OrdAlg.to_section.surj {X : OrdAlg.{ℓ}}
    {S : X.BasicOpen} (SJC : S.set.JoinClosed)
    (s : Sec (eq S))
  : ∃ x, S.to_section SJC x = s
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

def OrdAlg.to_section__from_section {X : OrdAlg.{ℓ}}
    (S : X.BasicOpen) (SJC : S.set.JoinClosed)
  : FunRel (S.to_section SJC) ∘ InvFunRel (S.to_section SJC) = Alg.IdRel _
 := begin
      apply funext, intro x, apply funext, intro y,
      apply eq.symm, apply iff.to_eq, apply iff.intro,
      { intro H,
        have Q := OrdAlg.to_section.surj SJC x,
        cases Q with y' E, subst E,
        have Q := OrdAlg.to_section.surj SJC y,
        cases Q with y₀ E, subst E,
        refine exists.intro y₀ (and.intro H rfl),
      },
      { intro H, cases H with w H,
        cases H with E₁ E₂,
        have E₁' := E₁.symm, subst E₁', clear E₁,
        have E₂' := E₂.symm, subst E₂', clear E₂,
        exact rfl
      }
    end

def OrdAlg.from_section__to_section {X : OrdAlg.{ℓ}}
    (S : X.BasicOpen) (SJC : S.set.JoinClosed)
  : InvFunRel (S.to_section SJC) ∘ FunRel (S.to_section SJC) = Alg.IdRel _
 := begin
      apply funext, intro x, apply funext, intro y,
      apply eq.symm, apply iff.to_eq, apply iff.intro,
      { intro E, have E' : x = y := E, subst E', clear E,
        exact exists.intro (S.to_section SJC x) (and.intro rfl rfl)
      },
      { intro H, cases H with w H,
        cases H with E₁ E₂,
        have E₁' := E₁.symm, subst E₁', clear E₁,
        have E₂' := OrdAlg.to_section.inj SJC E₂, subst E₂', clear E₂,
        exact rfl
      }
    end

def ToSection {X : OrdAlg.{ℓ}}
    (S : X.BasicOpen) (SJC : S.set.JoinClosed)
    : OrdRel
        (BasisAlg S SJC)
        ((X.Struct).Section (eq S))
 := (FunRel (S.to_section SJC)).OrdRel

def FromSection {X : OrdAlg.{ℓ}}
    (S : X.BasicOpen) (SJC : S.set.JoinClosed)
    : OrdRel
        ((X.Struct).Section (eq S))
        (BasisAlg S SJC)
 := (InvFunRel (S.to_section SJC)).OrdRel

def OrdAlg.ToSection_FromSection {X : OrdAlg.{ℓ}}
    (S : X.BasicOpen) (SJC : S.set.JoinClosed)
  : ToSection S SJC ∘∘ FromSection S SJC = OrdAlg.IdRel _
 := begin
      apply OrdRel.eq,
      apply funext, intro x, apply funext, intro y,
      apply eq.symm, apply iff.to_eq, apply iff.intro,
      { exact sorry
      },
      { exact sorry
      }
    end

def OrdAlg.FromSection_ToSection {X : OrdAlg.{ℓ}}
    (S : X.BasicOpen) (SJC : S.set.JoinClosed)
  : FromSection S SJC ∘∘ ToSection S SJC = OrdAlg.IdRel _
 := begin
      apply OrdRel.eq,
      apply funext, intro x, apply funext, intro y,
      apply eq.symm, apply iff.to_eq, apply iff.intro,
      { exact sorry
      },
      { exact sorry
      }
    end

def OrdAlg.Spec (X : OrdAlg.{ℓ})
  : OrdAlgSpace
 := { Pt := X.Pt
    , Top := X.Top
    , Sh := X.Struct
    , stalk := true.intro
    }

def PrimeRel.Spec {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
    (rP : r.PrimeRel)
  : OrdAlgSpaceMorphism B.Spec A.Spec
 := { map := PrimeRel.Map r rP
    , sh :=
        { rel := λ U,
          { rel := λ s t
            , ∀ (p : {p // p ∈ B.Top.Open (((PrimeRel.Map r rP).preimage U).val)})
              , r.rel (s.fn { val := (PrimeRel.Map r rP).map p.val
                            , property := (PrimeRel.Map r rP).in_preimage p
                            })
                      (t.fn p)
          , action := sorry
          }
        , res := sorry
        }
    , stalk := true.intro
    }

def JoinRel.Spec {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
    (rJ : r.JoinRel)
  : OrdAlgSpaceMorphism A.Spec B.Spec
 := { map := JoinRel.Map r rJ
    , sh :=
        { rel := λ U,
          { rel := λ s t
            , ∀ (p : {p // p ∈ A.Top.Open (((JoinRel.Map r rJ).preimage U).val)})
              , r.rel (t.fn p)
                      (s.fn { val := (JoinRel.Map r rJ).map p.val
                            , property := (JoinRel.Map r rJ).in_preimage p
                            })
          , action
             := begin
                  apply funext, intro s, apply funext, intro t,
                  apply iff.to_eq, apply iff.intro,
                  { intro H, intro q,
                    cases H with t' H, cases H with H Lt,
                    cases H with s' H, cases H with Ls H,
                    have Q := H q, clear H,
                    --
                    apply cast (congr_fun (congr_fun r.action _) _),
                    -- refine exists.intro _ (and.intro (exists.intro _ (and.intro _ Q)) _),
                    --
                    exact sorry
                  },
                  { exact sorry
                  }
                end
          }
        , res := sorry
        }
    , stalk := true.intro
    }

def JoinRel.Spec.JoinRel {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
    (rJ : r.JoinRel)
    (rDC : r.rel.DownClosed)
    (p : A.Pt)
  : ((JoinRel.Spec r rJ).sh.rel (eq (Nhbd ((JoinRel.Map r rJ).map p)))).rel.Flip.DownClosed
 := begin
      intros x₁ x₂ y₁ y₂ y₃ R₁ R₂ J,
      dsimp [Rel.Flip, OrdAlg.Spec, OrdAlg.Struct, Sheaf.DirectIm] at *,
      --
      have Hp : p ∈ (OrdAlg.Top A).Open (((JoinRel.Map r rJ).preimage (eq (Nhbd ((JoinRel.Map r rJ).map p)))).val), from
        begin
          existsi A.OpenBasis.Open (Nhbd p),
          refine exists.intro _ Nhbd.mem,
          refine exists.intro (Nhbd p) (and.intro _ rfl),
          exact sorry
        end,
      have R₁' := R₁ { val := p, property := Hp }, clear R₁,
      have R₂' := R₂ { val := p, property := Hp }, clear R₂,
      have Jy' := J { val := (JoinRel.Map r rJ).map p
                    , property := (JoinRel.Map r rJ).in_preimage { val := p, property := Hp }
                    }, clear J,
      dsimp at *,
      have Q := rDC R₁' R₂' Jy',
      --
      cases Q with x₃ Q, cases Q with R₃ Jx,
      refine exists.intro
              { fn := λ p, x₃
              , continuous := sorry
              }
              _,
      apply and.intro,
      { intro q, simp,
        exact sorry -- continuity of y₃
      },
      { intro q, simp,
        exact sorry -- continuity of x₁ and x₂
      }
    end

end Sep
