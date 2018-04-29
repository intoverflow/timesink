/- Affine separation schemes
 -
 -/
import .spec
import .localization
import ..top.sheaf

namespace Sep
universes ℓ ℓ₁ ℓ₂
open Top

def rehome_prime {X : OrdAlg.{ℓ}}
    {u o : X.Top.OI}
    (q : {p // p ∈ X.Top.Open u})
    (H : X.Top.Open u ⊆ X.Top.Open o)
  : {p // p ∈ X.Top.Open o}
 := { val := q.val
    , property := H q.property
    }

structure ClosedAlg
 := (alg : OrdAlg.{ℓ})
    (closed : alg.ord.Closed)

def ClosedAlg.Pt (X : ClosedAlg) := X.alg.Pt
def ClosedAlg.Top (X : ClosedAlg) := X.alg.Top
def ClosedAlg.BasicOpen (X : ClosedAlg) := X.alg.BasicOpen
def ClosedAlg.ZeroPt (X : ClosedAlg) := X.alg.ZeroPt

def PrimeAlg {X : ClosedAlg.{ℓ}}
    (p : X.alg.Pt)
  : OrdAlg.{ℓ}
 := X.alg.Localize X.closed p.set.Compl
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

def BasisAlg {X : ClosedAlg.{ℓ}}
    (S : X.alg.BasicOpen) (SJC : S.set.JoinClosed)
  : OrdAlg.{ℓ}
 := X.alg.Localize X.closed S.set SJC
      begin
        intros x H,
        exact or.inl (S.fixed H)
      end

structure Sec {X : ClosedAlg.{ℓ}} (o : X.Top.OI)
  : Type.{ℓ}
 := (fn : ∀ (p : {p // p ∈ X.Top.Open o})
          , (PrimeAlg p.val).alg.τ)
    (continuous
      : ∀ (p : {p // p ∈ X.Top.Open o})
        , ∃ (u : {u // X.Top.Open u ⊆ X.Top.Open o})
          , p.val ∈ X.Top.Open u.val
          ∧ (∀ (q : {p // p ∈ X.Top.Open u})
             , fn p ≤ fn (rehome_prime q u.property)))
            --  , fn (rehome_prime q u.property) = a))

def Sec.eq {X : ClosedAlg.{ℓ}} {o : X.Top.OI}
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

def res {X : ClosedAlg.{ℓ}} {o u : X.Top.OI}
    (H : X.Top.Open u ⊆ X.Top.Open o)
  : Sec o → Sec u
 := λ s
    , { fn := λ p, s.fn (rehome_prime p H)
      , continuous
         := sorry
      }

def SecAlg {X : ClosedAlg.{ℓ}} (o : X.Top.OI)
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
    }

def SecAlg.UpClosed (X : OrdAlg.{ℓ}) (XUC : X.ord.UpClosed)
    (o : X.Top.OI)
  : (@SecAlg { ClosedAlg
             . alg := X
             , closed := or.inl @XUC
             } o).ord.UpClosed
 := begin
      exact sorry
    end

def SecAlg.DownClosed (X : OrdAlg.{ℓ}) (XDC : X.ord.DownClosed)
    (o : X.Top.OI)
  : (@SecAlg { ClosedAlg
             . alg := X
             , closed := or.inr @XDC
             } o).ord.DownClosed
 := begin
      exact sorry
    end

def SecAlg.Closed {X : ClosedAlg.{ℓ}}
    (o : X.Top.OI)
  : (SecAlg o).ord.Closed
 := begin
      cases X with X XC,
      cases XC with XC XC,
      { apply or.inl,
        apply SecAlg.UpClosed
      },
      { apply or.inr,
        apply SecAlg.DownClosed
      }
    end

def ClosedAlg.StructPreSh (X : ClosedAlg.{ℓ})
  : PreSheaf X.Top OrdAlgCat
 := { Section := SecAlg
    , ρ := λ U₁ U₂ H
           , { rel := λ s₁ s₂, s₂ = res H s₁
             , total := λ s, exists.intro _ rfl
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
    }

def ClosedAlg.StructSh (X : ClosedAlg.{ℓ})
  : Top.Sheaf X.Top OrdAlgCat OrdAlgCat.HasProducts
 := { sh := X.StructPreSh
    , glue := λ U UU Ucover, sorry
    }

def ClosedAlg.to_section (X : ClosedAlg.{ℓ})
    (S : X.BasicOpen) (SJC : S.set.JoinClosed)
  : (BasisAlg S SJC).alg.τ → (X.StructSh.sh.Section (eq S)).alg.τ
 := λ a₀
    , { fn := λ p, a₀
        , continuous
            := λ p, exists.intro
                      { val := eq S
                      , property := λ q Hq, Hq
                      }
                      begin
                        apply and.intro p.property,
                        intro q,
                        apply OrdAlg.refl
                      end
      }

def to_section.inj {X : ClosedAlg.{ℓ}}
    {S : X.BasicOpen} (SJC : S.set.JoinClosed)
    {x₁ x₂ : X.alg.alg.τ}
    (E : X.to_section S SJC x₁ = X.to_section S SJC x₂)
  : x₁ = x₂
 := begin
      have Q₁ := congr_arg (λ (x : Sec (eq S)), x.fn) E,
      have Q₂ := congr_fun Q₁ { val := X.ZeroPt
                              , property := ZeroPt.Everywhere
                              },
      exact Q₂
    end

def to_section.surj {X : ClosedAlg.{ℓ}}
    {S : X.BasicOpen} (SJC : S.set.JoinClosed)
    (s : Sec (eq S))
  : ∃ x, (X.StructSh.sh.Section (eq S)).ord s (X.to_section S SJC x)
 := begin
      existsi s.fn { val := X.ZeroPt, property := ZeroPt.Everywhere },
      intro p,
      have Q := s.continuous p,
      cases Q with U Q, cases Q with Hp E,
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
      exact E'
    end

-- def OrdAlg.to_section__from_section {X : ClosedAlg.{ℓ}}
--     (S : X.BasicOpen) (SJC : S.set.JoinClosed)
--   : FunRel (X.to_section S SJC) ∘ InvFunRel (X.to_section S SJC) = Alg.IdRel _
--  := begin
--       apply funext, intro x, apply funext, intro y,
--       apply eq.symm, apply iff.to_eq, apply iff.intro,
--       { intro H,
--         have Q := to_section.surj SJC x,
--         cases Q with y' E, subst E,
--         have Q := to_section.surj SJC y,
--         cases Q with y₀ E, subst E,
--         refine exists.intro y₀ (and.intro H rfl),
--       },
--       { intro H, cases H with w H,
--         cases H with E₁ E₂,
--         have E₁' := E₁.symm, subst E₁', clear E₁,
--         have E₂' := E₂.symm, subst E₂', clear E₂,
--         exact rfl
--       }
--     end

-- def OrdAlg.from_section__to_section {X : ClosedAlg.{ℓ}}
--     (S : X.BasicOpen) (SJC : S.set.JoinClosed)
--   : InvFunRel (X.to_section S SJC) ∘ FunRel (X.to_section S SJC) = Alg.IdRel _
--  := begin
--       apply funext, intro x, apply funext, intro y,
--       apply eq.symm, apply iff.to_eq, apply iff.intro,
--       { intro E, have E' : x = y := E, subst E', clear E,
--         exact exists.intro (X.to_section S SJC x) (and.intro rfl rfl)
--       },
--       { intro H, cases H with w H,
--         cases H with E₁ E₂,
--         have E₁' := E₁.symm, subst E₁', clear E₁,
--         have E₂' := to_section.inj SJC E₂, subst E₂', clear E₂,
--         exact rfl
--       }
--     end

def ToSection {X : ClosedAlg.{ℓ}}
    (S : X.BasicOpen) (SJC : S.set.JoinClosed)
    : OrdRel
        (BasisAlg S SJC)
        (X.StructSh.sh.Section (eq S))
 := (FunRel (X.to_section S SJC)).OrdRel (λ x, exists.intro _ rfl)

def FromSection {X : ClosedAlg.{ℓ}}
    (S : X.BasicOpen) (SJC : S.set.JoinClosed)
    : OrdRel
        (X.StructSh.sh.Section (eq S))
        (BasisAlg S SJC)
 := { rel := λ x y, x ≤ ClosedAlg.to_section X S SJC y
    , total := to_section.surj SJC
    , action
       := begin
            apply funext, intro x, apply funext, intro y,
            apply iff.to_eq, apply iff.intro,
            { intro H,
              cases H with y' H, cases H with H Hy,
              cases H with x' H, cases H with H Hx,
              apply OrdAlg.trans _ _ _ _ H,
              apply OrdAlg.trans _ _ _ _ Hx,
              intro p,
              dsimp [ClosedAlg.to_section],
              cases Hy,
              { apply Localization.locl.base, exact Rxy },
              { refine Localization.locl.join _ Rx Ry J,
                intro F,
                cases p with p Hp,
                cases Hp with U Hp, cases Hp with H Hp,
                cases H with U₀ H, cases H with H E,
                subst E,
                have E := H.symm, subst E,
                apply cast (congr_fun Hp s),
                exact and.intro Hs F
              }
            },
            { intro H,
              refine exists.intro _ (and.intro _ (OrdAlg.refl _ _)),
              refine exists.intro _ (and.intro _ H),
              intro p,
              apply OrdAlg.refl
            }
          end
    }

def ToSection_FromSection {X : ClosedAlg.{ℓ}}
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

def FromSection_ToSection {X : ClosedAlg.{ℓ}}
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

def ClosedAlg.Spec (X : ClosedAlg.{ℓ})
  : ShSpace OrdAlgCat
 := { Pt := X.Pt
    , Top := X.Top
    , Prod := OrdAlgCat.HasProducts
    , Sh := X.StructSh
    }

def PrimeRel.Spec {A : ClosedAlg.{ℓ₁}} {B : ClosedAlg.{ℓ₁}}
    (r : OrdRel A.alg B.alg)
    (rP : r.PrimeRel)
  : ShHom B.Spec A.Spec
 := { map := PrimeRel.Map r rP
    , sh :=
        { hom := λ U,
          { rel := λ s t
            , ∀ (p : {p // p ∈ B.Top.Open (((PrimeRel.Map r rP).preimage U).val)})
              , r.rel (s.fn { val := (PrimeRel.Map r rP).map p.val
                            , property := (PrimeRel.Map r rP).in_preimage p
                            })
                      (t.fn p)
          , total := sorry
          , action := sorry
          }
        , natural := sorry
        }
    }

def JoinRel.Spec {A : ClosedAlg.{ℓ₁}} {B : ClosedAlg.{ℓ₁}}
    (r : OrdRel A.alg B.alg)
    (rJ : r.JoinRel)
  : ShHom A.Spec B.Spec
 := { map := JoinRel.Map r rJ
    , sh :=
        { hom := λ U,
          { rel := λ s t
            , ∀ (p : {p // p ∈ A.Top.Open (((JoinRel.Map r rJ).preimage U).val)})
              , r.rel (t.fn p)
                      (s.fn { val := (JoinRel.Map r rJ).map p.val
                            , property := (JoinRel.Map r rJ).in_preimage p
                            })
          , total := sorry
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
        , natural := sorry
        }
    }

def JoinRel.Spec.JoinRel {A : ClosedAlg.{ℓ₁}} {B : ClosedAlg.{ℓ₁}}
    (r : OrdRel A.alg B.alg)
    (rJ : r.JoinRel)
    (rDC : r.rel.DownClosed)
    (p : A.Pt)
  : ((JoinRel.Spec r rJ).sh.hom (eq (Nhbd ((JoinRel.Map r rJ).map p)))).rel.Flip.DownClosed
 := begin
      intros x₁ x₂ y₁ y₂ y₃ R₁ R₂ J,
      have Hp : A.Top.Open (((JoinRel.Map r rJ).preimage (eq (Nhbd ((JoinRel.Map r rJ).map p)))).val)
                  p, from
        begin
          existsi A.alg.OpenBasis.Open (Nhbd p),
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
