/- Affine separation schemes
 -
 -/
import .sheaf
import .primeSpec
import .localization

namespace Sep
universes ℓ ℓ₁ ℓ₂
open Top

def expand_prime {X : OrdAlg.{ℓ}}
    {o : (OrdAlg.PrimeSpec.Topology X).OI}
    (u : {u // (OrdAlg.PrimeSpec.Topology X).Open u ⊆ (OrdAlg.PrimeSpec.Topology X).Open o})
    (q : {p // p ∈ (OrdAlg.PrimeSpec.Topology X).Open u})
  : {p // p ∈ (OrdAlg.PrimeSpec.Topology X).Open o}
 := { val := q.val
    , property := u.property q.property
    }

def local_helper {X : OrdAlg.{ℓ}} (S : Set X.alg)
  (HS : Rel.FnInv (X.ord) S.Compl = S.Compl)
  : X.ord.Local S
 := begin
      apply Confined.Local,
      intros x Hx,
      rw HS.symm,
      exact Hx
    end

def PrimeAlg {X : OrdAlg.{ℓ}} (XUC : X.ord.UpClosed)
    (p : X.PrimeSpec)
  : OrdAlg.{ℓ}
 := UpClosed.Prime.Localize X @XUC p.set
              begin
                apply local_helper,
                rw Set.ComplCompl,
                exact p.locl
              end
              p.prime

structure Sec {X : OrdAlg.{ℓ}} (XUC : X.ord.UpClosed)
    (o : (OrdAlg.PrimeSpec.Topology X).OI)
  : Type.{ℓ}
 := (fn : ∀ (p : {p // p ∈ (OrdAlg.PrimeSpec.Topology X).Open o})
          , (PrimeAlg @XUC p.val).alg.τ)
    (continuous
      : ∀ (p : {p // p ∈ (OrdAlg.PrimeSpec.Topology X).Open o})
        , ∃ (u : {u // (OrdAlg.PrimeSpec.Topology X).Open u ⊆ (OrdAlg.PrimeSpec.Topology X).Open o})
            (a : X.alg.τ)
          , p.val ∈ (OrdAlg.PrimeSpec.Topology X).Open u.val
          ∧ (∀ (q : {p // p ∈ (OrdAlg.PrimeSpec.Topology X).Open u})
              , fn (expand_prime u q) = a))

def Sec.eq {X : OrdAlg.{ℓ}} {XUC : X.ord.UpClosed}
    {o : (OrdAlg.PrimeSpec.Topology X).OI}
    (s₁ s₂ : Sec @XUC o)
    (E : ∀ (p : {p // p ∈ (OrdAlg.PrimeSpec.Topology X).Open o})
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

def res {X : OrdAlg.{ℓ}} (XUC : X.ord.UpClosed)
    {o u : (OrdAlg.PrimeSpec.Topology X).OI}
    (H : (OrdAlg.PrimeSpec.Topology X).Open u ⊆ (OrdAlg.PrimeSpec.Topology X).Open o)
  : Sec @XUC o → Sec @XUC u
 := λ s
    , { fn := λ p, s.fn (expand_prime {val := u, property := H} p)
      , continuous
         := sorry
      }

def SecAlg {X : OrdAlg.{ℓ}} (XUC : X.ord.UpClosed) (o : (OrdAlg.PrimeSpec.Topology X).OI)
  : OrdAlg.{ℓ}
 := { alg :=  { τ := Sec @XUC o
              , join := λ s₁ s₂ s₃
                        , ∀ (p : {p // p ∈ (OrdAlg.PrimeSpec.Topology X).Open o})
                          , (PrimeAlg @XUC p.val).alg.join (s₁.fn p) (s₂.fn p) (s₃.fn p)
              , comm := λ s₁ s₃ s₃ J p, (PrimeAlg @XUC p.val).alg.comm (J p)
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
             , (∀ (p : {p // p ∈ (OrdAlg.PrimeSpec.Topology X).Open o})
                , (PrimeAlg @XUC p.val).ord (s₁.fn p) (s₂.fn p))
    , refl := λ s p
              , (PrimeAlg @XUC p.val).refl (s.fn p)
    , trans := λ s₁ s₂ s₃ L₁₂ L₂₃ p
               , (PrimeAlg @XUC p.val).trans _ _ _ (L₁₂ p) (L₂₃ p)
    }

def OrdAlg.Struct (X : OrdAlg.{ℓ}) (XUC : X.ord.UpClosed)
  : Sheaf (OrdAlg.PrimeSpec.Topology X)
 := { Section := SecAlg @XUC
    , ρ := λ U₁ U₂ H
           , { rel := λ s₁ s₂, s₂ = res @XUC H s₁
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

def OrdAlg.to_section {X : OrdAlg.{ℓ}} (XUC : X.ord.UpClosed)
    (S : Set X.alg)
  : X.alg.τ → Sec @XUC (eq S)
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

def OrdAlg.to_section.inj {X : OrdAlg.{ℓ}} (XUC : X.ord.UpClosed)
    {S : Set X.alg}
    {x₁ x₂ : X.alg.τ}
    (E : OrdAlg.to_section @XUC S x₁ = OrdAlg.to_section @XUC S x₂)
  : x₁ = x₂
 := begin
      have Q₁ := congr_arg (λ (x : Sec @XUC (eq S)), x.fn) E,
      have Q₂ := congr_fun Q₁ { val := X.ZeroPt, property := ZeroPt.Everywhere },
      exact Q₂
    end

def OrdAlg.to_section.surj {X : OrdAlg.{ℓ}} (XUC : X.ord.UpClosed)
    {S : Set X.alg}
    (s : Sec @XUC (eq S))
  : ∃ x, OrdAlg.to_section @XUC S x = s
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

def OrdAlg.ToSection {X : OrdAlg.{ℓ}} (XUC : X.ord.UpClosed)
    (S : Set X.alg) (HS : X.ord.FnInv S.Compl = S.Compl) (SJC : S.JoinClosed)
    : OrdRel
        (UpClosed.JoinClosed.Localize X @XUC S (local_helper _ HS) SJC)
        ((OrdAlg.Struct X @XUC).Section (eq S))
 := { rel := λ x y, y = OrdAlg.to_section @XUC S x
    , incr := λ x₁ x₂ y₂ E L₁₂
              , begin
                  subst E,
                  refine exists.intro _ (and.intro rfl _),
                  intro p,
                  simp [OrdAlg.to_section],
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
                    exact Hp (and.intro Hs F)
                  }
                end
    }

def OrdAlg.FromSection {X : OrdAlg.{ℓ}} (XUC : X.ord.UpClosed)
    (S : Set X.alg) (SJC : S.JoinClosed)
    (HS : X.ord.FnInv S.Compl = S.Compl)
    : OrdRel
        ((OrdAlg.Struct X @XUC).Section (eq S))
        (UpClosed.JoinClosed.Localize X @XUC S (local_helper _ HS) SJC)
 := { rel := λ x y, x = OrdAlg.to_section @XUC S y
    , incr := λ v₁ v₂ w₂ E L₁₂
              , begin
                  subst E,
                  have Q := OrdAlg.to_section.surj @XUC v₁,
                  cases Q with w₁ Hw₁,
                  existsi w₁,
                  apply and.intro Hw₁.symm,
                  subst Hw₁,
                  have HS' : X.ord.FnInv (JoinClosure S).Compl = (JoinClosure S).Compl, from
                    begin
                      rw JoinClosed.JoinClosure @SJC,
                      exact HS
                    end,
                  have Q := L₁₂ { val := X.BigPt @XUC S HS'
                                , property := BigPt.In
                                },
                  cases Q ; clear Q,
                  { apply Localization.locl.base, exact Rxy
                  },
                  { have Hs' : s ∈ S, from
                      begin
                        dsimp [OrdAlg.BigPt] at Hs,
                        rw Set.ComplCompl at Hs,
                        rw JoinClosed.JoinClosure @SJC at Hs,
                        assumption
                      end,
                    exact Localization.locl.join Hs' Rx Ry J
                  }
                end
    }

-- namespace Structure
-- namespace Section

-- def non_vanishing {X : Alg.{ℓ}}
--     (u : (Alg.PrimeSpec.Topology X).OI)
--   : Type.{ℓ}
--  := {f // ∀ (q : {p // p ∈ (Alg.PrimeSpec.Topology X).Open u}) , ¬ f ∈ q.val.set}

-- def non_vanishing.res {X : Alg.{ℓ}}
--     {u u' : (Alg.PrimeSpec.Topology X).OI}
--     (H : (Alg.PrimeSpec.Topology X).Open u' ⊆ (Alg.PrimeSpec.Topology X).Open u)
--     (f : Localization.Mon (non_vanishing u))
--   : Localization.Mon (non_vanishing u')
--  := Localization.Mon.subtype f
--       (λ a Ha q F, Ha { val := q.val, property := H q.property } F)

-- def non_vanishing.to {X : Alg.{ℓ}}
--     {u : (Alg.PrimeSpec.Topology X).OI}
--     (q : {p // p ∈ (Alg.PrimeSpec.Topology X).Open u})
--     (f : Localization.Mon (non_vanishing u))
--   : Localization.Mon q.val.prime.Complement_JoinClosed.Alg.τ
--  := Localization.Mon.subtype f
--       (λ a Ha F, Ha { val := q.val, property := q.property } F)

-- structure τ {X : Alg.{ℓ}} (o : (Alg.PrimeSpec.Topology X).OI)
--   : Type.{ℓ}
--  := (fn : ∀ (p : {p // p ∈ (Alg.PrimeSpec.Topology X).Open o})
--           , (PrimeLocalize p.val).τ)
--     (continuous
--       : ∀ (p : {p // p ∈ (Alg.PrimeSpec.Topology X).Open o})
--         , ∃ (u : {u // (Alg.PrimeSpec.Topology X).Open u ⊆ (Alg.PrimeSpec.Topology X).Open o})
--             (ff : Localization.Mon (non_vanishing u.val))
--             (a : X.τ)
--           , p.val ∈ (Alg.PrimeSpec.Topology X).Open u.val
--           ∧ (∀ (q : {p // p ∈ (Alg.PrimeSpec.Topology X).Open u})
--               , fn (expand_prime u q)
--                   == X.localize_at q a (non_vanishing.to q ff) ))

-- def τ.eq {X : Alg.{ℓ}} (o : (Alg.PrimeSpec.Topology X).OI)
--     (s₁ s₂ : τ o)
--     (E : ∀ (p : {p // p ∈ (Alg.PrimeSpec.Topology X).Open o})
--          , (s₁.fn p) = (s₂.fn p))
--   : s₁ = s₂
--  := begin
--       cases s₁ with s₁ Hs₁,
--       cases s₂ with s₂ Hs₂,
--       have E' : s₁ = s₂, from
--         begin
--           apply funext, intro p, apply E
--         end,
--       subst E'
--     end

-- def res {X : Alg.{ℓ}}
--     {o u : (Alg.PrimeSpec.Topology X).OI}
--     (H : (Alg.PrimeSpec.Topology X).Open u ⊆ (Alg.PrimeSpec.Topology X).Open o)
--   : τ o → τ u
--  := λ s
--     , { fn := λ p, cast begin trivial end (s.fn (expand_prime {val := u, property := H} p))
--       , continuous
--          := begin
--               intro p,
--               have C := s.continuous (expand_prime {val := u, property := H} p),
--               cases C with u' C,
--               cases C with ff C,
--               cases C with a C,
--               let u'' := (Alg.PrimeSpec.Topology X).inter u u',
--               have Hu₁ : (Alg.PrimeSpec.Topology X).Open u'' ⊆ (Alg.PrimeSpec.Topology X).Open u := Topology.Inter.Subset_l _ _,
--               have Hu₂ : (Alg.PrimeSpec.Topology X).Open u'' ⊆ (Alg.PrimeSpec.Topology X).Open u' := Topology.Inter.Subset_r _ _,
--               refine exists.intro { val := u'', property := Hu₁ } _,
--               refine exists.intro (non_vanishing.res Hu₂ ff) _,
--               existsi a,
--               apply and.intro,
--               { simp [u''], rw Topology.Ointer,
--                 exact and.intro p.property C.1
--               },
--               intro q,
--               exact sorry -- is true
--             end
--       }

-- def res_id {X : Alg.{ℓ}}
--     {o : (Alg.PrimeSpec.Topology X).OI}
--     {H : (Alg.PrimeSpec.Topology X).Open o ⊆ (Alg.PrimeSpec.Topology X).Open o}
--     {s : τ o}
--   : res H s = s
--  := begin
--       apply τ.eq, intro p, simp [res],
--       apply eq_of_heq,
--       have E : cast _ (s.fn (expand_prime ⟨o, H⟩ p)) == s.fn (expand_prime ⟨o, H⟩ p) := cast_heq rfl _,
--       refine heq.trans E _,
--       clear E,
--       have E : expand_prime ⟨o, H⟩ p = p, from
--         begin cases p with p Hp, trivial end,
--       rw E
--     end

-- def res_circ {X : Alg.{ℓ}}
--     {o₁ o₂ o₃ : (Alg.PrimeSpec.Topology X).OI}
--     {H₁₂ : (Alg.PrimeSpec.Topology X).Open o₂ ⊆ (Alg.PrimeSpec.Topology X).Open o₁}
--     {H₂₃ : (Alg.PrimeSpec.Topology X).Open o₃ ⊆ (Alg.PrimeSpec.Topology X).Open o₂}
--     {H₁₃ : (Alg.PrimeSpec.Topology X).Open o₃ ⊆ (Alg.PrimeSpec.Topology X).Open o₁}
--     {s : τ o₁}
--   : res H₂₃ (res H₁₂ s) = res H₁₃ s
--  := begin
--       apply τ.eq, intro p, simp [res],
--       exact sorry -- is true
--     end

-- def locl {X : Alg}
--     {U : (Alg.PrimeSpec.Topology X).OI}
--     {UU : set ((Alg.PrimeSpec.Topology X).OI)}
--     (Ucover : (Alg.PrimeSpec.Topology X).Open U = ⋃₀((Alg.PrimeSpec.Topology X).Open <$> UU))
--     {s t : τ U}
--     (E : ∀ (V : {V : (Alg.PrimeSpec.Topology X).OI // V ∈ UU})
--          , res (Topology.Cover.Subset Ucover V.property) s
--             = res (Topology.Cover.Subset Ucover V.property) t)
--   : s = t
--  := begin
--       apply τ.eq,
--       intro p,
--       cases p with p Hp,
--       have Qp := Hp,
--       rw Ucover at Qp,
--       cases Qp with V HV,
--       cases HV with HV Hp',
--       cases HV with u Hu,
--       cases Hu with Hu E',
--       subst E',
--       have E' := congr_fun
--                   (congr_arg τ.fn (E { val := u, property := Hu }))
--                   { val := p, property := Hp' },
--       simp [res] at E',
--       refine eq.trans _ (eq.trans E' _),
--       { exact sorry -- is true
--       },
--       { exact sorry -- is true
--       }
--     end

-- noncomputable def glue {X : Alg}
--     {U : (Alg.PrimeSpec.Topology X).OI}
--     {UU : set ((Alg.PrimeSpec.Topology X).OI)}
--     (Ucover : (Alg.PrimeSpec.Topology X).Open U = ⋃₀((Alg.PrimeSpec.Topology X).Open <$> UU))
--     (loc : Π (V : {V : (Alg.PrimeSpec.Topology X).OI // V ∈ UU}), τ V.val)
--     (E : ∀ (V₁ V₂ : {V : (Alg.PrimeSpec.Topology X).OI // V ∈ UU})
--          , res (Topology.Inter.Subset_l _ V₂.val) (loc V₁)
--             = res (Topology.Inter.Subset_r V₁.val _) (loc V₂))
--   : τ U
--  := { fn := λ p, let v := Topology.Cover.mem_fn Ucover p
--                  in cast begin trivial end
--                       ((loc { val := v.val, property := v.property.1 }).fn
--                            { val := p.val, property := v.property.2 })
--     , continuous
--        := begin
--             intro p,
--             let v := Topology.Cover.mem_fn Ucover p,
--             have Q := (loc { val := v.val, property := v.property.1 }).continuous
--                            { val := p.val, property := v.property.2 },
--             cases Q with v' Q,
--             cases Q with ff Q,
--             cases Q with a Q,
--             refine exists.intro { val := v'.val, property := _ } _,
--             { intros x Hx,
--               apply Topology.Cover.Subset Ucover v.property.1,
--               apply v'.property,
--               exact Hx
--             },
--             existsi ff,
--             existsi a,
--             apply and.intro Q.1,
--             intro q,
--             refine heq.trans _ (Q.2 q),
--             simp,
--             exact sorry -- is true
--           end
--     }

-- end Section


-- def Section {X : Alg.{ℓ}} (o : (Alg.PrimeSpec.Topology X).OI)
--   : Alg.{ℓ}
--  := { τ := Section.τ o
--     , join := λ s₁ s₂ s₃
--               , ∀ (p : {p // p ∈ (Alg.PrimeSpec.Topology X).Open o})
--                 , (PrimeLocalize p.val).join (s₁.fn p) (s₂.fn p) (s₃.fn p)
--     , comm := λ s₁ s₃ s₃ J p, (PrimeLocalize p.val).comm (J p)
--     , assoc := λ s₁ s₂ s₃ s₁₂ s₁₂₃ J₁₂ J₁₂₃ P C
--                , sorry
--               --  , C { x := { fn := λ p, begin end
--               --             , continuous := begin end
--               --             }
--               --      , J₁ := begin end
--               --      , J₂ := begin end
--               --      }
--     }

-- end Structure

-- def Alg.Struct (X : Alg.{ℓ})
--   : Sheaf (Alg.PrimeSpec.Topology X)
--  := { Section := Structure.Section
--     , ρ := λ U₁ U₂ H s₁ s₂, s₂ = Structure.Section.res H s₁
--     , ρ_id
--        := λ U H
--           , begin
--               apply funext, intro s₁,
--               apply funext, intro s₂,
--               apply iff.to_eq, apply iff.intro,
--               { intro E, rw [Structure.Section.res_id] at E, exact E.symm },
--               { intro E, rw [Structure.Section.res_id], exact E.symm }
--             end
--     , ρ_circ
--        := λ U₁ U₂ U₃ H₁₂ H₂₃ H₁₃
--           , begin
--               apply funext, intro s₁,
--               apply funext, intro s₂,
--               apply iff.to_eq, apply iff.intro,
--               { intro E, cases E with s' E, simp at E,
--                 cases E with E₁ E₂, subst E₂, subst E₁,
--                 rw [Structure.Section.res_circ]
--               },
--               { intro E,
--                 existsi Structure.Section.res H₁₂ s₁,
--                 simp, subst E,
--                 rw [Structure.Section.res_circ]
--               }
--             end
--     , locl
--        := λ U UU Ucover s t E
--           , begin
--               apply Structure.Section.locl Ucover,
--               intro V,
--               have Q := congr_fun (E V)
--                           (Structure.Section.res
--                             (Topology.Cover.Subset Ucover V.property)
--                             s),
--               simp at Q,
--               rw Q.symm,
--               exact true.intro
--             end
--     , glue
--        := λ U UU Ucover loc E
--           , begin
--               refine exists.intro (Structure.Section.glue Ucover loc _) _,
--               { intros V₁ V₂,
--                 have Q := congr_fun (E V₁ V₂)
--                             (Structure.Section.res
--                               (Topology.Inter.Subset_l _ V₂.val)
--                               (loc V₁)),
--                 simp at Q,
--                 refine cast _ true.intro,
--                 refine eq.trans _ Q,
--                 apply iff.to_eq, apply iff.intro,
--                 { intro H, trivial },
--                 { intro H, exact true.intro }
--               },
--               { intro V,
--                 apply Structure.Section.τ.eq,
--                 intro p,
--                 simp [Structure.Section.glue, Structure.Section.res],
--                 exact sorry -- is true
--               }
--             end
--     }

-- def Alg.to_section_on_rep {X : Alg.{ℓ}} {S : Set X}
--     (a₀ : (Localization.valid_local (JoinClosure.JoinClosed S)))
--   : (X.Struct.Section (eq S)).τ
--  := let f' : ∀ (p : {p // p ∈ (Alg.PrimeSpec.Topology X).Open (eq S)})
--                 , Localization.Mon p.val.prime.Complement_JoinClosed.Alg.τ
--               := begin
--                     intro p,
--                     refine Localization.Mon.subtype a₀.val.2 _,
--                     { intros x Sx,
--                       cases p with p Hp,
--                       cases Hp with p₀ Hp,
--                       cases Hp with Hp' Hp,
--                       cases Hp' with oi Hoi,
--                       cases Hoi with Hoi E,
--                       subst E, cases Hoi,
--                       induction Sx with x' F x₁ x₂ x₃ J S₁ S₂,
--                       { intro F', exact Hp (and.intro F F') },
--                       { intro F',
--                         cases p.prime _ _ _ J F' with H H,
--                         { exact ih_1 H },
--                         { exact ih_2 H }
--                       }
--                     }
--                   end
--     in { fn := λ p
--                 , ⟦ { val := (a₀.val.1, f' p)
--                     , property
--                       := begin
--                             cases a₀.property with a₀' H,
--                             cases H with s₀' H,
--                             existsi a₀',
--                             existsi f' p,
--                             cases a₀ with a₀'' s₀'',
--                             cases H,
--                             apply Localization.equiv.refl
--                           end
--                       } ⟧
--         , continuous
--           := begin
--                 intro p,
--                 refine exists.intro { val := eq S, property := λ x H, H } _,
--                 simp,
--                 refine exists.intro (Localization.Mon.subtype a₀.val.2 _) _,
--                 { intros x Sx q,
--                   cases q with q Hq,
--                   cases Hq with q₀ Hq,
--                   cases Hq with Hq' Hq,
--                   cases Hq' with oi Hoi,
--                   cases Hoi with Hoi E,
--                   subst E, cases Hoi,
--                   induction Sx with x' F x₁ x₂ x₃ J S₁ S₂,
--                   { intro F', exact Hq (and.intro F F') },
--                   { intro F',
--                     cases q.prime _ _ _ J F' with H H,
--                     { exact ih_1 H },
--                     { exact ih_2 H }
--                   }
--                 },
--                 cases a₀ with a₀ H₀,
--                 cases H₀ with a₀' H₀,
--                 cases H₀ with s₀' H₀,
--                 cases H₀,
--                 existsi a₀',
--                 apply and.intro p.property,
--                 intro q,
--                 simp [Alg.localize_at],
--                 --
--                 exact sorry
--               end
--         }

-- def Alg.to_section (X : Alg.{ℓ}) (S : Set X)
--     (a₀ : S.Localize.τ)
--   : (X.Struct.Section (eq S)).τ
--  := quot.lift_on a₀ Alg.to_section_on_rep
--       begin
--         intros a b E,
--         cases a with a Ha,
--         cases a with a sa,
--         cases b with b Hb,
--         cases b with b sb,
--         cases E,
--         apply Structure.Section.τ.eq,
--         intro p,
--         simp [Alg.to_section_on_rep],
--         apply quot.sound,
--         constructor,
--         exact sorry -- is true
--       end

-- def Alg.to_global_section (X : Alg.{ℓ})
--     (a : X.τ)
--   : (X.Struct.Section (Alg.PrimeSpec.Topology X).whole).τ
--  := { fn := λ p, X.localize_at p a (Localization.Mon.zero _)
--     , continuous
--        := begin
--             intro p,
--             refine exists.intro { val := (Alg.PrimeSpec.Topology X).whole, property := (λ q Hq, Hq) } _,
--             existsi Localization.Mon.zero _,
--             existsi a,
--             apply and.intro (Alg.PrimeSpec.Topology X).in_whole,
--             intro q,
--             simp [Alg.localize_at],
--             exact sorry -- is true
--           end
--     }


-- namespace BasisStruct

-- def res_inter_l {X : Alg.{ℓ₁}}
--     {S₁ S₂ : Set X}
--   : PrimeSpec.BasicOpen (S₁ ∪ S₂) ⊆ PrimeSpec.BasicOpen S₁
--  := @OpenBasis.Inter.Subset_l _ (Alg.PrimeSpec.OpenBasis X) S₁ S₂

-- def res_inter_r {X : Alg.{ℓ₁}}
--     {S₁ S₂ : Set X}
--   : PrimeSpec.BasicOpen (S₁ ∪ S₂) ⊆ PrimeSpec.BasicOpen S₂
--  := @OpenBasis.Inter.Subset_r _ (Alg.PrimeSpec.OpenBasis X) S₁ S₂

-- def res_cover {X : Alg.{ℓ₁}}
--     {S : Set X} {SS : set (Set X)}
--     (Scover : PrimeSpec.BasicOpen S = set.sUnion (PrimeSpec.BasicOpen <$> SS))
--     {S' : {S' // S' ∈ SS}}
--   : PrimeSpec.BasicOpen S'.val ⊆ PrimeSpec.BasicOpen S
--  := @OpenBasis.Cover.Subset _ (Alg.PrimeSpec.OpenBasis X) S SS Scover S'.val S'.property


-- def res {X : Alg.{ℓ₁}}
--     {S₁ S₂ : Set X}
--     (s₁ : {s₁ // S₁ s₁})
--     (Res : PrimeSpec.BasicOpen S₂ ⊆ PrimeSpec.BasicOpen S₁)
--   : (X.Localize S₁).τ → (X.Localize S₂).τ
--  := sorry

-- def extend {X : Alg.{ℓ₁}}
--     {S₁ S₂ : Set X}
--     (Res : PrimeSpec.BasicOpen S₂ ⊆ PrimeSpec.BasicOpen S₁)
--   : (X.Localize S₂).τ → (X.Localize S₁).τ
--  := sorry


-- def ρ {X : Alg.{ℓ₁}}
--     (S₁ S₂ : Set X) (Res : PrimeSpec.BasicOpen S₂ ⊆ PrimeSpec.BasicOpen S₁)
--   : Rel (X.Localize S₁) (X.Localize S₂)
--  := sorry

-- def ρ_id {X : Alg.{ℓ₁}}
--     (S : Set X)
--     (Res : PrimeSpec.BasicOpen S ⊆ PrimeSpec.BasicOpen S)
--   : ρ S S Res = Alg.IdRel (X.Localize S)
--  := sorry

-- def ρ_circ {X : Alg.{ℓ₁}}
--     (S₁ S₂ S₃ : Set X)
--     (Res₁₂ : PrimeSpec.BasicOpen S₂ ⊆ PrimeSpec.BasicOpen S₁)
--     (Res₂₃ : PrimeSpec.BasicOpen S₃ ⊆ PrimeSpec.BasicOpen S₂)
--     (Res₁₃ : PrimeSpec.BasicOpen S₃ ⊆ PrimeSpec.BasicOpen S₁)
--   : ρ S₂ S₃ Res₂₃ ∘ ρ S₁ S₂ Res₁₂ = ρ S₁ S₃ Res₁₃
--  := sorry

-- def locl {X : Alg.{ℓ₁}}
--     (S : Set X) (SS : set (Set X))
--     (Scover : PrimeSpec.BasicOpen S = set.sUnion (PrimeSpec.BasicOpen <$> SS))
--     (s t : (X.Localize S).τ)
--     (E : ∀ (S' : {S' // S' ∈ SS})
--           , ρ S S' (res_cover Scover) s
--               = ρ S S' (res_cover Scover) t)
--   : s = t
--  := sorry

-- def glue_rel {X : Alg.{ℓ₁}}
--     {S : Set X} {SS : set (Set X)}
--     (Scover : PrimeSpec.BasicOpen S = set.sUnion (PrimeSpec.BasicOpen <$> SS))
--     {W : Alg.{ℓ₂}}
--     (r : ∀ (S' : {S' // S' ∈ SS}), Rel W (X.Localize S'))
--     (E : ∀ (S₁ S₂ : {S' // S' ∈ SS})
--           , ρ S₁.val (S₁ ∪ S₂) res_inter_l ∘ r S₁
--             = ρ S₂.val (S₁ ∪ S₂) res_inter_r ∘ r S₂)
--   : Rel W (X.Localize S)
--  := sorry

-- def glue_eq {X : Alg.{ℓ₁}}
--     {S : Set X} {SS : set (Set X)}
--     (Scover : PrimeSpec.BasicOpen S = set.sUnion (PrimeSpec.BasicOpen <$> SS))
--     {W : Alg.{ℓ₂}}
--     (r : ∀ (S' : {S' // S' ∈ SS}), Rel W (X.Localize S'))
--     (E : ∀ (S₁ S₂ : {S' // S' ∈ SS})
--           , ρ S₁.val (S₁ ∪ S₂) res_inter_l ∘ r S₁
--             = ρ S₂.val (S₁ ∪ S₂) res_inter_r ∘ r S₂)
--   : ∀ S', r S' = ρ S S' (res_cover Scover) ∘ (glue_rel Scover r E)
--  := sorry

-- end BasisStruct

-- def Alg.BasisStruct (X : Alg.{ℓ₁})
--   : BasisSheaf (Alg.PrimeSpec.OpenBasis X)
--  := { Section := X.Localize
--     , ρ := BasisStruct.ρ
--     , ρ_id := BasisStruct.ρ_id
--     , ρ_circ := BasisStruct.ρ_circ
--     , locl := BasisStruct.locl
--     , glue := @BasisStruct.glue_rel X
--     , glue_eq := @BasisStruct.glue_eq X
--     }

end Sep
