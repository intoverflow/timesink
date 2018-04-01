/- Affine separation schemes
 -
 -/
import .sheaf
import .primeSpec
import .localization

namespace Sep
universes ℓ ℓ₁ ℓ₂
open Top

namespace Struct
namespace Section

def expand_prime {X : Alg.{ℓ}}
    {o : (Alg.PrimeSpec.Topology X).OI}
    (u : {u // (Alg.PrimeSpec.Topology X).Open u ⊆ (Alg.PrimeSpec.Topology X).Open o})
    (q : {p // p ∈ (Alg.PrimeSpec.Topology X).Open u})
  : {p // p ∈ (Alg.PrimeSpec.Topology X).Open o}
 := { val := q.val
    , property := u.property q.property
    }

def non_vanishing {X : Alg.{ℓ}}
    (u : (Alg.PrimeSpec.Topology X).OI)
  : Type.{ℓ}
 := {f // ∀ (q : {p // p ∈ (Alg.PrimeSpec.Topology X).Open u}) , ¬ f ∈ q.val.set}

def non_vanishing.res {X : Alg.{ℓ}}
    {u u' : (Alg.PrimeSpec.Topology X).OI}
    -- {u u' : {u // (Alg.PrimeSpec.Topology X).Open u ⊆ (Alg.PrimeSpec.Topology X).Open o}}
    (H : (Alg.PrimeSpec.Topology X).Open u' ⊆ (Alg.PrimeSpec.Topology X).Open u)
    (f : non_vanishing u)
  : non_vanishing u'
 := { val := f.val
    , property := λ q, f.property
                          { val := q.val
                          , property := H q.property
                          }
    }

def non_vanishing.to {X : Alg.{ℓ}}
    {o : (Alg.PrimeSpec.Topology X).OI}
    {u : {u // (Alg.PrimeSpec.Topology X).Open u ⊆ (Alg.PrimeSpec.Topology X).Open o}}
    (q : {p // p ∈ (Alg.PrimeSpec.Topology X).Open u})
    (f : non_vanishing u.val)
  : q.val.prime.Complement_JoinClosed.Alg.τ
 := { val := f.val, property := f.property q }

def non_vanishing.to.val {X : Alg.{ℓ}}
    {o : (Alg.PrimeSpec.Topology X).OI}
    {u : {u // (Alg.PrimeSpec.Topology X).Open u ⊆ (Alg.PrimeSpec.Topology X).Open o}}
    {q : {p // p ∈ (Alg.PrimeSpec.Topology X).Open u}}
    {f : non_vanishing u.val}
  : (non_vanishing.to q f).val = f.val
 := rfl

structure τ {X : Alg.{ℓ}} (o : (Alg.PrimeSpec.Topology X).OI)
  : Type.{ℓ}
 := (fn : ∀ (p : {p // p ∈ (Alg.PrimeSpec.Topology X).Open o})
          , (PrimeLocalize p.val).τ)
    (continuous
      : ∀ (p : {p // p ∈ (Alg.PrimeSpec.Topology X).Open o})
        , ∃ (u : {u // (Alg.PrimeSpec.Topology X).Open u ⊆ (Alg.PrimeSpec.Topology X).Open o})
            (ff : list (non_vanishing u.val))
            (a : X.τ)
          , p.val ∈ (Alg.PrimeSpec.Topology X).Open u.val
          ∧ (∀ (q : {p // p ∈ (Alg.PrimeSpec.Topology X).Open u})
              , fn (expand_prime u q) = X.localize_at q a (list.map (non_vanishing.to q) ff)))

def τ.eq {X : Alg.{ℓ}} (o : (Alg.PrimeSpec.Topology X).OI)
    (s₁ s₂ : τ o)
    (E : ∀ (p : {p // p ∈ (Alg.PrimeSpec.Topology X).Open o})
         , (s₁.fn p) = (s₂.fn p))
  : s₁ = s₂
 := begin
      cases s₁ with s₁ Hs₁,
      cases s₂ with s₂ Hs₂,
      have E' : s₁ = s₂, from
        begin
          apply funext, intro p,
          apply PrimeLocalize.eq,
          apply congr_arg _ (E p)
        end,
      subst E'
    end

def res {X : Alg.{ℓ}}
    {o u : (Alg.PrimeSpec.Topology X).OI}
    (H : (Alg.PrimeSpec.Topology X).Open u ⊆ (Alg.PrimeSpec.Topology X).Open o)
  : τ o → τ u
 := λ s
    , { fn := λ p, cast
                    begin simp [expand_prime] end
                    (s.fn (expand_prime {val := u, property := H} p))
      , continuous
         := begin
              intro p,
              have C := s.continuous (expand_prime {val := u, property := H} p),
              cases C with u' C,
              cases C with ff C,
              cases C with a C,
              let u'' := (Alg.PrimeSpec.Topology X).inter u u',
              have Hu₁ : (Alg.PrimeSpec.Topology X).Open u'' ⊆ (Alg.PrimeSpec.Topology X).Open u := Topology.Inter.Subset_l _ _,
              have Hu₂ : (Alg.PrimeSpec.Topology X).Open u'' ⊆ (Alg.PrimeSpec.Topology X).Open u' := Topology.Inter.Subset_r _ _,
              refine exists.intro { val := u'', property := Hu₁ } _,
              refine exists.intro (list.map (non_vanishing.res Hu₂) ff) _,
              existsi a,
              apply and.intro,
              { simp [u''], rw Topology.Ointer,
                exact and.intro p.property C.1
              },
              intro q,
              exact sorry -- is true
            end
      }

def res_id {X : Alg.{ℓ}}
    {o : (Alg.PrimeSpec.Topology X).OI}
    {H : (Alg.PrimeSpec.Topology X).Open o ⊆ (Alg.PrimeSpec.Topology X).Open o}
    {s : τ o}
  : res H s = s
 := begin
      apply τ.eq, intro p, simp [res],
      apply eq_of_heq,
      have E : cast _ (s.fn (expand_prime ⟨o, H⟩ p)) == s.fn (expand_prime ⟨o, H⟩ p) := cast_heq rfl _,
      refine heq.trans E _,
      clear E,
      have E : expand_prime ⟨o, H⟩ p = p, from
        begin cases p with p Hp, trivial end,
      rw E
    end

def res_circ {X : Alg.{ℓ}}
    {o₁ o₂ o₃ : (Alg.PrimeSpec.Topology X).OI}
    {H₁₂ : (Alg.PrimeSpec.Topology X).Open o₂ ⊆ (Alg.PrimeSpec.Topology X).Open o₁}
    {H₂₃ : (Alg.PrimeSpec.Topology X).Open o₃ ⊆ (Alg.PrimeSpec.Topology X).Open o₂}
    {H₁₃ : (Alg.PrimeSpec.Topology X).Open o₃ ⊆ (Alg.PrimeSpec.Topology X).Open o₁}
    {s : τ o₁}
  : res H₂₃ (res H₁₂ s) = res H₁₃ s
 := begin
      apply τ.eq, intro p, simp [res],
      exact sorry
    end

def locl {X : Alg}
    {U : (Alg.PrimeSpec.Topology X).OI}
    {UU : set ((Alg.PrimeSpec.Topology X).OI)}
    (Ucover : (Alg.PrimeSpec.Topology X).Open U = ⋃₀((Alg.PrimeSpec.Topology X).Open <$> UU))
    {s t : τ U}
    (E : ∀ (V : {V : (Alg.PrimeSpec.Topology X).OI // V ∈ UU})
         , res (Topology.Cover.Subset Ucover V.property) s
            = res (Topology.Cover.Subset Ucover V.property) t)
  : s = t
 := begin
      apply τ.eq,
      intro p,
      cases p with p Hp,
      have Qp := Hp,
      rw Ucover at Qp,
      cases Qp with V HV,
      cases HV with HV Hp',
      cases HV with u Hu,
      cases Hu with Hu E',
      subst E',
      have E' := congr_fun (congr_arg τ.fn (E { val := u, property := Hu })) ⟨p, Hp'⟩,
      simp [res] at E',
      refine eq.trans _ (eq.trans E' _),
      { exact sorry -- true
      },
      { exact sorry -- true
      }
    end

end Section

def Section {X : Alg.{ℓ}} (o : (Alg.PrimeSpec.Topology X).OI)
  : Alg.{ℓ}
 := { τ := Section.τ o
    , join := λ s₁ s₂ s₃
              , ∀ (p : {p // p ∈ (Alg.PrimeSpec.Topology X).Open o})
                , (PrimeLocalize p.val).join (s₁.fn p) (s₂.fn p) (s₃.fn p)
    , comm := λ s₁ s₃ s₃ J p, (PrimeLocalize p.val).comm (J p)
    , assoc := λ s₁ s₂ s₃ s₁₂ s₁₂₃ J₁₂ J₁₂₃ P C
               , sorry
              --  , C { x := { fn := λ p, begin end
              --             , continuous := begin end
              --             }
              --      , J₁ := begin end
              --      , J₂ := begin end
              --      }
    }

end Struct

def Alg.Struct (X : Alg.{ℓ})
  : Sheaf (Alg.PrimeSpec.Topology X)
 := { Section := Struct.Section
    , ρ := λ U₁ U₂ H s₁ s₂, s₂ = Struct.Section.res H s₁
    , ρ_id
       := λ U H
          , begin
              apply funext, intro s₁,
              apply funext, intro s₂,
              apply iff.to_eq, apply iff.intro,
              { intro E, rw [Struct.Section.res_id] at E, exact E.symm },
              { intro E, rw [Struct.Section.res_id], exact E.symm }
            end
    , ρ_circ
       := λ U₁ U₂ U₃ H₁₂ H₂₃ H₁₃
          , begin
              apply funext, intro s₁,
              apply funext, intro s₂,
              apply iff.to_eq, apply iff.intro,
              { intro E, cases E with s' E, simp at E,
                cases E with E₁ E₂, subst E₂, subst E₁,
                rw [Struct.Section.res_circ]
              },
              { intro E,
                existsi Struct.Section.res H₁₂ s₁,
                simp, subst E,
                rw [Struct.Section.res_circ]
              }
            end
    , locl
       := λ U UU Ucover s t E
          , begin
              apply Struct.Section.locl Ucover,
              intro V,
              have Q := congr_fun (E V)
                          (Struct.Section.res
                            (Topology.Cover.Subset Ucover V.property)
                            s),
              simp at Q,
              rw Q.symm,
              exact true.intro
            end
    , glue := sorry
    }


def Alg.to_section (X : Alg.{ℓ})
    (a : X.τ)
  : (X.Struct.Section (Alg.PrimeSpec.Topology X).whole).τ
 := { fn := λ p, X.localize_at p a []
    , continuous
       := begin
            intro p,
            refine exists.intro { val := (Alg.PrimeSpec.Topology X).whole, property := (λ q Hq, Hq) } _,
            existsi list.nil,
            existsi a,
            apply and.intro (Alg.PrimeSpec.Topology X).in_whole,
            intro q,
            trivial
          end
    }


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
