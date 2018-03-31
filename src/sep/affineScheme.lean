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

def non_vanishing {X : Alg.{ℓ}}
    {o : (Alg.PrimeSpec.Topology X).OI}
    (u : {u // (Alg.PrimeSpec.Topology X).Open u ⊆ (Alg.PrimeSpec.Topology X).Open o})
  : Type.{ℓ}
 := {f // ∀ (q : {p // p ∈ (Alg.PrimeSpec.Topology X).Open u}) , ¬ f ∈ q.val.set}

def non_vanishing.res {X : Alg.{ℓ}}
    {o : (Alg.PrimeSpec.Topology X).OI}
    {u : {u // (Alg.PrimeSpec.Topology X).Open u ⊆ (Alg.PrimeSpec.Topology X).Open o}}
    (q : {p // p ∈ (Alg.PrimeSpec.Topology X).Open u})
    (f : non_vanishing u)
  : q.val.prime.Complement_JoinClosed.Alg.τ
 := { val := f.val, property := f.property q }

def non_vanishing.res.val {X : Alg.{ℓ}}
    {o : (Alg.PrimeSpec.Topology X).OI}
    {u : {u // (Alg.PrimeSpec.Topology X).Open u ⊆ (Alg.PrimeSpec.Topology X).Open o}}
    {q : {p // p ∈ (Alg.PrimeSpec.Topology X).Open u}}
    {f : non_vanishing u}
  : (non_vanishing.res q f).val = f.val
 := rfl

def expand_prime {X : Alg.{ℓ}}
    {o : (Alg.PrimeSpec.Topology X).OI}
    {u : {u // (Alg.PrimeSpec.Topology X).Open u ⊆ (Alg.PrimeSpec.Topology X).Open o}}
    (q : {p // p ∈ (Alg.PrimeSpec.Topology X).Open u})
  : {p // p ∈ (Alg.PrimeSpec.Topology X).Open o}
 := { val := q.val
    , property := u.property q.property
    }

structure τ {X : Alg.{ℓ}} (o : (Alg.PrimeSpec.Topology X).OI)
  : Type.{ℓ}
 := (fn : ∀ (p : {p // p ∈ (Alg.PrimeSpec.Topology X).Open o})
          , (PrimeLocalize p.val).τ)
    (continuous
      : ∀ (p : {p // p ∈ (Alg.PrimeSpec.Topology X).Open o})
        , ∃ (u : {u // (Alg.PrimeSpec.Topology X).Open u ⊆ (Alg.PrimeSpec.Topology X).Open o})
            (ff : list (non_vanishing u))
            (a : X.τ)
          , p.val ∈ (Alg.PrimeSpec.Topology X).Open u
          ∧ (∀ (q : {p // p ∈ (Alg.PrimeSpec.Topology X).Open u})
              , fn (expand_prime q) = X.localize_at q a (list.map (non_vanishing.res q) ff)))

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
    , ρ := sorry
    , ρ_id := sorry
    , ρ_circ := sorry
    , locl := sorry
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
