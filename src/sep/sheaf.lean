/- Sheaves of separation algebras
 -
 -/
import .basic
import .rel
import ..top.basic

namespace Sep
universes ℓ₁ ℓ₂
open Top

structure Sheaf {A : Type.{ℓ₁}} (TA : Topology A)
 := (Section : TA.OI → Alg.{ℓ₂})
    (ρ : ∀ (U₁ U₂ : TA.OI) (Res : TA.Open U₂ ⊆ TA.Open U₁)
         , Rel (Section U₁) (Section U₂))
    (ρ_id : ∀ (U : TA.OI) (Res : TA.Open U ⊆ TA.Open U)
            , ρ U U Res = (Section U).IdRel)
    (ρ_circ : ∀ (U₁ U₂ U₃ : TA.OI)
                (Res₁₂ : TA.Open U₂ ⊆ TA.Open U₁)
                (Res₂₃ : TA.Open U₃ ⊆ TA.Open U₂)
                (Res₁₃ : TA.Open U₃ ⊆ TA.Open U₁)
              , ρ U₂ U₃ Res₂₃ ∘ ρ U₁ U₂ Res₁₂ = ρ U₁ U₃ Res₁₃)
    (locl : ∀ (U : TA.OI) (UU : set TA.OI)
              (Ucover : TA.Open U = set.sUnion (TA.Open <$> UU))
              (s t : (Section U).τ)
              (E : ∀ (V : {V // V ∈ UU})
                    , ρ U V (Topology.Cover.Subset Ucover V.property) s
                      = ρ U V (Topology.Cover.Subset Ucover V.property) t)
            , s = t)
    (glue : ∀ (U : TA.OI) (UU : set TA.OI)
              (Ucover : TA.Open U = set.sUnion (TA.Open <$> UU))
              (loc : ∀ (V : {V // V ∈ UU}), (Section V.val).τ)
              (E : ∀ (V₁ V₂ : {V // V ∈ UU})
                   , ρ V₁ (V₁ ∩ V₂) (Topology.Inter.Subset_l V₁ V₂) (loc V₁)
                     = ρ V₂ (V₁ ∩ V₂) (Topology.Inter.Subset_r V₁ V₂) (loc V₂))
            , ∃ (x : (Section U).τ)
              , ∀ (V : {V // V ∈ UU})
                , ρ U V (Topology.Cover.Subset Ucover V.property) x (loc V))

structure BasisSheaf {A : Type.{ℓ₁}} (TA : OpenBasis A)
 := (Section : TA.OI → Alg.{ℓ₂})
    (ρ : ∀ (oi₁ oi₂ : TA.OI) (Res : TA.Open oi₂ ⊆ TA.Open oi₁)
         , Rel (Section oi₁) (Section oi₂))
    (ρ_id : ∀ (oi : TA.OI) (Res : TA.Open oi ⊆ TA.Open oi)
            , ρ oi oi Res = (Section oi).IdRel)
    (ρ_circ : ∀ (oi₁ oi₂ oi₃ : TA.OI)
                (Res₁₂ : TA.Open oi₂ ⊆ TA.Open oi₁)
                (Res₂₃ : TA.Open oi₃ ⊆ TA.Open oi₂)
                (Res₁₃ : TA.Open oi₃ ⊆ TA.Open oi₁)
              , ρ oi₂ oi₃ Res₂₃ ∘ ρ oi₁ oi₂ Res₁₂ = ρ oi₁ oi₃ Res₁₃)
    (locl : ∀ (oi : TA.OI) (OI : set TA.OI)
              (Ucover : TA.Open oi = set.sUnion (TA.Open <$> OI))
              (s t : (Section oi).τ)
              (E : ∀ (oi' : {oi' // oi' ∈ OI})
                    , ρ oi oi' (OpenBasis.Cover.Subset Ucover oi'.property) s
                      = ρ oi oi' (OpenBasis.Cover.Subset Ucover oi'.property) t)
            , s = t)
    (glue : ∀ {oi : TA.OI} {OI : set TA.OI}
              (Ucover : TA.Open oi = set.sUnion (TA.Open <$> OI))
              {W : Alg.{ℓ₁}}
              {r : ∀ (oi' : {oi' // oi' ∈ OI}), Rel W (Section oi'.val)}
              (E : ∀ (oi₁ oi₂ : {oi' // oi' ∈ OI})
                   , ρ oi₁ (oi₁ ∩ oi₂) (OpenBasis.Inter.Subset_l oi₁ oi₂) ∘ r oi₁
                     = ρ oi₂ (oi₁ ∩ oi₂) (OpenBasis.Inter.Subset_r oi₁ oi₂) ∘ r oi₂)
            , Rel W (Section oi))
    (glue_eq : ∀ {oi : TA.OI} {OI : set TA.OI}
                 (Ucover : TA.Open oi = set.sUnion (TA.Open <$> OI))
                 {W : Alg.{ℓ₁}}
                 {r : ∀ (oi' : {oi' // oi' ∈ OI}), Rel W (Section oi'.val)}
                 (E : ∀ (oi₁ oi₂ : {oi' // oi' ∈ OI})
                      , ρ oi₁ (oi₁ ∩ oi₂) (OpenBasis.Inter.Subset_l oi₁ oi₂) ∘ r oi₁
                        = ρ oi₂ (oi₁ ∩ oi₂) (OpenBasis.Inter.Subset_r oi₁ oi₂) ∘ r oi₂)
               , ∀ oi', r oi' = ρ oi oi' (OpenBasis.Cover.Subset Ucover oi'.property)
                                  ∘ glue Ucover E)

    -- (glue : ∀ (oi : TA.OI) (OI : set TA.OI)
    --           (Ucover : TA.Open oi = set.sUnion (TA.Open <$> OI))
    --           (loc : ∀ (oi' : {oi' // oi' ∈ OI}), (Section oi').τ)
    --           (E : ∀ (oi₁ oi₂ : {oi' // oi' ∈ OI})
    --                , ρ oi₁ (oi₁ ∩ oi₂) (OpenBasis.Inter.Subset_l oi₁ oi₂) (loc oi₁)
    --                  = ρ oi₂ (oi₁ ∩ oi₂) (OpenBasis.Inter.Subset_r oi₁ oi₂) (loc oi₂))
    --         , ∃ (g : (Section oi).τ)
    --           , ∀ (oi' : {oi' // oi' ∈ OI})
    --             , ρ oi (oi ∩ oi') (OpenBasis.Inter.Subset_l oi oi') g
    --              = ρ oi' (oi ∩ oi') (OpenBasis.Inter.Subset_r oi oi') (loc oi'))

--
-- Come back after you've shown that you can take inverse limits of
-- separation algebras; define the Section over U to be the inverse limit
-- of the sections over the basic open sets V ⊆ U.
--
-- def BasisSheaf.Sheaf {A : Type.{ℓ₁}} {TA : OpenBasis A}
--     (F : BasisSheaf.{ℓ₁ ℓ₂} TA)
--   : Sheaf TA.Topology
--  := { Section := begin end
--     , ρ := begin end
--     , ρ_id := begin end
--     , ρ_circ := begin end
--     , locl := begin end
--     , glue := begin end
--     }

end Sep
