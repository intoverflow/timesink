/- Sheaves of separation algebras
 -
 -/
import .basic
import .rel
import .ordalg
import ..top.basic

namespace Sep
universes ℓ₁ ℓ₂ ℓ₃ ℓ₄
open Top

structure Sheaf {A : Type.{ℓ₁}} (TA : Topology A)
 := (Section : TA.OI → OrdAlg.{ℓ₂})
    (Stalk : A → true) -- TODO: stalks and their univ property
    (ρ : ∀ (U₁ U₂ : TA.OI) (Res : TA.Open U₂ ⊆ TA.Open U₁)
         , OrdRel (Section U₁) (Section U₂))
    (ρ_id : ∀ (U : TA.OI) (Res : TA.Open U ⊆ TA.Open U)
            , (ρ U U Res).rel = (Section U).alg.IdRel)
    (ρ_circ : ∀ (U₁ U₂ U₃ : TA.OI)
                (Res₁₂ : TA.Open U₂ ⊆ TA.Open U₁)
                (Res₂₃ : TA.Open U₃ ⊆ TA.Open U₂)
                (Res₁₃ : TA.Open U₃ ⊆ TA.Open U₁)
              , (ρ U₂ U₃ Res₂₃).rel ∘ (ρ U₁ U₂ Res₁₂).rel = (ρ U₁ U₃ Res₁₃).rel)
    (locl : ∀ (U : TA.OI) (UU : set TA.OI)
              (Ucover : TA.Open U = set.sUnion (TA.Open <$> UU))
              (s t : (Section U).alg.τ)
              (E : ∀ (V : {V // V ∈ UU})
                    , (ρ U V (Topology.Cover.Subset Ucover V.property)).rel s
                      = (ρ U V (Topology.Cover.Subset Ucover V.property)).rel t)
            , s = t)
    (glue : ∀ (U : TA.OI) (UU : set TA.OI)
              (Ucover : TA.Open U = set.sUnion (TA.Open <$> UU))
              (loc : ∀ (V : {V // V ∈ UU}), (Section V.val).alg.τ)
              (E : ∀ (V₁ V₂ : {V // V ∈ UU})
                   , (ρ V₁ (V₁ ∩ V₂) (Topology.Inter.Subset_l V₁ V₂)).rel (loc V₁)
                     = (ρ V₂ (V₁ ∩ V₂) (Topology.Inter.Subset_r V₁ V₂)).rel (loc V₂))
            , ∃ (x : (Section U).alg.τ)
              , ∀ (V : {V // V ∈ UU})
                , (ρ U V (Topology.Cover.Subset Ucover V.property)).rel x (loc V))

def Sheaf.DirectIm {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
    {TA : Topology A} {TB : Topology B}
    (S : Sheaf.{ℓ₁ ℓ₃} TA)
    (f : Map TA TB)
  : Sheaf.{ℓ₂ ℓ₃} TB
 := { Section := λ U, S.Section (f.preimage U).val
    , Stalk := λ A, true.intro
    , ρ := λ U₁ U₂ H, S.ρ _ _ (f.subset H)
    , ρ_id := λ U H, S.ρ_id _ (f.subset H)
    , ρ_circ := λ U₁ U₂ U₃ H₁₂ H₂₃ H₁₃
                , S.ρ_circ _ _ _ (f.subset H₁₂) (f.subset H₂₃) (f.subset H₁₃)
    , locl := λ U UU Ucover s t V
              , sorry
    , glue := sorry
    }

structure SheafMorphism {A : Type.{ℓ₁}} {TA : Topology A}
    (S₁ S₂ : Sheaf TA)
 := (rel : ∀ (U : TA.OI), OrdRel (S₁.Section U) (S₂.Section U))
    (res : ∀ (U₁ U₂ : TA.OI) (H : TA.Open U₂ ⊆ TA.Open U₁)
           , (S₂.ρ _ _ H).action ∘ (rel U₁).action
              = (rel U₂).action ∘ (S₁.ρ _ _ H).action)

structure OrdAlgSpace
 := (Pt : Type.{ℓ₁})
    (Top : Topology Pt)
    (Sh : Sheaf.{ℓ₁ ℓ₂} Top)
    (stalk : true) -- TODO: stalks are local OrdAlgs

structure OrdAlgSpaceMorphism
    (X : OrdAlgSpace.{ℓ₁ ℓ₂}) (Y : OrdAlgSpace.{ℓ₃ ℓ₄})
 := (map : Map X.Top Y.Top)
    (sh : SheafMorphism Y.Sh (X.Sh.DirectIm map))
    (stalk : true) -- TODO: rel on stalks are local OrdRels

end Sep
