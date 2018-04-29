/- Sheaves
 -
 -/
import .basic
import ..cat.basic

namespace Top
universes ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄

open Cat

structure PreSheaf {A : Type.{ℓ₁}} (TA : Topology A) (C : Cat.{ℓ₂ ℓ₃})
 := (Section : TA.OI → C.obj)
    (ρ : ∀ (U₁ U₂ : TA.OI) (Res : TA.Open U₂ ⊆ TA.Open U₁)
         , C.hom (Section U₁) (Section U₂))
    (ρ_id : ∀ (U : TA.OI) (Res : TA.Open U ⊆ TA.Open U)
            , (ρ U U Res) = C.id _)
    (ρ_circ : ∀ (U₁ U₂ U₃ : TA.OI)
                (Res₁₂ : TA.Open U₂ ⊆ TA.Open U₁)
                (Res₂₃ : TA.Open U₃ ⊆ TA.Open U₂)
                (Res₁₃ : TA.Open U₃ ⊆ TA.Open U₁)
              , C.circ (ρ U₂ U₃ Res₂₃) (ρ U₁ U₂ Res₁₂) = ρ U₁ U₃ Res₁₃)


def PreSheaf.Eql.Codom {C : Cat.{ℓ₂ ℓ₃}} {A : Type.{ℓ₁}} {TA : Topology A}
    (CProd : C.HasProducts)
    (Psh : PreSheaf TA C)
    (U : TA.OI) (UU : set TA.OI)
    (Ucover : TA.Open U = set.sUnion (TA.Open <$> UU))
 := CProd { u₁u₂ : TA.OI × TA.OI // u₁u₂.1 ∈ UU ∧ u₁u₂.2 ∈ UU }
          (λ u₁u₂, Psh.Section (TA.inter u₁u₂.val.1 u₁u₂.val.2))

def PreSheaf.Eql.Dom {C : Cat.{ℓ₂ ℓ₃}} {A : Type.{ℓ₁}} {TA : Topology A}
    (CProd : C.HasProducts)
    (Psh : PreSheaf TA C)
    (U : TA.OI) (UU : set TA.OI)
    (Ucover : TA.Open U = set.sUnion (TA.Open <$> UU))
 := CProd { u : TA.OI // u ∈ UU }
          (λ u, Psh.Section u)

def PreSheaf.Eql.left {C : Cat.{ℓ₂ ℓ₃}} {A : Type.{ℓ₁}} {TA : Topology A}
    (CProd : C.HasProducts)
    (Psh : PreSheaf TA C)
    (U : TA.OI) (UU : set TA.OI)
    (Ucover : TA.Open U = set.sUnion (TA.Open <$> UU))
  : C.hom (PreSheaf.Eql.Dom CProd Psh U UU Ucover).1.obj
          (PreSheaf.Eql.Codom CProd Psh U UU Ucover).1.obj
 := (PreSheaf.Eql.Codom CProd Psh U UU Ucover).2.univ
      { obj := (PreSheaf.Eql.Dom CProd Psh U UU Ucover).1.obj
      , proj := λ u₁u₂, C.circ
                          (Psh.ρ _ _ (Topology.Inter.Subset_l _ _))
                          ((PreSheaf.Eql.Dom CProd Psh U UU Ucover).1.proj
                            { val := u₁u₂.val.1
                            , property := u₁u₂.property.1
                            })
      }

def PreSheaf.Eql.right {C : Cat.{ℓ₂ ℓ₃}} {A : Type.{ℓ₁}} {TA : Topology A}
    (CProd : C.HasProducts)
    (Psh : PreSheaf TA C)
    (U : TA.OI) (UU : set TA.OI)
    (Ucover : TA.Open U = set.sUnion (TA.Open <$> UU))
  : C.hom (PreSheaf.Eql.Dom CProd Psh U UU Ucover).1.obj
          (PreSheaf.Eql.Codom CProd Psh U UU Ucover).1.obj
 := (PreSheaf.Eql.Codom CProd Psh U UU Ucover).2.univ
      { obj := (PreSheaf.Eql.Dom CProd Psh U UU Ucover).1.obj
      , proj := λ u₁u₂, C.circ
                          (Psh.ρ _ _ (Topology.Inter.Subset_r _ _))
                          ((PreSheaf.Eql.Dom CProd Psh U UU Ucover).1.proj
                            { val := u₁u₂.val.2
                            , property := u₁u₂.property.2
                            })
      }

def PreSheaf.Eql.direct {C : Cat.{ℓ₂ ℓ₃}} {A : Type.{ℓ₁}} {TA : Topology A}
    (CProd : C.HasProducts)
    (Psh : PreSheaf TA C)
    (U : TA.OI) (UU : set TA.OI)
    (Ucover : TA.Open U = set.sUnion (TA.Open <$> UU))
  : C.hom (Psh.Section U)
          (PreSheaf.Eql.Codom CProd Psh U UU Ucover).1.obj
 := (PreSheaf.Eql.Codom CProd Psh U UU Ucover).2.univ
      { obj := Psh.Section U
      , proj := λ u₁u₂
                , Psh.ρ _ _
                    begin
                      intros p H,
                      apply Topology.Cover.Subset Ucover u₁u₂.property.1,
                      apply Topology.Inter.Subset_l _ _ H,
                    end
      }

def PreSheaf.Eql.eq {C : Cat.{ℓ₂ ℓ₃}} {A : Type.{ℓ₁}} {TA : Topology A}
    (CProd : C.HasProducts)
    (Psh : PreSheaf TA C)
    (U : TA.OI) (UU : set TA.OI)
    (Ucover : TA.Open U = set.sUnion (TA.Open <$> UU))
  : C.hom (Psh.Section U)
          (PreSheaf.Eql.Dom CProd Psh U UU Ucover).1.obj
 := (PreSheaf.Eql.Dom CProd Psh U UU Ucover).2.univ
      { obj := Psh.Section U
      , proj := λ u, Psh.ρ _ _ (Topology.Cover.Subset Ucover u.property)
      }

def PreSheaf.Eql {C : Cat.{ℓ₂ ℓ₃}} {A : Type.{ℓ₁}} {TA : Topology A}
    (CProd : C.HasProducts)
    (Psh : PreSheaf TA C)
    (U : TA.OI) (UU : set TA.OI)
    (Ucover : TA.Open U = set.sUnion (TA.Open <$> UU))
  : C.Eql (PreSheaf.Eql.left CProd Psh U UU Ucover)
          (PreSheaf.Eql.right CProd Psh U UU Ucover)
 := { obj := Psh.Section U
    , eq := PreSheaf.Eql.eq CProd Psh U UU Ucover
    , Eeq
       := begin
            refine @eq.trans _ _ (PreSheaf.Eql.direct CProd Psh U UU Ucover) _ _ _,
            { apply (PreSheaf.Eql.Codom CProd Psh U UU Ucover).2.uniq { obj := _, proj := _ },
              intro u₁u₂,
              rw C.circ_assoc,
              apply eq.symm,
              have Q := ((PreSheaf.Eql.Codom CProd Psh U UU Ucover).2.eq _ u₁u₂).symm,
              refine eq.trans (Cat.circ_congr Q rfl) _, clear Q,
              rw (Cat.circ_assoc _).symm,
              have Q := ((PreSheaf.Eql.Dom CProd Psh U UU Ucover).2.eq _ { val := u₁u₂.val.1, property := u₁u₂.property.1 }).symm,
              refine eq.trans (Cat.circ_congr rfl Q) _, clear Q,
              simp,
              apply Psh.ρ_circ
            },
            { apply eq.symm,
              apply (PreSheaf.Eql.Codom CProd Psh U UU Ucover).2.uniq { obj := _, proj := _ },
              intro u₁u₂,
              rw C.circ_assoc,
              apply eq.symm,
              have Q := ((PreSheaf.Eql.Codom CProd Psh U UU Ucover).2.eq _ u₁u₂).symm,
              refine eq.trans (Cat.circ_congr Q rfl) _, clear Q,
              rw (Cat.circ_assoc _).symm,
              have Q := ((PreSheaf.Eql.Dom CProd Psh U UU Ucover).2.eq _ { val := u₁u₂.val.2, property := u₁u₂.property.2 }).symm,
              refine eq.trans (Cat.circ_congr rfl Q) _, clear Q,
              simp,
              apply Psh.ρ_circ
            }
          end
    }


structure Sheaf {A : Type.{ℓ₁}} (TA : Topology A)
    (C : Cat.{ℓ₂ ℓ₃})
    (CProd : C.HasProducts)
 := (sh : PreSheaf TA C)
    (glue : ∀ (U : TA.OI) (UU : set TA.OI)
              (Ucover : TA.Open U = set.sUnion (TA.Open <$> UU))
            , C.Equalizer (PreSheaf.Eql CProd sh U UU Ucover))

def PreSheaf.DirectIm {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
    {TA : Topology A} {TB : Topology B}
    {C : Cat.{ℓ₃ ℓ₄}}
    (S : PreSheaf.{ℓ₁ ℓ₃} TA C)
    (f : Map TA TB)
  : PreSheaf.{ℓ₂ ℓ₃} TB C
 := { Section := λ U, S.Section (f.preimage U).val
    , ρ := λ U₁ U₂ H, S.ρ _ _ (f.subset H)
    , ρ_id := λ U H, S.ρ_id _ (f.subset H)
    , ρ_circ := λ U₁ U₂ U₃ H₁₂ H₂₃ H₁₃
                , S.ρ_circ _ _ _ (f.subset H₁₂) (f.subset H₂₃) (f.subset H₁₃)
    }

def Sheaf.DirectIm {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
    {TA : Topology A} {TB : Topology B}
    {C : Cat.{ℓ₃ ℓ₄}}
    {CProd₁ : C.HasProducts}
    {CProd₂ : C.HasProducts}
    (S : Sheaf.{ℓ₁ ℓ₃} TA C CProd₁)
    (f : Map TA TB)
  : Sheaf.{ℓ₂ ℓ₃} TB C CProd₂
 := { sh := PreSheaf.DirectIm S.sh f
    , glue := λ U UU Ucover, sorry
    }

structure PreSheafHom {A : Type.{ℓ₁}} {TA : Topology A}
    {C : Cat.{ℓ₂ ℓ₃}}
    (Sh₁ Sh₂ : PreSheaf TA C)
 := (hom : ∀ (U : TA.OI), C.hom (Sh₁.Section U) (Sh₂.Section U))
    (natural : ∀ (U₁ U₂ : TA.OI) (H : TA.Open U₂ ⊆ TA.Open U₁)
               , C.circ (Sh₂.ρ U₁ U₂ H) (hom U₁)
                  = C.circ (hom U₂) (Sh₁.ρ U₁ U₂ H))

def SheafHom {A : Type.{ℓ₁}} {TA : Topology A}
    {C : Cat.{ℓ₂ ℓ₃}}
    {CProd : C.HasProducts}
    (Sh₁ Sh₂ : Sheaf TA C CProd)
 := PreSheafHom Sh₁.sh Sh₂.sh


structure {i c₁ c₂} ShSpace (C : Cat.{c₁ c₂})
 := (Pt : Type.{i})
    (Top : Topology Pt)
    (Prod : C.HasProducts)
    (Sh : Sheaf Top C Prod)

structure {i j c₁ c₂} ShHom
    {C : Cat.{c₁ c₂}}
    (GA : ShSpace.{i c₁ c₂} C) (GB : ShSpace.{j c₁ c₂} C)
 := (map : Map GA.Top GB.Top)
    (sh : SheafHom GB.Sh (GA.Sh.DirectIm map))

end Top
