/- Categories
 -
 -/
namespace Cat
universes ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄

structure Cat
 := (obj : Type.{ℓ₁})
    (hom : obj → obj → Type.{ℓ₂})
    (id : ∀ X, hom X X)
    (circ : ∀ {A B C}, hom B C → hom A B → hom A C)
    (circ_id_r : ∀ {A B} (f : hom A B), circ f (id _) = f)
    (circ_id_l : ∀ {A B} (f : hom A B), circ (id _) f = f)
    (circ_assoc : ∀ {A B C D} {h : hom C D} {g : hom B C} {f : hom A B}
                  , circ h (circ g f) = circ (circ h g) f)

def Cat.circ_congr {C : Cat.{ℓ₁ ℓ₂}} {X Y Z : C.obj}
    {g₁ g₂ : C.hom Y Z} {f₁ f₂ : C.hom X Y}
    (Eg : g₁ = g₂) (Ef : f₁ = f₂)
  : C.circ g₁ f₁ = C.circ g₂ f₂
 := begin subst Eg, subst Ef end

structure Cat.Prod (C : Cat.{ℓ₁ ℓ₂}) (I : Type.{ℓ}) (f : I → C.obj)
 := (obj : C.obj)
    (proj : ∀ (i : I), C.hom obj (f i))

structure Cat.Product (C : Cat.{ℓ₁ ℓ₂}) {I : Type.{ℓ}} {f : I → C.obj}
    (O : C.Prod I f)
 := (univ : ∀ (u : C.Prod I f)
            , C.hom u.obj O.obj)
    (eq : ∀ (u : C.Prod I f) (i : I)
          , u.proj i = C.circ (O.proj i) (univ u))
    (uniq : ∀ (u : C.Prod I f)
              (h : C.hom u.obj O.obj)
              (Hh : ∀ (i : I), u.proj i = C.circ (O.proj i) h)
            , h = univ u)

def Cat.HasProducts (C : Cat.{ℓ₁ ℓ₂})
 := ∀ (I : Type.{ℓ}) (f : I → C.obj)
    , Σ (p : C.Prod I f), C.Product p


structure Cat.Eql (C : Cat.{ℓ₁ ℓ₂}) {X Y : C.obj} (f g : C.hom X Y)
 := (obj : C.obj)
    (eq : C.hom obj X)
    (Eeq : C.circ f eq = C.circ g eq)

structure Cat.Equalizer (C : Cat.{ℓ₁ ℓ₂}) {X Y : C.obj} {f g : C.hom X Y}
    (O : C.Eql f g)
 := (univ : ∀ (u : C.Eql f g)
            , C.hom u.obj O.obj)
    (eq : ∀ (u : C.Eql f g)
          , u.eq = C.circ O.eq (univ u))
    (uniq : ∀ (u : C.Eql f g)
              (h : C.hom u.obj O.obj) (Hh : u.eq = C.circ O.eq h)
            , h = univ u)

def Cat.HasEqualizers (C : Cat.{ℓ₁ ℓ₂})
 := ∀ (X Y : C.obj) (f g : C.hom X Y)
    , Σ (e : C.Eql f g), C.Equalizer e

end Cat
