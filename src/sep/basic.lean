/- Separation algebras
 -
 -/
namespace Sep
universes ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄

-- Separation algebras
structure Alg.Assoc {A' : Type ℓ} {join : A' → A' → set A'}
  {x₁ x₂ x₃ x₁x₂ x₁x₂x₃}
  (H₁ : join x₁ x₂ x₁x₂) (H₂ : join x₁x₂ x₃ x₁x₂x₃)
 := (x : A')
    (J₁ : join x₂ x₃ x)
    (J₂ : join x₁ x x₁x₂x₃)

structure Alg
 := (τ : Type ℓ)
    (join : τ → τ → set τ)
    (comm : ∀ {x₁ x₂ x₃}, join x₁ x₂ x₃ → join x₂ x₁ x₃)
    (assoc₁ : ∀ {x₁ x₂ x₃ x₁x₂ x₁x₂x₃}
                (H₁ : join x₁ x₂ x₁x₂) (H₂ : join x₁x₂ x₃ x₁x₂x₃)
              , Alg.Assoc H₁ H₂)

def Alg.assoc₂ (A : Alg.{ℓ})
  {x₁ x₂ x₃ x₂x₃ x₁x₂x₃}
  (H₁ : A.join x₂ x₃ x₂x₃) (H₂ : A.join x₁ x₂x₃ x₁x₂x₃)
  : Alg.Assoc H₁ (A.comm H₂)
:= A.assoc₁ H₁ (A.comm H₂)

def Set (A : Alg.{ℓ}) := set A.τ

class has_sepmul (α : Type ℓ) := (sepmul : α → α → α)
infix <*> := has_sepmul.sepmul

instance Set_has_emptyc (A : Alg.{ℓ}) : has_emptyc (Set A) := set.has_emptyc
instance Set_has_subset (A : Alg.{ℓ}) : has_subset (Set A) := set.has_subset
instance Set_has_inter (A : Alg.{ℓ}) : has_inter (Set A) := set.has_inter
instance Set_has_union (A : Alg.{ℓ}) : has_union (Set A) := set.has_union
instance Set_has_mem (A : Alg.{ℓ}) : has_mem A.τ (Set A) := set.has_mem

def Set.nonempty {A : Alg.{ℓ}} (S : Set A) : Prop
 := ∃ x, x ∈ S

def EmptySet (A : Alg.{ℓ}) : Set A := λ a, false
def WholeSet (A : Alg.{ℓ}) : Set A := λ a, true


-- An equivalence relation on sets; happens to imply equality but is easier to prove
def SetEq {A : Alg.{ℓ}} (S₁ S₂ : Set A) : Prop
 := ∀ x, x ∈ S₁ ↔ x ∈ S₂

def SetEq.refl {A : Alg.{ℓ}} (S : Set A)
  : SetEq S S
:= λ x, iff.refl _

def SetEq.symm {A : Alg.{ℓ}} {S₁ S₂ : Set A}
  : SetEq S₁ S₂ → SetEq S₂ S₁
:= λ H x, iff.symm (H x)

def SetEq.trans {A : Alg.{ℓ}} {S₁ S₂ S₃ : Set A}
  : SetEq S₁ S₂ → SetEq S₂ S₃ → SetEq S₁ S₃
:= λ H₁₂ H₂₃ x, iff.trans (H₁₂ x) (H₂₃ x)

def SetEq.to_eq {A : Alg.{ℓ}} {S₁ S₂ : Set A}
  : SetEq S₁ S₂ → S₁ = S₂
:= λ H, funext (λ x, iff.to_eq (H x))



-- Identity elements
structure Alg.Ident (A : Alg.{ℓ})
 := (one : A.τ)
    (join_one_r : ∀ x, A.join x one x)
    (join_one_uniq_r : ∀ {x y}, A.join x one y → y = x)

def Alg.Ident.join_one_l {A : Alg.{ℓ}} (A₁ : A.Ident)
  : ∀ x, A.join A₁.one x x
:= λ x, A.comm (A₁.join_one_r x)

def Alg.Ident.join_one_uniq_l {A : Alg.{ℓ}} (A₁ : A.Ident)
  : ∀ {x y}, A.join A₁.one x y → y = x
:= λ x y H, A₁.join_one_uniq_r (A.comm H)

-- Identity elements are unique
def Ident.uniq (A : Alg.{ℓ}) (Ae₁ Ae₂ : A.Ident)
  : Ae₁ = Ae₂
:= let H := Ae₁.join_one_uniq_r (A.comm (Ae₂.join_one_r Ae₁.one))
in begin cases Ae₁, cases Ae₂, simp * at * end



/- The Join function
 -
 -/
def Alg.Join (A : Alg.{ℓ})
  : Set A → Set A → Set A
:= λ X₁ X₂ x₃, ∃ x₁ x₂, X₁ x₁ ∧ X₂ x₂ ∧ A.join x₁ x₂ x₃

instance Set_has_sepmul (A : Alg.{ℓ}) : has_sepmul (Set A)
 := { sepmul := A.Join
    }

def Alg.Join.show {A : Alg.{ℓ}} {X₁ X₂ : Set A}
    {x₁ x₂ x₃} (H₁ : X₁ x₁) (H₂ : X₂ x₂) (Hx : A.join x₁ x₂ x₃)
  : A.Join X₁ X₂ x₃
:= ⟨ x₁, x₂, H₁, H₂, Hx ⟩

def Alg.Join.elim {A : Alg.{ℓ}} {X₁ X₂ : Set A} {x₃}
    (H : A.Join X₁ X₂ x₃)
    {P : Prop}
  : (∀ {x₁ x₂}, X₁ x₁ → X₂ x₂ → A.join x₁ x₂ x₃ → P) → P
:= λ C, begin
          cases H with x₁ H, cases H with x₂ H,
          exact C H.1 H.2.1 H.2.2
        end

-- The join relation is a special case of the Join function
def Alg.join_Join (A : Alg.{ℓ}) {x₁ x₂ x₃}
  : A.join x₁ x₂ x₃ ↔ A.Join (eq x₁) (eq x₂) x₃
:= iff.intro
     (λ H, Alg.Join.show (eq.refl x₁) (eq.refl x₂) H)
     (λ H, Alg.Join.elim H (λ x₁' x₂' H₁ H₂ Hx, begin rw [H₁, H₂], exact Hx end))

-- The Join function is commutative
def Alg.Join.comm (A : Alg.{ℓ}) {X₁ X₂ : Set A}
  : X₁ <*> X₂ = X₂ <*> X₁
 := begin
      apply funext, intro x,
      refine iff.to_eq (iff.intro _ _),
      repeat
        { intro H, apply Alg.Join.elim H,
          intros x₁' x₂' H₁ H₂ Hx,
          exact Alg.Join.show H₂ H₁ (A.comm Hx)
        }
    end

-- The Join function is associative
def Alg.Join.assoc (A : Alg.{ℓ}) {X₁ X₂ X₃ : Set A}
  : (X₁ <*> X₂) <*> X₃ = X₁ <*> (X₂ <*> X₃)
 := begin
      apply funext, intro z,
      refine iff.to_eq (iff.intro _ _),
      { intro H, cases H with x₁ H, cases H with x₂ H,
        cases H with H' H, cases H' with y₁ H', cases H' with y₂ H',
        cases A.assoc₁ H'.2.2 H.2 with y₂x₂ ω₁ ω₂,
        existsi y₁, existsi y₂x₂,
        refine and.intro H'.1 (and.intro _ ω₂),
        existsi y₂, existsi x₂,
        refine and.intro H'.2.1 (and.intro H.1 ω₁)
      },
      { intro H, cases H with x₁ H, cases H with x₂ H,
        cases H with X₁x₁ H, cases H with H' H, cases H' with y₁ H', cases H' with y₂ H',
        cases A.assoc₁ (A.comm H'.2.2) (A.comm H) with y₁x₁ ω₁ ω₂,
        existsi y₁x₁, existsi y₂,
        refine and.intro _ (and.intro H'.2.1 (A.comm ω₂)),
        existsi x₁, existsi y₁,
        exact and.intro X₁x₁ (and.intro H'.1 (A.comm ω₁))
      },
    end



/- The "divides" relation
 -
 -/
structure Alg.Divides (A : Alg.{ℓ}) (x₁ x₃ : A.τ)
 := (x : A.τ)
    (j : A.join x₁ x x₃)

-- Divides is transitive
def Divides.trans {A : Alg.{ℓ}} {x₁ x₂ x₃}
  : A.Divides x₁ x₂ → A.Divides x₂ x₃ → A.Divides x₁ x₃
 := λ d₁₂ d₂₃
    , let a := A.assoc₁ d₁₂.j d₂₃.j
      in { x := a.x
         , j := a.J₂
         }

-- In a sep alg with identity, Divides is reflective
def Divides.refl (A : Alg.{ℓ}) (A₁ : A.Ident) (x : A.τ)
  : A.Divides x x
 := { x := A₁.one
    , j := A₁.join_one_r x
    }



/- Units
 -
 -/
def Alg.Unit (A : Alg.{ℓ}) (u : A.τ) : Type ℓ
 := ∀ x, A.Divides u x

-- If w divides a unit, then w is also a unit
def Unit.Divides (A : Alg.{ℓ}) {u} (uUnit : A.Unit u) (w : A.τ)
  : A.Divides w u → A.Unit w
 := begin
      intro H,
      intro x,
      apply Divides.trans H,
      apply uUnit
    end



/- Primes
 -
 -/
structure Alg.Prime (A : Alg.{ℓ}) (p : A.τ)
 := (u : A.τ)
    (proper : A.Divides p u → false)
    (prime : ∀ {x₁ x₂ x₃}
             , A.join x₁ x₂ x₃ → A.Divides p x₃
             → A.Divides p x₁ ⊕ A.Divides p x₂)



/- Ideals
 -
 -/
def Set.Ideal {A : Alg.{ℓ}} (I : Set A) : Prop
 := ∀ {x₁ x₂ x₃}, x₁ ∈ I → A.join x₁ x₂ x₃ → x₃ ∈ I

structure Set.Proper {A : Alg.{ℓ}} (I : Set A)
 := (z : A.τ)
    (proper : ¬ z ∈ I)

def Proper.one_not_elem {A : Alg.{ℓ}} (A₁ : A.Ident) {I : Set A} (Iideal : I.Ideal) (Iproper : I.Proper)
  : ¬ A₁.one ∈ I
:= begin
     intro H',
     exact Iproper.proper (Iideal H' (A₁.join_one_l Iproper.z))
   end

def Set.Prime {A : Alg.{ℓ}} (I : Set A)
 := ∀ {x₁ x₂ x₃}, A.join x₁ x₂ x₃ → x₃ ∈ I → x₁ ∈ I ∨ x₂ ∈ I

-- The whole set is an ideal
def TrivialIdeal (A : Alg.{ℓ}) : (WholeSet A).Ideal
 := λ x₁ x₂ x₃ Ix₁ H, Ix₁

-- The empty set is an ideal
def EmptyIdeal (A : Alg.{ℓ}) : (EmptySet A).Ideal
 := λ x₁ x₂ x₃ Ix₁ H, Ix₁

-- In a separation algebra with identity, the empty set is a proper set
def EmptyIdeal.Proper {A : Alg.{ℓ}} (A₁ : A.Ident) : (EmptySet A).Proper
 := { z := A₁.one, proper := false.elim }

-- In a separation algebra with identity, the empty set is a prime ideal
def EmptyIdeal.Prime {A : Alg.{ℓ}} (A₁ : A.Ident) : (EmptySet A).Prime
 := λ x₁ x₂ x₃ H, false.elim

-- Ideal generated by a set of elements
def GenIdeal {A : Alg.{ℓ}} (gen : Set A) : Set A
 := λ y, (gen y) ∨ (∃ x (H : A.Divides x y), gen x)

def GenIdeal.Ideal (A : Alg.{ℓ}) (gen : Set A) : (GenIdeal gen).Ideal
 := λ a₁ a₂ a₃ Ia₁ H
    , or.elim Ia₁
        (λ gen_a₁, or.inr ⟨a₁, { x := a₂, j := H }, gen_a₁⟩)
        (λ r, begin
                apply or.inr,
                cases r with x r, cases r with r_div_y gen_r,
                existsi x, existsi (Divides.trans r_div_y { x := a₂, j := H}),
                assumption
              end)

def GenIdeal.mem {A : Alg.{ℓ}} (gen : Set A)
  : gen ⊆ (GenIdeal gen)
:= λ x H, or.inl H

-- Ideal generated by an element
def GenIdeal₁ (A : Alg.{ℓ}) (x : A.τ) : Set A
 := GenIdeal (eq x)

def GenIdeal₁_member {A : Alg.{ℓ}} (x : A.τ)
  : x ∈ (GenIdeal₁ A x)
:= GenIdeal.mem (eq x) (eq.refl x)



/- Operations on ideals
 -
 -/

-- -- Unions
-- def UnionIdeal {A : Alg.{ℓ}} (I₁ I₂ : A.Ideal) : A.Ideal
-- := { elem := λ y, I₁.elem y ∨ I₂.elem y
--    , ideal_l := λ x₁ x₂ x₃ Ix₁ H
--                 , or.elim Ix₁
--                     (λ ω, or.inl (I₁.ideal_l ω H))
--                     (λ ω, or.inr (I₂.ideal_l ω H))
--    }

-- -- Unions are commutative
-- def UnionIdeal.comm {A : Alg.{ℓ}} {I₁ I₂ : A.Ideal}
--   : IdealEq (UnionIdeal I₁ I₂) (UnionIdeal I₂ I₁)
-- := λ x, by simp [UnionIdeal]

-- -- Unions are associative
-- def UnionIdeal.assoc {A : Alg.{ℓ}} {I₁ I₂ I₃ : A.Ideal}
--   : IdealEq (UnionIdeal (UnionIdeal I₁ I₂) I₃) (UnionIdeal I₁ (UnionIdeal I₂ I₃))
-- := λ x, by simp [UnionIdeal]

-- -- The EmptyIdeal is an identity for UnionIdeal
-- def UnionIdeal.empty {A : Alg.{ℓ}} (I : A.Ideal)
--   : IdealEq (UnionIdeal (EmptyIdeal A) I) I
-- := λ x, by simp [UnionIdeal, EmptyIdeal]

-- -- The TrivialIdeal is an annihilator for UnionIdeal
-- def UnionIdeal.trivial {A : Alg.{ℓ}} (I : A.Ideal)
--   : IdealEq (UnionIdeal (TrivialIdeal A) I) (TrivialIdeal A)
-- := λ x, by simp [UnionIdeal, TrivialIdeal]


-- -- Intersections
-- def IntersectionIdeal {A : Alg.{ℓ}} (I₁ I₂ : A.Ideal) : A.Ideal
-- := { elem := λ y, I₁.elem y ∧ I₂.elem y
--    , ideal_l := λ x₁ x₂ x₃ Ix₁ H
--                 , and.intro
--                     (I₁.ideal_l Ix₁.1 H)
--                     (I₂.ideal_l Ix₁.2 H)
--    }

-- -- Intersections are commutative
-- def IntersectionIdeal.comm {A : Alg.{ℓ}} {I₁ I₂ : A.Ideal}
--   : IdealEq (IntersectionIdeal I₁ I₂)
--             (IntersectionIdeal I₂ I₁)
-- := λ x, by simp [IntersectionIdeal]

-- -- Intersections are associative
-- def IntersectionIdeal.assoc {A : Alg.{ℓ}} {I₁ I₂ I₃ : A.Ideal}
--   : IdealEq (IntersectionIdeal (IntersectionIdeal I₁ I₂) I₃)
--             (IntersectionIdeal I₁ (IntersectionIdeal I₂ I₃))
-- := λ x, by simp [IntersectionIdeal]

-- -- Intersections distribute over unions
-- def IntersectionIdeal.union {A : Alg.{ℓ}} {I₁ I₂ I₃ : A.Ideal}
--   : IdealEq (IntersectionIdeal I₁ (UnionIdeal I₂ I₃))
--             (UnionIdeal (IntersectionIdeal I₁ I₂) (IntersectionIdeal I₁ I₃))
-- := λ x, begin
--           simp [IntersectionIdeal, UnionIdeal],
--           apply iff.intro,
--           { intro H, cases H with H₁ H₂₃, cases H₂₃ with H₂ H₃,
--             { exact or.inl (and.intro H₁ H₂) },
--             { exact or.inr (and.intro H₁ H₃) }
--           },
--           { intro H, cases H with H₁ H₂,
--             { exact and.intro H₁.1 (or.inl H₁.2) },
--             { exact and.intro H₂.1 (or.inr H₂.2) }
--           }
--         end

-- -- The EmptyIdeal is an annihilator for IntersectionIdeal
-- def IntersectionIdeal.empty {A : Alg.{ℓ}} (I : A.Ideal)
--   : IdealEq (IntersectionIdeal (EmptyIdeal A) I) (EmptyIdeal A)
-- := λ x, by simp [IntersectionIdeal, EmptyIdeal]

-- -- The TrivialIdeal is an identity for IntersectionIdeal
-- def IntersectionIdeal.trivial {A : Alg.{ℓ}} (I : A.Ideal)
--   : IdealEq (IntersectionIdeal (TrivialIdeal A) I) I
-- := λ x, by simp [IntersectionIdeal, TrivialIdeal]


-- -- Joins
-- def JoinIdeal {A : Alg.{ℓ}} (I₁ I₂ : A.Ideal) : A.Ideal
-- := { elem := I₁.elem <*> I₂.elem
--    , ideal_l := λ x₁ x₂ x₃ Ix₁ H
--                 , begin
--                     apply Alg.Join.elim Ix₁,
--                     intros y₁ y₂ H₁ H₂ H',
--                     cases (A.assoc₁ H' H) with y₂x₂ ω₂₁ ω₂₂,
--                     exact Alg.Join.show H₁ (I₂.ideal_l H₂ ω₂₁) ω₂₂
--                   end
--    }

-- -- Joins are commutative
-- def JoinIdeal.comm {A : Alg.{ℓ}} {I₁ I₂ : A.Ideal}
--   : IdealEq (JoinIdeal I₁ I₂) (JoinIdeal I₂ I₁)
-- := λ x, begin simp [JoinIdeal], rw [Alg.Join.comm] end

-- -- Joins are associative
-- def JoinIdeal.assoc {A : Alg.{ℓ}} {I₁ I₂ I₃ : A.Ideal}
--   : IdealEq (JoinIdeal (JoinIdeal I₁ I₂) I₃) (JoinIdeal I₁ (JoinIdeal I₂ I₃))
-- := λ x, begin simp [JoinIdeal], rw [Alg.Join.assoc] end

-- -- The EmptyIdeal is an annihilator for JoinIdeal
-- def JoinIdeal.empty {A : Alg.{ℓ}} (I : A.Ideal)
--   : IdealEq (JoinIdeal (EmptyIdeal A) I) (EmptyIdeal A)
-- := λ x, begin
--           simp [JoinIdeal, Alg.Join, EmptyIdeal],
--           intro H, cases H with x₁ H, cases H with x₂ H,
--           apply H.1
--         end

-- -- In a sep alg with identity, the TrivialIdeal is an identity for JoinIdeal
-- def JoinIdeal.trivial {A : Alg.{ℓ}} (A₁ : A.Ident) (I : A.Ideal)
--   : IdealEq (JoinIdeal (TrivialIdeal A) I) I
-- := λ x, iff.intro
--           begin
--             simp [JoinIdeal, Alg.Join, TrivialIdeal],
--             intro H, cases H with x₁ H, cases H with x₂ H,
--             exact I.ideal_r H.2.1 H.2.2
--           end
--           begin
--             intro H,
--             existsi A₁.one, existsi x,
--             refine and.intro _ (and.intro H (A₁.join_one_l x)),
--             trivial
--           end


end Sep
