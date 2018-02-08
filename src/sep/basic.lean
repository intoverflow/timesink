/- Separation algebras
 -
 -/
namespace Sep
universes ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄

-- Separation algebras
structure Alg (A' : Type ℓ)
 := (join : A' → A' → set A')
    (comm : ∀ {x₁ x₂ x₃}, join x₁ x₂ x₃ → join x₂ x₁ x₃)
    (assoc : ∀ {x₁ x₂ x₃ x₁x₂ x₁x₂x₃}
             , join x₁ x₂ x₁x₂ → join x₁x₂ x₃ x₁x₂x₃
             → ∃ x₂x₃, join x₂ x₃ x₂x₃ ∧ join x₁ x₂x₃ x₁x₂x₃)

-- Identity elements
structure Alg.Ident {A' : Type ℓ} (A : Alg A')
 := (one : A')
    (join_one_r : ∀ x, A.join x one x)
    (join_one_uniq_r : ∀ {x y}, A.join x one y → y = x)

def Alg.Ident.join_one_l {A' : Type ℓ} {A : Alg A'} (A₁ : A.Ident)
  : ∀ x, A.join A₁.one x x
:= λ x, A.comm (A₁.join_one_r x)

def Alg.Ident.join_one_uniq_l {A' : Type ℓ} {A : Alg A'} (A₁ : A.Ident)
  : ∀ {x y : A'}, A.join A₁.one x y → y = x
:= λ x y H, A₁.join_one_uniq_r (A.comm H)

-- Identity elements are unique
def Ident.uniq {A' : Type ℓ} {A : Alg A'} (Ae₁ Ae₂ : A.Ident)
  : Ae₁ = Ae₂
:= let H := Ae₁.join_one_uniq_r (A.comm (Ae₂.join_one_r Ae₁.one))
in begin cases Ae₁, cases Ae₂, simp * at * end



/- The Join function
 -
 -/
def Alg.Join {A' : Type ℓ} (A : Alg A')
  : set A' → set A' → set A'
:= λ X₁ X₂ x₃, ∃ x₁ x₂, X₁ x₁ ∧ X₂ x₂ ∧ A.join x₁ x₂ x₃

-- The join relation is a special case of the Join function
def Alg.join_Join {A' : Type ℓ} (A : Alg A') (x₁ x₂ x₃ : A')
  : A.join x₁ x₂ x₃ ↔ A.Join (eq x₁) (eq x₂) x₃
:= iff.intro
     (λ H, begin
             existsi x₁, existsi x₂,
             exact and.intro (eq.refl x₁) (and.intro (eq.refl x₂) H)
           end)
     (λ H, begin
             cases H with y₁ H, cases H with y₂ H,
             rw [H.1, H.2.1],
             exact H.2.2
           end)

-- The Join function is commutative
def Alg.Join.comm {A' : Type ℓ} {A : Alg A'} {X₁ X₂ : set A'}
  : A.Join X₁ X₂ = A.Join X₂ X₁
 := begin
      apply funext, intro x,
      refine iff.to_eq (iff.intro _ _),
      repeat
        { intro H, cases H with x₁ H, cases H with x₂ H,
          existsi x₂, existsi x₁,
          exact and.intro H.2.1 (and.intro H.1 (A.comm H.2.2))
        }
    end

-- The Join function is associative
def Alg.Join.assoc {A' : Type ℓ} {A : Alg A'} {X₁ X₂ X₃ : set A'}
  : A.Join (A.Join X₁ X₂) X₃ = A.Join X₁ (A.Join X₂ X₃)
 := begin
      apply funext, intro x₃,
      refine iff.to_eq (iff.intro _ _),
      { intro H, cases H with x₁ H, cases H with x₂ H,
        cases H with H' H, cases H' with y₁ H', cases H' with y₂ H',
        cases A.assoc H'.2.2 H.2 with y₂x₂ ω,
        simp [Alg.Join],
        existsi y₁, existsi y₂x₂,
        refine and.intro H'.1 (and.intro ω.2 _),
        existsi y₂, existsi x₂,
        refine and.intro H'.2.1 (and.intro H.1 ω.1)
      },
      { intro H, cases H with x₁ H, cases H with x₂ H,
        cases H with X₁x₁ H, cases H with H' H, cases H' with y₁ H', cases H' with y₂ H',
        cases A.assoc (A.comm H'.2.2) (A.comm H) with y₁x₁ ω,
        simp [Alg.Join],
        existsi y₁x₁, existsi y₂,
        refine and.intro H'.2.1 (and.intro (A.comm ω.2) _),
        existsi x₁, existsi y₁,
        exact and.intro X₁x₁ (and.intro H'.1 (A.comm ω.1))
      },
    end



/- The "divides" relation
 -
 -/
def Alg.Divides {A' : Type ℓ} (A : Alg A') (x₁ x₃ : A') : Prop
 := ∃ x₂, A.join x₁ x₂ x₃

-- Divides is transitive
def Divides.trans {A' : Type ℓ} {A : Alg A'} {x₁ x₂ x₃ : A'}
  : A.Divides x₁ x₂ → A.Divides x₂ x₃ → A.Divides x₁ x₃
 := λ d₁₂ d₂₃
    , exists.elim d₁₂ (λ d₁ ω₁
    , exists.elim d₂₃ (λ d₂ ω₂
    , exists.elim (A.assoc ω₁ ω₂) (λ x H
    , exists.intro x H.2)))

-- In a sep alg with identity, Divides is reflective
def Divides.refl {A' : Type ℓ} {A : Alg A'} (A₁ : A.Ident) (x : A')
  : A.Divides x x
 := exists.intro A₁.one (A₁.join_one_r x)



/- Units
 -
 -/
def Alg.Unit {A' : Type ℓ} (A : Alg A') (u : A') : Prop
 := ∀ x, A.Divides u x

-- If w divides a unit, then w is also a unit
def Unit.Divides {A' : Type ℓ} {A : Alg A'} {u : A'} (uUnit : A.Unit u) (w : A')
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
structure Alg.Prime {A' : Type ℓ} (A : Alg A') (p : A')
 := (not_unit : ∃ x, ¬ A.Divides p x)
    (prime : ∀ x₁ x₂ x₃, A.Divides p x₃ → A.join x₁ x₂ x₃ → A.Divides p x₁ ∨ A.Divides p x₂)


/- Ideals
 -
 -/
structure Alg.Ideal {A' : Type ℓ} (A : Alg A')
 := (elem : set A')
    (ideal_l : ∀ {x₁ x₂ x₃}, elem x₁ → A.join x₁ x₂ x₃ → elem x₃)

def Alg.Ideal.ideal_r {A' : Type ℓ} {A : Alg A'} (I : A.Ideal)
  : ∀ {x₁ x₂ x₃}, I.elem x₂ → A.join x₁ x₂ x₃ → I.elem x₃
:= λ x₁ x₂ x₃ Ix₂ H, I.ideal_l Ix₂ (A.comm H)

def Alg.Ideal.Proper {A' : Type ℓ} {A : Alg A'} (I : A.Ideal) : Prop
 := ∃ z₀, ¬ I.elem z₀

def Ideal.Proper.one_not_elem {A' : Type ℓ} {A : Alg A'} (A₁ : A.Ident) (I : A.Ideal) (H : I.Proper)
  : ¬ I.elem A₁.one
:= begin
     intro H',
     cases H with z₀ H,
     exact H (I.ideal_l H' (A₁.join_one_l z₀))
   end

structure Alg.Ideal.Prime {A' : Type ℓ} {A : Alg A'} (I : A.Ideal)
 := (prime : ∀ {x₁ x₂ x₃}, A.join x₁ x₂ x₃ → I.elem x₃ → I.elem x₁ ∨ I.elem x₂)
    (proper: I.Proper)

-- The whole set is an ideal
def TrivialIdeal {A' : Type ℓ} (A : Alg A') : A.Ideal
 := { elem := λ y, true
    , ideal_l := λ x₁ x₂ x₃ Ix₁ H, Ix₁
    }

-- The empty set is an ideal
def EmptyIdeal {A' : Type ℓ} (A : Alg A') : A.Ideal
 := { elem := λ y, false
    , ideal_l := λ x₁ x₂ x₃ Ix₁ H, Ix₁
    }

-- In a separation algebra with identity, the empty set is a prime ideal
def EmptyIdeal.Prime {A' : Type ℓ} {A : Alg A'} (A₁ : A.Ident) : (EmptyIdeal A).Prime
 := { prime := λ x₁ x₂ x₃ H, false.elim
    , proper := exists.intro A₁.one false.elim
    }



/- Equality of ideals
 -
 -/

-- Simple equality helper
def Ideal_eq {A' : Type ℓ} {A : Alg A'}
  : ∀ {I₁ I₂ : A.Ideal}, I₁.elem = I₂.elem → I₁ = I₂
| (Ideal.mk e₁ i₁) (Ideal.mk e₂ i₂) H := begin simp * at H, subst H end

-- An equivalence relation; happens to imply equality but is easier to prove
def IdealEq {A' : Type ℓ} {A : Alg A'} (I₁ I₂ : A.Ideal) : Prop
 := ∀ x, I₁.elem x ↔ I₂.elem x

def IdealEq.refl {A' : Type ℓ} {A : Alg A'} (I : A.Ideal)
  : IdealEq I I
:= λ x, iff.refl _

def IdealEq.symm {A' : Type ℓ} {A : Alg A'} {I₁ I₂ : A.Ideal}
  : IdealEq I₁ I₂ → IdealEq I₂ I₁
:= λ H x, iff.symm (H x)

def IdealEq.trans {A' : Type ℓ} {A : Alg A'} {I₁ I₂ I₃ : A.Ideal}
  : IdealEq I₁ I₂ → IdealEq I₂ I₃ → IdealEq I₁ I₃
:= λ H₁₂ H₂₃ x, iff.trans (H₁₂ x) (H₂₃ x)

def IdealEq.to_eq {A' : Type ℓ} {A : Alg A'} {I₁ I₂ : A.Ideal}
  : IdealEq I₁ I₂ → I₁ = I₂
:= λ H, Ideal_eq (funext (λ x, iff.to_eq (H x)))



/- Operations on ideals
 -
 -/

-- Unions
def UnionIdeal {A' : Type ℓ} {A : Alg A'} (I₁ I₂ : A.Ideal) : A.Ideal
:= { elem := λ y, I₁.elem y ∨ I₂.elem y
   , ideal_l := λ x₁ x₂ x₃ Ix₁ H
                , or.elim Ix₁
                    (λ ω, or.inl (I₁.ideal_l ω H))
                    (λ ω, or.inr (I₂.ideal_l ω H))
   }

-- Unions are commutative
def UnionIdeal.comm {A' : Type ℓ} {A : Alg A'} {I₁ I₂ : A.Ideal}
  : IdealEq (UnionIdeal I₁ I₂) (UnionIdeal I₂ I₁)
:= λ x, by simp [UnionIdeal]

-- Unions are associative
def UnionIdeal.assoc {A' : Type ℓ} {A : Alg A'} {I₁ I₂ I₃ : A.Ideal}
  : IdealEq (UnionIdeal (UnionIdeal I₁ I₂) I₃) (UnionIdeal I₁ (UnionIdeal I₂ I₃))
:= λ x, by simp [UnionIdeal]

-- The EmptyIdeal is an identity for UnionIdeal
def UnionIdeal.empty {A' : Type ℓ} {A : Alg A'} (I : A.Ideal)
  : IdealEq (UnionIdeal (EmptyIdeal A) I) I
:= λ x, by simp [UnionIdeal, EmptyIdeal]

-- The TrivialIdeal is an annihilator for UnionIdeal
def UnionIdeal.trivial {A' : Type ℓ} {A : Alg A'} (I : A.Ideal)
  : IdealEq (UnionIdeal (TrivialIdeal A) I) (TrivialIdeal A)
:= λ x, by simp [UnionIdeal, TrivialIdeal]


-- Intersections
def IntersectionIdeal {A' : Type ℓ} {A : Alg A'} (I₁ I₂ : A.Ideal) : A.Ideal
:= { elem := λ y, I₁.elem y ∧ I₂.elem y
   , ideal_l := λ x₁ x₂ x₃ Ix₁ H
                , and.intro
                    (I₁.ideal_l Ix₁.1 H)
                    (I₂.ideal_l Ix₁.2 H)
   }

-- Intersections are commutative
def IntersectionIdeal.comm {A' : Type ℓ} {A : Alg A'} {I₁ I₂ : A.Ideal}
  : IdealEq (IntersectionIdeal I₁ I₂) (IntersectionIdeal I₂ I₁)
:= λ x, by simp [IntersectionIdeal]

-- Intersections are associative
def IntersectionIdeal.assoc {A' : Type ℓ} {A : Alg A'} {I₁ I₂ I₃ : A.Ideal}
  : IdealEq (IntersectionIdeal (IntersectionIdeal I₁ I₂) I₃) (IntersectionIdeal I₁ (IntersectionIdeal I₂ I₃))
:= λ x, by simp [IntersectionIdeal]

-- Intersections distribute over unions
def IntersectionIdeal.union {A' : Type ℓ} {A : Alg A'} {I₁ I₂ I₃ : A.Ideal}
  : IdealEq (IntersectionIdeal I₁ (UnionIdeal I₂ I₃))
            (UnionIdeal (IntersectionIdeal I₁ I₂) (IntersectionIdeal I₁ I₃))
:= λ x, begin
          simp [IntersectionIdeal, UnionIdeal],
          apply iff.intro,
          { intro H, cases H with H₁ H₂₃, cases H₂₃ with H₂ H₃,
            { exact or.inl (and.intro H₁ H₂) },
            { exact or.inr (and.intro H₁ H₃) }
          },
          { intro H, cases H with H₁ H₂,
            { exact and.intro H₁.1 (or.inl H₁.2) },
            { exact and.intro H₂.1 (or.inr H₂.2) }
          }
        end

-- The EmptyIdeal is an annihilator for IntersectionIdeal
def IntersectionIdeal.empty {A' : Type ℓ} {A : Alg A'} (I : A.Ideal)
  : IdealEq (IntersectionIdeal (EmptyIdeal A) I) (EmptyIdeal A)
:= λ x, by simp [IntersectionIdeal, EmptyIdeal]

-- The TrivialIdeal is an identity for IntersectionIdeal
def IntersectionIdeal.trivial {A' : Type ℓ} {A : Alg A'} (I : A.Ideal)
  : IdealEq (IntersectionIdeal (TrivialIdeal A) I) I
:= λ x, by simp [IntersectionIdeal, TrivialIdeal]


-- Joins
def JoinIdeal {A' : Type ℓ} {A : Alg A'} (I₁ I₂ : A.Ideal) : A.Ideal
:= { elem := A.Join I₁.elem I₂.elem
   , ideal_l := λ x₁ x₂ x₃ Ix₁ H
                , begin
                    cases Ix₁ with y₁ Ix₁,
                    cases Ix₁ with y₂ ω₁,
                    cases A.assoc ω₁.2.2 H with y₂x₂ ω₂,
                    existsi y₁, existsi y₂x₂,
                    apply and.intro ω₁.1,
                    refine and.intro _ ω₂.2,
                    exact I₂.ideal_l ω₁.2.1 ω₂.1
                  end
   }

-- Joins are commutative
def JoinIdeal.comm {A' : Type ℓ} {A : Alg A'} {I₁ I₂ : A.Ideal}
  : IdealEq (JoinIdeal I₁ I₂) (JoinIdeal I₂ I₁)
:= λ x, begin simp [JoinIdeal], rw [Alg.Join.comm] end

-- Joins are associative
def JoinIdeal.assoc {A' : Type ℓ} {A : Alg A'} {I₁ I₂ I₃ : A.Ideal}
  : IdealEq (JoinIdeal (JoinIdeal I₁ I₂) I₃) (JoinIdeal I₁ (JoinIdeal I₂ I₃))
:= λ x, begin simp [JoinIdeal], rw [Alg.Join.assoc] end

-- The EmptyIdeal is an annihilator for JoinIdeal
def JoinIdeal.empty {A' : Type ℓ} {A : Alg A'} (I : A.Ideal)
  : IdealEq (JoinIdeal (EmptyIdeal A) I) (EmptyIdeal A)
:= λ x, begin
          simp [JoinIdeal, Alg.Join, EmptyIdeal],
          intro H,
          cases H with x₁ H, cases H with x₂ H,
          exact H
        end

-- In a sep alg with identity, the TrivialIdeal is an identity for JoinIdeal
def JoinIdeal.trivial {A' : Type ℓ} {A : Alg A'} (A₁ : A.Ident) (I : A.Ideal)
  : IdealEq (JoinIdeal (TrivialIdeal A) I) I
:= λ x, iff.intro
          begin
            simp [JoinIdeal, Alg.Join, TrivialIdeal],
            intro H, cases H with x₁ H, cases H with x₂ H,
            exact I.ideal_r H.1 H.2
          end
          begin
            simp [JoinIdeal, Alg.Join, TrivialIdeal],
            intro H,
            existsi A₁.one, existsi x,
            exact and.intro H (A₁.join_one_l x)
          end


-- Ideal generated by a set of elements
def GenIdeal {A' : Type ℓ} (A : Alg A') (gen : set A') : A.Ideal
 := { elem := λ y, (gen y) ∨ (∃ x, gen x ∧ A.Divides x y)
    , ideal_l
     := λ x₁ x₂ x₃ Ix₁ H
        , or.elim Ix₁
            (λ Ix₁_l, or.inr (exists.intro x₁ (and.intro Ix₁_l (exists.intro x₂ H))))
            (λ Ix₁_r, exists.elim Ix₁_r (λ x ω
             , or.inr (exists.intro x (and.intro ω.1 (Divides.trans ω.2 (exists.intro x₂ H))))))
    }

def GenIdeal_member {A' : Type ℓ} {A : Alg A'} (gen : set A')
  : ∀ x, gen x → (GenIdeal A gen).elem x
:= λ x H, or.inl H

-- Ideal generated by an element
def GenIdeal₁ {A' : Type ℓ} (A : Alg A') (x : A') : A.Ideal
 := GenIdeal A (eq x)

def GenIdeal₁_member {A' : Type ℓ} {A : Alg A'} (x : A')
  : (GenIdeal₁ A x).elem x
:= GenIdeal_member _ x (eq.refl x)



/- Functions between separation algebras
 -
 -/
structure Hom {A₁' : Type ℓ₁} (A₁ : Alg A₁') {A₂' : Type ℓ₂} (A₂ : Alg A₂')
 := (fn : A₁' → set A₂')
    (linear : ∀ {x₁ x₂ x₃} {y₁ y₂ y₃}
              , fn x₁ y₁ → fn x₂ y₂ → fn x₃ y₃
              → A₁.join x₁ x₂ x₃ → A₂.join y₁ y₂ y₃)

-- The function induced by a Hom relation
def Hom.Fn {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} (f : Hom A₁ A₂)
  : set A₁' → set A₂'
:= λ X, λ y, ∃ x, X x ∧ f.fn x y

def Hom.Fn.subset {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} (f : Hom A₁ A₂)
  : ∀ (X₁ X₂ : set A₁'), X₁ ⊆ X₂ → f.Fn X₁ ⊆ f.Fn X₂
 := λ X₁ X₂ H y Hy
    , begin
        cases Hy with x Hx,
        existsi x,
        exact and.intro (H Hx.1) Hx.2
      end

-- The inverse image of the function induced by a Hom relation
def Hom.FnInv {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} (f : Hom A₁ A₂)
  : set A₂' → set A₁'
:= λ Y x, (∀ y', f.fn x y' → Y y')

def Hom.FnInv.subset {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} (f : Hom A₁ A₂)
  : ∀ (Y₁ Y₂ : set A₂')
    , Y₁ ⊆ Y₂ → f.FnInv Y₁ ⊆ f.FnInv Y₂
 := λ Y₁ Y₂ H x Hx y Hxy, H (Hx _ Hxy)

def Hom.Fn_FnInv {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} (f : Hom A₁ A₂)
  : ∀ (Y : set A₂'), f.Fn (f.FnInv Y) ⊆ Y
:= begin
     intros Y y H,
     simp [Hom.Fn] at H, cases H with x H,
     simp [Hom.FnInv] at H,
     apply H.2, apply H.1
   end


-- Upwards and downwards closure
def Hom.DownClosed {A₁' : Type ℓ₁} (A₁ : Alg A₁') {A₂' : Type ℓ₂} (A₂ : Alg A₂') (f : A₁' → set A₂') : Prop
  := ∀ {n₁ n₂} {m₁ m₂ m₃}
     , f n₁ m₁ → f n₂ m₂ → A₂.join m₁ m₂ m₃
     → ∃ (n₃ : A₁'), f n₃ m₃ ∧ A₁.join n₁ n₂ n₃

def Hom.UpClosed {A₁' : Type ℓ₁} (A₁ : Alg A₁') {A₂' : Type ℓ₂} (A₂ : Alg A₂') (f : A₁' → set A₂') : Prop
  := ∀ {m₁ m₂ m₃ : A₁'} {n₃ : A₂'}
     , A₁.join m₁ m₂ m₃ → f m₃ n₃
     → ∃ (n₁ n₂ : A₂'), A₂.join n₁ n₂ n₃ ∧ f m₁ n₁ ∧ f m₂ n₂

def Hom.Dist₁ {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} (f : Hom A₁ A₂) : Prop
  := ∀ (X₁ X₂ : set A₁')
     , A₂.Join (f.Fn X₁) (f.Fn X₂) ⊆ f.Fn (A₁.Join X₁ X₂)

def Hom.Dist₁.DownClosed {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} (f : Hom A₁ A₂) (fDist : f.Dist₁)
  : Hom.DownClosed A₁ A₂ f.fn
 := λ x₁ x₂ y₁ y₂ y₃ Hxy₁ Hxy₂ Hy
    , let q := @fDist (eq x₁) (eq x₂) y₃
                  (exists.intro y₁
                  (exists.intro y₂
                  (and.intro ⟨_, eq.refl _, Hxy₁⟩ (and.intro ⟨_, eq.refl _, Hxy₂⟩ Hy))))
      in begin
            simp [Alg.Join, Hom.fn] at q,
            simp [Hom.Fn] at q,
            cases q with x₃ H, cases H with Hxy₃ H',
            cases H' with x₁' H', cases H' with x₂' H',
            cases H' with H₁ H, cases H with H₂ H,
            subst H₁, subst H₂,
            existsi x₃, exact and.intro Hxy₃ H
          end

def Hom.Dist₂ {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} (f : Hom A₁ A₂) : Prop
  := ∀ (X₁ X₂ : set A₁')
     , f.Fn (A₁.Join X₁ X₂) ⊆ A₂.Join (f.Fn X₁) (f.Fn X₂)

def Hom.Dist₂.UpClosed {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} (f : Hom A₁ A₂) (fDist : f.Dist₂)
  : Hom.UpClosed A₁ A₂ f.fn
 := λ x₁ x₂ x₃ y₃ Hx Hxy₃
    , let q := @fDist (eq x₁) (eq x₂) y₃ ⟨x₃, ⟨x₁, x₂, (and.intro (eq.refl _) (and.intro (eq.refl _) Hx)) ⟩, Hxy₃⟩
      in begin
            simp [Alg.Join, Hom.fn] at q,
            simp [Hom.Fn] at q,
            cases q with y₁ H, cases H with y₂ H, cases H with Hy H,
            cases H with H₁ H₂, cases H₁ with x₁' H₁, cases H₂ with x₂' H₂,
            cases H₁ with H₁' H₁, cases H₂ with H₂' H₂,
            subst H₁', subst H₂',
            existsi y₁, existsi y₂,
            exact and.intro Hy (and.intro H₁ H₂)
         end

def Hom.Dist {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} (f : Hom A₁ A₂) : Prop
  := ∀ (X₁ X₂ : set A₁')
     , A₂.Join (f.Fn X₁) (f.Fn X₂) = f.Fn (A₁.Join X₁ X₂)

def Hom.Dist_iff {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} (f : Hom A₁ A₂)
  : f.Dist ↔ f.Dist₁ ∧ f.Dist₂
 := iff.intro
      (λ H, and.intro
              (λ X₁ X₂ y H', begin rw [H X₁ X₂] at H', exact H' end)
              (λ X₁ X₂ y H', begin rw [H X₁ X₂], exact H' end))
      (λ H X₁ X₂, funext (λ y, iff.to_eq (iff.intro (λ H', H.1 X₁ X₂ H') (λ H', H.2 X₁ X₂ H'))))



-- An equivalence relation on Homs; happens to imply equality but is easier to prove
def HomEq {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} (f₁ f₂ : Hom A₁ A₂) : Prop
  := ∀ x₁ x₂, f₁.fn x₁ x₂ ↔ f₂.fn x₁ x₂

def HomEq.refl {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} (f : Hom A₁ A₂) : HomEq f f
  := λ x₁ x₂, by trivial

def HomEq.symm {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} {f₁ f₂ : Hom A₁ A₂} (H : HomEq f₁ f₂) : HomEq f₂ f₁
  := λ x₁ x₂, iff.symm (H _ _)

def HomEq.trans {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} {f₁ f₂ f₃ : Hom A₁ A₂} (H₁₂ : HomEq f₁ f₂) (H₂₃ : HomEq f₂ f₃) : HomEq f₁ f₃
  := λ x₁ x₂, iff.trans (H₁₂ _ _) (H₂₃ _ _)

def HomEq.to_eq {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} {f₁ f₂ : Hom A₁ A₂}
  : HomEq f₁ f₂ → f₁ = f₂
 := begin
      intro H,
      cases f₁ with fn₁ linear₁, cases f₂ with fn₂ linear₂,
      have ω : fn₁ = fn₂, from
        begin
          apply funext, intro x₁,
          apply funext, intro x₂,
          apply iff.to_eq,
          apply H
        end,
      subst ω
    end


-- The identity hom
def Alg.IdHom {A' : Type ℓ} (A : Alg A') : Hom A A
 := { fn := eq
    , linear := λ x₁ x₂ x₃ y₁ y₂ y₃ H₁ H₂ H₃ H
                , begin subst H₁, subst H₂, subst H₃, exact H end
    }

-- Composition of homs
def Hom.circ {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} {A₃' : Type ℓ₃} {A₃ : Alg A₃'}
  (g : Hom A₂ A₃) (f : Hom A₁ A₂) : Hom A₁ A₃
 := { fn := λ x₁ x₃, ∃ x₂, f.fn x₁ x₂ ∧ g.fn x₂ x₃
    , linear := λ x₁ x₂ x₃ y₁ y₂ y₃ H₁ H₂ H₃ H
                , begin
                    cases H₁ with fx₁ H₁,
                    cases H₂ with fx₂ H₂,
                    cases H₃ with fx₃ H₃,
                    apply g.linear H₁.2 H₂.2 H₃.2,
                    apply f.linear H₁.1 H₂.1 H₃.1,
                    exact H
                  end
    }

-- Composition with IdHom on the left
def Hom.circ.id_l {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} (f : Hom A₁ A₂)
  : HomEq (Hom.circ A₂.IdHom f) f
 := begin
      intros x₁ x₂,
      simp [Hom.circ, Alg.IdHom],
      apply iff.intro,
      { intro H, cases H with x H,
        cases H with Hxx₂ H,
        subst Hxx₂,
        exact H
      },
      { intro H,
        existsi x₂,
        exact and.intro (eq.refl x₂) H
      }
    end

-- Composition with IdHom on the right
def Hom.circ.id_r {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} (f : Hom A₁ A₂)
  : HomEq (Hom.circ f A₁.IdHom) f
 := begin
      intros x₁ x₂,
      simp [Hom.circ, Alg.IdHom],
      apply iff.intro,
      { intro H, cases H with x H,
        cases H with Hxx₂ H,
        subst Hxx₂,
        exact H
      },
      { intro H,
        existsi x₁,
        exact and.intro (eq.refl x₁) H
      }
    end

-- Composition of homs is associative
def Hom.circ.assoc {A₁' : Type ℓ₁} {A₁ : Alg A₁'} {A₂' : Type ℓ₂} {A₂ : Alg A₂'} {A₃' : Type ℓ₃} {A₃ : Alg A₃'} {A₄' : Type ℓ₄} {A₄ : Alg A₄'}
  {h : Hom A₃ A₄} {g : Hom A₂ A₃} {f : Hom A₁ A₂}
  : HomEq (Hom.circ (Hom.circ h g) f) (Hom.circ h (Hom.circ g f))
 := begin
      intros x₁ x₂,
      simp [Hom.circ],
      apply iff.intro,
      { intro H, cases H with fx₁ H, cases H with H H', cases H' with gfx₁ H',
        existsi gfx₁,
        apply and.intro H'.2,
        existsi fx₁,
        exact and.intro H H'.1
      },
      { intro H, cases H with gfx₁ H, cases H with H H', cases H' with fx₁ H',
        existsi fx₁,
        apply and.intro H'.1,
        existsi gfx₁,
        exact and.intro H'.2 H
      }
    end


end Sep
