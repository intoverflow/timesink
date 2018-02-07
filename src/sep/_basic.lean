/- Separation algebras
 -
 -/



namespace Sep

-- Separation algebras
structure Alg (A : Type) : Type
 := (join : A → A → set A)
    (comm : ∀ {x₁ x₂ x₃}, join x₁ x₂ x₃ → join x₂ x₁ x₃)
    (assoc : ∀ {x₁ x₂ x₃ x₁x₂ x₁x₂x₃}
             , join x₁ x₂ x₁x₂ → join x₁x₂ x₃ x₁x₂x₃
             → ∃ x₂x₃, join x₂ x₃ x₂x₃ ∧ join x₁ x₂x₃ x₁x₂x₃)

-- Identity elements
structure Ident {A' : Type} (A : Alg A') : Type
 := (one : A')
    (join_one_r : ∀ x, A.join x one x)
    (join_one_uniq_r : ∀ {x y}, A.join x one y → y = x)

def Ident.join_one_l {A' : Type} {A : Alg A'} (A₁ : Ident A)
  : ∀ x, A.join A₁.one x x
:= λ x, A.comm (A₁.join_one_r x)

def Ident.join_one_uniq_l {A' : Type} {A : Alg A'} (A₁ : Ident A)
  : ∀ {x y : A'}, A.join A₁.one x y → y = x
:= λ x y H, A₁.join_one_uniq_r (A.comm H)

-- Identity elements are unique
def Ident.uniq {A' : Type} {A : Alg A'} (Ae₁ Ae₂ : Ident A)
  : Ae₁ = Ae₂
:= let H := Ae₁.join_one_uniq_r (A.comm (Ae₂.join_one_r Ae₁.one))
in begin cases Ae₁, cases Ae₂, simp * at * end



/- The Join function
 -
 -/
def Alg.Join {A' : Type} (A : Alg A')
  : set A' → set A' → set A'
:= λ X₁ X₂ x₃, ∃ x₁ x₂, X₁ x₁ ∧ X₂ x₂ ∧ A.join x₁ x₂ x₃

-- The join relation is a special case of the Join function
def Alg.join_Join {A' : Type} (A : Alg A') (x₁ x₂ x₃ : A')
  : A.join x₁ x₂ x₃ ↔ Alg.Join A (eq x₁) (eq x₂) x₃
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
def Alg.Join.comm {A' : Type} {A : Alg A'} {X₁ X₂ : set A'}
  : Alg.Join A X₁ X₂ = Alg.Join A X₂ X₁
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
def Alg.Join.assoc {A' : Type} {A : Alg A'} {X₁ X₂ X₃ : set A'}
  : Alg.Join A (Alg.Join A X₁ X₂) X₃ = Alg.Join A X₁ (Alg.Join A X₂ X₃)
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
def Divides {A' : Type} (A : Alg A') (x₁ x₃ : A') : Prop
 := ∃ x₂, A.join x₁ x₂ x₃

-- Divides is transitive
def Divides_trans {A' : Type} {A : Alg A'} {x₁ x₂ x₃ : A'}
  : Divides A x₁ x₂ → Divides A x₂ x₃ → Divides A x₁ x₃
 := λ d₁₂ d₂₃
    , exists.elim d₁₂ (λ d₁ ω₁
    , exists.elim d₂₃ (λ d₂ ω₂
    , exists.elim (A.assoc ω₁ ω₂) (λ x H
    , exists.intro x H.2)))

-- In a sep alg with identity, Divides is reflective
def Divides_refl {A' : Type} {A : Alg A'} (A₁ : Ident A) (x : A')
  : Divides A x x
 := exists.intro A₁.one (A₁.join_one_r x)



/- Ideals
 -
 -/
structure Ideal {A' : Type} (A : Alg A') : Type
 := (elem : set A')
    (ideal_l : ∀ {x₁ x₂ x₃}, elem x₁ → A.join x₁ x₂ x₃ → elem x₃)

def Ideal.ideal_r {A' : Type} {A : Alg A'} (I : Ideal A)
  : ∀ {x₁ x₂ x₃}, I.elem x₂ → A.join x₁ x₂ x₃ → I.elem x₃
:= λ x₁ x₂ x₃ Ix₂ H, I.ideal_l Ix₂ (A.comm H)

def ProperIdeal {A' : Type} {A : Alg A'} (I : Ideal A) : Prop
 := ∃ z₀, ¬ I.elem z₀

structure PrimeIdeal {A' : Type} {A : Alg A'} (I : Ideal A) : Type
 := (prime : ∀ {x₁ x₂ x₃}, A.join x₁ x₂ x₃ → I.elem x₃ → I.elem x₁ ∨ I.elem x₂)
    (proper: ProperIdeal I)

-- The whole set is an ideal
def TrivialIdeal {A' : Type} (A : Alg A') : Ideal A
 := { elem := λ y, true
    , ideal_l := λ x₁ x₂ x₃ Ix₁ H, Ix₁
    }

-- The empty set is an ideal
def EmptyIdeal {A' : Type} (A : Alg A') : Ideal A
 := { elem := λ y, false
    , ideal_l := λ x₁ x₂ x₃ Ix₁ H, Ix₁
    }

-- In a separation algebra with identity, the empty set is a prime ideal
def EmptyPrimeIdeal {A' : Type} {A : Alg A'} (A₁ : Ident A) : PrimeIdeal (EmptyIdeal A)
 := { prime := λ x₁ x₂ x₃ H, false.elim
    , proper := exists.intro A₁.one false.elim
    }



/- Equality of ideals
 -
 -/

-- Simple equality helper
def Ideal_eq {A' : Type} {A : Alg A'}
  : ∀ {I₁ I₂ : Ideal A}, I₁.elem = I₂.elem → I₁ = I₂
| (Ideal.mk e₁ i₁) (Ideal.mk e₂ i₂) H := begin simp * at H, subst H end

-- An equivalence relation; happens to imply equality but is easier to prove
def IdealEq {A' : Type} {A : Alg A'} (I₁ I₂ : Ideal A) : Prop
 := ∀ x, I₁.elem x ↔ I₂.elem x

def IdealEq.refl {A' : Type} {A : Alg A'} (I : Ideal A)
  : IdealEq I I
:= λ x, iff.refl _

def IdealEq.symm {A' : Type} {A : Alg A'} {I₁ I₂ : Ideal A}
  : IdealEq I₁ I₂ → IdealEq I₂ I₁
:= λ H x, iff.symm (H x)

def IdealEq.trans {A' : Type} {A : Alg A'} {I₁ I₂ I₃ : Ideal A}
  : IdealEq I₁ I₂ → IdealEq I₂ I₃ → IdealEq I₁ I₃
:= λ H₁₂ H₂₃ x, iff.trans (H₁₂ x) (H₂₃ x)

def IdealEq.to_eq {A' : Type} {A : Alg A'} {I₁ I₂ : Ideal A}
  : IdealEq I₁ I₂ → I₁ = I₂
:= λ H, Ideal_eq (funext (λ x, iff.to_eq (H x)))



/- Operations on ideals
 -
 -/

-- Unions
def UnionIdeal {A' : Type} {A : Alg A'} (I₁ I₂ : Ideal A) : Ideal A
:= { elem := λ y, I₁.elem y ∨ I₂.elem y
   , ideal_l := λ x₁ x₂ x₃ Ix₁ H
                , or.elim Ix₁
                    (λ ω, or.inl (I₁.ideal_l ω H))
                    (λ ω, or.inr (I₂.ideal_l ω H))
   }

-- Unions are commutative
def UnionIdeal.comm {A' : Type} {A : Alg A'} {I₁ I₂ : Ideal A}
  : IdealEq (UnionIdeal I₁ I₂) (UnionIdeal I₂ I₁)
:= λ x, by simp [UnionIdeal]

-- Unions are associative
def UnionIdeal.assoc {A' : Type} {A : Alg A'} {I₁ I₂ I₃ : Ideal A}
  : IdealEq (UnionIdeal (UnionIdeal I₁ I₂) I₃) (UnionIdeal I₁ (UnionIdeal I₂ I₃))
:= λ x, by simp [UnionIdeal]

-- The EmptyIdeal is an identity for UnionIdeal
def UnionIdeal.empty {A' : Type} {A : Alg A'} (I :Ideal A)
  : IdealEq (UnionIdeal (EmptyIdeal A) I) I
:= λ x, by simp [UnionIdeal, EmptyIdeal]

-- The TrivialIdeal is an annihilator for UnionIdeal
def UnionIdeal.trivial {A' : Type} {A : Alg A'} (I :Ideal A)
  : IdealEq (UnionIdeal (TrivialIdeal A) I) (TrivialIdeal A)
:= λ x, by simp [UnionIdeal, TrivialIdeal]


-- Intersections
def IntersectionIdeal {A' : Type} {A : Alg A'} (I₁ I₂ : Ideal A) : Ideal A
:= { elem := λ y, I₁.elem y ∧ I₂.elem y
   , ideal_l := λ x₁ x₂ x₃ Ix₁ H
                , and.intro
                    (I₁.ideal_l Ix₁.1 H)
                    (I₂.ideal_l Ix₁.2 H)
   }

-- Intersections are commutative
def IntersectionIdeal.comm {A' : Type} {A : Alg A'} {I₁ I₂ :Ideal A}
  : IdealEq (IntersectionIdeal I₁ I₂) (IntersectionIdeal I₂ I₁)
:= λ x, by simp [IntersectionIdeal]

-- Intersections are associative
def IntersectionIdeal.assoc {A' : Type} {A : Alg A'} {I₁ I₂ I₃ : Ideal A}
  : IdealEq (IntersectionIdeal (IntersectionIdeal I₁ I₂) I₃) (IntersectionIdeal I₁ (IntersectionIdeal I₂ I₃))
:= λ x, by simp [IntersectionIdeal]

-- Intersections distribute over unions
def IntersectionIdeal.union {A' : Type} {A : Alg A'} {I₁ I₂ I₃ : Ideal A}
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
def IntersectionIdeal.empty {A' : Type} {A : Alg A'} (I :Ideal A)
  : IdealEq (IntersectionIdeal (EmptyIdeal A) I) (EmptyIdeal A)
:= λ x, by simp [IntersectionIdeal, EmptyIdeal]

-- The TrivialIdeal is an identity for IntersectionIdeal
def IntersectionIdeal.trivial {A' : Type} {A : Alg A'} (I :Ideal A)
  : IdealEq (IntersectionIdeal (TrivialIdeal A) I) I
:= λ x, by simp [IntersectionIdeal, TrivialIdeal]


-- Joins
def JoinIdeal {A' : Type} {A : Alg A'} (I₁ I₂ : Ideal A) : Ideal A
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
def JoinIdeal.comm {A' : Type} {A : Alg A'} {I₁ I₂ :Ideal A}
  : IdealEq (JoinIdeal I₁ I₂) (JoinIdeal I₂ I₁)
:= λ x, begin simp [JoinIdeal], rw [Alg.Join.comm] end

-- Joins are associative
def JoinIdeal.assoc {A' : Type} {A : Alg A'} {I₁ I₂ I₃ : Ideal A}
  : IdealEq (JoinIdeal (JoinIdeal I₁ I₂) I₃) (JoinIdeal I₁ (JoinIdeal I₂ I₃))
:= λ x, begin simp [JoinIdeal], rw [Alg.Join.assoc] end

-- The EmptyIdeal is an annihilator for JoinIdeal
def JoinIdeal.empty {A' : Type} {A : Alg A'} (I :Ideal A)
  : IdealEq (JoinIdeal (EmptyIdeal A) I) (EmptyIdeal A)
:= λ x, begin
          simp [JoinIdeal, Alg.Join, EmptyIdeal],
          intro H,
          cases H with x₁ H, cases H with x₂ H,
          exact H
        end

-- In a sep alg with identity, the TrivialIdeal is an identity for JoinIdeal
def JoinIdeal.trivial {A' : Type} {A : Alg A'} (A₁ : Ident A) (I :Ideal A)
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
def GenIdeal {A' : Type} (A : Alg A') (gen : set A') : Ideal A
 := { elem := λ y, (gen y) ∨ (∃ x, gen x ∧ Divides A x y)
    , ideal_l
     := λ x₁ x₂ x₃ Ix₁ H
        , or.elim Ix₁
            (λ Ix₁_l, or.inr (exists.intro x₁ (and.intro Ix₁_l (exists.intro x₂ H))))
            (λ Ix₁_r, exists.elim Ix₁_r (λ x ω
             , or.inr (exists.intro x (and.intro ω.1 (Divides_trans ω.2 (exists.intro x₂ H))))))
    }

def GenIdeal_member {A' : Type} {A : Alg A'} (gen : set A')
  : ∀ x, gen x → (GenIdeal A gen).elem x
:= λ x H, or.inl H

-- Ideal generated by an element
def GenIdeal₁ {A' : Type} (A : Alg A') (x : A') : Ideal A
 := GenIdeal A (eq x)

def GenIdeal₁_member {A' : Type} {A : Alg A'} (x : A')
  : (GenIdeal₁ A x).elem x
:= GenIdeal_member _ x (eq.refl x)


end Sep
