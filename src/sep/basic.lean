/- Separation algebras
 -
 -/
namespace Sep
universes ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄

-- Separation algebras
structure Alg.Assoc {A' : Type ℓ} (join : A' → A' → set A')
  {x₁ x₂ x₃ x₁x₂ x₁x₂x₃}
  (H₁ : join x₁ x₂ x₁x₂) (H₂ : join x₁x₂ x₃ x₁x₂x₃)
 := (x : A')
    (J₁ : join x₂ x₃ x)
    (J₂ : join x₁ x x₁x₂x₃)

def IsAssoc {A' : Type ℓ} (join : A' → A' → set A') : Prop
 := ∀ {x₁ x₂ x₃ x₁x₂ x₁x₂x₃}
      (H₁ : join x₁ x₂ x₁x₂) (H₂ : join x₁x₂ x₃ x₁x₂x₃)
      {P : Prop}
      (C : Alg.Assoc join H₁ H₂ → P)
    , P

structure Alg
 := (τ : Type ℓ)
    (join : τ → τ → set τ)
    (comm : ∀ {x₁ x₂ x₃}, join x₁ x₂ x₃ → join x₂ x₁ x₃)
    (assoc : IsAssoc join)


-- Subsets of separation algebras
def Set (A : Alg.{ℓ}) := set A.τ

class has_sepmul (α : Type ℓ) := (sepmul : α → α → α)
infix <*> := has_sepmul.sepmul

instance Set_has_emptyc (A : Alg.{ℓ}) : has_emptyc (Set A) := set.has_emptyc
instance Set_has_subset (A : Alg.{ℓ}) : has_subset (Set A) := set.has_subset
instance Set_has_inter (A : Alg.{ℓ}) : has_inter (Set A) := set.has_inter
instance Set_has_union (A : Alg.{ℓ}) : has_union (Set A) := set.has_union
instance Set_has_mem (A : Alg.{ℓ}) : has_mem A.τ (Set A) := set.has_mem

def Set.Cover.Subset {A : Alg.{ℓ}}
    {S : Set A} {SS : set (Set A)}
    (Scover : S = set.sUnion SS)
    {T : Set A} (SST : T ∈ SS)
  : T ⊆ S
 := begin
      intros x H,
      rw Scover,
      existsi T,
      exact exists.intro SST H
    end

def Set.Subset.trans {A : Alg.{ℓ}}
    {S₁ S₂ S₃ : Set A}
    (H₁₂ : S₁ ⊆ S₂) (H₂₃ : S₂ ⊆ S₃)
  : S₁ ⊆ S₃
 := λ s H, H₂₃ (H₁₂ H)

def Set.nonempty {A : Alg.{ℓ}} (S : Set A) : Prop
 := ∃ x, x ∈ S

def Alg.EmptySet (A : Alg.{ℓ}) : Set A := λ a, false
def Alg.WholeSet (A : Alg.{ℓ}) : Set A := λ a, true

def Set.Compl {A : Alg.{ℓ}} (S : Set A) : Set A
 := set.compl S

def Set.ComplCompl {A : Alg.{ℓ}} (S : Set A)
  : S.Compl.Compl = S
 := begin
      apply funext, intro s,
      apply iff.to_eq,
      apply iff.intro,
      { intro H₁,
        apply classical.by_contradiction,
        intro H₂,
        exact H₁ H₂
      },
      { intros H₁ H₂,
        exact H₂ H₁
      }
    end

def Set.mem_nonempty {A : Alg.{ℓ}} {S : Set A}
    {x} (H : x ∈ S)
  : S ≠ ∅
 := λ Q, cast (congr_fun Q x) H

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
     (λ H, Alg.Join.show rfl rfl H)
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
        apply A.assoc H'.2.2 H.2,
        intro a,
        existsi y₁, existsi a.x,
        refine and.intro H'.1 (and.intro _ a.J₂),
        existsi y₂, existsi x₂,
        refine and.intro H'.2.1 (and.intro H.1 a.J₁)
      },
      { intro H, cases H with x₁ H, cases H with x₂ H,
        cases H with X₁x₁ H, cases H with H' H, cases H' with y₁ H', cases H' with y₂ H',
        apply A.assoc (A.comm H'.2.2) (A.comm H),
        intro a,
        existsi a.x, existsi y₂,
        refine and.intro _ (and.intro H'.2.1 (A.comm a.J₂)),
        existsi x₁, existsi y₁,
        exact and.intro X₁x₁ (and.intro H'.1 (A.comm a.J₁))
      },
    end



/- The "divides" relation
 -
 -/
def Alg.Divides (A : Alg.{ℓ}) (x₁ x₃ : A.τ)
  : Prop
 := ∀ (P : Prop)
      (C₁ : ∀ {x}, A.join x₁ x x₃ → P)
      (C₂ : x₁ = x₃ → P)
    , P

-- Divides is transitive
def Divides.trans {A : Alg.{ℓ}} {x₁ x₂ x₃}
  : A.Divides x₁ x₂ → A.Divides x₂ x₃ → A.Divides x₁ x₃
 := λ d₁₂ d₂₃ P C₁ C₂
    , begin
        apply d₁₂,
        { intros x'₁ Jx'₁,
          apply d₂₃,
          { intros x'₂ Jx'₂,
            apply A.assoc Jx'₁ Jx'₂, intro a,
            exact C₁ a.J₂
          },
          { intro E, subst E, exact C₁ Jx'₁ }
        },
        { intro E, subst E,
          apply d₂₃,
          { intros x'₂ Jx'₂,
            exact C₁ Jx'₂
          },
          { apply C₂ }
        }
      end

-- Divides is reflective
def Divides.refl (A : Alg.{ℓ}) (x : A.τ)
  : A.Divides x x
 := λ P C₁ C₂ , C₂ rfl


/- Parts
 -
 -/
def Alg.Part (A : Alg.{ℓ}) (m : A.τ) : Prop
 := ∃ m₂ m₃, A.join m m₂ m₃



/- Units
 -
 -/
def Alg.Unit (A : Alg.{ℓ}) : Set A
 := λ u, ∀ x, A.Divides u x

-- If w divides a unit, then w is also a unit
def Unit.Divides {A : Alg.{ℓ}} {u} (uUnit : A.Unit u) (v : A.τ)
  : A.Divides v u → A.Unit v
 := begin
      intro H,
      intro x,
      apply Divides.trans H,
      apply uUnit
    end

-- Distinct units join with each other to form new units
def Unit.Join {A : Alg.{ℓ}}
    {u₁} (Uu₁ : A.Unit u₁)
    {u₂} (Uu₂ : A.Unit u₂)
    {P : Prop}
    (C : ∀ u₃, u₃ ∈ A.join u₁ u₂ → A.Unit u₃ → P)
    (E : u₁ = u₂ → P)
  : P
 := begin
      apply Uu₁ u₂,
      { intros w Jw,
        apply Uu₂ w,
        { intros v Jv,
          apply A.assoc (A.comm Jv) (A.comm Jw),
          intro a,
          apply C a.x (A.comm a.J₁),
          apply Unit.Divides Uu₂,
          intros P C₁ C₂,
          exact C₁ (A.comm a.J₂)
        },
        { intro E', subst E', apply C, repeat { assumption } }
      },
      { exact E }
    end

def Alg.ProperUnit (A : Alg.{ℓ}) : Set A
 := λ u, ∀ x, ∃ xu, A.join u xu x

def ProperUnit.Unit {A : Alg.{ℓ}} {u : A.τ}
    (uU : u ∈ A.ProperUnit)
  : u ∈ A.Unit
 := begin
      intro x,
      cases uU x with xu Hxu,
      intros P C₁ C₂,
      exact C₁ Hxu
    end

def Alg.StrongUnit (A : Alg.{ℓ}) : Set A
 := λ u, u ∈ A.Unit ∧ (∀ v, v ∈ A.Unit → A.join u v ⊆ A.Unit)

-- If w divides a proper unit, then w is also a unit
def ProperUnit.Divides {A : Alg.{ℓ}} {u}
    (uUnit : A.ProperUnit u)
    (v : A.τ)
  : A.Divides v u → A.ProperUnit v
 := begin
      intro H,
      intro x,
      apply H; clear H,
      { intros w Jvwu,
        cases uUnit x with xu Ju,
        apply A.assoc Jvwu Ju,
        intro a,
        existsi a.x,
        exact a.J₂
      },
      { intro E, subst E,
        exact uUnit x
      }
    end

-- Proper units join with each other to form new proper units
def ProperUnit.Join {A : Alg.{ℓ}}
    {u₁} (Uu₁ : A.ProperUnit u₁)
    {u₂} (Uu₂ : A.ProperUnit u₂)
  : ∃ u₃, u₃ ∈ A.join u₁ u₂ ∧ A.ProperUnit u₃
 := begin
      cases Uu₁ u₂ with w Jw,
      cases Uu₂ w with v Jv,
      apply A.assoc (A.comm Jv) (A.comm Jw),
      intro a,
      existsi a.x,
      apply and.intro (A.comm a.J₁),
      apply ProperUnit.Divides Uu₂,
      intros P C₁ C₂,
      exact C₁ (A.comm a.J₂)
    end

/- Linear elements
 -
 -/
def Alg.Linear (A : Alg.{ℓ}) : Set A
 := λ u
    , (∀ x, ∃! y, A.join u x y)
      ∧ (∀ x₁ x₂, A.join u x₁ = A.join u x₂ → x₁ = x₂)

def Linear.injective {A : Alg.{ℓ}} {l : A.τ} (lLinear : A.Linear l)
    {x₁ x₂ y : A.τ}
    (J₁ : A.join l x₁ y) (J₂ : A.join l x₂ y)
  : x₁ = x₂
 := begin
      apply lLinear.2,
      apply funext, intro y₁,
      apply iff.to_eq, apply iff.intro,
      { intro J₁',
        have Q₁ := lLinear.1 x₁,
        cases Q₁ with y₁ Q₁,
        cases Q₁ with Jy₁ Q₁,
        have P := Q₁ _ J₁',
        subst P,
        have P := Q₁ _ J₁,
        subst P,
        exact J₂
      },
      { intro J₂',
        have Q₁ := lLinear.1 x₂,
        cases Q₁ with y₁ Q₁,
        cases Q₁ with Jy₁ Q₁,
        have P := Q₁ _ J₂',
        subst P,
        have P := Q₁ _ J₂,
        subst P,
        exact J₁
      }
    end

def Linear.well_defined {A : Alg.{ℓ}} {l : A.τ} (lLinear : A.Linear l)
    {x y₁ y₂ : A.τ}
    (J₁ : A.join l x y₁) (J₂ : A.join l x y₂)
  : y₁ = y₂
 := begin
      have Q := lLinear.1 x,
      cases Q with y Q,
      cases Q with Jy Q,
      refine eq.trans (Q _ J₁) (Q _ J₂).symm,
    end


/- Linear units
 -
 -/
def Alg.LinearUnit (A : Alg.{ℓ}) : Set A
  := A.ProperUnit ∩ A.Linear

def LinearUnit.Ident (A : Alg.{ℓ})
    (H : ∃ u, u ∈ A.LinearUnit)
  : ∃ i, (∀ x, A.join i x = eq x)
 := begin
      cases H with u Hu,
      cases Hu.1 u with i Hi,
      existsi i,
      intro x₁, apply funext, intro x₂,
      apply iff.to_eq, apply iff.intro,
      { intro J,
        have Q₁ := Hu.2.1 x₁,
        cases Q₁ with y₁ Q₁,
        cases Q₁ with Jy₁ Q₁,
        have Q₂ := Hu.2.1 x₂,
        cases Q₂ with y₂ Q₂,
        cases Q₂ with Jy₂ Q₂,
        apply A.assoc J (A.comm Jy₂),
        intro a, cases a with a J₁ J₂,
        have E : a = y₁ := Q₁ _ (A.comm J₁),
        subst E, clear Q₁ J₁,
        refine Linear.injective Hu.2 Jy₁ _,
        apply A.assoc (A.comm Jy₁) (A.comm J₂),
        intro a', cases a' with a' J₁' J₂',
        have E : u = a' := Linear.well_defined Hu.2 Hi J₁',
        subst E,
        have E : y₂ = a := Linear.well_defined Hu.2 (A.comm J₂') Jy₁,
        subst E,
        exact Jy₂
      },
      { intro E, subst E,
        have Q := Hu.2.1 x₁,
        cases Q with y Q,
        cases Q with Jy Q,
        apply A.assoc Hi Jy,
        intro a, cases a with a J₁ J₂,
        have E : x₁ = a := Linear.injective Hu.2 Jy J₂,
        subst E,
        exact J₁
      }
    end

def LinearUnit.GroupIdent (A : Alg.{ℓ})
    (H : ∃ u, u ∈ A.LinearUnit)
  : ∃ i, (i ∈ A.LinearUnit ∧ ∀ x, A.join i x = eq x)
 := begin
      cases LinearUnit.Ident A H with i Hi,
      cases H with u Hu,
      existsi i,
      refine and.intro _ Hi,
      apply and.intro,
      { apply ProperUnit.Divides Hu.1,
        intros P C₁ C₂,
        apply @C₁ u,
        rw Hi
      },
      apply and.intro,
      { intro x, existsi x,
        apply and.intro,
        { simp, rw Hi },
        { intros y Hy, rw Hi at Hy, exact Hy.symm }
      },
      { intros x₁ x₂ J,
        repeat { rw Hi at J },
        rw J
      }
    end


/- Weak identities
 -
 -/
def Alg.WeakIdentity (A : Alg.{ℓ}) (w : A.τ) : Prop
 := ∀ (x), A.join w x x

def WeakIdentity.Unit {A : Alg.{ℓ}} {w : A.τ} (wWeak : A.WeakIdentity w)
  : A.Unit w
 := λ x P C₁ C₂, C₁ (wWeak x)


/- Rational and integral sets
 -
 -/

-- A set is Rational if it contains all of the linear units.
def Set.Rational {A : Alg.{ℓ}} (R : Set A) : Prop
 := A.Unit ∩ A.Linear ⊆ R

-- A set is Integral if it contains no units.
def Set.Integral {A : Alg.{ℓ}} (I : Set A) : Prop
 := ∀ x, x ∈ I → ¬ (A.Unit x ∧ A.Linear x)

-- Arbitrary unions of integral sets are again integral
def Integral.Union {A : Alg.{ℓ}}
    (PP : set (Set A))
    (H : ∀ (p : Set A), p ∈ PP → p.Integral)
  : Set.Integral (set.sUnion PP)
 := begin
      intros x Hx F,
      cases Hx with p HS,
      cases HS with HPP Hxp,
      exact H p HPP x Hxp F
    end


/- Primes
 -
 -/
structure Alg.Prime (A : Alg.{ℓ}) (p : A.τ)
 := (u : A.τ)
    (proper : A.Divides p u → false)
    (prime : ∀ {x₁ x₂ x₃}
             , A.join x₁ x₂ x₃ → A.Divides p x₃
             → A.Divides p x₁ ∨ A.Divides p x₂)



/- Important kinds of sets
 -
 -/
def Set.Ideal {A : Alg.{ℓ}} (I : Set A) : Prop
 := ∀ {x₁ x₂ x₃}, x₁ ∈ I → A.join x₁ x₂ x₃ → x₃ ∈ I

def Ideal.Overlap {A : Alg.{ℓ}} (I S : Set A)
  : Set A
 := λ x, x ∈ I ∧ (∃ y, (y ∈ S) ∧ (∀ {z}, ¬ A.join x y z))

infix <-> := Ideal.Overlap

def Overlap.Ideal {A : Alg.{ℓ}} {I₁ I₂ : Set A}
  (I₁ideal : I₁.Ideal)
  : (I₁ <-> I₂).Ideal
 := begin
      intros x₁ x₂ x₃ Ix₁ Jx,
      apply and.intro (I₁ideal Ix₁.1 Jx),
      cases Ix₁ with Ix₁ Hy,
      cases Hy with y Hy,
      existsi y,
      apply and.intro Hy.1,
      intros z Jz,
      apply A.assoc (A.comm Jx) Jz, intro a,
      apply Hy.2 a.J₁
    end

def Set.WeakIdeal {A : Alg.{ℓ}} (I : Set A) : Prop
 := ∀ {x₁ x₂ x₃}, x₁ ∈ I → A.join x₁ x₂ x₃ → ∃ x₃', A.join x₁ x₂ x₃' ∧ x₃' ∈ I

def Ideal.WeakIdeal {A : Alg.{ℓ}} (I : Set A)
  : I.Ideal → I.WeakIdeal
 := λ IIdeal x₁ x₂ x₃ Ix₁ Jx
    , exists.intro x₃ (and.intro Jx (IIdeal Ix₁ Jx))

def Set.Proper {A : Alg.{ℓ}} (I : Set A)
  : Prop
 := ∀ {P : Prop} (C : ∀ z, ¬ z ∈ I → P), P

def Proper.one_not_elem {A : Alg.{ℓ}} (A₁ : A.Ident) {I : Set A} (Iideal : I.Ideal) (Iproper : I.Proper)
  : ¬ A₁.one ∈ I
:= begin
     intro H',
     apply Iproper,
     intros z Hz,
     apply Hz,
     exact Iideal H' (A₁.join_one_l z)
   end

-- A set S is a sub-algebra if it associates
def Set.SubAlg {A : Alg.{ℓ}} (S : Set A) : Prop
 := ∀ (x₁ x₂ x₃ x₁₂ x₁₂₃ : {x // S x})
      (H₁ : A.join x₁ x₂ x₁₂) (H₂ : A.join x₁₂ x₃ x₁₂₃)
      {P : Prop}
      (C : ∀ (a : Alg.Assoc A.join H₁ H₂), a.x ∈ S → P)
    , P

-- Subalgebras are, of course, algebras
def Set.SubAlg.Alg {A : Alg.{ℓ}} {S : Set A}
    (SSA : S.SubAlg)
  : Alg.{ℓ}
 := { τ := { x // S x}
    , join := λ x₁ x₂ x₃, A.join x₁.val x₂.val x₃.val
    , comm := λ x₁ x₂ x₃ J, A.comm J
    , assoc := λ x₁ x₂ x₃ x₁₂ x₁₂₃ J₁₂ J₁₂₃ P C
               , begin
                  apply SSA _ _ _ _ _ J₁₂ J₁₂₃,
                  intros a Sa,
                  apply C,
                  exact { x := { val := a.x, property := Sa }
                        , J₁ := a.J₁
                        , J₂ := a.J₂
                        }
                 end
    }

-- A set S is join-closed if:  S <*> S ⊆ S
def Set.JoinClosed {A : Alg.{ℓ}} (S : Set A) : Prop
  := ∀ (b₁ b₂ b₃)
     , b₃ ∈ A.join b₁ b₂
     → b₁ ∈ S → b₂ ∈ S
     → b₃ ∈ S

-- Join-closed sets are subalgebras in a very strong way
def Set.JoinClosed.assoc {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
    {s₁ s₂ s₃ s₁₂ s₁₂₃}
    {J₁₂ : s₁₂ ∈ A.join s₁ s₂}
    {J₁₂₃ : s₁₂₃ ∈ A.join s₁₂ s₃}
    (a : Alg.Assoc A.join J₁₂ J₁₂₃)
    (S₁ : s₁ ∈ S) (S₂ : s₂ ∈ S) (S₃ : s₃ ∈ S)
  : a.x ∈ S
 := begin
      apply SJC _ _ _ a.J₁,
      repeat { assumption }
    end

def Set.JoinClosed.SubAlg {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : S.SubAlg
 := begin
      intros x₁ x₂ x₃ x₁₂ x₁₂₃ J₁₂ J₁₂₃ P C,
      apply A.assoc J₁₂ J₁₂₃,
      intro a,
      have Ha := Set.JoinClosed.assoc SJC a x₁.property x₂.property x₃.property,
      exact C a Ha
    end

def Set.JoinClosed.Alg {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : Alg.{ℓ}
 := SJC.SubAlg.Alg

-- The join-closure of a set of elements
inductive JoinClosure {A : Alg.{ℓ}} (S : Set A)
  : Set A
| gen : ∀ {x}, x ∈ S → JoinClosure x
| mul : ∀ {x₁ x₂ x₃}
        , x₃ ∈ A.join x₁ x₂
        → JoinClosure x₁
        → JoinClosure x₂
        → JoinClosure x₃

def JoinClosure.JoinClosed {A : Alg.{ℓ}} (S : Set A)
  : (JoinClosure S).JoinClosed
 := begin
      intros x₁ x₂ x₃ Jx Gx₁ Gx₂,
      exact JoinClosure.mul Jx Gx₁ Gx₂
    end

def Alg.JoinClosure₁ (A : Alg.{ℓ}) (x : A.τ) : Set A
 := JoinClosure (eq x)

def JoinClosure₁.JoinClosed {A : Alg.{ℓ}} (x : A.τ)
  : (A.JoinClosure₁ x).JoinClosed
 := JoinClosure.JoinClosed _


-- A set S is prime if:  a <*> b ∩ S ≠ ∅ implies a ∈ S or b ∈ S
def Set.Prime {A : Alg.{ℓ}} (I : Set A) : Prop
 := ∀ (x₁ x₂ x₃)
    , x₃ ∈ A.join x₁ x₂
    → x₃ ∈ I
    → x₁ ∈ I ∨ x₂ ∈ I

def Set.StrongPrime {A : Alg.{ℓ}} (I : Set A) : Prop
 := ∀ (x₁ x₂ x₃)
    , x₃ ∈ A.join x₁ x₂
    → x₃ ∈ I
    → x₁ ∈ I ∧ x₂ ∈ I

def Set.StrongPrime.Prime {A : Alg.{ℓ}} {I : Set A}
    (ISP : I.StrongPrime)
  : I.Prime
 := begin
      intros x₁ x₂ x₃ Jx Ix₃,
      exact or.inl (ISP _ _ _ Jx Ix₃).1
    end

-- Arbitrary unions of primes are again prime
def Prime.Union {A : Alg.{ℓ}}
    (PP : set (Set A))
    (H : ∀ (p : Set A), p ∈ PP → p.Prime)
  : Set.Prime (set.sUnion PP)
 := begin
      intros x₁ x₂ x₃ Jx H,
      cases H with p H,
      cases H with pPrime' px₃,
      have pPrime : Set.Prime p := H p pPrime',
      have Q := pPrime _ _ _ Jx px₃,
      cases Q with Q Q,
      { apply or.inl,
        existsi p,
        exact exists.intro pPrime' Q
      },
      { apply or.inr,
        existsi p,
        exact exists.intro pPrime' Q
      }
    end

-- The set of units is prime
def Alg.Unit.Prime (A : Alg.{ℓ})
  : A.Unit.Prime
 := begin
      intros x₁ x₂ x₃ Jx Hx₃,
      apply or.inl,
      have Dx : A.Divides x₁ x₃ := λ P C₁ C₂, C₁ Jx,
      exact Unit.Divides Hx₃ _ Dx
    end

-- The set of proper units is prime
def Alg.ProperUnit.StrongPrime (A : Alg.{ℓ})
    : A.ProperUnit.StrongPrime
 := begin
      intros x₁ x₂ u Jx Hu,
      apply and.intro,
      { intro x,
        cases Hu x with xu Ju,
        apply A.assoc Jx Ju,
        intro a,
        existsi a.x,
        exact a.J₂
      },
      { intro x,
        cases Hu x with xu Ju,
        apply A.assoc (A.comm Jx) Ju,
        intro a,
        existsi a.x,
        exact a.J₂
      }
    end

-- A set S is full if:  a <*> b ∩ S ≠ ∅ implies a <*> b ⊆ S
def Set.Full {A : Alg.{ℓ}} (p : Set A) : Prop
 := ∀ {x₁ x₂ x₃}
    , x₃ ∈ A.join x₁ x₂
    → x₃ ∈ p
    → A.join x₁ x₂ ⊆ p

-- Prime ideals are full
def PrimeIdeal.Full {A : Alg.{ℓ}} {p : Set A}
    (pPrime : p.Prime)
    (pIdeal : p.Ideal)
  : p.Full
 := begin
      intros x₁ x₂ x₃ Jx Px x₃' Jx',
      cases pPrime _ _ _ Jx Px with H₁ H₂,
      { exact pIdeal H₁ Jx' },
      { exact pIdeal H₂ (A.comm Jx') }
    end

-- The complement of a prime set is join-closed
def Set.Prime.Complement_JoinClosed {A : Alg.{ℓ}} {p : Set A}
    (pPrime : p.Prime)
  : p.Compl.JoinClosed
 := begin
      intros x₁ x₂ x₃ Jx Px₁ Px₂,
      intro Px₃,
      cases pPrime _ _ _ Jx Px₃ with Px₁' Px₂',
      { exact Px₁ Px₁' },
      { exact Px₂ Px₂' }
    end

-- The complement of a join-closed set is a prime set
def Set.JoinClosed.Complement_Prime {A : Alg.{ℓ}} {S : Set A}
    (SJC : S.JoinClosed)
  : S.Compl.Prime
 := begin
      intros x₁ x₂ x₃ Jx Sx₃,
      cases classical.em (x₁ ∈ S) with Sx₁ Sx₁,
      { cases classical.em (x₂ ∈ S) with Sx₂ Sx₂,
        { apply false.elim, apply Sx₃,
          exact SJC _ _ _ Jx Sx₁ Sx₂
        },
        { exact or.inr Sx₂ }
      },
      { exact or.inl Sx₁ }
    end

-- The whole set is an ideal
def WholeIdeal (A : Alg.{ℓ}) : (A.WholeSet).Ideal
 := λ x₁ x₂ x₃ Ix₁ H, Ix₁

-- The whole set is join-closed
def WholeJoinClosed (A : Alg.{ℓ}) : (A.WholeSet).JoinClosed
 := λ x₁ x₂ x₃ Jx H₁ H₂, true.intro

-- The whole set is a prime set
def WholePrime (A : Alg.{ℓ}) : (A.WholeSet).Prime
 := λ x₁ x₂ x₃ Jx H, or.inl true.intro

-- The empty set is an ideal
def EmptyIdeal (A : Alg.{ℓ}) : (A.EmptySet).Ideal
 := λ x₁ x₂ x₃ Ix₁ H, Ix₁

-- In a separation algebra with identity, the empty set is a proper set
def EmptyProper.Proper {A : Alg.{ℓ}} (A₁ : A.Ident) : (A.EmptySet).Proper
 := λ P C, C A₁.one false.elim

-- The empty set is join-closed
def EmptyJoinClosed (A : Alg.{ℓ}) : (A.EmptySet).JoinClosed
 := λ x₁ x₂ x₃ Jx H₁ H₂, false.elim H₁

-- The empty set is a prime set
def EmptyPrime (A : Alg.{ℓ}) : (A.EmptySet).Prime
 := λ x₁ x₂ x₃ H, false.elim

-- Ideal generated by a set of elements
def GenIdeal {A : Alg.{ℓ}} (gen : Set A) : Set A
 := λ y, (∃ x, A.Divides x y ∧ gen x)

def GenIdeal.Ideal {A : Alg.{ℓ}} (gen : Set A) : (GenIdeal gen).Ideal
 := λ a₁ a₂ a₃ Ia₁ H
    , begin
        cases Ia₁ with x Hx,
        cases Hx with Dxa₁ Gx,
        existsi x,
        refine and.intro _ Gx,
        apply Divides.trans @Dxa₁,
        intros P C₁ C₂,
        exact C₁ H
      end

def GenIdeal.mem {A : Alg.{ℓ}} (gen : Set A)
  : gen ⊆ (GenIdeal gen)
 := begin
      intros x Gx,
      existsi x,
      refine and.intro _ Gx,
      apply Divides.refl
    end

def GenIdeal.nonempty {A : Alg.{ℓ}} {gen : Set A} (gen_notempty : gen ≠ ∅)
  : GenIdeal gen ≠ ∅
 := begin
      intro H,
      apply gen_notempty,
      apply funext, intro x,
      apply iff.to_eq,
      apply iff.intro,
      { intro G,
        rw H.symm,
        apply GenIdeal.mem,
        assumption
      },
      { exact false.elim }
    end

-- Ideal generated by an element
def Alg.GenIdeal₁ (A : Alg.{ℓ}) (x : A.τ) : Set A
 := GenIdeal (eq x)

def GenIdeal₁.Ideal {A : Alg.{ℓ}} (x : A.τ)
  : (A.GenIdeal₁ x).Ideal
 := @GenIdeal.Ideal A (eq x)

def GenIdeal₁.nonempty {A : Alg.{ℓ}} (x : A.τ)
  : A.GenIdeal₁ x ≠ ∅
 := GenIdeal.nonempty (λ H, cast (congr_fun H x) rfl)

def GenIdeal₁.mem {A : Alg.{ℓ}} (x : A.τ)
  : x ∈ (A.GenIdeal₁ x)
:= GenIdeal.mem (eq x) rfl


-- Generating sets
def Set.Generating {A : Alg.{ℓ}} (G : Set A) : Prop
 := ∀ x, ∃ g, A.Divides g x ∧ g ∈ G

def Set.NonGenerating {A : Alg.{ℓ}} (G : Set A) : Prop
 := ∃ x, ∀ g, ¬ (A.Divides g x ∧ g ∈ G)

def NonGenerating_iff {A : Alg.{ℓ}} (G : Set A)
  : G.NonGenerating ↔ ¬ G.Generating
 := begin
      apply iff.intro,
      { intros HG F,
        cases HG with x Hx,
        cases F x with g Hg,
        exact Hx g Hg
      },
      { intros HG,
        simp [Set.Generating, Set.NonGenerating] at *,
        apply classical.by_contradiction, intro F,
        apply HG,
        intro x,
        apply classical.by_contradiction, intro F',
        apply F,
        existsi x,
        intros g Hg,
        apply F',
        existsi g,
        exact Hg
      }
    end

-- Prime set generated by a set of elements
def GenPrime {A : Alg.{ℓ}} (gen : Set A) : Set A
 := λ y, ∃ x, A.Divides y x ∧ gen x

def GenPrime.Prime {A : Alg.{ℓ}} (gen : Set A)
  : (GenPrime gen).Prime
 := begin
      intros x₁ x₂ x₃ Jx Px₃,
      { cases Px₃ with x Hx,
        cases Hx with Dx₃x Gx,
        apply Dx₃x,
        { intros x₂' Jx',
          apply or.inr,
          apply A.assoc Jx Jx', intro a₁,
          apply A.assoc a₁.J₁ (A.comm a₁.J₂), intro a₂,
          existsi x,
          refine and.intro _ Gx,
          intros P C₁ C₂, exact C₁ a₂.J₂,
        },
        { intro E, subst E,
          apply or.inl,
          existsi x₃,
          exact and.intro (λ P C₁ C₂, C₁ Jx) Gx
        }
      }
    end

def GenPrime.mem {A : Alg.{ℓ}} (gen : Set A)
  : gen ⊆ (GenPrime gen)
 := begin
      intros x Gx,
      existsi x,
      exact and.intro (λ P C₁ C₂, C₂ rfl) Gx,
    end

def GenPrime.nonempty {A : Alg.{ℓ}} {gen : Set A} (gen_notempty : gen ≠ ∅)
  : GenPrime gen ≠ ∅
 := begin
      intro H,
      apply gen_notempty,
      apply funext, intro x,
      apply iff.to_eq,
      apply iff.intro,
      { intro G,
        rw H.symm,
        apply GenPrime.mem,
        assumption
      },
      { exact false.elim }
    end

-- Prime set generated by an element
def Alg.GenPrime₁ (A : Alg.{ℓ}) (x : A.τ) : Set A
 := GenPrime (eq x)

def GenPrime₁.Prime {A : Alg.{ℓ}} (x : A.τ)
  : (A.GenPrime₁ x).Prime
 := @GenPrime.Prime A (eq x)

def GenPrime₁.nonempty {A : Alg.{ℓ}} (x : A.τ)
  : A.GenPrime₁ x ≠ ∅
 := GenPrime.nonempty (λ H, cast (congr_fun H x) rfl)

def GenPrime₁.mem {A : Alg.{ℓ}} (x : A.τ)
  : x ∈ (A.GenPrime₁ x)
:= GenPrime.mem (eq x) rfl


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
def IntersectionIdeal {A : Alg.{ℓ}} {I₁ I₂ : Set A}
    (I₁Ideal : I₁.Ideal)
    (I₂Ideal : I₂.Ideal)
  : (I₁ ∩ I₂).Ideal
 := λ x₁ x₂ x₃ Ix Jx
    , and.intro (I₁Ideal Ix.1 Jx) (I₂Ideal Ix.2 Jx)

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
