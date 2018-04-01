/- Localization
 -
 -/
import .basic
import .option
import .prod
import .rel
import .primeSpec
import ..extralib

namespace Sep
universes ℓ

namespace Localization

structure Mon (A : Alg.{ℓ})
  : Type.{ℓ}
 := (supp : list A.τ)
    (e : {a // a ∈ supp} → ℤ)

def Mon.zero (A : Alg.{ℓ})
  : Mon A
 := { supp := []
    , e := λ a, 0
    }

def Mon.single {A : Alg.{ℓ}} (a : A.τ)
  : Mon A
 := { supp := [a]
    , e := λ a', 1
    }

def Mon.opt_single {A : Alg.{ℓ}} (a : option A.τ)
 := match a with
      | some a' := Mon.single a'
      | none := Mon.zero A
    end

noncomputable def Mon.fn {A : Alg.{ℓ}}
    (M : Mon A) (a : A.τ)
  : ℤ
 := match classical.prop_decidable (a ∈ M.supp) with
      | (is_true H) := M.e { val := a, property := H }
      | (is_false H) := 0
    end

def recip {A : Alg.{ℓ}}
    (aa : list A.τ)
  : Mon A
 := { supp := aa
    , e := λ a, - 1
    }

noncomputable def add {A : Alg.{ℓ}}
    (M₁ M₂ : Mon A)
  : Mon A
 := { supp := list.append M₁.supp M₂.supp
    , e := λ a, M₁.fn a + M₂.fn a
    }

noncomputable instance Mon.has_add {A : Alg.{ℓ}} : has_add (Mon A)
 := { add := add }

def linear {A : Alg.{ℓ}}
    (M₁ M₂ : Mon A) (a : A.τ)
  : Mon.fn (add M₁ M₂) a = Mon.fn M₁ a + Mon.fn M₂ a
 := sorry

inductive Mon.simpl {A : Alg.{ℓ}}
  : Mon A → Mon A → Prop
| refl : ∀ s, Mon.simpl s s
| step  : ∀ (a₁ a₂ a₃ : A.τ) (r s : Mon A)
            (J : A.join a₁ a₂ a₃)
            (Hrs : Mon.simpl (Mon.single a₃ + r) s)
         , Mon.simpl (Mon.single a₁ + Mon.single a₁ + r)
                     s

def Mon.simpl.trans {A : Alg.{ℓ}}
    {m₁ m₂ m₃ : Mon A}
  : Mon.simpl m₁ m₂ → Mon.simpl m₂ m₃ → Mon.simpl m₁ m₃
 := begin
      intros H₁₂ H₂₃,
      induction H₁₂,
      { exact H₂₃ },
      { apply Mon.simpl.step _ _ _ _ _ J (ih_1 H₂₃),
      }
    end

def Mon.join (A : Alg.{ℓ})
  : Mon A → Mon A → Mon A → Prop
 := λ x₁ x₂ x₃
    , ∃ (x₃' : Mon A)
      , (∀ a, x₁.fn a + x₂.fn a = x₃'.fn a)
      ∧ Mon.simpl x₃' x₃

def MonAlg (A : Alg.{ℓ})
  : Alg.{ℓ}
 := { τ := Mon A
    , join := Mon.join A
    , comm
       := begin
            -- intros x₁ x₂ x₃ Jx,
            -- intro a,
            -- rw (Jx a).symm,
            -- simp
            exact sorry
          end
    , assoc
       := begin
            -- intros x₁ x₂ x₃ x₁₂ x₁₂₃ J₁₂ J₁₂₃,
            -- intros P C, apply C ; clear C P,
            -- refine { x := Mon.add x₂ x₃, J₁ := _, J₂ := _ },
            -- { intro a, rw Mon.fn.linear },
            -- { intro a,
            --   rw (J₁₂₃ a).symm,
            --   rw (J₁₂ a).symm,
            --   rw Mon.fn.linear,
            --   simp
            -- }
            exact sorry
          end
    }


def FormalLocal {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : Alg.{ℓ}
 := Alg.Prod A.Opt (MonAlg SJC.Alg)

inductive hide {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
  : Rel (FormalLocal SJC) (FormalLocal SJC)
| refl : ∀ m, hide m m
| hide : ∀ (s₁ : SJC.Alg.τ)
           (s₂ : (MonAlg SJC.Alg).τ)
         , hide
            (some s₁.val, s₂)
            (none, add (Mon.single s₁) s₂)

def hide.by_cases {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {m₁ m₂ : (FormalLocal SJC).τ}
    (H : hide m₁ m₂)
  : m₁ = m₂
    ∨ ∃ (s₁ : SJC.Alg.τ) (s₂ : (MonAlg SJC.Alg).τ)
      , m₁ = (some s₁.val, s₂)
      ∧ m₂ = (none, add (Mon.single s₁) s₂)
 := begin
      cases H,
      { exact or.inl rfl },
      { apply or.inr,
        existsi s₁, existsi s₂,
        exact and.intro rfl rfl
      }
    end

inductive unhide {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
  : Rel (FormalLocal SJC) (FormalLocal SJC)
| refl : ∀ m, unhide m m
| unhide : ∀ (x₁ x₃ : A.Opt.τ) (s₂ : SJC.Alg.τ)
             (s : (MonAlg SJC.Alg).τ)
             (J : A.Opt.join x₁ (some s₂.val) x₃)
           , unhide
              (x₁, add (Mon.single s₂) s)
              (x₃, s)

def unhide.by_cases {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {m₁ m₂ : (FormalLocal SJC).τ}
    (H : unhide m₁ m₂)
  : m₁ = m₂
    ∨ ∃ (x₁ x₃ : A.Opt.τ) (s₂ : SJC.Alg.τ)
        (s : (MonAlg SJC.Alg).τ)
      , A.Opt.join x₁ (some s₂.val) x₃
        ∧ m₁ = (x₁, add (Mon.single s₂) s)
        ∧ m₂ = (x₃, s)
 := begin
      cases H,
      { exact or.inl rfl },
      { apply or.inr,
        existsi x₁, existsi x₃, existsi s₂, existsi s,
        apply and.intro J,
        exact and.intro rfl rfl
      }
    end

def hide.unhide {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x y : (FormalLocal SJC).τ}
    (H : hide x y)
  : unhide y x
 := begin
      cases H,
      { apply unhide.refl },
      { apply unhide.unhide, constructor }
    end

def join {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
  : (FormalLocal SJC).τ → (FormalLocal SJC).τ → (FormalLocal SJC).τ → Prop
 := λ x₁ x₂ z₃
    , ∃ y₁ y₂ y₃
      , (FormalLocal SJC).join y₁ y₂ y₃
      ∧ hide x₁ y₁
      ∧ hide x₂ y₂
      ∧ unhide y₃ z₃

def join.comm {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ x₃ : (FormalLocal SJC).τ}
    (J : join x₁ x₂ x₃)
  : join x₂ x₁ x₃
 := sorry

def ident {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
  : (FormalLocal SJC).τ
 := (none, Mon.zero SJC.Alg)

def ident_left {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x : (FormalLocal SJC).τ}
  : join ident x x
 := sorry


def equiv {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
  : (FormalLocal SJC).τ → (FormalLocal SJC).τ → Prop
 := λ m₁ m₂
    , ∃ n x
      , join n m₁ x ∧ join n m₂ x

def equiv.refl {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    (x : (FormalLocal SJC).τ)
  : equiv x x
 := begin
      existsi ident,
      existsi x,
      exact and.intro ident_left ident_left
    end

def equiv.symm {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ : (FormalLocal SJC).τ}
    (E : equiv x₁ x₂)
  : equiv x₂ x₁
 := begin
      cases E with n E, cases E with x E,
      cases E with J₁ J₂,
      existsi n, existsi x,
      apply and.intro,
      repeat { assumption }
    end

def equiv.trans {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ x₃ : (FormalLocal SJC).τ}
    (E₁₂ : equiv x₁ x₂) (E₂₃ : equiv x₂ x₃)
  : equiv x₁ x₃
 := begin
      cases E₁₂ with n₁₂ E₁₂,
      cases E₁₂ with x₁₂ J₁₂,
      cases J₁₂ with J₁₂₁ J₁₂₂,
      cases E₂₃ with n₂₃ E₂₃,
      cases E₂₃ with x₂₃ J₂₃,
      cases J₂₃ with J₂₃₂ J₂₃₃,
      exact sorry
    end

def join.equiv {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ x₃ z₁ z₂ z₃ : (FormalLocal SJC).τ}
    (Jx : join x₁ x₂ x₃)
    (E₁ : equiv x₁ z₁)
    (E₂ : equiv x₂ z₂)
    (E₃ : equiv x₃ z₃)
  : join z₁ z₂ z₃
 := sorry

instance equiv_setoid {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : setoid (FormalLocal SJC).τ
 := { r := equiv
    , iseqv := begin
                 apply and.intro equiv.refl,
                 apply and.intro,
                 { apply equiv.symm },
                 { apply equiv.trans }
               end
    }


def τ {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : Type.{ℓ}
 := quot (@equiv _ _ SJC)

def local_join {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : τ SJC → τ SJC → τ SJC → Prop
 := quotient.lift₃
      join
      (λ x₁ x₂ x₃ z₁ z₂ z₃ E₁ E₂ E₃
       , iff.to_eq
          (iff.intro
            (λ Jx, join.equiv Jx E₁ E₂ E₃)
            (λ Jx, join.equiv Jx E₁.symm E₂.symm E₃.symm)))

end Localization

def Set.JoinClosed.Localize {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : Alg.{ℓ}
 := { τ := {x : Localization.τ SJC // ∃ a f, x = ⟦ (some a, f) ⟧}
    , join := λ x₁ x₂ x₃, Localization.local_join SJC x₁ x₂ x₃
    , comm := sorry
    , assoc := sorry
    }

def PrimeLocalize {A : Alg.{ℓ}} (p : A.PrimeSpec)
  : Alg.{ℓ}
 := p.prime.Complement_JoinClosed.Localize

def PrimeLocalize.eq {A : Alg.{ℓ}} {p : A.PrimeSpec}
    (a₁ a₂ : (PrimeLocalize p).τ)
    (H : a₁.val = a₂.val)
  : a₁ = a₂
 := begin
      cases a₁ with a₁ H₁,
      cases a₂ with a₂ H₂,
      simp at H, subst H
    end

def Alg.localize_at (A : Alg.{ℓ})
    (q : A.PrimeSpec)
    (a : A.τ)
    (ff : list q.prime.Complement_JoinClosed.Alg.τ)
  : (PrimeLocalize q).τ
 := { val := ⟦ (some a, Localization.recip ff) ⟧
    , property := exists.intro _ (exists.intro _ (quot.sound (Localization.equiv.refl _)))
    }

end Sep
