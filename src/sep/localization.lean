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

noncomputable def sub {A : Alg.{ℓ}}
    (M₁ M₂ : Mon A)
  : Mon A
 := { supp := list.append M₁.supp M₂.supp
    , e := λ a, M₁.fn a - M₂.fn a
    }

noncomputable instance Mon.has_sub {A : Alg.{ℓ}} : has_sub (Mon A)
 := { sub := sub }

def add.linear {A : Alg.{ℓ}}
    (M₁ M₂ : Mon A) (a : A.τ)
  : Mon.fn (M₁ + M₂) a = Mon.fn M₁ a + Mon.fn M₂ a
 := sorry

def sub.linear {A : Alg.{ℓ}}
    (M₁ M₂ : Mon A) (a : A.τ)
  : Mon.fn (M₁ - M₂) a = Mon.fn M₁ a - Mon.fn M₂ a
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

def Mon.join.pre_simpl {A : Alg.{ℓ}}
    {x₁ x₂ x₃ x₁' x₂' x₃' : Mon A}
    (J : ∀ a, x₁'.fn a + x₂'.fn a = x₃'.fn a)
    (S₁ : Mon.simpl x₁ x₁')
    (S₂ : Mon.simpl x₂ x₂')
    (S₃ : Mon.simpl x₃' x₃)
  : Mon.join A x₁ x₂ x₃
 := sorry

def MonAlg (A : Alg.{ℓ})
  : Alg.{ℓ}
 := { τ := Mon A
    , join := Mon.join A
    , comm
       := begin
            intros x₁ x₂ x₃ Jx,
            cases Jx with x₃' H,
            existsi x₃',
            refine and.intro _ H.2,
            intro a,
            rw (H.1 a).symm,
            simp
          end
    , assoc
       := begin
            intros x₁ x₂ x₃ x₁₂ x₁₂₃ J₁₂ J₁₂₃,
            cases J₁₂ with x₁₂' J₁₂,
            cases J₁₂ with E₁₂ S₁₂,
            cases J₁₂₃ with x₁₂₃' J₁₂₃,
            cases J₁₂₃ with E₁₂₃ S₁₂₃,
            intros P C, apply C ; clear C P,
            refine { x := x₂ + x₃ + x₁₂ - x₁₂', J₁ := _, J₂ := _ },
            { existsi x₂ + x₃,
              apply and.intro,
              { intro a, exact (add.linear _ _ a).symm },
              { exact sorry -- true by S₁₂
              }
            },
            { existsi x₁₂₃',
              refine and.intro _ S₁₂₃,
              intro a,
              have E : Mon.fn x₁ a + Mon.fn (x₂ + x₃ + x₁₂ - x₁₂') a
                        = Mon.fn x₁ a + Mon.fn x₂ a + Mon.fn (x₃ + x₁₂ - x₁₂') a, from
                begin
                  exact sorry
                end,
              rw E, clear E,
              rw E₁₂ a,
              have E : Mon.fn x₁₂' a + Mon.fn (x₃ + x₁₂ - x₁₂') a
                        = Mon.fn x₃ a + Mon.fn x₁₂ a, from
                begin
                  exact sorry
                end,
              rw E, clear E,
              rw (E₁₂₃ a).symm,
              simp
            }
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
 := begin
      cases J with y₁ J,
      cases J with y₂ J,
      cases J with y₃ J,
      cases J with J H,
      cases H with H₁ H,
      cases H with H₂ H₃,
      existsi y₂, existsi y₁, existsi y₃,
      apply and.intro ((FormalLocal SJC).comm J),
      apply and.intro H₂,
      apply and.intro H₁,
      exact H₃
    end

def ident {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
  : (FormalLocal SJC).τ
 := (none, Mon.zero SJC.Alg)

def ident_left {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x : (FormalLocal SJC).τ}
  : join ident x x
 := begin
      existsi ident, existsi x, existsi x,
      apply and.intro,
      { constructor,
        { constructor },
        { existsi x.snd,
          apply and.intro,
          { intro a, exact sorry -- is true
          },
          apply Mon.simpl.refl
        }
      },
      apply and.intro,
      { apply hide.refl },
      apply and.intro,
      { apply hide.refl },
      { apply unhide.refl }
    end


def equiv {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
  : (FormalLocal SJC).τ → (FormalLocal SJC).τ → Prop
 := λ m₁ m₂
    , ∃ n x
      , join (none, n) m₁ x ∧ join (none, n) m₂ x

def equiv.refl {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    (x : (FormalLocal SJC).τ)
  : equiv x x
 := begin
      existsi Mon.zero SJC.Alg,
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
      cases E₁₂ with n₁₂ E₁₂, cases E₁₂ with x₁₂ J₁₂, cases J₁₂ with J₁₂₁ J₁₂₂,
      --
      cases J₁₂₁ with n₁₁₂' J₁₂₁, cases J₁₂₁ with x₁' J₁₂₁, cases J₁₂₁ with x₁₁₂' J₁₂₁,
      cases J₁₂₁ with J₁₂₁ H, cases H with H H₁₂₁, cases H₁₂₁ with H₁₂₁ UH₁₂₁,
      cases H, clear H,
      --
      cases J₁₂₂ with n₂₁₂' J₁₂₂, cases J₁₂₂ with x₂' J₁₂₂, cases J₁₂₂ with x₂₁₂' J₁₂₂,
      cases J₁₂₂ with J₁₂₂ H, cases H with H H₁₂₂, cases H₁₂₂ with H₁₂₂ UH₁₂₂,
      cases H, clear H,
      --
      cases E₂₃ with n₂₃ E₂₃, cases E₂₃ with x₂₃ J₂₃, cases J₂₃ with J₂₃₂ J₂₃₃,
      --
      cases J₂₃₂ with n₁₂₃' J₂₃₂, cases J₂₃₂ with x₂'' J₂₃₂, cases J₂₃₂ with x₁₂₃' J₂₃₂,
      cases J₂₃₂ with J₂₃₂ H, cases H with H H₂₃₂, cases H₂₃₂ with H₂₃₂ UH₂₃₂,
      cases H, clear H,
      --
      cases J₂₃₃ with n₂₂₃' J₂₃₃, cases J₂₃₃ with x₃' J₂₃₃, cases J₂₃₃ with x₂₂₃' J₂₃₃,
      cases J₂₃₃ with J₂₃₃ H, cases H with H H₂₃₃, cases H, clear H,
      cases H₂₃₃ with H₂₃₃ UH₂₃₃,
      --
      existsi (add n₁₂ n₂₃),
      --
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

def Set.AvoidingPrime {A : Alg.{ℓ}} (S : Set A)
  : A.PrimeSpec
 := { set := set.sUnion (λ (p : Set A), p.Prime ∧ p.Integral ∧ S ∩ p = ∅)
    , prime := begin apply Prime.Union, intros p H, exact H.1 end
    , integral := begin apply Integral.Union, intros p H, exact H.2.1 end
    }

def Set.Localize {A : Alg.{ℓ}} (S : Set A)
  : Alg.{ℓ}
 := PrimeLocalize S.AvoidingPrime

noncomputable def Set.local_represent {A : Alg.{ℓ}} (S : Set A)
    (af : S.Localize.τ)
  : {xf : A.τ × (Localization.MonAlg _).τ
       // af.val = ⟦(some xf.1, xf.2)⟧}
 := let x := classical.indefinite_description _ af.property
 in let f := classical.indefinite_description _ x.property
    in { val := (x, f), property := f.property }


end Sep
