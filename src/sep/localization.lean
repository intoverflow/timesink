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

def Mon.equiv {A : Alg.{ℓ}}
    (M₁ M₂ : Mon A)
  : Prop
 := ∀ a, M₁.fn a = M₂.fn a

def Mon.equiv.refl {A : Alg.{ℓ}}
    (M : Mon A)
  : Mon.equiv M M
 := λ a, rfl

def Mon.equiv.trans {A : Alg.{ℓ}}
    {M₁ M₂ M₃ : Mon A}
    (E₁ : Mon.equiv M₁ M₂) (E₂ : Mon.equiv M₂ M₃)
  : Mon.equiv M₁ M₃
 := λ a, eq.trans (E₁ a) (E₂ a)

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
| equiv : ∀ s₁ s₂, Mon.equiv s₁ s₂ → Mon.simpl s₁ s₂
| step  : ∀ (s₁ s₂ : Mon A) (a₁ a₂ a₃ : A.τ) (r : Mon A)
            (J : A.join a₁ a₂ a₃)
            (Hls : Mon.simpl s₁ (Mon.single a₁ + Mon.single a₂ + r))
            (Hrs : Mon.simpl (Mon.single a₃ + r) s₂)
         , Mon.simpl s₁ s₂

def Mon.simpl.along_equiv {A : Alg.{ℓ}}
    {s₁ s₂ s : Mon A}
    (E : Mon.equiv s₁ s₂)
    (S : Mon.simpl s₂ s)
  : Mon.simpl s₁ s
 := begin
      induction S with _ _ S,
      { apply Mon.simpl.equiv,
        apply Mon.equiv.trans,
        repeat { assumption }
      },
      { exact Mon.simpl.step _ _ _ _ _ _ J (ih_1 E) Hrs }
    end

def Mon.simpl.refl {A : Alg.{ℓ}}
    (s : Mon A)
  : Mon.simpl s s
 := Mon.simpl.equiv _ _ (Mon.equiv.refl s)

def Mon.simpl.trans {A : Alg.{ℓ}}
    {m₁ m₂ m₃ : Mon A}
  : Mon.simpl m₁ m₂ → Mon.simpl m₂ m₃ → Mon.simpl m₁ m₃
 := begin
      intros H₁₂ H₂₃,
      induction H₁₂ with _ _ H₁₂,
      { exact Mon.simpl.along_equiv H₁₂ H₂₃ },
      { exact Mon.simpl.step _ _ _ _ _ _ J Hls (ih_2 H₂₃) }
    end

def Mon.simpl.linear {A : Alg.{ℓ}}
    {s s₁ s₂ : Mon A}
    (H : Mon.simpl s₁ s₂)
  : Mon.simpl (s + s₁) (s + s₂)
 := sorry

def Mon.simpl.add_assoc {A : Alg.{ℓ}}
    {s₁ s₂ s₃ : Mon A}
  : Mon.simpl (s₁ + (s₂ + s₃)) ((s₁ + s₂) + s₃)
 := sorry

def Mon.join (A : Alg.{ℓ})
  : Mon A → Mon A → Mon A → Prop
 := λ x₁ x₂ x₃
    , ∃ (x₃' : Mon A)
      , (∀ a, x₁.fn a + x₂.fn a = x₃'.fn a)
      ∧ Mon.simpl x₃' x₃

-- def Mon.join.pre_simpl {A : Alg.{ℓ}}
--     {x₁ x₂ x₃ x₁' x₂' x₃' : Mon A}
--     (J : ∀ a, x₁'.fn a + x₂'.fn a = x₃'.fn a)
--     (S₁ : Mon.simpl x₁ x₁')
--     (S₂ : Mon.simpl x₂ x₂')
--     (S₃ : Mon.simpl x₃' x₃)
--   : Mon.join A x₁ x₂ x₃
--  := sorry

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
| none : ∀ s, hide (none, s) (none, s)
| refl : ∀ x s (Hx : ¬ x ∈ S), hide (some x, s) (some x, s)
| hide : ∀ (s₁ : SJC.Alg.τ)
           (s₂ : (MonAlg SJC.Alg).τ)
         , hide
            (some s₁.val, s₂)
            (none, add (Mon.single s₁) s₂)

def do_hide {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    (x : (FormalLocal SJC).τ)
  : ∃ x', hide x x'
 := begin
      cases x with x s,
      cases x with x,
      { existsi (none, s), apply hide.none },
      { cases classical.em (x ∈ S) with Q Q,
        { let x' : (Set.JoinClosed.Alg SJC).τ
                 := { val := x, property := Q },
          existsi (none, add (Mon.single x') s),
          exact hide.hide x' s
        },
        { existsi (some x, s),
          apply hide.refl _ _ Q
        }
      }
    end

def hide.by_cases {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {m₁ m₂ : (FormalLocal SJC).τ}
    (H : hide m₁ m₂)
  : (m₁.fst = none ∧ m₂.fst = none ∧ m₁.snd = m₂.snd)
    ∨ (∃ x (s : (MonAlg SJC.Alg).τ)
       , (¬ x ∈ S) ∧ m₁ = (some x, s) ∧ m₂ = (some x, s))
    ∨ (∃ (s₁ : SJC.Alg.τ) (s₂ : (MonAlg SJC.Alg).τ)
       , m₁ = (some s₁.val, s₂)
       ∧ m₂ = (none, add (Mon.single s₁) s₂))
 := begin
      cases H,
      { apply or.inl, simp },
      { apply or.inr, apply or.inl,
        existsi x, existsi s,
        apply and.intro Hx,
        simp
      },
      { apply or.inr, apply or.inr,
        existsi s₁, existsi s₂,
        simp
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

-- def hide.unhide {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
--     {x y : (FormalLocal SJC).τ}
--     (H : hide x y)
--   : unhide y x
--  := begin
--       cases H,
--       { apply unhide.refl },
--       { apply unhide.unhide, constructor }
--     end

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
      cases do_hide x with x' Hx',
      existsi ident, existsi x', existsi x',
      apply and.intro,
      { constructor,
        { constructor },
        { existsi x'.snd,
          apply and.intro,
          { intro a, exact sorry -- is true
          },
          apply Mon.simpl.refl
        }
      },
      apply and.intro,
      { apply hide.none },
      apply and.intro,
      { exact Hx' },
      { cases Hx',
        { apply unhide.refl },
        { apply unhide.refl },
        { apply unhide.unhide,
          constructor
        }
      }
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
      --
      exact sorry
    end

def join_along_hide {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x y z x₁ x₂ z₁: (FormalLocal SJC).τ}
    (H₁ : hide x x₁)
    (H₂ : hide x x₂)
    (UH : unhide z₁ z)
    (J : (FormalLocal SJC).join x₁ y z₁)
  : ∃ z₂, (FormalLocal SJC).join x₂ y z₂ ∧ unhide z₂ z
 := begin
      cases H₁ with H₁ ; clear H₁,
      { cases H₂ with H₂ ; clear H₂,
        existsi z₁, exact and.intro J UH,
      },
      { cases H₂ with H₂ ; clear H₂,
        { existsi z₁, exact and.intro J UH },
        { cases UH with UH w₁ w₃ w₂ ws Jw ; clear UH,
          { existsi (y.fst, add (Mon.single s₁) z.snd),
            apply and.intro,
            { apply and.intro,
              { constructor },
              cases J with J₁ J₂,
              cases J₂ with ω J₂,
              existsi (add (Mon.single s₁) ω),
              simp at *,
              apply and.intro,
              { exact Mon.simpl.linear J₂.1 },
              { intro a,
                have E : Mon.fn (add (Mon.single s₁) s) a
                          = Mon.fn (Mon.single s₁) a + Mon.fn s a, from
                  begin apply add.linear end,
                rw E, clear E,
                have E : Mon.fn (add (Mon.single s₁) ω) a
                          = Mon.fn (Mon.single s₁) a + Mon.fn ω a, from
                  begin apply add.linear end,
                rw E, clear E,
                rw (J₂.2 a).symm,
                simp
              }
            },
            { cases z with z sz,
              apply unhide.unhide,
              exact (Alg.Opt A).comm J.1
            }
          },
          { apply (Alg.Opt A).assoc ((Alg.Opt A).comm J.1) Jw,
            intro a, cases a with a Ha₁ Ha₂,
            cases Ha₁ with _ _ a Ja,
            have Ha : a ∈ S, from
              begin
                apply SJC _ _ _ Ja s₁.property w₂.property,
              end,
            let a' : (Set.JoinClosed.Alg SJC).τ
                  := { val := a, property := Ha },
            refine exists.intro (y.fst, add (Mon.single a') ws) _,
            apply and.intro,
            { apply and.intro,
              { constructor },
              { cases J with J₁ J₂,
                cases J₂ with ω J₂,
                existsi (add (Mon.single s₁) ω),
                simp at *,
                apply and.intro,
                { refine Mon.simpl.trans (Mon.simpl.linear J₂.1) _,
                  refine simpl.step _ _ s₁ w₂ a' ws Ja _ (Mon.simpl.refl _),
                  exact Mon.simpl.add_assoc
                },
                { intro a,
                  have E : Mon.fn (add (Mon.single s₁) s) a
                            = Mon.fn (Mon.single s₁) a + Mon.fn s a, from
                    begin apply add.linear end,
                  rw E, clear E,
                  have E : Mon.fn (add (Mon.single s₁) ω) a
                            = Mon.fn (Mon.single s₁) a + Mon.fn ω a, from
                    begin apply add.linear end,
                  rw E, clear E,
                  rw (J₂.2 a).symm,
                  simp
                }
              }
            },
            { apply unhide.unhide,
              exact Ha₂
            }
          }
        }
      },
      { cases H₂.by_cases with H₂' H₂',
        { cases H₂' with E H₂', injection E
        },
        { cases H₂' with H₂' H₂',
          { cases H₂' with x' H₂',
            cases H₂' with s' H₂',
            cases H₂' with F H₂',
            cases H₂' with E H₂',
            injection E with E₁ E₂, clear E E₂,
            injection E₁ with E₁', clear E₁,
            subst E₁',
            exact false.elim (F s₁.property)
          },
          { cases H₂' with a₁ H₂',
            cases H₂' with a₂ H₂',
            cases H₂' with E₁ E₂,
            subst E₂,
            injection E₁ with E₁₁ E₁₂, clear E₁,
            subst E₁₂,
            injection E₁₁ with E₁₁', clear E₁₁,
            cases a₁ with a₁ Hs₁',
            simp at E₁₁', subst E₁₁',
            cases s₁ with s₁ Hs₁,
            existsi z₁,
            exact and.intro J UH
          }
        }
      }
    end

def join.equiv₁ {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ x₃ z₁ : (FormalLocal SJC).τ}
    (J : join x₁ x₂ x₃)
    (E₁ : equiv x₁ z₁)
  : join z₁ x₂ x₃
 := begin
      cases E₁ with n₁ E₁, cases E₁ with w E₁, cases E₁ with Jx Jz,
      cases J with x₁₁ J, cases J with x₂' J, cases J with x₃' J,
      cases J with J Hx, cases Hx with Hx₁₁ Hx, cases Hx with Hx₂ UHx₃',
      --
      cases Jx with n₁' Jx, cases Jx with x₁₂ Jx, cases Jx with z₁₁ Jx,
      cases Jx with Jz₁₁ Hx, cases Hx with E Hx, cases Hx with Hx₁₂ UHz₁₁w,
      cases E, clear E,
      --
      have J_along := join_along_hide Hx₁₁ Hx₁₂ UHx₃' J,
      cases J_along with x₃'' J_along,
      cases J_along with J' UHx₃'',
      clear UHx₃' J x₃' Hx₁₁ x₁₁,
      --
      cases Jz with n₁' Jz, cases Jz with z₁' Jz, cases Jz with z₁₂ Jz,
      cases Jz with Jz₁₂ Hz, cases Hz with E Hz, cases Hz with Hz UHz₁₂w,
      cases E, clear E,
      --
      cases Jz₁₁ with E₁ Jz₁₁,
      cases Jz₁₂ with E₂ Jz₁₂,
      have E₁₁ := Alg.Opt.join_none_l E₁, clear E₁,
      have E₁₂ := Alg.Opt.join_none_l E₂, clear E₂,
      cases x₁₂ with x₁₂ sx₁₂,
      cases z₁' with z₁' sz₁',
      cases z₁₁ with z₁₁ s₁₁,
      cases z₁₂ with z₁₂ s₁₂,
      simp at *,
      subst E₁₁, subst E₁₂,
      -- cases x₁ with x₁ sx₁,
      -- cases z₁ with z₁ sz₁,
      -- cases w with w s,
      -- cases x₁₁ with x₁₁ sx₁₁,
      --
      --
      exact sorry,
      -- existsi (w, add s n₁),
      -- existsi x₂', existsi x₃'',
      -- refine and.intro _ (and.intro _ (and.intro Hx₂ UHx₃'')),
    end

def join.equiv₃ {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ x₃ z₃ : (FormalLocal SJC).τ}
    (Jx : join x₁ x₂ x₃)
    (E₃ : equiv x₃ z₃)
  : join x₁ x₂ z₃
 := sorry

def join.equiv {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ x₃ z₁ z₂ z₃ : (FormalLocal SJC).τ}
    (Jx : join x₁ x₂ x₃)
    (E₁ : equiv x₁ z₁)
    (E₂ : equiv x₂ z₂)
    (E₃ : equiv x₃ z₃)
  : join z₁ z₂ z₃
 := begin
      have Q₁ := join.equiv₁ Jx E₁,
      have Q₂ := join.comm (join.equiv₁ (join.comm Q₁) E₂),
      exact join.equiv₃ Q₂ E₃
    end

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
