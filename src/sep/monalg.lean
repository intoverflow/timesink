/- Monomial algebras
 -
 -/
import .basic
import .option
import .prod
import .rel
import .primeSpec
import ..extralib

namespace Sep
universes ℓ ℓ₁ ℓ₂

namespace MonAlg

structure Mon (A : Type.{ℓ})
  : Type.{ℓ}
 := (supp : list A)
    (e : {a // a ∈ supp} → ℤ)

def Mon.subtype {A : Type.{ℓ}} {P₁ P₂ : set A}
    (m : Mon {a // P₁ a})
    (H : ∀ a, P₁ a → P₂ a)
  : Mon {a // P₂ a}
 := { supp := list.map
              (λ (a : {a // P₁ a})
                , { val := a.val
                  , property := H a.val a.property
                  })
              m.supp
    , e := λ z, let Q₁ : P₁ z.val.val
                      := begin
                          cases m with ms me,
                          cases z with z Hz,
                          induction ms with s ss,
                          { exact false.elim Hz },
                          cases Hz with Hz Hz,
                          { refine cast _ s.property,
                            cases z with z Hz',
                            injection Hz with E,
                            subst E
                          },
                          { refine ih_1
                                    (λ w, me { val := w.val, property := or.inr w.property })
                                    Hz
                          }
                        end
            in let z' : { a // P₁ a }
                      := { val := z.val.val, property := Q₁ }
            in let Q₂ : z' ∈ m.supp
                      := begin
                          cases m with ms me,
                          cases z with z Hz,
                          induction ms with s ss,
                          { exact false.elim Hz },
                          cases Hz with Hz Hz,
                          { cases z with z Hz',
                            cases s with s Hs,
                            injection Hz with E,
                            subst E,
                            exact or.inl rfl
                          },
                          { apply or.inr,
                            dsimp at ih_1,
                            apply ih_1 (λ w, me { val := w.val, property := or.inr w.property }) _
                          }
                        end
            in m.e { val := z', property := Q₂ }
    }

def Mon.zero (A : Type.{ℓ})
  : Mon A
 := { supp := []
    , e := λ a, 0
    }

def Mon.single {A : Type.{ℓ}} (a : A)
  : Mon A
 := { supp := [a]
    , e := λ a', 1
    }

noncomputable def Mon.fn {A : Type.{ℓ}}
    (M : Mon A) (a : A)
  : ℤ
 := match classical.prop_decidable (a ∈ M.supp) with
      | (is_true H) := M.e { val := a, property := H }
      | (is_false H) := 0
    end

def Mon.fn.zero {A : Type.{ℓ}}
    {a : A}
  : Mon.fn (Mon.zero A) a = 0
 := begin
      simp [Mon.fn],
      cases classical.prop_decidable (a ∈ (Mon.zero A).supp) with Q Q,
      { apply rfl },
      { cases Q }
    end

def Mon.equiv {A : Type.{ℓ}}
    (M₁ M₂ : Mon A)
  : Prop
 := ∀ a, M₁.fn a = M₂.fn a

def Mon.equiv.refl {A : Type.{ℓ}}
    (M : Mon A)
  : Mon.equiv M M
 := λ a, rfl

def Mon.equiv.symm {A : Type.{ℓ}}
    {M₁ M₂ : Mon A}
    (E : Mon.equiv M₁ M₂)
  : Mon.equiv M₂ M₁
 := begin intro a, rw E a end

def Mon.equiv.trans {A : Type.{ℓ}}
    {M₁ M₂ M₃ : Mon A}
    (E₁ : Mon.equiv M₁ M₂) (E₂ : Mon.equiv M₂ M₃)
  : Mon.equiv M₁ M₃
 := λ a, eq.trans (E₁ a) (E₂ a)

def recip {A : Type.{ℓ}}
    (aa : list A)
  : Mon A
 := { supp := aa
    , e := λ a, - 1
    }

noncomputable def add {A : Type.{ℓ}}
    (M₁ M₂ : Mon A)
  : Mon A
 := { supp := list.append M₁.supp M₂.supp
    , e := λ a, M₁.fn a + M₂.fn a
    }

noncomputable instance Mon.has_add {A : Type.{ℓ}} : has_add (Mon A)
 := { add := add }

noncomputable def sub {A : Type.{ℓ}}
    (M₁ M₂ : Mon A)
  : Mon A
 := { supp := list.append M₁.supp M₂.supp
    , e := λ a, M₁.fn a - M₂.fn a
    }

noncomputable instance Mon.has_sub {A : Type.{ℓ}} : has_sub (Mon A)
 := { sub := sub }

def add.linear {A : Type.{ℓ}}
    (M₁ M₂ : Mon A) (a : A)
  : Mon.fn (M₁ + M₂) a = Mon.fn M₁ a + Mon.fn M₂ a
 := sorry

def sub.linear {A : Type.{ℓ}}
    (M₁ M₂ : Mon A) (a : A)
  : Mon.fn (M₁ - M₂) a = Mon.fn M₁ a - Mon.fn M₂ a
 := sorry

def add.zero_r {A : Type.{ℓ}}
    {M : Mon A}
  : Mon.equiv (M + Mon.zero A) M
 := begin
      intro a,
      rw add.linear,
      rw Mon.fn.zero,
      simp
    end

inductive Mon.simpl_step {A : Alg.{ℓ}}
    : Mon A.τ → Mon A.τ → Prop
| equiv : ∀ m₁ m₂ (E : Mon.equiv m₁ m₂)
          , Mon.simpl_step m₁ m₂
| join : ∀ s₁ s₂ s₃ s
           (J : A.join s₁ s₂ s₃)
         , Mon.simpl_step (Mon.single s₁ + Mon.single s₂ + s)
                          (Mon.single s₃ + s)
| split : ∀ s₁ s₂ s₃ s
            (J : A.join s₁ s₂ s₃)
          , Mon.simpl_step (Mon.single s₃ + s)
                           ((Mon.single s₁ + Mon.single s₂) + s)

inductive Mon.simpl {A : Alg.{ℓ}}
    : Mon A.τ → Mon A.τ → Prop
| refl : ∀ m, Mon.simpl m m
| step : ∀ m₁ m₂ m₃ (S₁₂ : Mon.simpl_step m₁ m₂) (S₂₃ : Mon.simpl m₂ m₃)
         , Mon.simpl m₁ m₃

def Mon.simpl.trans {A : Alg.{ℓ}}
    {m₁ m₂ m₃ : Mon A.τ}
    (H₁₂ : Mon.simpl m₁ m₂) (H₂₃ : Mon.simpl m₂ m₃)
  : Mon.simpl m₁ m₃
 := begin
      induction H₁₂,
      { assumption },
      { exact Mon.simpl.step _ _ _ S₁₂ (ih_1 H₂₃) }
    end

def Mon.simpl.symm {A : Alg.{ℓ}}
    {m₁ m₂ : Mon A.τ}
    (H : Mon.simpl m₁ m₂)
  : Mon.simpl m₂ m₁
 := begin
      induction H,
      { apply Mon.simpl.refl },
      { apply Mon.simpl.trans ih_1, clear ih_1,
        refine Mon.simpl.step _ _ _ _ (Mon.simpl.refl _),
        cases S₁₂,
        { apply Mon.simpl_step.equiv,
          apply E.symm
        },
        { apply Mon.simpl_step.split, assumption },
        { apply Mon.simpl_step.join, assumption }
      }
    end

def Mon.join (A : Alg.{ℓ})
  : Mon A.τ → Mon A.τ → Mon A.τ → Prop
 := λ x₁ x₂ x₃
    , ∃ y₁ y₂ y₃
      , Mon.equiv (y₁ + y₂) y₃
      ∧ Mon.simpl y₁ x₁ ∧ Mon.simpl y₂ x₂ ∧ Mon.simpl x₃ y₃

def Mon.join.assoc {A : Alg.{ℓ}}
    (w₁ w₂ w₃ w₁₂₃ y₁₂ z₁₂ : Mon A.τ)
    (Sy : simpl z₁₂ y₁₂)
    (H : ∃ y₁ y₂ z₃ z₁₂₃
         , (Mon.equiv (y₁ + y₂) y₁₂ ∧ Mon.equiv (z₁₂ + z₃) z₁₂₃)
         ∧ (simpl y₁ w₁ ∧ simpl y₂ w₂ ∧ simpl z₃ w₃ ∧ simpl w₁₂₃ z₁₂₃))
  : ∃ a a₁ a₂ v₁ v₂ v₃ v₁₂₃
    , (Mon.equiv (v₂ + v₃) a₁ ∧ Mon.equiv (v₁ + a₂) v₁₂₃)
    ∧ (simpl a a₁ ∧ simpl a₂ a ∧ simpl v₁ w₁ ∧ simpl v₂ w₂ ∧ simpl v₃ w₃ ∧ simpl w₁₂₃ v₁₂₃)
 := begin
      induction Sy with yv₁₂ yi₁ yi₂ yi₃ ySi₁₂ ySi₂₃ yIH,
      { cases H with e₁ H, cases H with e₂ H, cases H with f₃ H, cases H with f₁₂₃ H,
        cases H with E H, cases E with E₁₂ E₁₂₃,
        cases H with T₁ H, cases H with T₂ H, cases H with T₃ T₁₂₃,
        existsi e₂ + f₃, existsi e₂ + f₃, existsi e₂ + f₃,
        existsi e₁, existsi e₂, existsi f₃, existsi f₁₂₃,
        apply and.intro,
        { apply and.intro (Mon.equiv.refl _),
          intro a,
          rw (E₁₂₃ a).symm,
          repeat { rw add.linear },
          rw (E₁₂ a).symm,
          rw add.linear, simp
        },
        repeat { apply and.intro (Mon.simpl.refl _) },
        repeat { try { apply and.intro }, assumption }
      },
      { apply yIH, clear yIH,
        cases H with e₁ H, cases H with e₂ H, cases H with f₃ H, cases H with f₁₂₃ H,
        cases H with E H, cases E with E₁₂ E₁₂₃,
        cases H with T₁ H, cases H with T₂ H, cases H with T₃ T₁₂₃,
        cases ySi₁₂,
        { existsi e₁, existsi e₂, existsi f₃, existsi f₁₂₃,
          apply and.intro,
          { apply and.intro E₁₂,
            intro a, rw (E₁₂₃ a).symm,
            repeat { rw add.linear },
            rw (E a).symm
          },
          { repeat { try { apply and.intro }, assumption } }
        },
        { existsi e₁, existsi e₂,
          existsi f₃, existsi Mon.single s₃ + (f₁₂₃ - Mon.single s₁ - Mon.single s₂),
          have E : ((Mon.single s₁ + Mon.single s₂) + s) + f₃
                    =  ({supp := list.append ((Mon.single s₁ + Mon.single s₂).supp) (s.supp)
                        , e := λ (a : {a // a ∈ list.append ((Mon.single s₁ + Mon.single s₂).supp) (s.supp)}),
                                  Mon.fn (Mon.single s₁ + Mon.single s₂) ↑a + Mon.fn s ↑a
                        } + f₃) := rfl,
          rw E.symm at E₁₂₃, clear E,
          apply and.intro,
          { apply and.intro E₁₂,
            intro a,
            have E : (Mon.single s₃ + s + f₃)
                      = ({supp := list.append ((Mon.single s₃).supp) (s.supp),
                e := λ (a : {a // a ∈ list.append ((Mon.single s₃).supp) (s.supp)}),
                        Mon.fn (Mon.single s₃) ↑a + Mon.fn s ↑a} +
                f₃) := rfl,
            rw E.symm, clear E,
            repeat { rw add.linear at * },
            repeat { rw sub.linear at * },
            rw (E₁₂₃ a).symm,
            repeat { rw sub.linear at * },
            repeat { rw add.linear at * },
            simp at *
          },
          { repeat { apply and.intro, assumption },
            apply Mon.simpl.trans T₁₂₃,
            refine Mon.simpl.step _ _ _
              (Mon.simpl_step.equiv _ _ _)
              (Mon.simpl.step _ _ _ (Mon.simpl_step.join _ _ _ _ J) (Mon.simpl.refl _)),
            intro a,
            repeat { rw add.linear },
            repeat { rw sub.linear },
            simp
          }
        },
        { existsi e₁, existsi e₂,
          existsi f₃, existsi Mon.single s₁ + Mon.single s₂ + (f₁₂₃ - Mon.single s₃),
          have E : Mon.single s₃ + s + f₃
                    = { supp := list.append ((Mon.single s₃).supp) (s.supp)
                      , e := λ (a : {a // a ∈ list.append ((Mon.single s₃).supp) (s.supp)})
                             , Mon.fn (Mon.single s₃) ↑a + Mon.fn s ↑a
                      } + f₃ := rfl,
          rw E.symm at *, clear E,
          have E : Mon.single s₁ + Mon.single s₂ + s
                    = { supp := list.append ((Mon.single s₁ + Mon.single s₂).supp) (s.supp)
                      , e := λ (a : {a // a ∈ list.append ((Mon.single s₁ + Mon.single s₂).supp) (s.supp)})
                             , Mon.fn (Mon.single s₁ + Mon.single s₂) ↑a + Mon.fn s ↑a
                      } := rfl,
          rw E.symm at *, clear E,
          apply and.intro,
          { apply and.intro E₁₂,
            intro a,
            repeat { rw add.linear },
            repeat { rw sub.linear },
            rw (E₁₂₃ a).symm,
            repeat { rw add.linear },
            simp
          },
          { repeat { apply and.intro, assumption },
            apply Mon.simpl.trans T₁₂₃,
            refine Mon.simpl.step _ _ _
              (Mon.simpl_step.equiv _ _ _)
              (Mon.simpl.step _ _ _ (Mon.simpl_step.split _ _ _ _ J) (Mon.simpl.refl _)),
            intro a,
            repeat { rw add.linear },
            repeat { rw sub.linear },
            simp
          }
        }
      }
    end

def MonAlg (A : Alg.{ℓ})
  : Alg.{ℓ}
 := { τ := Mon A.τ
    , join := Mon.join A
    , comm
       := begin
            intros x₁ x₂ x₃ Jx,
            cases Jx with y₁ Jx, cases Jx with y₂ Jx, cases Jx with y₃ Jx,
            existsi y₂, existsi y₁, existsi y₃,
            cases Jx with E Jx, cases Jx with S₁ Jx, cases Jx with S₂ S₃,
            apply and.intro,
            { intro a, rw add.linear, rw (E a).symm, rw add.linear, simp },
            repeat { try { apply and.intro }, assumption }
          end
    , assoc
       := begin
            intros x₁ x₂ x₃ x₁₂ x₁₂₃ J₁₂ J₁₂₃,
            cases J₁₂ with y₁ J₁₂, cases J₁₂ with y₂ J₁₂, cases J₁₂ with y₁₂ J₁₂,
            cases J₁₂ with E₁₂ J₁₂, cases J₁₂ with T₁ J₁₂, cases J₁₂ with T₂ Ty,
            cases J₁₂₃ with z₁₂ J₁₂₃, cases J₁₂₃ with z₃ J₁₂₃, cases J₁₂₃ with z₁₂₃ J₁₂₃,
            cases J₁₂₃ with E₁₂₃ J₁₂₃, cases J₁₂₃ with Tz J₁₂₃, cases J₁₂₃ with T₃ T₁₂₃,
            --
            have T₁₂ : Mon.simpl z₁₂ y₁₂ := Mon.simpl.trans Tz Ty,
            --
            have Q := Mon.join.assoc x₁ x₂ x₃ x₁₂₃ y₁₂ z₁₂ T₁₂
                        begin
                          existsi y₁, existsi y₂, existsi z₃, existsi z₁₂₃,
                          apply and.intro,
                          repeat { try { apply and.intro }, assumption }
                        end,
            cases Q with a Q, cases Q with a₁ Q, cases Q with a₂ Q,
            cases Q with v₁ Q, cases Q with v₂ Q, cases Q with v₃ Q, cases Q with v₁₂₃ Q,
            cases Q with E Q, cases E with E₁ E₂,
            cases Q with Sa₁ Q, cases Q with Sa₂ Q,
            cases Q with S₁ Q, cases Q with s₂ Q, cases Q with S₃ S₁₂₃,
            intros P C,
            refine C { x := a, J₁ := _, J₂ := _ },
            { existsi v₂, existsi v₃, existsi a₁,
              repeat { try { apply and.intro }, assumption }
            },
            { existsi v₁, existsi a₂, existsi v₁₂₃,
              repeat { try { apply and.intro }, assumption }
            }
          end
    }


def FormalLocal {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : Alg.{ℓ}
 := Alg.Prod A.Opt (MonAlg SJC.Alg)

inductive simpl_step {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
  : Rel (FormalLocal SJC) (FormalLocal SJC)
| mon : ∀ x s₁ s₂ (S₁₂ : Mon.simpl_step s₁ s₂)
        , simpl_step (x, s₁) (x, s₂)
| join : ∀ x₁ x₃ (s₂ : SJC.Alg.τ) s
           (J : A.Opt.join x₁ (some s₂.val) (some x₃))
         , simpl_step (x₁, s) (some x₃, sub s (Mon.single s₂))

inductive simpl {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
  : Rel (FormalLocal SJC) (FormalLocal SJC)
| refl : ∀ x, simpl x x
| step : ∀ x₁ x₂ x₃ (S₁₂ : simpl_step x₁ x₂) (S₂₃ : simpl x₂ x₃), simpl x₁ x₃

def simpl.trans {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ x₃ : (FormalLocal SJC).τ}
    (S₁₂ : simpl x₁ x₂) (S₂₃ : simpl x₂ x₃)
  : simpl x₁ x₃
 := begin
      induction S₁₂,
      { assumption },
      { apply simpl.step,
        { assumption },
        { apply ih_1, assumption }
      }
    end

-- def simpl.symm {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
--     {x₁ x₂ : (FormalLocal SJC).τ}
--     (S : simpl x₁ x₂)
--   : simpl x₂ x₁
--  := begin
--       induction S,
--       { apply simpl.refl },
--       { apply simpl.trans ih_1,
--         clear ih_1,
--         cases S₁₂ ; clear S₁₂,
--         { refine simpl.step _ _ _ _ (simpl.refl _),
--           apply simpl_step.equiv, apply Mon.equiv.symm, assumption
--         },
--         { apply simpl.step _ _ _ (simpl_step.split_l _ _ _ _ J),
--           refine simpl.step _ _ _ (simpl_step.equiv _ _ _ _) (simpl.refl _),
--           intro a,
--           apply eq.trans (add.linear _ _ _),
--           apply eq.trans (congr_arg _ (sub.linear _ _ _)),
--           simp
--         },
--         { apply simpl.step _ _ _ (simpl_step.join_l _ _ _ _ J),
--           refine simpl.step _ _ _ (simpl_step.equiv _ _ _ _) (simpl.refl _),
--           intro a,
--           apply eq.trans (sub.linear _ _ _),
--           apply eq.trans (congr_arg (λ x, x - Mon.fn (Mon.single s₂) a) (add.linear _ _ _)),
--           simp
--         },
--         { apply simpl.step _ _ _ (simpl_step.split_r _ _ _ _ _ J),
--           apply simpl.refl
--         },
--         { apply simpl.step _ _ _ (simpl_step.join_r _ _ _ _ _ J),
--           apply simpl.refl
--         }
--       }
--     end

def join {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
  : (FormalLocal SJC).τ → (FormalLocal SJC).τ → (FormalLocal SJC).τ → Prop
 := λ x₁ x₂ x₃
    , ∃ y₁ y₂ y₃
      , (FormalLocal SJC).join y₁ y₂ y₃
      ∧ simpl x₁ y₁
      ∧ simpl x₂ y₂
      ∧ simpl y₃ x₃

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

def join.assoc {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    (w₁ w₂ w₃ w₁₂₃ y₁₂ z₁₂ : (FormalLocal SJC).τ)
    (Sy : simpl y₁₂ z₁₂)
    (H : ∃ y₁ y₂ z₃ z₁₂₃
         , ((FormalLocal SJC).join y₁ y₂ y₁₂ ∧ (FormalLocal SJC).join z₁₂ z₃ z₁₂₃)
         ∧ (simpl w₁ y₁ ∧ simpl w₂ y₂ ∧ simpl w₃ z₃ ∧ simpl z₁₂₃ w₁₂₃))
  : ∃ a a₁ a₂ v₁ v₂ v₃ v₁₂₃
    , ((FormalLocal SJC).join v₂ v₃ a₁ ∧ (FormalLocal SJC).join v₁ a₂ v₁₂₃)
    ∧ (simpl a₁ a ∧ simpl a a₂ ∧ simpl w₁ v₁ ∧ simpl w₂ v₂ ∧ simpl w₃ v₃ ∧ simpl v₁₂₃ w₁₂₃)
 := begin
      induction Sy with yv₁₂ yi₁ yi₂ yi₃ ySi₁₂ ySi₂₃ yIH,
      { cases H with e₁ H, cases H with e₂ H, cases H with f₃ H, cases H with f₁₂₃ H,
        cases H with E H, cases E with E₁₂ E₁₂₃,
        cases H with T₁ H, cases H with T₂ H, cases H with T₃ T₁₂₃,
        apply (FormalLocal SJC).assoc E₁₂ E₁₂₃,
        intro a,
        existsi a.x, existsi a.x, existsi a.x,
        existsi e₁, existsi e₂, existsi f₃, existsi f₁₂₃,
        apply and.intro,
        { exact and.intro a.J₁ a.J₂ },
        { repeat { apply and.intro, apply simpl.refl },
          repeat { try { apply and.intro }, assumption }
        }
      },
      { apply yIH, clear yIH,
        cases H with e₁ H, cases H with e₂ H, cases H with f₃ H, cases H with f₁₂₃ H,
        cases H with E H, cases E with E₁₂ E₁₂₃,
        cases H with T₁ H, cases H with T₂ H, cases H with T₃ T₁₂₃,
        cases ySi₁₂,
        { exact sorry -- is true
        },
        { apply A.Opt.assoc E₁₂.1 J,
          intro a,
          existsi e₁, existsi (a.x, sub e₂.snd (Mon.single s₂)),
          existsi f₃, existsi f₁₂₃,
          apply and.intro,
          { apply and.intro,
            { apply and.intro a.J₂,
              exact sorry -- is true
            },
            { assumption }
          },
          { refine and.intro T₁ (and.intro _ (and.intro T₃ T₁₂₃)),
            apply simpl.trans T₂,
            cases a with a, simp,
            cases a with a,
            { exact false.elim (Alg.Opt.join_some_r J₁ rfl) },
            cases e₂ with e₂ se₂,
            exact simpl.step _ _ _ (simpl_step.join _ _ _ _ J₁) (simpl.refl _)
          }
        }
      }
    end

def join.IsAssoc {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : IsAssoc (@join A S SJC)
 := λ w₁ w₂ w₃ w₁₂ w₁₂₃ J₁₂ J₁₂₃
    , begin
        intros P C,
        cases J₁₂ with y₁ J₁₂, cases J₁₂ with y₂ J₁₂, cases J₁₂ with y₁₂ J₁₂,
        cases J₁₂ with J₁₂ Ty, cases Ty with T₁ Ty, cases Ty with T₂ Ty,
        cases J₁₂₃ with z₁₂ J₁₂₃, cases J₁₂₃ with z₃ J₁₂₃, cases J₁₂₃ with z₁₂₃ J₁₂₃,
        cases J₁₂₃ with J₁₂₃ Tz, cases Tz with Tz Tz', cases Tz' with T₃ T₁₂₃,
        --
        have Q := join.assoc w₁ w₂ w₃ w₁₂₃ y₁₂ z₁₂ (simpl.trans Ty Tz)
                    begin
                      existsi y₁, existsi y₂, existsi z₃, existsi z₁₂₃,
                      apply and.intro (and.intro J₁₂ J₁₂₃),
                      repeat { try { apply and.intro }, assumption },
                    end,
        cases Q with a Q, cases Q with a₁ Q, cases Q with a₂ Q,
        cases Q with v₁ Q, cases Q with v₂ Q, cases Q with v₃ Q, cases Q with v₁₂₃ Q,
        cases Q with J Q, cases J with J₁ J₂,
        cases Q with Sa₁ Q, cases Q with Sa₂ Q,
        cases Q with S₁ Q, cases Q with S₂ Q, cases Q with S₃ S₁₂₃,
        refine C { x := a, J₁ := _, J₂ := _ },
        { existsi v₂, existsi v₃, existsi a₁,
          repeat { try {apply and.intro}, assumption }
        },
        { existsi v₁, existsi a₂, existsi v₁₂₃,
          repeat { try {apply and.intro}, assumption }
        }
      end

def ident {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
  : (FormalLocal SJC).τ
 := (none, Mon.zero _)

def ident_left {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x : (FormalLocal SJC).τ}
  : join ident x x
 := begin
      existsi ident, existsi x, existsi x,
      apply and.intro,
      { apply and.intro,
        { constructor },
        { existsi ident.snd, existsi x.snd, existsi x.snd,
          apply and.intro,
          { intro a,
            rw add.linear,
            simp [ident],
            rw Mon.fn.zero,
            simp
          },
          { repeat { try { apply and.intro }, apply Mon.simpl.refl }
          }
        }
      },
      apply and.intro,
      { apply simpl.refl },
      apply and.intro,
      repeat { apply simpl.refl }
    end

inductive equiv {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
  : (FormalLocal SJC).τ → (FormalLocal SJC).τ → Prop
| intro : ∀ a s₁ s₂ (S₁₂ : Mon.simpl s₁ s₂)
          , equiv (a, s₁) (a, s₂)

def equiv.refl {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    (x : (FormalLocal SJC).τ)
  : equiv x x
 := begin
      cases x with x s,
      constructor,
      apply Mon.simpl.refl
    end

def equiv.symm {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x y : (FormalLocal SJC).τ}
    (H : equiv x y)
  : equiv y x
 := begin
      cases H,
      constructor,
      apply Mon.simpl.symm,
      assumption
    end

def equiv.trans {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ x₃ : (FormalLocal SJC).τ}
    (H₁₂ : equiv x₁ x₂) (H₂₃ : equiv x₂ x₃)
  : equiv x₁ x₃
 := begin
      cases H₁₂, cases H₂₃,
      constructor,
      apply Mon.simpl.trans,
      repeat { assumption }
    end

def equiv.simpl {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x y : (FormalLocal SJC).τ}
    (E : equiv x y)
  : simpl x y
 := begin
      cases E,
      induction S₁₂,
      { apply simpl.refl },
      { refine simpl.trans _ (ih_1 (equiv.intro _ _ _ S₂₃)),
        refine simpl.step _ _ _ _ (simpl.refl _),
        apply simpl_step.mon,
        assumption
      }
    end

def join.equiv₁ {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ x₃ z₁ : (FormalLocal SJC).τ}
    (Jx : join x₁ x₂ x₃)
    (E₁ : equiv x₁ z₁)
  : join z₁ x₂ x₃
 := begin
      cases Jx with y₁ Jx, cases Jx with y₂ Jx, cases Jx with y₃ Jx,
      cases Jx with Jy Sxy, cases Sxy with Sxy₁ Sxy, cases Sxy with Sxy₂ Sxy₃,
      existsi y₁, existsi y₂, existsi y₃,
      apply and.intro Jy,
      refine and.intro _ (and.intro Sxy₂ Sxy₃),
      exact simpl.trans (equiv.simpl E₁.symm) Sxy₁
    end

def join.equiv₃ {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ x₃ z₃ : (FormalLocal SJC).τ}
    (Jx : join x₁ x₂ x₃)
    (E₃ : equiv x₃ z₃)
  : join x₁ x₂ z₃
 := begin
      cases Jx with y₁ Jx, cases Jx with y₂ Jx, cases Jx with y₃ Jx,
      cases Jx with Jy Sxy, cases Sxy with Sxy₁ Sxy, cases Sxy with Sxy₂ Sxy₃,
      existsi y₁, existsi y₂, existsi y₃,
      apply and.intro Jy,
      refine and.intro Sxy₁ (and.intro Sxy₂ _),
      exact simpl.trans Sxy₃ (equiv.simpl E₃)
    end

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

def valid_local {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : Type.{ℓ}
 := {x : (FormalLocal SJC).τ // ∃ a f, equiv x (some a, f)}

instance valid_local_setoid {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : setoid (valid_local SJC)
 := { r := λ x₁ x₂, equiv x₁.val x₂.val
    , iseqv := begin
                 apply and.intro,
                 { intro x, apply equiv.refl },
                 apply and.intro,
                 { intros x₁ x₂ H, apply equiv.symm H },
                 { intros x₁ x₂ x₃ H₁₂ H₂₃, apply equiv.trans H₁₂ H₂₃ }
               end
    }

def τ {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : Type.{ℓ}
 := @quot (valid_local SJC) (λ x₁ x₂, @equiv _ _ SJC x₁.val x₂.val)

def coset {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    (a : A.τ) (s : Mon SJC.Alg.τ)
  : valid_local SJC
 := { val := (some a, s)
    , property := begin existsi a, existsi s, apply equiv.refl end
    }

def local_join {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : τ SJC → τ SJC → τ SJC → Prop
 := quotient.lift₃
      (λ x₁ x₂ x₃, join x₁.val x₂.val x₃.val)
      (λ x₁ x₂ x₃ z₁ z₂ z₃ E₁ E₂ E₃
       , iff.to_eq
          (iff.intro
            (λ Jx, join.equiv Jx E₁ E₂ E₃)
            (λ Jx, join.equiv Jx E₁.symm E₂.symm E₃.symm)))

end MonAlg

def Set.JoinClosed.Localize {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : Alg.{ℓ}
 := { τ := MonAlg.τ SJC
    , join := MonAlg.local_join SJC
    , comm
       := λ x₁ x₂ x₃ J
          , begin
              induction x₁ with x₁,
              induction x₂ with x₂,
              induction x₃ with x₃,
              { simp [MonAlg.local_join] at *,
                simp [quotient.lift₃] at *,
                simp [quotient.lift] at *,
                exact MonAlg.join.comm J
              },
              repeat { trivial }
            end
    , assoc
       := λ x₁ x₂ x₃ x₁₂ x₁₂₃ J₁₂ J₁₂₃
          , begin
              intros P C,
              induction x₁ with x₁,
              induction x₂ with x₂,
              induction x₃ with x₃,
              induction x₁₂ with x₁₂,
              induction x₁₂₃ with x₁₂₃,
              { apply MonAlg.join.IsAssoc SJC J₁₂ J₁₂₃,
                intro a, cases a with a J₁ J₂,
                cases a with a s,
                cases a with a,
                { -- in this case, S cannot be empty, or J₁ is a contradiction.
                  -- So we can use a representative of S.
                  have Hs₀ : ∃ s₀, s₀ ∈ S, from sorry,
                  cases Hs₀ with s₀ Hs₀,
                  let s' := MonAlg.sub s (MonAlg.Mon.single ⟨s₀, Hs₀⟩),
                  have E' : MonAlg.equiv (some s₀, s') (none, s), from sorry,
                  refine C { x := quot.mk _ { val := (some s₀, s'), property := _ }
                          , J₁ := _
                          , J₂ := _
                          },
                  { existsi s₀, existsi s', apply MonAlg.equiv.refl },
                  { exact sorry },
                  { exact sorry }
                },
                { refine C { x := quot.mk _ { val := (some a, s), property := _ }
                          , J₁ := J₁
                          , J₂ := J₂
                          },
                  existsi a, existsi s, apply MonAlg.equiv.refl,
                }
              },
              repeat { trivial }
            end
    }

def PrimeLocalize {A : Alg.{ℓ}} (p : A.PrimeSpec)
  : Alg.{ℓ}
 := p.prime.Complement_JoinClosed.Localize

def Alg.localize_at (A : Alg.{ℓ})
    (q : A.PrimeSpec)
    (a : A.τ)
    (ff : MonAlg.Mon q.prime.Complement_JoinClosed.Alg.τ)
  : (PrimeLocalize q).τ
 := ⟦ { val := (some a, ff)
      , property := exists.intro _ (exists.intro _ (MonAlg.equiv.refl _))
      } ⟧

def Set.Localize {A : Alg.{ℓ}} (S : Set A)
  : Alg.{ℓ}
 := Set.JoinClosed.Localize (JoinClosure.JoinClosed S)

end Sep
