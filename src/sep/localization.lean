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

def Mon.fn.zero {A : Alg.{ℓ}}
    {a : A.τ}
  : Mon.fn (Mon.zero A) a = 0
 := begin
      simp [Mon.fn],
      cases classical.prop_decidable (a ∈ (Mon.zero A).supp) with Q Q,
      { apply rfl },
      { cases Q }
    end

def Mon.equiv {A : Alg.{ℓ}}
    (M₁ M₂ : Mon A)
  : Prop
 := ∀ a, M₁.fn a = M₂.fn a

def Mon.equiv.refl {A : Alg.{ℓ}}
    (M : Mon A)
  : Mon.equiv M M
 := λ a, rfl

def Mon.equiv.symm {A : Alg.{ℓ}}
    {M₁ M₂ : Mon A}
    (E : Mon.equiv M₁ M₂)
  : Mon.equiv M₂ M₁
 := begin intro a, rw E a end

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

def add.zero_r {A : Alg.{ℓ}}
    {M : Mon A}
  : Mon.equiv (M + Mon.zero A) M
 := begin
      intro a,
      rw add.linear,
      rw Mon.fn.zero,
      simp
    end

def Mon.equiv.opt_single_none {A : Alg.{ℓ}}
    (s : Mon A)
  : Mon.equiv s (Mon.opt_single none + s)
 := begin
      intro a,
      rw add.linear,
      exact sorry
    end

def Mon.join (A : Alg.{ℓ})
  : Mon A → Mon A → Mon A → Prop
 := λ x₁ x₂ x₃
    , Mon.equiv (x₁ + x₂) x₃

def MonAlg (A : Alg.{ℓ})
  : Alg.{ℓ}
 := { τ := Mon A
    , join := Mon.join A
    , comm
       := begin
            intros x₁ x₂ x₃ Jx,
            intro a,
            rw (Jx a).symm,
            repeat { rw add.linear },
            simp
          end
    , assoc
       := begin
            intros x₁ x₂ x₃ x₁₂ x₁₂₃ J₁₂ J₁₂₃,
            intros P C,
            refine C { x := x₂ + x₃, J₁ := Mon.equiv.refl _, J₂ := _ },
            intro a,
            rw (J₁₂₃ a).symm,
            repeat { rw add.linear },
            rw (J₁₂ a).symm,
            repeat { rw add.linear },
            simp
          end
    }


def FormalLocal {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : Alg.{ℓ}
 := Alg.Prod A.Opt (MonAlg SJC.Alg)

inductive simpl_step {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
  : Rel (FormalLocal SJC) (FormalLocal SJC)
| equiv : ∀ x s₁ s₂ (E : Mon.equiv s₁ s₂)
          , simpl_step (x, s₁) (x, s₂)
| join_l : ∀ x₁ x₃ (s₂ : SJC.Alg.τ) s
             (J : A.Opt.join x₁ (some s₂.val) (some x₃))
           , simpl_step (x₁, s) (some x₃, sub s (Mon.single s₂))
| split_l : ∀ x₁ x₃ (s₂ : SJC.Alg.τ) s
              (J : A.Opt.join x₁ (some s₂.val) (some x₃))
            , simpl_step (some x₃, s) (x₁, add (Mon.single s₂) s)
| join_r : ∀ x s₁ s₂ s₃ s
             (J : SJC.Alg.join s₁ s₂ s₃)
           , simpl_step (x, add (add (Mon.single s₁) (Mon.single s₂)) s)
                        (x, add (Mon.single s₃) s)
| split_r : ∀ x s₁ s₂ s₃ s
              (J : SJC.Alg.join s₁ s₂ s₃)
            , simpl_step (x, add (Mon.single s₃) s)
                         (x, add (add (Mon.single s₁) (Mon.single s₂)) s)

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

def simpl.symm {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ : (FormalLocal SJC).τ}
    (S : simpl x₁ x₂)
  : simpl x₂ x₁
 := begin
      induction S,
      { apply simpl.refl },
      { apply simpl.trans ih_1,
        clear ih_1,
        cases S₁₂ ; clear S₁₂,
        { refine simpl.step _ _ _ _ (simpl.refl _),
          apply simpl_step.equiv, apply Mon.equiv.symm, assumption
        },
        { apply simpl.step _ _ _ (simpl_step.split_l _ _ _ _ J),
          refine simpl.step _ _ _ (simpl_step.equiv _ _ _ _) (simpl.refl _),
          intro a,
          apply eq.trans (add.linear _ _ _),
          apply eq.trans (congr_arg _ (sub.linear _ _ _)),
          simp
        },
        { apply simpl.step _ _ _ (simpl_step.join_l _ _ _ _ J),
          refine simpl.step _ _ _ (simpl_step.equiv _ _ _ _) (simpl.refl _),
          intro a,
          apply eq.trans (sub.linear _ _ _),
          apply eq.trans (congr_arg (λ x, x - Mon.fn (Mon.single s₂) a) (add.linear _ _ _)),
          simp
        },
        { apply simpl.step _ _ _ (simpl_step.split_r _ _ _ _ _ J),
          apply simpl.refl
        },
        { apply simpl.step _ _ _ (simpl_step.join_r _ _ _ _ _ J),
          apply simpl.refl
        }
      }
    end

def join {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
  : (FormalLocal SJC).τ → (FormalLocal SJC).τ → (FormalLocal SJC).τ → Prop
 := λ x₁ x₂ x₃
    , ∃ y₁ y₂ y₃
      , (FormalLocal SJC).join y₁ y₂ y₃
      ∧ simpl x₁ y₁
      ∧ simpl x₂ y₂
      ∧ simpl x₃ y₃

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

def join.IsAssoc_helper {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    (w₁ w₂ w₃ w₁₂₃ y₁₂ z₁₂ : (FormalLocal SJC).τ)
    (S₁₂ : simpl y₁₂ z₁₂)
    (H : ∃ y₁ y₂ z₃ z₁₂₃
         , ((FormalLocal SJC).join y₁ y₂ y₁₂ ∧ (FormalLocal SJC).join z₁₂ z₃ z₁₂₃)
         ∧ (simpl w₁ y₁ ∧ simpl w₂ y₂ ∧ simpl w₃ z₃ ∧ simpl w₁₂₃ z₁₂₃))
  : ∃ v₁ v₂ v₁₂ v₃ v₁₂₃
         , ((FormalLocal SJC).join v₁ v₂ v₁₂ ∧ (FormalLocal SJC).join v₁₂ v₃ v₁₂₃)
         ∧ (simpl y₁₂ v₁₂ ∧ simpl w₁ v₁ ∧ simpl w₂ v₂ ∧ simpl w₃ v₃ ∧ simpl w₁₂₃ v₁₂₃)
 := begin
      induction S₁₂ with v₁₂ i₁ i₂ i₃ Si₁₂ Si₂₃ IH,
      { cases H with v₁ H, cases H with v₂ H, cases H with v₃ H, cases H with v₁₂₃ H,
        existsi v₁, existsi v₂, existsi v₁₂, existsi v₃, existsi v₁₂₃,
        refine and.intro H.1 (and.intro (simpl.refl _) H.2)
      },
      { cases H with e₁ H, cases H with e₂ H, cases H with f₃ H, cases H with f₁₂₃ H,
        cases H with J H, cases J with Je Jf,
        cases H with Se₁ H, cases H with Se₂ H, cases H with Sf₃ Sf₁₂₃,
        --
        have Q : ∃ (y₁ y₂ z₃ z₁₂₃ : (FormalLocal SJC).τ)
                  , ((FormalLocal SJC).join y₁ y₂ i₂ ∧ (FormalLocal SJC).join i₃ z₃ z₁₂₃)
                  ∧ (simpl w₁ y₁ ∧ simpl w₂ y₂ ∧ simpl w₃ z₃ ∧ simpl w₁₂₃ z₁₂₃), from
          begin
            clear IH,
            exact sorry
          end,
        have H := IH Q, clear IH Q,
        cases H with v₁ H, cases H with v₂ H, cases H with v₁₂ H, cases H with v₃ H, cases H with v₁₂₃ H,
        existsi v₁, existsi v₂, existsi v₁₂, existsi v₃, existsi v₁₂₃,
        refine and.intro H.1 (and.intro _ H.2.2),
        exact simpl.step _ _ _ Si₁₂ H.2.1
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
        have Q := join.IsAssoc_helper w₁ w₂ w₃ w₁₂₃ y₁₂ z₁₂ (simpl.trans Ty.symm Tz)
                    begin
                      existsi y₁, existsi y₂, existsi z₃, existsi z₁₂₃,
                      apply and.intro (and.intro J₁₂ J₁₂₃),
                      repeat { apply and.intro, assumption },
                      assumption
                    end,
        cases Q with v₁ Q, cases Q with v₂ Q, cases Q with v₁₂ Q, cases Q with v₃ Q, cases Q with v₁₂₃ Q,
        cases Q with F Swv, cases F with F₁₂ F₁₂₃,
        cases Swv with Swv₁₂ Swv, cases Swv with Swv₁ Swv, cases Swv with Swv₂ Swv, cases Swv with Swv₃ Swv₁₂₃,
        apply (FormalLocal SJC).assoc F₁₂ F₁₂₃,
        intro a, cases a with a ω₁₂ ω₁₂₃,
        refine C { x := a, J₁ := _, J₂ := _ },
        { existsi v₂, existsi v₃, existsi a,
          repeat { apply and.intro, assumption },
          apply simpl.refl
        },
        { existsi v₁, existsi a, existsi v₁₂₃,
          repeat { apply and.intro, assumption },
          exact and.intro (simpl.refl _) Swv₁₂₃
        }
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
      { apply and.intro,
        { constructor },
        { intro a,
          rw add.linear,
          simp [ident],
          rw Mon.fn.zero,
          simp
        }
      },
      apply and.intro,
      { apply simpl.refl },
      apply and.intro,
      repeat { apply simpl.refl }
    end


namespace equiv
-- this is the equivalence relation you'd think you want,
-- but it turns out it's equivalent to simpl!

structure equiv_witness {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    (x₁ x₂ : (FormalLocal SJC).τ)
 := (n as bs : (MonAlg (Set.JoinClosed.Alg SJC)).τ)
    (a b : A.Opt.τ)
    (Sa : simpl (a, as) x₁)
    (Sb : simpl (b, bs) x₂)
    (Sn : simpl (a, add as n) (b, add bs n))

def equiv {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    (x₁ x₂ : (FormalLocal SJC).τ)
  : Prop
 := ∀ (P : Prop) (C : equiv_witness x₁ x₂ → P), P

def equiv.simpl {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ : (FormalLocal SJC).τ}
    (E : equiv x₁ x₂)
  : simpl x₁ x₂
 := begin
      rename E E', apply E', intro E,
      have H : simpl x₁ (x₁.fst, sub (add x₁.snd E.n) E.n), from sorry,
      apply simpl.trans H, clear H,
      have H : simpl (x₁.fst, sub (add x₁.snd E.n) E.n)
                     (E.a, sub (add E.as E.n) E.n), from sorry,
      apply simpl.trans H, clear H,
      have H : simpl (E.a, sub (add E.as E.n) E.n)
                     (E.b, sub (add E.bs E.n) E.n), from sorry,
      apply simpl.trans H, clear H,
      have H : simpl (E.b, sub (add E.bs E.n) E.n)
                     (x₂.fst, sub (add x₂.snd E.n) E.n), from sorry,
      apply simpl.trans H, clear H,
      have H : simpl (x₂.fst, sub (add x₂.snd E.n) E.n) x₂, from sorry,
      exact H
    end

def equiv.refl {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    (x : (FormalLocal SJC).τ)
  : equiv x x
 := begin
      intros P C,
      refine C { n := Mon.zero _, as := x.snd, bs := x.snd
               , a := x.fst, b := x.fst
               , Sa := _, Sb := _, Sn := _
               },
      repeat { cases x, apply simpl.refl }
    end

def equiv.symm {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ : (FormalLocal SJC).τ}
    (E : equiv x₁ x₂)
  : equiv x₂ x₁
 := begin
      intros P C,
      apply E, intro E',
      exact C { n := E'.n, as := E'.bs, bs := E'.as
              , a := E'.b, b := E'.a
              , Sa := E'.Sb, Sb := E'.Sa, Sn := E'.Sn.symm
              }
    end

def equiv.trans {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ x₃ : (FormalLocal SJC).τ}
    (E₁₂ : equiv x₁ x₂) (E₂₃ : equiv x₂ x₃)
  : equiv x₁ x₃
 := begin
      intros P C,
      apply E₁₂, intro E,
      apply E₂₃, intro F,
      exact C { n := add E.n F.n, as := E.as, bs := F.bs
              , a := E.a, b := F.b
              , Sa := E.Sa, Sb := F.Sb
              , Sn := begin
                        have H  : simpl (E.a, add (E.as) (add (E.n) (F.n)))
                                        (E.b, add (E.bs) (add (E.n) (F.n))), from
                          sorry,
                        apply simpl.trans H, clear H,
                        have H  : simpl (E.b, add (E.bs) (add (E.n) (F.n)))
                                        (x₂.fst, add x₂.snd (add (E.n) (F.n))), from
                          sorry,
                        apply simpl.trans H, clear H,
                        have H  : simpl (x₂.fst, add x₂.snd (add (E.n) (F.n)))
                                        (F.a, add (F.as) (add (E.n) (F.n))), from
                          sorry,
                        apply simpl.trans H, clear H,
                        have H  : simpl (F.a, add (F.as) (add (E.n) (F.n)))
                                        (F.b, add (F.bs) (add (E.n) (F.n))), from
                          sorry,
                        apply H
                      end
              }
    end
end equiv

def join.simpl₁ {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ x₃ z₁ : (FormalLocal SJC).τ}
    (Jx : join x₁ x₂ x₃)
    (E₁ : simpl x₁ z₁)
  : join z₁ x₂ x₃
 := begin
      cases Jx with y₁ Jx, cases Jx with y₂ Jx, cases Jx with y₃ Jx,
      cases Jx with Jy Sxy, cases Sxy with Sxy₁ Sxy, cases Sxy with Sxy₂ Sxy₃,
      existsi y₁, existsi y₂, existsi y₃,
      apply and.intro Jy,
      refine and.intro _ (and.intro Sxy₂ Sxy₃),
      exact simpl.trans E₁.symm Sxy₁
    end

def join.simpl₃ {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ x₃ z₃ : (FormalLocal SJC).τ}
    (Jx : join x₁ x₂ x₃)
    (E₃ : simpl x₃ z₃)
  : join x₁ x₂ z₃
 := begin
      cases Jx with y₁ Jx, cases Jx with y₂ Jx, cases Jx with y₃ Jx,
      cases Jx with Jy Sxy, cases Sxy with Sxy₁ Sxy, cases Sxy with Sxy₂ Sxy₃,
      existsi y₁, existsi y₂, existsi y₃,
      apply and.intro Jy,
      refine and.intro Sxy₁ (and.intro Sxy₂ _),
      exact simpl.trans E₃.symm Sxy₃
    end

def join.simpl {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {x₁ x₂ x₃ z₁ z₂ z₃ : (FormalLocal SJC).τ}
    (Jx : join x₁ x₂ x₃)
    (E₁ : simpl x₁ z₁)
    (E₂ : simpl x₂ z₂)
    (E₃ : simpl x₃ z₃)
  : join z₁ z₂ z₃
 := begin
      have Q₁ := join.simpl₁ Jx E₁,
      have Q₂ := join.comm (join.simpl₁ (join.comm Q₁) E₂),
      exact join.simpl₃ Q₂ E₃
    end

instance simpl_setoid {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : setoid (FormalLocal SJC).τ
 := { r := simpl
    , iseqv := begin
                 apply and.intro simpl.refl,
                 apply and.intro,
                 { apply simpl.symm },
                 { apply simpl.trans }
               end
    }


def τ {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : Type.{ℓ}
 := quot (@simpl _ _ SJC)

def local_join {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : τ SJC → τ SJC → τ SJC → Prop
 := quotient.lift₃
      join
      (λ x₁ x₂ x₃ z₁ z₂ z₃ E₁ E₂ E₃
       , iff.to_eq
          (iff.intro
            (λ Jx, join.simpl Jx E₁ E₂ E₃)
            (λ Jx, join.simpl Jx E₁.symm E₂.symm E₃.symm)))

def local_join.join {A : Alg.{ℓ}} {S : Set A} {SJC : S.JoinClosed}
    {a₁ : A.τ}
    {f₁ : (Localization.MonAlg (Set.JoinClosed.Alg SJC)).τ}
    {a₂ : A.τ}
    {f₂ : (Localization.MonAlg (Set.JoinClosed.Alg SJC)).τ}
    {a₃ : A.τ}
    {f₃ : (Localization.MonAlg (Set.JoinClosed.Alg SJC)).τ}
    {a₃ : A.τ}
    {f₃ : (Localization.MonAlg (Set.JoinClosed.Alg SJC)).τ}
    (J : local_join SJC ⟦(some a₁, f₁)⟧ ⟦(some a₂, f₂)⟧ ⟦(some a₃, f₃)⟧)
  : join (some a₁, f₁) (some a₂, f₂) (some a₃, f₃)
 := begin
      exact J
    end

end Localization

def Set.JoinClosed.Localize {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
  : Alg.{ℓ}
 := { τ := {x : Localization.τ SJC // ∃ a f, x = ⟦ (some a, f) ⟧}
    , join := λ x₁ x₂ x₃, Localization.local_join SJC x₁.val x₂.val x₃.val
    , comm
       := λ x₁ x₂ x₃ J
          , begin
              cases x₁ with x₁ r₁,
              cases x₂ with x₂ r₂,
              cases x₃ with x₃ r₃,
              induction x₁ with x₁,
              induction x₂ with x₂,
              induction x₃ with x₃,
              { simp [Localization.local_join] at *,
                simp [quotient.lift₃] at *,
                simp [quotient.lift] at *,
                exact Localization.join.comm J
              },
              repeat { trivial }
            end
    , assoc
       := λ x₁ x₂ x₃ x₁₂ x₁₂₃ J₁₂ J₁₂₃
          , begin
              cases x₁ with x₁ r₁, cases r₁ with a₁ r₁, cases r₁ with f₁ E₁,
              cases x₂ with x₂ r₂, cases r₂ with a₂ r₂, cases r₂ with f₂ E₂,
              cases x₃ with x₃ r₃, cases r₃ with a₃ r₃, cases r₃ with f₃ E₃,
              cases x₁₂ with x₁₂ r₁₂, cases r₁₂ with a₁₂ r₁₂, cases r₁₂ with f₁₂ E₁₂,
              cases x₁₂₃ with x₁₂₃ r₁₂₃, cases r₁₂₃ with a₁₂₃ r₁₂₃, cases r₁₂₃ with f₁₂₃ E₁₂₃,
              dsimp at *,
              rw E₁ at *, rw E₂ at *, rw E₃ at *, rw E₁₂ at *, rw E₁₂₃ at *,
              intros P C,
              apply Localization.join.IsAssoc SJC J₁₂ J₁₂₃,
              intro a, cases a with a J₁ J₂, cases a with a s, cases a with a,
              { -- in this case, S cannot be empty, or J₁ is a contradiction.
                -- So we can use a representative of S.
                have Hs₀ : ∃ s₀, s₀ ∈ S, from sorry,
                cases Hs₀ with s₀ Hs₀,
                let s' := Localization.sub s (Localization.Mon.single ⟨s₀, Hs₀⟩),
                have E' : quot.mk Localization.simpl (some s₀, s') = ⟦(none, s)⟧, from sorry,
                refine C { x := { val := quot.mk _ (some s₀, s'), property := _ }
                         , J₁ := _
                         , J₂ := _
                         },
                { existsi s₀, existsi s', trivial },
                { simp at *, rw E₂, rw E₃, rw E', exact J₁ },
                { simp at *, rw E₁, rw E₁₂₃, rw E', exact J₂ }
              },
              { refine C { x := { val := quot.mk _ (some a, s), property := _ }
                         , J₁ := _
                         , J₂ := _
                         },
                { existsi a, existsi s, trivial },
                { simp at *, rw E₂, rw E₃, exact J₁ },
                { simp at *, rw E₁, rw E₁₂₃, exact J₂ }
              },
            end
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
    , property := exists.intro _ (exists.intro _ (quot.sound (Localization.simpl.refl _)))
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
