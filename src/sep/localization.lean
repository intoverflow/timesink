/- Localization
 -
 -/
import .basic
import .ordalg

namespace Sep
universes ℓ


namespace Localization

inductive locl_step {A : Alg.{ℓ}} (S : Set A)
  : Rel A A
| refl : ∀ x, locl_step x x
| join : ∀ {x y s : A.τ} (Hs : s ∈ S)
           (J : A.join s x y)
         , locl_step x y

def locl_step.increasing {A : Alg.{ℓ}} (S : Set A)
    (s : A.τ) (Hs : s ∈ S)
  : (locl_step S).increasing s
 := begin
      intros x y J,
      exact locl_step.join Hs J
    end

def locl_step.trans {A : Alg.{ℓ}} {S : Set A} (SJC : S.JoinClosed)
    {x₁ x₂ x₃ : A.τ}
  : (locl_step S).Trans
 := begin
      intros x₁ x₂ x₃ E₁₂ E₂₃,
      cases E₁₂ with _ _ y₁₂ s₁₂ Hs₁₂ J₁₂ ; clear E₁₂,
      { assumption
      },
      { cases E₂₃ with _ _ y₂₃ s₂₃ Hs₂₃ J₂₃ ; clear E₂₃,
        { apply locl_step.join,
          repeat { assumption }
        },
        { apply A.assoc (A.comm J₁₂) (A.comm J₂₃),
          intro a,
          refine locl_step.join _ (A.comm a.J₂),
          { apply SJC _ _ _ a.J₁,
            repeat { assumption }
          }
        }
      }
    end

def locl_step.UpClosed {A : Alg.{ℓ}} (S : Set A)
  : (locl_step S).UpClosed
 := begin
      intros x₁ x₂ x₃ y₃ J R₃,
      cases R₃ with _ _ y s Hs J' ; clear R₃,
      { existsi x₁, existsi x₂,
        apply and.intro J,
        exact and.intro (locl_step.refl _ _) (locl_step.refl _ _)
      },
      { apply A.assoc J (A.comm J'),
        intro a,
        existsi x₁, existsi a.x,
        apply and.intro a.J₂,
        apply and.intro (locl_step.refl _ _),
        exact locl_step.join Hs (A.comm a.J₁)
      }
    end

def locl_step.DownClosed {A : Alg.{ℓ}} {S : Set A}
    (SJC : S.JoinClosed)
  : (locl_step S).DownClosed
 := begin
      intros x₁ x₂ y₁ y₂ y₃ R₁ R₂ J,
      cases R₁ with _ _ y₁ s₁ Hs₁ J₁ ; clear R₁,
      { cases R₂ with _ _ y₂ s₂ Hs₂ J₂ ; clear R₂,
        { existsi y₃,
          exact and.intro (locl_step.refl _ _) J
        },
        { apply A.assoc J₂ (A.comm J),
          intro a, existsi a.x,
          refine and.intro _ (A.comm a.J₁),
          apply locl_step.join Hs₂ a.J₂
        }
      },
      { cases R₂ with _ _ y₂ s₂ Hs₂ J₂ ; clear R₂,
        { apply A.assoc J₁ J,
          intro a, existsi a.x,
          refine and.intro _ a.J₁,
          exact locl_step.join Hs₁ a.J₂
        },
        { apply A.assoc J₁ J, intro a₁,
          apply A.assoc J₂ (A.comm a₁.J₁), intro a₂,
          existsi a₂.x,
          refine and.intro _ (A.comm a₂.J₁),
          apply A.assoc (A.comm a₂.J₂) (A.comm a₁.J₂),
          intro s,
          have Hs : s.x ∈ S, from
            begin
              apply SJC,
              apply s.J₁,
              repeat { assumption }
            end,
          exact locl_step.join Hs (A.comm s.J₂)
        }
      }
    end

inductive locl {A : Alg.{ℓ}} (S : Set A) (r : Rel A A)
  : Rel A A
| base : ∀ {x y} (Rxy : r x y), locl x y
| join : ∀ {x₁ x₂ y₂ y₁ s : A.τ}
           (Hs : s ∈ S)
           (Rx : r x₁ x₂)
           (Ry : r y₂ y₁)
           (J : A.join s x₂ y₂)
         , locl x₁ y₁

def locl.refl {A : Alg.{ℓ}} {S : Set A} {r : Rel A A}
    (r_refl : r.Refl)
  : (locl S r).Refl
 := λ a, locl.base S (r_refl a)

def locl.locl_step {A : OrdAlg.{ℓ}} {S : Set A.alg}
    {x y} (H : locl_step S x y)
  : locl S A.ord x y
 := begin
      cases H,
      { apply locl.refl A.refl },
      { apply locl.join Hs (A.refl _) (A.refl _) J }
    end

def locl.increasing₁ {A : Alg.{ℓ}} {S : Set A} {r : Rel A A}
    (r_refl : r.Refl)
  : S ⊆ (locl S r).increasing
 := begin
      intros s Hs x y J,
      exact locl.join Hs (r_refl _) (r_refl _) J
    end

def locl.increasing₂ {A : Alg.{ℓ}} {S : Set A} {r : Rel A A}
  : r.increasing ⊆ (locl S r).increasing
 := begin
      intros s Hs x y J,
      apply locl.base,
      exact Hs x y J
    end

def locl.recover {A : Alg.{ℓ}} {S : Set A} {r : Rel A A}
    (r_trans : r.Trans)
    (HS : S ⊆ r.increasing)
  : locl S r = r
 := begin
      apply funext, intro x, apply funext, intro y,
      apply iff.to_eq, apply iff.intro,
      { intro L, cases L with   _ _ R  _ x₂ y₂ _ s Hs Rx Ry J ; clear L,
        { assumption },
        { have Q := HS Hs _ _ J,
          apply r_trans, assumption,
          apply r_trans, assumption,
          assumption
        }
      },
      { intro H, apply locl.base, assumption }
    end

def locl.iff {A : Alg.{ℓ}} {S : Set A} {r : Rel A A}
    (r_refl : r.Refl)
    (r_trans : r.Trans)
  : locl S r = r ∘ locl_step S ∘ r
 := begin
      apply funext, intro x, apply funext, intro y,
      apply iff.to_eq, apply iff.intro,
      { intro L, cases L with   _ _ R  _ x₂ y₂ _ s Hs Rx Ry J ; clear L,
        { existsi x, refine and.intro _ R,
          existsi x, apply and.intro (r_refl _),
          apply locl_step.refl
        },
        { existsi y₂, refine and.intro _ Ry,
          existsi x₂, apply and.intro Rx,
          exact locl_step.join Hs J
        }
      },
      { intro H,
        cases H with y₂ H, cases H with H Ry,
        cases H with x₂ H, cases H with Rx H,
        cases H,
        { apply locl.base, apply r_trans, repeat { assumption } },
        { exact locl.join Hs Rx Ry J }
      }
    end

def locl.iff₂ {A : Alg.{ℓ}} {S : Set A} {r : Rel A A}
    (r_refl : r.Refl)
    (r_trans : r.Trans)
    {x y}
  : locl S r x y = (r ∘ locl_step S ∘ r) x y
 := begin rw locl.iff r_refl r_trans end

def locl.trans {A : Alg.{ℓ}} (S : Set A) (r : Rel A A)
    (SJC : S.JoinClosed)
    (r_closed : (r.Local S ∧ r.LocallyUpClosed S) ∨ r.LocallyDownClosed S)
    (r_refl : r.Refl)
    (r_trans : r.Trans)
  : (locl S r).Trans
 := begin
      intros x₁ x₂ x₃ E₁₂ E₂₃,
      cases E₁₂ with   _ _ R₁₂  _ x₁₂ y₁₂ _ s₁₂ Hs₁₂ Rx₁₂ Ry₁₂ J₁₂ ; clear E₁₂,
      { cases E₂₃ with _ _ R₂₃  _ x₂₃ y₂₃ _ s₂₃ Hs₂₃ Rx₂₃ Ry₂₃ J₂₃ ; clear E₂₃,
        { apply locl.base, apply r_trans, repeat { assumption } },
        { exact locl.join Hs₂₃ (r_trans _ _ _ R₁₂ Rx₂₃) Ry₂₃ J₂₃ }
      },
      { cases E₂₃ with _ _ R₂₃  _ x₂₃ y₂₃ _ s₂₃ Hs₂₃ Rx₂₃ Ry₂₃ J₂₃ ; clear E₂₃,
        { exact locl.join Hs₁₂ Rx₁₂ (r_trans _ _ _ Ry₁₂ R₂₃) J₁₂ },
        { have Ryx : r y₁₂ x₂₃ := r_trans _ _ _ Ry₁₂ Rx₂₃,
          clear Ry₁₂ Rx₂₃,
          cases r_closed with rUC rDC,
          { cases rUC with Hr rUC,
            have Q := rUC _ _ _ _ Hs₁₂ J₁₂ Ryx,
            cases Q with s₁₂' Q, cases Q with x₁₂' Q,
            cases Q with J' Q, cases Q with Rs₁₂' Rx₁₂',
            have Rx : r x₁ x₁₂' := r_trans _ _ _ Rx₁₂ Rx₁₂',
            clear J₁₂ Ryx Rx₁₂ Rx₁₂',
            apply A.assoc J' (A.comm J₂₃), intro a₁,
            apply A.assoc a₁.J₁ (A.comm a₁.J₂), intro s,
            have Q := Hr ⟨s₁₂, and.intro Hs₁₂ Rs₁₂'⟩,
            cases Q with Q Q,
            { have Hs : s.x ∈ S := SJC _ _ _ s.J₁ Hs₂₃ Q,
              exact locl.join Hs Rx Ry₂₃ (A.comm s.J₂)
            },
            { have Rx' := Q _ _ J',
              exact locl.join Hs₂₃ (r_trans _ _ _ Rx Rx') Ry₂₃ J₂₃
            }
          },
          { have Q := rDC _ _ _ _ _ Hs₂₃ J₂₃ (r_refl _) Ryx,
            cases Q with y₂₃' Q, cases Q with Ry₂₃' J',
            apply A.assoc J₁₂ (A.comm J'), intro a₁,
            apply A.assoc a₁.J₁ (A.comm a₁.J₂), intro s,
            have Hs : s.x ∈ S := SJC _ _ _ s.J₁ Hs₂₃ Hs₁₂,
            exact locl.join Hs Rx₁₂ (r_trans _ _ _ Ry₂₃' Ry₂₃) (A.comm s.J₂)
          }
        }
      }
    end

def locl.flat_trans {A : Alg.{ℓ}} (S : Set A) (r : Rel A A)
    (SJC : S.JoinClosed)
    (rUC : r.UpClosed)
    (rDC : r.DownClosed)
    (r_refl : r.Refl)
    (r_trans : r.Trans)
  : (locl S r).Trans
 := begin
      intros x₁ x₂ x₃ E₁₂ E₂₃,
      cases E₁₂ with   _ _ R₁₂  _ x₁₂ y₁₂ _ s₁₂ Hs₁₂ Rx₁₂ Ry₁₂ J₁₂ ; clear E₁₂,
      { cases E₂₃ with _ _ R₂₃  _ x₂₃ y₂₃ _ s₂₃ Hs₂₃ Rx₂₃ Ry₂₃ J₂₃ ; clear E₂₃,
        { apply locl.base,
          apply r_trans,
          repeat { assumption }
        },
        { exact locl.join Hs₂₃ (r_trans _ _ _ R₁₂ Rx₂₃) Ry₂₃ J₂₃ }
      },
      { cases E₂₃ with _ _ R₂₃  _ x₂₃ y₂₃ _ s₂₃ Hs₂₃ Rx₂₃ Ry₂₃ J₂₃ ; clear E₂₃,
        { exact locl.join Hs₁₂ Rx₁₂ (r_trans _ _ _ Ry₁₂ R₂₃) J₁₂ },
        { have Ryx : r y₁₂ x₂₃ := r_trans _ _ _ Ry₁₂ Rx₂₃,
          clear Ry₁₂ Rx₂₃,
          have Q := rUC J₁₂ Ryx,
          cases Q with n₁ Q, cases Q with n₂ Q,
          cases Q with Jn Q, cases Q with Rn₁ Rn₂,
          apply A.assoc (A.comm Jn) (A.comm J₂₃), intro a,
          have Q := rDC Rn₁ (r_refl _) a.J₁,
          cases Q with s₃ Q, cases Q with Rs₃ Js,
          have Hs₃ : s₃ ∈ S, from
            begin
              apply SJC _ _ _ Js,
              repeat { assumption }
            end,
          have Q := rDC Rn₂ Rs₃ a.J₂,
          cases Q with x₃' Q,
          cases Q with Rx₃' J,
          exact locl.join Hs₃ Rx₁₂ (r_trans _ _ _ Rx₃' Ry₂₃) (A.comm J)
        }
      }
    end

def locl.LocallyUpClosed {A : Alg.{ℓ}} (S : Set A) (r : Rel A A)
    {L : Set A}
    (HL : r.Fn L ⊆ L)
    (rUC : r.LocallyUpClosed L)
    (r_trans : r.Trans)
  : (locl S r).LocallyUpClosed L
 := begin
      intros x₁ x₂ x₃ y₃ Hx Jx L₃,
      cases L₃ with _ _ R  _ x y _ s Hs Rx Ry J ; clear L₃,
      { have Q := rUC _ _ _ _ Hx Jx R,
        cases Q with n₁ Q, cases Q with n₂ Q,
        cases Q with J' Q, cases Q with R₁ R₂,
        existsi n₁, existsi n₂,
        apply and.intro J',
        apply and.intro,
        repeat { apply locl.base, assumption }
      },
      { have Q := rUC _ _ _ _ Hx Jx Rx,
        cases Q with x₁' Q, cases Q with x₂' Q,
        cases Q with Jx' Q, cases Q with Rx₁' Rx₂',
        apply A.assoc Jx' (A.comm J), intro a₁,
        have Q := rUC _ _ _ _ (HL ⟨x₁, and.intro Hx Rx₁'⟩) a₁.J₂ Ry,
        cases Q with n₁ Q, cases Q with n₂ Q,
        cases Q with Jn Q, cases Q with Rn₁ Rn₂,
        existsi n₁, existsi n₂,
        apply and.intro Jn,
        apply and.intro,
        { apply locl.base, apply r_trans, repeat { assumption } },
        { exact locl.join Hs Rx₂' Rn₂ (A.comm a₁.J₁) }
      }
    end

def locl.UpClosed {A : Alg.{ℓ}} (S : Set A) (r : Rel A A)
    (rUC : r.UpClosed)
    (r_trans : r.Trans)
  : (locl S r).UpClosed
 := begin
      intros x₁ x₂ x₃ y₃ Jx R₃,
      cases R₃ with _ _ R  _ x y _ s Hs Rx Ry J ; clear R₃,
      { have Q := rUC Jx R,
        cases Q with n₁ Q, cases Q with n₂ Q,
        cases Q with J' Q, cases Q with R₁ R₂,
        existsi n₁, existsi n₂,
        apply and.intro J',
        apply and.intro,
        repeat { apply locl.base, assumption }
      },
      { have Q := rUC Jx Rx,
        cases Q with x₁' Q, cases Q with x₂' Q,
        cases Q with Jx' Q, cases Q with Rx₁' Rx₂',
        apply A.assoc Jx' (A.comm J), intro a₁,
        have Q := rUC a₁.J₂ Ry,
        cases Q with n₁ Q, cases Q with n₂ Q,
        cases Q with Jn Q, cases Q with Rn₁ Rn₂,
        existsi n₁, existsi n₂,
        apply and.intro Jn,
        apply and.intro,
        { apply locl.base, apply r_trans, repeat { assumption } },
        { exact locl.join Hs Rx₂' Rn₂ (A.comm a₁.J₁) }
      }
    end

def locl.LocallyDownClosed {A : Alg.{ℓ}} (S : Set A) (r : Rel A A)
    (SJC : S.JoinClosed)
    {L : Set A}
    (Lprime : L.Prime)
    (HL : r.FnInv L ⊆ L)
    (HLS : S ∩ L = ∅)
    (rDC : r.LocallyDownClosed L)
    (r_refl : r.Refl)
    (r_trans : r.Trans)
  : (locl S r).LocallyDownClosed L
 := begin
      intros p₁ p₂ q₁ q₂ q₃ Hp₁ Jb L₁ L₂,
      cases L₁ with _ _ R₁  _ x₁ y₁ _ s₁ Hs₁ Rx₁ Ry₁ J₁ ; clear L₁,
      { cases L₂ with _ _ R₂  _ x₂ y₂ _ s₂ Hs₂ Rx₂ Ry₂ J₂ ; clear L₂,
        { have Q := rDC _ _ _ _ _ Hp₁ Jb R₁ R₂,
          cases Q with n₃ Q, cases Q with R₃ Jx,
          existsi n₃,
          refine and.intro _ Jx,
          apply locl.base,
          assumption
        },
        { have Q := rDC _ _ _ _ _ Hp₁ Jb R₁ Ry₂,
          cases Q with b₃' Q,
          cases Q with Rb₃' Jb₃',
          apply A.assoc J₂ (A.comm Jb₃'), intro a,
          have Q := rDC _ _ _ _ _ (HL ⟨p₁, and.intro Hp₁ R₁⟩) (A.comm a.J₁) (r_refl _) Rx₂,
          cases Q with n₃ Q, cases Q with Rn₃ Jn₃,
          existsi n₃,
          refine and.intro _ Jn₃,
          exact locl.join Hs₂ Rn₃ Rb₃' a.J₂
        }
      },
      { cases L₂ with _ _ R₂  _ x₂ y₂ _ s₂ Hs₂ Rx₂ Ry₂ J₂ ; clear L₂,
        { have Q := rDC _ _ _ _ _ Hp₁ Jb Ry₁ R₂,
          cases Q with b₃' Q,
          cases Q with Rb₃' Jb₃',
          have Q := Lprime _ _ _ J₁ (HL ⟨p₁, and.intro Hp₁ Ry₁⟩),
          cases Q with HLs₁ HLx₁,
          { have Q : s₁ ∈ S ∩ L := and.intro Hs₁ HLs₁,
            rw HLS at Q,
            cases Q
          },
          { apply A.assoc J₁ Jb₃', intro a,
            have Q := rDC _ _ _ _ _ HLx₁ a.J₁ Rx₁ (r_refl _),
            cases Q with n₃ Q, cases Q with Rn₃ Jn₃,
            existsi n₃,
            refine and.intro _ Jn₃,
            exact locl.join Hs₁ Rn₃ Rb₃' a.J₂
          }
        },
        { have Q := rDC _ _ _ _ _ Hp₁ Jb Ry₁ Ry₂,
          cases Q with b₃' Q, cases Q with Rb₃' Jb₃',
          have Q := Lprime _ _ _ J₁ (HL ⟨p₁, and.intro Hp₁ Ry₁⟩),
          cases Q with HLs₁ HLx₁,
          { have Q : s₁ ∈ S ∩ L := and.intro Hs₁ HLs₁,
            rw HLS at Q,
            cases Q
          },
          { apply A.assoc J₁ Jb₃', intro a₁,
            apply A.assoc J₂ (A.comm a₁.J₁), intro a₂,
            have Q := rDC _ _ _ _ _ HLx₁ (A.comm a₂.J₁) Rx₁ Rx₂, clear Rx₁ Rx₂,
            cases Q with n₃ Q, cases Q with Rn₃ J,
            existsi n₃,
            refine and.intro _ J,
            apply A.assoc (A.comm a₂.J₂) (A.comm a₁.J₂), intro s,
            have Hs : s.x ∈ S, from
              begin
                apply SJC _ _ _ (A.comm s.J₁),
                repeat { assumption }
              end,
            exact locl.join Hs Rn₃ Rb₃' (A.comm s.J₂)
          }
        }
      }
    end

def locl.DownClosed {A : Alg.{ℓ}} (S : Set A) (r : Rel A A)
    (SJC : S.JoinClosed)
    (rDC : r.DownClosed)
    (r_refl : r.Refl)
    (r_trans : r.Trans)
  : (locl S r).DownClosed
 := begin
      intros p₁ p₂ q₁ q₂ q₃ L₁ L₂ Jb,
      cases L₁ with _ _ R₁  _ x₁ y₁ _ s₁ Hs₁ Rx₁ Ry₁ J₁ ; clear L₁,
      { cases L₂ with _ _ R₂  _ x₂ y₂ _ s₂ Hs₂ Rx₂ Ry₂ J₂ ; clear L₂,
        { have Q := rDC R₁ R₂ Jb,
          cases Q with n₃ Q, cases Q with R₃ Jx,
          existsi n₃,
          refine and.intro _ Jx,
          apply locl.base,
          assumption
        },
        { have Q := rDC R₁ Ry₂ Jb,
          cases Q with b₃' Q,
          cases Q with Rb₃' Jb₃',
          apply A.assoc J₂ (A.comm Jb₃'), intro a,
          have Q := rDC Rx₂ (r_refl _) a.J₁,
          cases Q with n₃ Q, cases Q with Rn₃ Jn₃,
          existsi n₃,
          refine and.intro _ (A.comm Jn₃),
          exact locl.join Hs₂ Rn₃ Rb₃' a.J₂
        }
      },
      { cases L₂ with _ _ R₂  _ x₂ y₂ _ s₂ Hs₂ Rx₂ Ry₂ J₂ ; clear L₂,
        { have Q := rDC Ry₁ R₂ Jb,
          cases Q with b₃' Q,
          cases Q with Rb₃' Jb₃',
          apply A.assoc J₁ Jb₃', intro a,
          have Q := rDC Rx₁ (r_refl _) a.J₁,
          cases Q with n₃ Q, cases Q with Rn₃ Jn₃,
          existsi n₃,
          refine and.intro _ Jn₃,
          exact locl.join Hs₁ Rn₃ Rb₃' a.J₂
        },
        { have Q := rDC Ry₁ Ry₂ Jb,
          cases Q with b₃' Q, cases Q with Rb₃' Jb₃', clear Ry₁ Ry₂ Jb,
          apply A.assoc J₁ Jb₃', intro a₁,
          apply A.assoc J₂ (A.comm a₁.J₁), intro a₂,
          have Q := rDC Rx₁ Rx₂ (A.comm a₂.J₁), clear Rx₁ Rx₂,
          cases Q with n₃ Q, cases Q with Rn₃ J,
          existsi n₃,
          refine and.intro _ J,
          apply A.assoc (A.comm a₂.J₂) (A.comm a₁.J₂), intro s,
          have Hs : s.x ∈ S, from
            begin
              apply SJC _ _ _ (A.comm s.J₁),
              repeat { assumption }
            end,
          exact locl.join Hs Rn₃ Rb₃' (A.comm s.J₂)
        }
      }
    end

end Localization

def OrdAlg.Localize (A : OrdAlg.{ℓ}) (AC : A.ord.Closed)
    (S : Set A.alg) (SJC : S.JoinClosed) (HS : A.ord.Local S)
  : OrdAlg.{ℓ}
 := { alg := A.alg
    , ord := Localization.locl S A.ord
    , refl := Localization.locl.refl A.refl
    , trans
       := begin
            apply Localization.locl.trans,
            { apply SJC },
            { cases AC with H H,
              { apply or.inl,
                apply and.intro HS,
                apply UpClosed.LocallyUpClosed,
                assumption
              },
              { apply or.inr,
                apply DownClosed.LocallyDownClosed,
                assumption
              }
            },
            { apply A.refl },
            { apply A.trans }
          end
    }

def OrdAlg.Localize.UpClosed (A : OrdAlg.{ℓ}) (AC : A.ord.UpClosed)
    (S : Set A.alg) (SJC : S.JoinClosed) (HS : A.ord.Local S)
  : (A.Localize (or.inl @AC) S SJC HS).ord.UpClosed
 := begin
      apply @Localization.locl.UpClosed,
      { exact @AC },
      { exact A.trans }
    end

def OrdAlg.Localize.DownClosed (A : OrdAlg.{ℓ}) (AC : A.ord.DownClosed)
    (S : Set A.alg) (SJC : S.JoinClosed) (HS : A.ord.Local S)
  : (A.Localize (or.inr @AC) S SJC HS).ord.DownClosed
 := begin
      apply @Localization.locl.DownClosed,
      { exact SJC },
      { exact @AC },
      { exact A.refl },
      { exact A.trans }
    end

end Sep
