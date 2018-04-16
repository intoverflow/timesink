
universes ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄

namespace set

def sInter {A : Type.{ℓ}} : set (set A) → set A
 := λ X a, ∀ X₀ ∈ X, a ∈ X₀

def in_append {A : Type.{ℓ}} {L₁ L₂ : list A}
  : ∀ {x}, x ∈ list.append L₁ L₂ → x ∈ L₁ ∨ x ∈ L₂
 := begin
      intros x Hx,
      induction L₁ with l₁ L₁,
      { induction L₂ with l₂ L₂,
        { exact false.elim Hx },
        { exact or.inr Hx }
      },
      { cases Hx with E Hx,
        { subst E, exact or.inl (or.inl rfl) },
        { cases ih_1 Hx with Q Q,
          { clear Hx, exact or.inl (or.inr Q) },
          { clear Hx, exact or.inr Q }
        }
      }
    end

def in_append_left {A : Type.{ℓ}} {L₁ L₂ : list A}
  : ∀ {x}, x ∈ L₁ → x ∈ list.append L₁ L₂
 := begin
      intros x Hx,
      induction L₁ with l₁ L₁,
      { exact false.elim Hx },
      { cases Hx with E Hx,
        { exact or.inl E },
        { exact or.inr (ih_1 Hx) }
      }
    end

def in_append_right {A : Type.{ℓ}} {L₁ L₂ : list A}
  : ∀ {x}, x ∈ L₂ → x ∈ list.append L₁ L₂
 := begin
      intros x Hx,
      induction L₁ with l₁ L₁,
      { exact Hx },
      { exact or.inr ih_1 }
    end

end set


namespace list

def elem_map {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B}
    {aa : list A} {b : B}
    (H : b ∈ list.map f aa)
  : ∃ a, b = f a ∧ a ∈ aa
 := begin
      induction aa with a aa,
      { exact false.elim H },
      { cases H with H H,
        { existsi a, apply and.intro H, apply or.inl rfl },
        { cases ih_1 H with a' Ha',
          clear H ih_1,
          existsi a',
          exact and.intro Ha'.1 (or.inr Ha'.2),
        }
      }
    end

end list


namespace quotient

universes u₁ u₂ u₃ u₄

def lift₃ {α : Sort u₁} {β : Sort u₂} {γ : Sort u₃} {φ : Sort u₄}
    [s₁ : setoid α] [s₂ : setoid β] [s₃ : setoid γ]
    (f : α → β → γ → φ)
    (c : ∀ a₁ a₂ a₃ b₁ b₂ b₃
         , a₁ ≈ b₁ → a₂ ≈ b₂ → a₃ ≈ b₃
         → f a₁ a₂ a₃ = f b₁ b₂ b₃)
    (q₁ : quotient s₁) (q₂ : quotient s₂) (q₃ : quotient s₃)
  : φ
 := quotient.lift
      (λ (a₁ : α)
        , quotient.lift
            (λ (a₂ : β)
              , quotient.lift
                  (f a₁ a₂)
                  (λ (a b : γ), c a₁ a₂ a a₁ a₂ b (setoid.refl _) (setoid.refl _))
                  q₃)
            (λ (a b : β) (h : a ≈ b)
              , quotient.ind
                  (λ (a' : γ), c a₁ a a' a₁ b a' (setoid.refl _) h (setoid.refl _))
                q₃)
            q₂)
      (λ (a b : α) (h : a ≈ b)
        , quotient.ind
            (λ (a' : β)
              , quotient.ind
                  (λ (a'' : γ), c a a' a'' b a' a'' h (setoid.refl _) (setoid.refl _))
                  q₃)
            q₂)
      q₁

end quotient
