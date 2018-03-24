
namespace set

universe ℓ

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

