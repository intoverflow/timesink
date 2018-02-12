/- Separation algebras
 -
 -/
import .basic

namespace Sep
universes ℓ₁ ℓ₂ ℓ₃ ℓ₄

/- Relations between separation algebras
 -
 -/
def Rel (A₁ : Alg.{ℓ₁}) (A₂ : Alg.{ℓ₂})
  := A₁.τ → Set A₂

-- An equivalence relation on relations; happens to imply equality but is easier to prove
def RelEq {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r₁ r₂ : Rel A₁ A₂) : Prop
  := ∀ x₁ x₂, r₁ x₁ x₂ ↔ r₂ x₁ x₂

def RelEq.refl {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : RelEq r r
  := λ x₁ x₂, by trivial

def RelEq.symm {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r₁ r₂ : Rel A₁ A₂}
    (H : RelEq r₁ r₂)
  : RelEq r₂ r₁
  := λ x₁ x₂, iff.symm (H _ _)

def RelEq.trans {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r₁ r₂ r₃ : Rel A₁ A₂}
    (H₁₂ : RelEq r₁ r₂) (H₂₃ : RelEq r₂ r₃)
  : RelEq r₁ r₃
  := λ x₁ x₂, iff.trans (H₁₂ _ _) (H₂₃ _ _)

def RelEq.to_eq {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r₁ r₂ : Rel A₁ A₂}
  : RelEq r₁ r₂ → r₁ = r₂
 := begin
      intro H,
      apply funext, intro x₁,
      apply funext, intro x₂,
      apply iff.to_eq,
      apply H
    end


-- Composition of relations
def Rel_comp {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {A₃ : Alg.{ℓ₃}}
  : Rel A₂ A₃ → Rel A₁ A₂ → Rel A₁ A₃
:= λ r₂ r₁ x₁ x₃
   , ∃ x₂, r₁ x₁ x₂ ∧ r₂ x₂ x₃

-- Composition is associative
def Rel_comp.assoc {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {A₃ : Alg.{ℓ₃}} {A₄ : Alg.{ℓ₄}}
    (r₃₄ : Rel A₃ A₄) (r₂₃ : Rel A₂ A₃) (r₁₂ : Rel A₁ A₂)
  : RelEq (Rel_comp (Rel_comp r₃₄ r₂₃) r₁₂) (Rel_comp r₃₄ (Rel_comp r₂₃ r₁₂))
 := λ x₁ x₄
    , iff.intro
        (λ H, begin
                cases H with x₂ H, cases H with H₁₂ H,
                cases H with x₃ H, cases H with H₂₃ H₃₄,
                existsi x₃, refine and.intro _ H₃₄,
                existsi x₂, exact and.intro H₁₂ H₂₃
              end)
        (λ H, begin
                cases H with x₃ H, cases H with H H₃₄,
                cases H with x₂ H, cases H with H₁₂ H₂₃,
                existsi x₂, apply and.intro H₁₂,
                existsi x₃, exact and.intro H₂₃ H₃₄
              end)

-- The function induced by a relation
def Rel.Fn {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂)
  : Set A₁ → Set A₂
:= λ X, λ y, ∃ x, X x ∧ f x y

def Rel.Fn.show {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {f : Rel A₁ A₂}
    {X : Set A₁} {y} (x) (Hx : x ∈ X) (Hf : f x y)
  : y ∈ f.Fn X
 := exists.intro x (and.intro Hx Hf)

def Rel.Fn.elim {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {f : Rel A₁ A₂}
    {X : Set A₁} {y} (H : y ∈ f.Fn X)
    {P : Prop}
    (C : ∀ {x}, x ∈ X → f x y → P)
  : P
 := begin cases H with x H, exact C H.1 H.2 end

def Rel.Fn.subset {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂)
  : ∀ (X₁ X₂ : Set A₁)
    , X₁ ⊆ X₂ → f.Fn X₁ ⊆ f.Fn X₂
 := λ X₁ X₂ H y Hy
    , begin
        cases Hy with x Hx,
        existsi x,
        exact and.intro (H Hx.1) Hx.2
      end


-- The inverse image of the function induced by a relation
def Rel.FnInv {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Set A₂ → Set A₁
 := λ Y x, (∃ y, y ∈ Y ∧ r x y)

def Rel.FnInv.show {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {f : Rel A₁ A₂}
    {Y : Set A₂} {x} {y} (Hxy : f x y) (Hy : y ∈ Y)
  : x ∈ f.FnInv Y
:= exists.intro y (and.intro Hy Hxy)

def Rel.FnInv.elim {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    {Y : Set A₂} {x} (Hx : x ∈ r.FnInv Y)
    {P : Prop}
  : (∀ y, y ∈ Y → r x y → P)
  → P
 := begin
      intro C,
      { cases Hx with y Hy,
        exact C y Hy.1 Hy.2
      }
    end

def Rel.FnInv.subset {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : ∀ (Y₁ Y₂ : Set A₂)
    , Y₁ ⊆ Y₂ → r.FnInv Y₁ ⊆ r.FnInv Y₂
 := λ Y₁ Y₂ HYY x Hx
    , begin
        apply Rel.FnInv.elim Hx,
        { intros y Hy Rxy,
          apply Rel.FnInv.show Rxy (HYY Hy)        }
      end


-- The kernel of the function induced by a relation
def Rel.Kern {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Set A₁
 := λ x, ∀ y, ¬ r x y

def Rel.KernIdeal {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {x₁ x₃}
    , A₁.Divides x₁ x₃
    → (∀ y₁, ¬ r x₁ y₁)
    → (∀ y₃, ¬ r x₃ y₃)

def Rel.FnKernIdeal {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
  := r.Kern.Ideal

def Rel.FnKernIdeal_iff {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : r.FnKernIdeal ↔ r.KernIdeal
 := begin
      apply iff.intro,
      { intro rLinear,
        intros x₁ x₃ Dx₁x₃ Kx₁ y₃ Rx₃y₃,
        apply Dx₁x₃, clear Dx₁x₃, intros x₂ Jx,
        apply rLinear Kx₁ Jx,
        assumption
      },
      { intro rLinear,
        intros x₁ x₂ x₃ Kx₁ Jx y₃ Rx₃y₃,
        refine rLinear _ Kx₁ _ Rx₃y₃,
        intros P C, exact C Jx
      }
    end


def Rel.KernPrime {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {x₁ x₂ x₃}
    , A₁.join x₁ x₂ x₃
    → (∀ y₃, ¬ r x₃ y₃)
    → (∀ y₁, ¬ r x₁ y₁) ∨ (∀ y₂, ¬ r x₂ y₂)

def Rel.FnKernPrime {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
  := r.Kern.Prime

def Rel.FnKernPrime_iff {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : r.FnKernPrime ↔ r.KernPrime
 := begin
      apply iff.intro,
      { intro rKP,
        intros x₁ x₂ x₃ Jx Kx₃,
        exact rKP Jx Kx₃
      },
      { intro rKP,
        intros x₁ x₂ x₃ Jx Kx₃,
        exact rKP Jx Kx₃
      }
    end


-- Downwards, (quasi)-upwards, and quasi-closure
def Rel.DownClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂) : Prop
  := ∀ {n₁ n₂} {m₁ m₂ m₃}
     , f n₁ m₁ → f n₂ m₂ → A₂.join m₁ m₂ m₃
     → ∃ n₃, f n₃ m₃ ∧ A₁.join n₁ n₂ n₃

def Rel.FnDownClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂) : Prop
  := ∀ (X₁ X₂ : Set A₁)
     , (f.Fn X₁ <*> f.Fn X₂) ⊆ f.Fn (X₁ <*> X₂)

def Rel.DownClosed_iff {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂)
  : f.FnDownClosed ↔ f.DownClosed
 := begin
      apply iff.intro,
      { intros H_dc n₁ n₂ fn₁ fn₂ m₃ Hfn₁ Hfn₂ HJ,
        apply Rel.Fn.elim
          (H_dc (eq n₁) (eq n₂)
                (Alg.Join.show (Rel.Fn.show _ rfl Hfn₁)
                               (Rel.Fn.show _ rfl Hfn₂)
                               HJ)),
        intros fx H' Hfx,
        existsi fx,
        apply and.intro Hfx,
        apply Alg.Join.elim H', clear H',
        intros x₁' x₂' Hx₁' Hx₂' HJ',
        subst Hx₁', subst Hx₂', assumption
      },
      { intros H_dc X₁ X₂ y Hy,
        apply Alg.Join.elim Hy, clear Hy,
        intros y₁ y₂ Hy₁ Hy₂ HJy,
        apply Rel.Fn.elim Hy₁, intros x₁ Hx₁ Hx₁y₁, clear Hy₁,
        apply Rel.Fn.elim Hy₂, intros x₂ Hx₂ Hx₂y₂, clear Hy₂,
        cases (H_dc Hx₁y₁ Hx₂y₂ HJy) with x H', cases H' with Hxy HJx,
        exact Rel.Fn.show x (Alg.Join.show Hx₁ Hx₂ HJx) Hxy
      }
    end


def Rel.QuasiUpClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {x₁ x₂ x₃} {y₃}
    , A₁.join x₁ x₂ x₃
    → ¬ x₁ ∈ r.Kern → ¬ x₂ ∈ r.Kern → r x₃ y₃
    → ∃ y₁' y₂', A₂.join y₁' y₂' y₃ ∧ r x₁ y₁' ∧ r x₂ y₂'

def Rel.UpClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂) : Prop
  := ∀ {m₁ m₂ m₃} {n₃}
     , A₁.join m₁ m₂ m₃ → f m₃ n₃
     → ∃ n₁ n₂, A₂.join n₁ n₂ n₃ ∧ f m₁ n₁ ∧ f m₂ n₂

def Rel.FnUpClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂) : Prop
  := ∀ (X₁ X₂ : Set A₁)
     , f.Fn (X₁ <*> X₂) ⊆ (f.Fn X₁ <*> f.Fn X₂)

def Rel.UpClosed_iff {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂)
  : f.FnUpClosed ↔ f.UpClosed
 := begin
      apply iff.intro,
      { intros H_uc m₁ m₂ m₃ n₃ HJm Hm₃n₃, 
        apply Alg.Join.elim
          (H_uc (eq m₁) (eq m₂)
                (Rel.Fn.show m₃ (Alg.Join.show rfl rfl HJm) Hm₃n₃)),
        intros n₁ n₂ Hn₁ Hn₂ HJn,
        existsi n₁, existsi n₂,
        apply and.intro HJn,
        apply Rel.Fn.elim Hn₁, intros m₁' Hm₁' Hm₁n₁, have Q : m₁ = m₁' := Hm₁', subst Q,
        apply Rel.Fn.elim Hn₂, intros m₂' Hm₂' Hm₂n₂, have Q : m₂ = m₂' := Hm₂', subst Q,
        exact and.intro Hm₁n₁ Hm₂n₂
      },
      { intros H_uc X₁ X₂ y Hy,
        apply Rel.Fn.elim Hy, clear Hy,
        intros x Hx Hxy,
        apply Alg.Join.elim Hx, clear Hx,
        intros x₁ x₂ Hx₁ Hx₂ HJx,
        cases (H_uc HJx Hxy) with y₁ H, cases H with y₂ H,
        exact Alg.Join.show (Rel.Fn.show x₁ Hx₁ H.2.1) (Rel.Fn.show x₂ Hx₂ H.2.2) H.1
      }
    end

def Rel.UpClosed_iff' {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : r.UpClosed ↔ r.KernIdeal ∧ r.QuasiUpClosed
 := begin
      apply iff.intro,
      { intro rUC,
        apply and.intro,
        { intros x₁ x₃ Dx₁x₃ Kx₁ y₃ Rx₃y₃,
          apply Dx₁x₃, intros x₂ Jx,
          cases rUC Jx Rx₃y₃ with y₁ Hy,
          cases Hy with y₂ Hy,
          exact Kx₁ _ Hy.2.1
        },
        { intros x₁ x₂ x₃ y₃ Jx Kx₁ Kx₂ Rx₃y₃,
          exact rUC Jx Rx₃y₃
        }
      },
      { intro rH, cases rH with rKI rL,
        intros m₁ m₂ m₃ n₃ Jm Rn₃m₃,
        have Km₁ : ¬ m₁ ∈ r.Kern, from
          begin
            intro H,
            have Q : m₃ ∈ r.Kern := rKI (λ P C, C Jm) @H,
            exact Q _ Rn₃m₃
          end,
        have Km₂ : ¬ m₂ ∈ r.Kern, from
          begin
            intro H,
            have Q : m₃ ∈ r.Kern := rKI (λ P C, C (A₁.comm Jm)) @H,
            exact Q _ Rn₃m₃
          end,
        apply rL Jm Km₁ Km₂ Rn₃m₃
      }
    end


def Rel.QuasiClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂) : Prop
 := ∀ {a₁ a₂ a₁₂} {fa₁₂ b₁ b₂ b₁₂}
      (Ha : A₁.join a₁ a₂ a₁₂) (Hfa₁₂ : f a₁₂ fa₁₂)
      (Ha₁b₁ : f a₁ b₁) (Ha₂b₂ : f a₂ b₂) (Hb : A₂.join b₁ b₂ b₁₂)
    , ∃ y a₁₂' b₁' b₂'
      , f a₁ b₁' ∧ f a₂ b₂'
      ∧ A₁.join a₁ a₂ a₁₂' ∧ f a₁₂' y ∧ A₂.join b₁' b₂' y

def Rel.FnQuasiClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂) : Prop
  := ∀ (X₁ X₂ : Set A₁)
     , Set.nonempty (f.Fn (X₁ <*> X₂))
     → Set.nonempty (f.Fn X₁ <*> f.Fn X₂)
     → Set.nonempty (f.Fn (X₁ <*> X₂) ∩ (f.Fn X₁ <*> f.Fn X₂))

-- note that the converse does not appear to be true.
def Rel.QuasiClosed_if {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂)
  : f.FnQuasiClosed → f.QuasiClosed
 := begin
      intros H_qc a₁ a₂ a₁₂ fa₁₂ b₁ b₂ b₁₂ Ha Hfa₁₂ Ha₁b₁ Ha₂b₂ Hb,
      refine exists.elim (H_qc (eq a₁) (eq a₂)
                            (exists.intro fa₁₂
                              (Rel.Fn.show a₁₂ (Alg.Join.show rfl rfl Ha) Hfa₁₂))
                            (exists.intro b₁₂
                              (Alg.Join.show
                                (Rel.Fn.show a₁ rfl Ha₁b₁)
                                (Rel.Fn.show a₂ rfl Ha₂b₂)
                                Hb))) _,
      intros y Hy,
      cases Hy with Hy₁ Hy₂,
      apply Rel.Fn.elim Hy₁, clear Hy₁,
      intros a₁₂' Ha₁₂' Ha₁₂y,
      apply Alg.Join.elim Hy₂, clear Hy₂,
      intros b₁' b₂' Hb₁' Hb₂' HJb,
      apply Rel.Fn.elim Hb₁', clear Hb₁', intros a₁' Ha₁' Hfa₁b₁', have Q : a₁ = a₁' := Ha₁', subst Q,
      apply Rel.Fn.elim Hb₂', clear Hb₂', intros a₂' Ha₂' Hfa₂b₂', have Q : a₂ = a₂' := Ha₂', subst Q,
      apply Alg.Join.elim Ha₁₂',
      intros a₁' a₂' Ha₁' Ha₂' HJa, subst Ha₁', subst Ha₂',
      existsi y, existsi a₁₂', existsi b₁', existsi b₂',
      repeat {try {assumption}, apply and.intro, assumption },
      assumption
    end


def Rel.IdealPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
  := ∀ {x₁ x₂ x₃} {y₁}
     , A₁.join x₁ x₂ x₃ → r x₁ y₁
     → (r x₃ y₁) ∨ (∃ y₂ y₃, r x₃ y₃ ∧ A₂.join y₁ y₂ y₃)

def IdealPres.KernPrime {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rIP : r.IdealPres)
  : r.KernPrime
 := begin
      intros x₁ x₂ x₃ Jx Kx₃,
      apply or.inl, intros y₁ Rx₁y₁,
      cases rIP Jx Rx₁y₁ with Rx₃y₁ Hy,
      { exact Kx₃ _ Rx₃y₁ },
      { cases Hy with y₂ Hy,
        cases Hy with y₃ Hy,
        exact Kx₃ _ Hy.1
      }
    end

def Rel.FnIdealPres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
  := ∀ {I : Set A₂} (Iideal : I.Ideal)
     , (r.FnInv I).Ideal

def Rel.IdealPres_iff {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  : r.FnIdealPres ↔ r.IdealPres
 := begin
      apply iff.intro,
      { intro rIP,
        intros x₁ x₂ x₃ y₁ Jx Rx₁y₁,
        have Q₀ : x₁ ∈ Rel.FnInv r (Alg.GenIdeal₁ A₂ y₁), from
          begin
            existsi y₁,
            apply and.intro,
            {apply GenIdeal₁.mem},
            {assumption}
          end,
        have Q := rIP (@GenIdeal₁.Ideal _ y₁) Q₀ Jx,
        cases Q with y₃ Hy₃,
        cases Hy₃ with Hy₃₁ Rx₃y₃,
        cases Hy₃₁ with E Hy₁,
        { subst E, apply or.inl, assumption },
        { cases Hy₁ with y₁' Hy₁',
          cases Hy₁' with Dy₁y₃ E,
          subst E,
          apply or.inr,
          apply Dy₁y₃,
          intros y₂ Jy,
          existsi y₂, existsi y₃,
          apply and.intro,
          repeat { assumption }
        }
      },
      { intro rIP,
        intros I Iideal,
        intros x₁ x₂ x₃ Hx₁ Hx,
        apply Rel.FnInv.elim Hx₁,
        intros y₁ Iy₁ Rx₁y₁,
        cases rIP Hx Rx₁y₁ with Rx₃y₁ Hy,
        { existsi y₁, apply and.intro, repeat {assumption}
        },
        { cases Hy with y₂ Hy, cases Hy with y₃ Hy,
          exact Rel.FnInv.show Hy.1 (Iideal Iy₁ Hy.2)
        }
      }
    end


def DownClosed.QuasiClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (f : Rel A₁ A₂)
  : f.DownClosed → f.QuasiClosed
 := λ H a₁ a₂ a₁₂ fa₁₂ b₁ b₂ b₁₂ Ha Hfa₁₂ Ha₁b₁ Ha₂b₂ Hb
    , begin
        apply exists.elim (H Ha₁b₁ Ha₂b₂ Hb),
        intros x Hx, cases Hx with Hx₁ Hx₂,
        existsi b₁₂, existsi x, existsi b₁, existsi b₂,
        repeat {try {assumption}, apply and.intro, assumption },
        assumption
      end

def UpClosed.QuasiClosed {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  : r.UpClosed → r.QuasiClosed
 := λ H a₁ a₂ a₁₂ fa₁₂ b₁ b₂ b₁₂ Ha Hfa₁₂ Ha₁b₁ Ha₂b₂ Hb
    , begin
        apply exists.elim (H Ha Hfa₁₂),
        intros y₁ Hy,
        cases Hy with y₂ Hy,
        cases Hy with Hy₁ Hy, cases Hy with Hy₂ H₃,
        existsi fa₁₂, existsi a₁₂, existsi y₁, existsi y₂,
        repeat {try {assumption}, apply and.intro, assumption },
        assumption
      end


-- Preservation of prime sets
def Rel.PrimePres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
 := ∀ {p : Set A₂} (pPrime : p.Prime)
      {x₁ x₂ x₃} {y₃}
      (Jx : x₃ ∈ A₁.join x₁ x₂)
      (Rx₃y₃ : r x₃ y₃)
      (Py₃ : y₃ ∈ p)
    , (∃ y₁, r x₁ y₁ ∧ y₁ ∈ p) ∨ (∃ y₂, r x₂ y₂ ∧ y₂ ∈ p)

def Rel.FnPrimePres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂) : Prop
  := ∀ {p : Set A₂} (pPrime : p.Prime)
     , (r.FnInv p).Prime

def Rel.PrimePres_iff {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : r.FnPrimePres ↔ r.PrimePres
 := begin
      apply iff.intro,
      { intro rPP,
        intros p pPrime x₁ x₂ x₃ y₃ Jx Rx₃y₃ Py₃,
        have Px₃ : x₃ ∈ r.FnInv p := Rel.FnInv.show Rx₃y₃ Py₃,
        cases rPP @pPrime Jx Px₃ with H H,
        { apply Rel.FnInv.elim H,
          intros y₁ Py₁ Rx₁y₁,
          apply or.inl, existsi y₁,
          apply and.intro, repeat {assumption}
        },
        { apply Rel.FnInv.elim H,
          intros y₂ Py₂ Rx₂y₂,
          apply or.inr, existsi y₂,
          apply and.intro, repeat {assumption}
        }
      },
      { intro rPP,
        intros p pPrime x₁ x₂ x₃ Jx Px₃,
        apply Rel.FnInv.elim Px₃,
        intros y₃ Py₃ Rx₃y₃,
        cases rPP @pPrime Jx Rx₃y₃ Py₃ with H H,
        { cases H with y₁ Hy₁,
          apply or.inl,
          exact Rel.FnInv.show Hy₁.1 Hy₁.2
        },
        { cases H with y₂ Hy₂,
          apply or.inr,
          exact Rel.FnInv.show Hy₂.1 Hy₂.2
        }
      }
    end

def UpClosed.PrimePres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  (rUC : r.UpClosed)
  : r.FnPrimePres
 := begin
      intros p pPrime,
      intros x₁ x₂ x₃ Jx Px₃,
      apply Rel.FnInv.elim Px₃,
      intros y₃ Py₃ Rx₃y₃,
      cases rUC Jx Rx₃y₃ with n₁ Hn,
      cases Hn with n₂ Hn,
      cases pPrime Hn.1 Py₃ with H H,
      { exact or.inl (Rel.FnInv.show Hn.2.1 H) },
      { exact or.inr (Rel.FnInv.show Hn.2.2 H) }
    end


/- Summary: we want UpClosed
 -
 -/

structure Hom (A₁ : Alg.{ℓ₁}) (A₂ : Alg.{ℓ₂})
 := (r : Rel A₁ A₂)
    (UpClosed : r.UpClosed)

def Hom.PrimePres {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}}
    (F : Hom A₁ A₂)
  : F.r.FnPrimePres
:= @UpClosed.PrimePres _ _ _ F.UpClosed

def Hom.KernIdeal {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}}
    (F : Hom A₁ A₂)
  : F.r.KernIdeal
 := (F.r.UpClosed_iff'.elim_left F.UpClosed).1

end Sep
