/- Donwards and upwards closure
 -
 -/
import .rel

namespace Sep
universes ℓ₁ ℓ₂


namespace DownCl

inductive τ {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : Type (max ℓ₁ ℓ₂)
| base : A₁.τ → τ
| cl : ∀ {m₁ m₂ m₃} (Jm : m₃ ∈ A₂.join m₁ m₂) (n₁ n₂ : τ), τ

inductive rel {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
  : τ r → A₂.τ → Prop
| base : ∀ {x} {y}, r x y → rel (τ.base r x) y
| cl : ∀ {m₁ m₂ m₃} (Jm : m₃ ∈ A₂.join m₁ m₂) (n₁ n₂ : τ r)
       , rel (τ.cl Jm n₁ n₂) m₃

def rel.elim {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    {t : τ r} {rt} (R : rel t rt)
    {P : Prop}
    (Cbase : ∀ {x} {y}
             , r x y
             → t = τ.base r x
             → rt = y
             → P)
    (Ccl : ∀ {m₁ m₂ m₃} (Jm : m₃ ∈ A₂.join m₁ m₂)
             (n₁ n₂ : τ r)
           , t = τ.cl Jm n₁ n₂
           → rt = m₃
           → P)
  : P
 := begin
      cases R,
      { apply Cbase, assumption, repeat {trivial} },
      { apply Ccl, repeat {trivial} }
    end

inductive valid {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : τ r → Prop
| base : ∀ {x}, valid (τ.base r x)
| cl : ∀ {m₁ m₂ m₃} (Jm : m₃ ∈ A₂.join m₁ m₂)
         {n₁ n₂ : τ r} (R₁ : rel n₁ m₁) (R₂ : rel n₂ m₂)
       , valid (τ.cl Jm n₁ n₂)

inductive join {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} (r : Rel A₁ A₂)
  : {k // valid r k} → {k // valid r k} → {k // valid r k} → Prop
| base : ∀ {n₁ n₂ n₃}
         , A₁.join n₁ n₂ n₃
         → join { val := τ.base r n₁, property := valid.base r }
                { val := τ.base r n₂, property := valid.base r }
                { val := τ.base r n₃, property := valid.base r }
| cl : ∀ {m₁' m₂' m₁ m₂ m₃}
         (n₁ n₂ n₃₁ n₃₂ : {k // valid r k})
         (Jm : m₃ ∈ A₂.join m₁ m₂)
         (Jm' : m₃ ∈ A₂.join m₁' m₂')
         (V₃ : valid r (τ.cl Jm n₃₁ n₃₂))
         (R₁ : rel n₁.val m₁') (R₂ : rel n₂.val m₂')
       , join n₁ n₂ { val := τ.cl Jm n₃₁ n₃₂, property := V₃ }

def join.elim {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    {x₁ x₂ x₃} (Jn : join r x₁ x₂ x₃)
    {P : Prop}
    (Cbase : ∀ {n₁ n₂ n₃}
               (Jn : A₁.join n₁ n₂ n₃)
               (E₁ : x₁ = { val := τ.base r n₁
                          , property := valid.base r })
               (E₂ : x₂ = { val := τ.base r n₂
                          , property := valid.base r })
               (E₃ : x₃ = { val := τ.base r n₃
                          , property := valid.base r })
             , P)
    (Ccl : ∀ {m₁' m₂' m₁ m₂ m₃}
             (n₃₁ n₃₂ : {k // valid r k})
             (Jm : m₃ ∈ A₂.join m₁ m₂)
             (Jm' : m₃ ∈ A₂.join m₁' m₂')
             (V₃ : valid r (τ.cl Jm n₃₁ n₃₂))
             (R₁ : rel x₁.val m₁') (R₂ : rel x₂.val m₂')
             (E : x₃ = { val := τ.cl Jm n₃₁ n₃₂, property := V₃ })
           , P)
  : P
 := begin
      cases Jn,
      { apply Cbase, repeat { assumption }, repeat { trivial } },
      { apply Ccl _ _ Jm Jm', repeat { assumption }, repeat { trivial } }
    end

def join.comm {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    {t₁ t₂ t₃} (J : join r t₁ t₂ t₃)
  : join r t₂ t₁ t₃
 := begin
      cases J,
      { constructor, apply A₁.comm, assumption },
      { constructor, apply A₂.comm Jm', repeat {assumption} }
    end

def join.assoc {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rUC : r.UpClosed)
  : IsAssoc (join r)
 := begin
      intros c₁ c₂ c₃ c₁c₂ c₁c₂c₃ H₁ H₂ P C,
      apply join.elim H₁,
      { intros n₁₁ n₁₂ n₁₃ Jn₁ E₁₁ E₁₂ E₁₃,
        subst E₁₁, subst E₁₂, subst E₁₃,
        apply join.elim H₂,
        { intros n₂₁ n₂₂ n₂₃ Jn₂ E₂₁ E₂₂ E₂₃,
          injection E₂₁ with E₂₁', clear E₂₁,
          injection E₂₁' with E₂₁'', clear E₂₁',
          subst E₂₁'', subst E₂₂, subst E₂₃,
          apply A₁.assoc Jn₁ Jn₂,
          intro a,
          exact C { x := { val := τ.base r a.x, property := valid.base r }
                  , J₁ := join.base r a.J₁
                  , J₂ := join.base r a.J₂
                  }
        },
        { intros m₂₁' m₂₂' m₂₁ m₂₂ m₂₃ n₂₃₁ n₂₃₂ Jm₂ Jm₂' V₂₃ R₂₁ R₂₂ E,
          subst E,
          have Hy := rUC Jn₁ begin cases R₂₁, assumption end,
          cases Hy with y₁ Hy, cases Hy with y₂ Hy,
          apply A₂.assoc Hy.1 Jm₂', intro a,
          let t : {k // valid r k}
               := { val := τ.base r n₁₂
                  , property := valid.base r
                  },
          refine C  { x := { val := τ.cl a.J₁ t c₃
                           , property := _
                           }
                    , J₁ := _
                    , J₂ := _
                    },
          { constructor, constructor, exact Hy.2.2, assumption },
          { constructor, exact a.J₁, constructor, exact Hy.2.2, assumption },
          { constructor, exact a.J₂, constructor, exact Hy.2.1, constructor }
        }
      },
      { intros m₁₁' m₁₂' m₁₁ m₁₂ m₁₃ n₁₃₁ n₁₃₂ Jm₁ Jm₁' V₁₃ R₁₁ R₁₂ E,
        subst E,
        apply join.elim H₂,
        { intros n₂₁ n₂₂ n₂₃ Jn₂ E₂₁ E₂₂ E₂₃, cases E₂₁ },
        { intros m₂₁' m₂₂' m₂₁ m₂₂ m₂₃ n₂₃₁ n₂₃₂ Jm₂ Jm₂' V₂₃ R₂₁ R₂₂ E,
          subst E,

          apply rel.elim R₂₁,
          { intros x y R E₁ E₂, cases E₁ },
          intros m₁ m₂ m₃ Jm n₁ n₂ E₁ E₂,
          injection E₁ with E'₁ E'₂ E'₃ E'₄ E'₅, clear E₁,
          subst E'₁, subst E'₂, subst E'₃, subst E'₄, subst E'₅,
          subst E₂,

          apply A₂.assoc Jm₁' Jm₂', intro a,
          refine C  { x := { val := τ.cl a.J₁ c₂ c₃
                           , property := _
                           }
                    , J₁ := _
                    , J₂ := _
                    },
          { constructor, repeat {assumption} },
          { constructor, exact a.J₁, repeat {assumption} },
          { constructor, exact a.J₂, repeat {assumption}, constructor }
        }
      }
    end

def Alg {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rUC : r.UpClosed)
  : Alg
 := { τ := { k // valid r k }
    , join := join r
    , comm := @join.comm _ _ r
    , assoc := @join.assoc _ _ _ @rUC
    }

def Rel {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Rel A₁ A₂}
    (rUC : r.UpClosed)
  : Rel (Alg @rUC) A₂
 := λ x, rel x.val

def Rel.DownClosed {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
  : (Rel @rUC).DownClosed
 := begin
      intros n₁ n₂ m₁ m₂ m₃ R₁ R₂ Jm,
      refine exists.intro
              { val := τ.cl Jm n₁.val n₂.val
              , property := valid.cl Jm R₁ R₂
              }
              _,
      apply and.intro,
      { constructor },
      { constructor, repeat {assumption} }
    end

def Rel.UpClosed {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
  : (Rel @rUC).UpClosed
 := begin
      intros m₁ m₂ m₃ n₃ Jm R,
      apply join.elim Jm,
      { intros x₁ x₂ x₃ Jn E₁ E₂ E₃,
        subst E₁, subst E₂, subst E₃,
        apply rel.elim R,
        { intros x y Rxy E₁ E₂,
          injection E₁ with E₁', clear E₁,
          subst E₁', subst E₂,
          have Hy := rUC Jn Rxy,
          cases Hy with y₁ Hy,
          cases Hy with y₂ Hy,
          existsi y₁, existsi y₂,
          apply and.intro Hy.1,
          apply and.intro,
          { constructor, exact Hy.2.1 },
          { constructor, exact Hy.2.2 }
        },
        { intros y₁ y₂ y₃ Jy x₁ x₂ E₁ E₂,
          cases E₁ }
      },
      { intros y₁' y₂' y₁ y₂ y₃ x₃₁ x₃₂ Jy Jy' V₃ R₁ R₂ E,
        subst E,
        apply rel.elim R,
        { intros x y Rxy E₁ E₂, cases E₁ },
        { intros z₁ z₂ z₃ Jz w₁ w₂ E₁ E₂,
          injection E₁ with E₁' E₂' E₃' E₄' E₅', clear E₁,
          subst E₁', subst E₂', subst E₃', subst E₄', subst E₅',
          subst E₂,
          existsi y₁', existsi y₂',
          apply and.intro Jy',
          apply and.intro,
          { assumption },
          { assumption }
        }
      }
    end

inductive From {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
  : Sep.Rel (Alg @rUC) A₁
| base : ∀ x, From { val := τ.base r x, property := valid.base r } x

def From.DownClosed {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
  : (From @rUC).DownClosed
 := begin
      intros n₁ n₂ m₁ m₂ m₃ R₁ R₂ Jm,
      let t : { k // valid r k }
            := { val := τ.base r m₃, property := valid.base r },
      existsi t,
      cases R₁,
      cases R₂,
      apply and.intro,
      { constructor },
      { constructor, assumption }
    end

def From.UpClosed {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
  : (From @rUC).UpClosed
 := begin
      intros m₁ m₂ m₃ n₃ Jm R₃,
      cases R₃,
      apply join.elim Jm,
      { intros x₁ x₂ x₃ Jx E₁ E₂ E₃,
        subst E₁, subst E₂,
        injection E₃ with E₃', clear E₃,
        injection E₃' with E₃'', clear E₃',
        subst E₃'',
        existsi x₁, existsi x₂,
        apply and.intro Jx,
        apply and.intro,
        repeat { constructor }
      },
      { intros, cases E }
    end


inductive To {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
  : Sep.Rel A₁ (Alg @rUC)
| base : ∀ x, To x { val := τ.base r x, property := valid.base r }

def To.elim {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    {rUC : r.UpClosed}
    {x} {y} (Txy : To @rUC x y)
    {P : Prop}
    (C : y = { val := τ.base r x, property := valid.base r } → P)
  : P
 := begin
      cases Txy,
      exact C rfl
    end

def To.UpClosed {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
  : (To @rUC).UpClosed
 := begin
      intros m₁ m₂ m₃ n₃ Jm R₃,
      let t₁ : (Alg @rUC).τ := { val := τ.base r m₁, property := valid.base r },
      let t₂ : (Alg @rUC).τ := { val := τ.base r m₂, property := valid.base r },
      existsi t₁, existsi t₂,
      apply and.intro,
      { cases R₃, constructor, assumption },
      apply and.intro,
      repeat { constructor }
    end

def To.NotDownClosed {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
  : (To @rUC).DownClosed → r.DownClosed
 := begin
      intro tDC,
      intros n₁ n₂ m₁ m₂ m₃ Rn₁m₁ Rn₂m₂ Jm,
      let base_n₁ : { k // valid r k }
                  := { val := τ.base r n₁, property := valid.base r },
      let base_n₂ : { k // valid r k }
                  := { val := τ.base r n₂, property := valid.base r },
      have RB₁ := rel.base Rn₁m₁,
      have RB₂ := rel.base Rn₂m₂,
      let cl_m₃ : { k // valid r k }
                := { val := τ.cl Jm base_n₁ base_n₂
                  , property := valid.cl Jm RB₁ RB₂
                  },
      have JB : (Alg @rUC).join base_n₁ base_n₂ cl_m₃, from
        begin constructor, repeat { assumption } end,
      have H := tDC (To.base @rUC n₁) (To.base @rUC n₂) JB,
      cases H with z Hz,
      existsi z,
      refine and.intro _ Hz.2,
      cases Hz.1
    end

def FromTo {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    {rUC : r.UpClosed}
  : From @rUC ∘ To @rUC = A₁.IdRel
 := begin
      apply RelEq.to_eq,
      intros x₀ y₀,
      apply iff.intro,
      { intro H, cases H with y H,
        cases H with H₁ H₂,
        cases H₂,
        apply To.elim H₁,
        intro E₁,
        injection E₁ with E₁' ; clear E₁,
        injection E₁' with E₁'' ; clear E₁',
        subst E₁'',
        apply rfl
      },
      { intro H, simp [Alg.IdRel] at H, subst H,
        let t : { k // valid r k }
             := { val := τ.base r x₀, property := valid.base r },
        existsi t,
        apply and.intro,
        repeat { constructor }
      }
    end

def Factor {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
  : (Rel @rUC ∘ To @rUC) = r
 := begin
      apply RelEq.to_eq,
      intros x y,
      apply iff.intro,
      { intro R,
        cases R with x' R,
        cases x' with x' Vx',
        cases R with R₁ R₂,
        apply To.elim R₁,
        intro E, injection E with E', clear E, subst E',
        apply rel.elim R₂,
        { intros x₁ y₂ R' E₁ E₂,
          simp at E₁, injection E₁ with E₁', clear E₁, subst E₁',
          subst E₂,
          assumption
        },
        { intros m₁ m₂ m₃ Jm n₁ n₂ E₁ E₂, cases E₁ }
      },
      { intro R,
        let t : { k // valid r k }
             := { val := τ.base r x, property := valid.base r },
        existsi t,
        apply and.intro,
        { constructor },
        { constructor, assumption }
      }
    end

def Rel.GT {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    {rUC : r.UpClosed}
  : r ∘ From @rUC ≤ Rel @rUC
 := begin
      intros x y Hx,
      cases Hx with x' Hx,
      cases Hx with Hx₁ Hx₂,
      cases Hx₁,
      constructor,
      assumption
    end


/- Universal property of the downwards closure
 -
 -/
inductive UnivTo' {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    (to' : Sep.Rel A₁ B₁)
    (rel' : Sep.Rel B₁ A₂)
  : Sep.Rel (Alg @rUC) B₁
| base : ∀ {x} {b} (T : to' x b)
         , UnivTo' { val := τ.base r x
                   , property := valid.base r
                   }
                   b
| cl : ∀ {m₁ m₂ m₃} {n₁ n₂}
         (Jm : m₃ ∈ A₂.join m₁ m₂) (V₃)
         {b₁ b₂ b₃} (Jb : b₃ ∈ B₁.join b₁ b₂)
         (U₁ : UnivTo' n₁ b₁)
         (U₂ : UnivTo' n₂ b₂)
         (R'₁ : rel' b₁ m₁)
         (R'₂ : rel' b₂ m₂)
         (R'₃ : rel' b₃ m₃)
       , UnivTo' { val := τ.cl Jm n₁.val n₂.val
                 , property := V₃
                 }
                 b₃

def UnivTo'.elim {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    {rUC : r.UpClosed}
    {B₁ : Sep.Alg.{ℓ₂}}
    {to' : Sep.Rel A₁ B₁}
    {rel' : Sep.Rel B₁ A₂}
    {x₀} {b₀} (U : UnivTo' @rUC to' rel' x₀ b₀)
    {P : Prop}
    (base : ∀ {x} (T : to' x b₀)
              (E : x₀ = { val := τ.base r x, property := valid.base r})
            , P)
    (cl : ∀ {m₁ m₂ m₃} {n₁ n₂}
            (Jm : m₃ ∈ A₂.join m₁ m₂) (V₃)
            {b₁ b₂} (Jb : b₀ ∈ B₁.join b₁ b₂)
            (U₁ : UnivTo' @rUC to' rel' n₁ b₁)
            (U₂ : UnivTo' @rUC to' rel' n₂ b₂)
            (R'₁ : rel' b₁ m₁)
            (R'₂ : rel' b₂ m₂)
            (R'₃ : rel' b₀ m₃)
            (E : x₀ = { val := τ.cl Jm n₁.val n₂.val, property := V₃ })
          , P)
  : P
 := begin
      cases U,
      { apply base, assumption, trivial },
      { apply cl Jm, repeat {assumption}, repeat {trivial} }
    end

def UnivTo'.To {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    {rUC : r.UpClosed}
    {B₁ : Sep.Alg.{ℓ₂}}
    (to' : Sep.Rel A₁ B₁)
    (rel' : Sep.Rel B₁ A₂)
  : to' = UnivTo' @rUC to' rel' ∘ To @rUC
 := sorry

def UnivTo'.Rel {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    {to' : Sep.Rel A₁ B₁}
    {rel' : Sep.Rel B₁ A₂}
    -- (to'UC : to'.UpClosed)
    (rel'eq : r = rel' ∘ to')
  : Rel @rUC = rel' ∘ UnivTo' @rUC to' rel'
 := begin
      apply RelEq.to_eq,
      intro x₀,
      cases x₀ with x₀ V₀,
      induction x₀ with x,
      { intro y₀
        , apply iff.intro,
        { intro Rxy₀,
          apply Rxy₀.elim; clear Rxy₀,
          { intros x' y' Rxy E₁ E₂,
            injection E₁ with E₁'; clear E₁,
            subst E₁', subst E₂,
            have Rxy' : ((rel' ∘ to') x y₀), from
              begin rw rel'eq at Rxy, assumption end,
            cases Rxy' with b Hb,
            existsi b,
            refine and.intro _ Hb.2,
            constructor,
            exact Hb.1
          },
          { intros m₁ m₂ m₃ Jm n₁ n₂ E₁ E₂,
            cases E₁
          }
        },
        { intro Q,
          cases Q with b Q,
          cases Q with U Rby₀,
          constructor,
          rw rel'eq,
          existsi b,
          apply U.elim,
          { intros x' T' E,
            injection E with E'; clear E,
            injection E' with E''; clear E',
            subst E'',
            apply and.intro,
            repeat {assumption}
          },
          { intros m₁ m₂ m₃ n₁ n₂ Jm V₃ b₁ b₂ Jb U₁ U₂ R₁ R₂ R₃ E₁,
            cases E₁
          }
        }
      },
      { intro y₀,
        apply iff.intro,
        { intro R₃,
          apply R₃.elim,
          { intros x y R E, cases E },
          { intros y₁ y₂ y₃ Jy x₁ x₂ E₁ E₂,
            injection E₁ with E'₁ E'₂ E'₃ E'₄ E'₅; clear E₁,
            subst E'₁, subst E'₂, subst E'₃, subst E'₄, subst E'₅, subst E₂,
            exact sorry -- use induction hypothesis
          }
        },
        { simp,
          exact sorry -- i hope it's true
        }
      },
    end

def UnivTo'.UpClosed {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    {to' : Sep.Rel A₁ B₁}
    {rel' : Sep.Rel B₁ A₂}
    (to'UC : to'.UpClosed)
    -- (rel'UC : rel'.UpClosed)
    (rel'eq : r = rel' ∘ to')
  : (UnivTo' @rUC to' rel').UpClosed
 := sorry

def UnivTo'.GT {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    (to' : Sep.Rel A₁ B₁)
    (rel' : Sep.Rel B₁ A₂)
  : (to' ∘ From @rUC) ≤ UnivTo' @rUC to' rel'
 := sorry



/- This part is junk I think
 -
 -/

def UnivTo {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    (to' : Sep.Rel A₁ B₁)
  : Sep.Rel (Alg @rUC) B₁
 := to' ∘ From @rUC

def UnivTo.To {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    (to' : Sep.Rel A₁ B₁)
  : to' = UnivTo @rUC to' ∘ To @rUC
 := begin
      apply eq.trans (Rel_comp.id_r _).symm,
      refine eq.trans _ Rel_comp.assoc.symm,
      exact Rel_comp.congr rfl FromTo.symm,
    end

def UnivTo.Defect {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    {to' : Sep.Rel A₁ B₁}
    {rel' : Sep.Rel B₁ A₂}
    (E : rel' ∘ to' = r)
  : rel' ∘ UnivTo @rUC to' = r ∘ From @rUC
 := begin
      apply eq.trans Rel_comp.assoc.symm,
      apply Rel_comp.congr E rfl
    end


/- Back to the good stuff
 -
 -/

def UnivFrom {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    (fr' : Sep.Rel B₁ A₁)
  : Sep.Rel B₁ (Alg @rUC)
 := To @rUC ∘ fr'

def UnivFrom.From {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    (fr' : Sep.Rel B₁ A₁)
  : fr' = From @rUC ∘ UnivFrom @rUC fr'
 := begin
      apply eq.trans (Rel_comp.id_l _).symm,
      refine eq.trans _ Rel_comp.assoc,
      refine Rel_comp.congr FromTo.symm rfl
    end


def UnivTo.UpClosed {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    (to' : Sep.Rel A₁ B₁)
    (to'UC : to'.UpClosed)
  : (UnivTo @rUC to').UpClosed
 := sorry -- follows from composition of upclosed functions

def UnivFrom.UpClosed {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    (fr' : Sep.Rel B₁ A₁)
    (fr'UC : fr'.UpClosed)
  : (UnivFrom @rUC fr').UpClosed
 := sorry

def UnivFrom.DownClosed {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    (fr' : Sep.Rel B₁ A₁)
    (fr'DC : fr'.DownClosed)
  : (UnivFrom @rUC fr').DownClosed
 := sorry


def UnivFromTo {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    (to' : Sep.Rel A₁ B₁)
    (fr' : Sep.Rel B₁ A₁)
    (E : fr' ∘ to' = A₁.IdRel)
  : UnivFrom @rUC fr' ∘ UnivTo @rUC to' = To @rUC ∘ From @rUC
 := begin
      apply eq.trans Rel_comp.assoc,
      apply eq.trans (Rel_comp.congr rfl Rel_comp.assoc.symm),
      apply eq.trans (Rel_comp.congr rfl (Rel_comp.congr E rfl)),
      exact Rel_comp.congr rfl (Rel_comp.id_l _)
    end

def UnivToFrom {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    (to' : Sep.Rel A₁ B₁)
    (fr' : Sep.Rel B₁ A₁)
  : UnivTo @rUC to' ∘ UnivFrom @rUC fr' = to' ∘ fr'
 := begin
      apply eq.trans Rel_comp.assoc,
      apply Rel_comp.congr rfl,
      apply eq.trans Rel_comp.assoc.symm,
      apply eq.trans _ (Rel_comp.id_l _),
      exact Rel_comp.congr FromTo rfl
    end


def UnivFactor {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    (to' : Sep.Rel A₁ B₁)
    (rel' : Sep.Rel B₁ A₂)
    (E : rel' ∘ to' = r)
  : (rel' ∘ UnivTo @rUC to' ∘ To @rUC) = r
 := begin
      refine eq.trans _ E,
      apply eq.trans (Rel_comp.congr rfl Rel_comp.assoc),
      apply eq.trans Rel_comp.assoc.symm,
      apply eq.trans (Rel_comp.congr rfl FromTo),
      apply Rel_comp.id_r
    end

def Rel.UnivGT₁ {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    (to' : Sep.Rel A₁ B₁)
    (rel' : Sep.Rel B₁ A₂)
    (E : rel' ∘ to' = r)
  : rel' ∘ UnivTo @rUC to' ≤ Rel @rUC
 := begin
      have H : rel' ∘ UnivTo @rUC to' = r ∘ From @rUC
            := UnivTo.Defect @rUC E,
      simp at *,
      rw H,
      apply Rel.GT
    end

def Rel.UnivGT₂ {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    (fr' : Sep.Rel B₁ A₁)
    (to' : Sep.Rel A₁ B₁)
    (rel' : Sep.Rel B₁ A₂)
    (E : rel' ∘ to' = r)
    (TF : to' ∘ fr' ≤ B₁.IdRel)
  : Rel @rUC ∘ UnivFrom @rUC fr' ≤ rel'
 := begin
      intros x₀ y₀ H,
      cases H with z H,
      cases z with z Vz,
      cases H with Uz Rz,
      cases Uz with x H,
      cases H with F'x Tx,
      apply Rz.elim,
      { intros x₁ y₁ R₁ E₁ E₂,
        simp at E₁, subst E₁, subst E₂,
        simp at E, rw E.symm at R₁,
        cases R₁ with b H,
        cases H with T'b R'b,
        apply Tx.elim,
        intro E,
        injection E with E'; clear E,
        injection E' with E''; clear E',
        subst E'',
        have H : x₀ = b, from
          begin
            apply TF,
            existsi x₁,
            apply and.intro,
            repeat { assumption }
          end,
        subst H,
        assumption
      },
      { intros m₁ m₂ m₃ Jm n₁ n₂ E₁ E₂,
        simp at E₁, subst E₁, subst E₂,
        apply Tx.elim,
        intro E₀, cases E₀
      }
    end


end DownCl

end Sep
