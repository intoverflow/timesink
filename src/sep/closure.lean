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

inductive To {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
  : Sep.Rel A₁ (Alg @rUC)
| intro : ∀ x, To x { val := τ.base r x, property := valid.base r }

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

end DownCl

end Sep
