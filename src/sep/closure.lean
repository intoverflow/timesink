/- Donwards closure. (Work in progress)
 -
 - Given an upwards closed relation r : X .→ Y, we construct
 - an algebra K and relations
 -   to : X .→ K    (upwards closed)
 -   from : K .→ X  (upwards and downwards closed)
 -   cl : K .→ Y   (upwards and downwards closed)
 - satisfying
 -   r = cl ∘ to
 -   from ∘ to = eq X
 -   to ∘ from ⊆ eq K
 -
 - We have some basic facts:
 -   * If `to` is downards closed, then so is `r`.
 -   * Every relation `s : A .→ X` which is upwards and downwards
 -     closed extends to a relation `e : A .→ K` which is also
 -     upwards and downards closed, and which satisfies
 -       r ∘ s ≤ cl ∘ e
 -     Furthermore, `e` is the "weakest" such relation: for every other
 -     relation `e' : A .→ K` which is both upwards and downards closed
 -     and which satisfies r ∘ s ≤ cl ∘ e', we have
 -       e' ⊆ e
 -
 - We also have the following characteristic property:
 -
 - For all other factorizations `r = X .-to'→ K' .-cl'→ Y` with
 - `to'` upwards closed and `cl'` both upwards and downwards closed,
 - there exists an upwards-closed relation `u : K .→ K'` such that
 -   to' = u ∘ to    (factorization of to')
 -   cl ⊆ cl' ∘ u    (cl "stronger" than cl')
 - Lastly, `u` is the "weakest" upwards-closed relation satisfying these
 - two conditions: for all other upwards-closed `u' : K .→ K'`
 - satisfying the two conditions above, we have
 -   u' ⊆ u
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
    {x₀ : τ r} {y₀} (R : rel x₀ y₀)
    {P : Prop}
    (Cbase : ∀ {x}
             , r x y₀
             → x₀ = τ.base r x
             → P)
    (Ccl : ∀ {m₁ m₂} (Jm : y₀ ∈ A₂.join m₁ m₂)
             (n₁ n₂ : τ r)
           , x₀ = τ.cl Jm n₁ n₂
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
         {n₁ n₂ : τ r} (V₁ : valid n₁) (V₂ : valid n₂)
         (R₁ : rel n₁ m₁) (R₂ : rel n₂ m₂)
       , valid (τ.cl Jm n₁ n₂)

def valid.elim {A₁ : Alg.{ℓ₁}} {A₂ : Alg.{ℓ₂}} {r : Rel A₁ A₂}
    {x₀ : τ r} (V : valid r x₀)
    {P : Prop}
    (base : ∀ {x} (E : x₀ = τ.base r x), P)
    (cl : ∀ {m₁ m₂ m₃} (Jm : m₃ ∈ A₂.join m₁ m₂)
            {n₁ n₂ : τ r} (V₁ : valid r n₁) (V₂ : valid r n₂)
            (R₁ : rel n₁ m₁) (R₂ : rel n₂ m₂)
            (E : x₀ = τ.cl Jm n₁ n₂)
          , P)
  : P
 := begin
      cases V,
      { apply base, trivial },
      { apply cl Jm V₁ V₂, repeat { assumption }, trivial }
    end

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
    (base : ∀ {n₁ n₂ n₃}
              (Jn : A₁.join n₁ n₂ n₃)
              (E₁ : x₁ = { val := τ.base r n₁
                         , property := valid.base r })
              (E₂ : x₂ = { val := τ.base r n₂
                         , property := valid.base r })
              (E₃ : x₃ = { val := τ.base r n₃
                         , property := valid.base r })
            , P)
    (cl : ∀ {m₁' m₂' m₁ m₂ m₃}
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
      { apply base, repeat { assumption }, repeat { trivial } },
      { apply cl _ _ Jm Jm', repeat { assumption }, repeat { trivial } }
    end

--
-- Can we strengthen join to get this eliminator?
-- It would imply UnivTo.UpClosed...
--
-- def join.elim' {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
--     {x₁ x₂ x₃} (Jn : join r x₁ x₂ x₃)
--     {P : Prop}
--     (base : ∀ {n₁ n₂ n₃}
--               (Jn : A₁.join n₁ n₂ n₃)
--               (E₁ : x₁ = { val := τ.base r n₁
--                          , property := valid.base r })
--               (E₂ : x₂ = { val := τ.base r n₂
--                          , property := valid.base r })
--               (E₃ : x₃ = { val := τ.base r n₃
--                          , property := valid.base r })
--             , P)
--     (cl : ∀ {m₁' m₂' m₁ m₂ m₃}
--             (Jm : m₃ ∈ A₂.join m₁ m₂)
--             (R₁ : rel x₁.val m₁') (R₂ : rel x₂.val m₂')
--             (E : x₃.val = τ.cl Jm x₁ x₂)
--           , P)
--   : P
--  := sorry

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
          { exact valid.cl _ t.property c₃.property (rel.base Hy.2.2) R₂₂ },
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
          { intros x R E₁, cases E₁ },
          intros m₁ m₂ Jm n₁ n₂ E₁,
          injection E₁ with E'₁ E'₂ E'₃ E'₄ E'₅, clear E₁,
          subst E'₁, subst E'₂, subst E'₃, subst E'₄, subst E'₅,
          apply A₂.assoc Jm₁' Jm₂', intro a,
          refine C  { x := { val := τ.cl a.J₁ c₂ c₃
                           , property := _
                           }
                    , J₁ := _
                    , J₂ := _
                    },
          { exact valid.cl _ c₂.property c₃.property R₁₂ R₂₂ },
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

inductive To {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
  : Sep.Rel A₁ (Alg @rUC)
| base : ∀ x, To x { val := τ.base r x, property := valid.base r }

inductive From {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
  : Sep.Rel (Alg @rUC) A₁
| base : ∀ x, From { val := τ.base r x, property := valid.base r } x



def Rel.DownClosed {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
  : (Rel @rUC).DownClosed
 := begin
      intros n₁ n₂ m₁ m₂ m₃ R₁ R₂ Jm,
      refine exists.intro
              { val := τ.cl Jm n₁.val n₂.val
              , property := valid.cl Jm n₁.property n₂.property R₁ R₂
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
        { intros x Rxy E₁,
          injection E₁ with E₁', clear E₁,
          subst E₁',
          have Hy := rUC Jn Rxy,
          cases Hy with y₁ Hy,
          cases Hy with y₂ Hy,
          existsi y₁, existsi y₂,
          apply and.intro Hy.1,
          apply and.intro,
          { constructor, exact Hy.2.1 },
          { constructor, exact Hy.2.2 }
        },
        { intros y₁ y₂ Jy x₁ x₂ E₁, cases E₁ }
      },
      { intros y₁' y₂' y₁ y₂ y₃ x₃₁ x₃₂ Jy Jy' V₃ R₁ R₂ E,
        subst E,
        apply rel.elim R,
        { intros x Rxy E₁, cases E₁ },
        { intros z₁ z₂ Jz w₁ w₂ E₁,
          injection E₁ with E₁' E₂' E₃' E₄' E₅', clear E₁,
          subst E₁', subst E₂', subst E₃', subst E₄', subst E₅',
          existsi y₁', existsi y₂',
          apply and.intro Jy',
          apply and.intro,
          { assumption },
          { assumption }
        }
      }
    end


def To.elim {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    {rUC : r.UpClosed}
    {x} {y} (Txy : To @rUC x y)
    {P : Prop}
    (base : y = { val := τ.base r x, property := valid.base r } → P)
  : P
 := begin
      cases Txy,
      { exact base rfl }
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

def To.DownClosed {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
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
                  , property := valid.cl Jm base_n₁.property base_n₂.property RB₁ RB₂
                  },
      have Jx : (Alg @rUC).join base_n₁ base_n₂ cl_m₃, from
        begin constructor, repeat { assumption } end,
      have H := tDC (To.base @rUC n₁) (To.base @rUC n₂) Jx,
      cases H with z Hz,
      apply Hz.1.elim,
      { intro E, cases E }
    end


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


def ToFrom {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    {rUC : r.UpClosed}
  : To @rUC ∘ From @rUC ≤ (Alg @rUC).IdRel
 := begin
      intros n₁ n₂ H,
      cases H with x H,
      cases H with F T,
      cases F,
      cases T,
      exact rfl
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
  : Rel @rUC ∘ To @rUC = r
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
        { intros x₁ R' E₁,
          simp at E₁, injection E₁ with E₁', clear E₁, subst E₁',
          assumption
        },
        { intros m₁ m₂ Jm n₁ n₂ E₁, cases E₁ }
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

def Rel.Minimal {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
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
inductive UnivTo {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    (to' : Sep.Rel A₁ B₁)
    (rel' : Sep.Rel B₁ A₂)
  : Sep.Rel (Alg @rUC) B₁
| base : ∀ {x} {b} (T : to' x b)
         , UnivTo { val := τ.base r x
                   , property := valid.base r
                   }
                   b
| cl : ∀ {m₁ m₂ m₃} {n₁ n₂} (V₁) (V₂)
         (Jm : m₃ ∈ A₂.join m₁ m₂) (V)
         {b₁ b₂ b₃} (Jb : b₃ ∈ B₁.join b₁ b₂)
         (U₁ : UnivTo { val := n₁, property := V₁ } b₁)
         (U₂ : UnivTo { val := n₂, property := V₂ } b₂)
       , UnivTo { val := τ.cl Jm n₁ n₂
                 , property := V
                 }
                 b₃


-- We can prove it if we have Jx.elim'
def UnivTo.UpClosed {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    {to' : Sep.Rel A₁ B₁}
    {rel' : Sep.Rel B₁ A₂}
    (to'UC : to'.UpClosed)
    -- (rel'UC : rel'.UpClosed)
    -- (rel'eq : r = rel' ∘ to')
  : (UnivTo @rUC to' rel').UpClosed
 := sorry
--  := begin
--       intros q₁ q₂ q₃ n₃' Jx Ux₃n₃,
--       cases Ux₃n₃; clear Ux₃n₃,
--       { apply Jx.elim; clear Jx,
--         { intros,
--           subst E₁, subst E₂,
--           injection E₃ with E; clear E₃,
--           injection E with E'; clear E,
--           subst E',
--           have H := to'UC Jn T,
--           cases H with b₁ H,
--           cases H with b₂ H,
--           existsi b₁, existsi b₂,
--           apply and.intro H.1,
--           apply and.intro,
--           { constructor, exact H.2.1 },
--           { constructor, exact H.2.2 }
--         },
--         { intros, cases E }
--       },
--       { apply Jx.elim'; clear Jx,
--         { intros, cases E₃ },
--         { intros,
--           injection E with E₁ E₂ E₃ E₄ E₅; clear E,
--           subst E₁, subst E₂, subst E₃, subst E₄, subst E₅,
--           existsi b₁, existsi b₂,
--           apply and.intro Jb,
--           apply and.intro,
--           { cases q₁ with q₁ V₁, exact U₁ },
--           { cases q₂ with q₂ V₂, exact U₂ }
--         }
--       }
--     end

def UnivTo.To {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    {rUC : r.UpClosed}
    {B₁ : Sep.Alg.{ℓ₂}}
    (to' : Sep.Rel A₁ B₁)
    (rel' : Sep.Rel B₁ A₂)
  : to' = UnivTo @rUC to' rel' ∘ To @rUC
 := begin
      apply RelEq.to_eq,
      intros x₀ y₀,
      apply iff.intro,
      { intro Tx₀y₀,
        let t : { k // valid r k }
             := { val := τ.base r x₀
                , property := valid.base r
                },
        existsi t,
        apply and.intro,
        { constructor },
        { constructor, assumption }
      },
      { intro Q, cases Q with x Q,
        cases Q with T U,
        cases U,
        { apply T.elim,
          intro E,
          injection E with E'; clear E,
          injection E' with E''; clear E',
          subst E'',
          assumption
        },
        { apply T.elim, intro E, cases E }
      }
    end

def UnivTo.Weakest {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    {to' : Sep.Rel A₁ B₁}
    {rel' : Sep.Rel B₁ A₂}
    {uto' : Sep.Rel (Alg @rUC) B₁}
    (Eto' : to' = uto' ∘ To @rUC)
    (uto'UC : uto'.UpClosed)
  : uto' ≤ UnivTo @rUC to' rel'
 := begin
      intro x₀,
      cases x₀ with x₀ V₀,
      simp at *,
      induction x₀ with x₀,
      { intros b₃ T'b₃,
        constructor,
        rw Eto',
        let t : { k // valid r k }
             := { val := τ.base r x₀, property := valid.base r },
        existsi t,
        refine and.intro _ T'b₃,
        constructor
      },
      { intros b₃ T'b₃,
        apply V₀.elim,
        { intros x E, cases E },
        { intros p₁ p₂ p₃ Jm q₁ q₂ Vq₁ Vq₂ Rq₁ Rq₂ E,
          injection E with E₁ E₂ E₃ E₄ E₅; clear E,
          subst E₁, subst E₂, subst E₃, subst E₄, subst E₅,
          have Jn : (Alg @rUC).join ⟨n₁, Vq₁⟩ ⟨n₂, Vq₂⟩ ⟨τ.cl Jm n₁ n₂, V₀⟩, from
            begin
              apply join.cl ⟨n₁, Vq₁⟩ ⟨n₂, Vq₂⟩ ⟨n₁, Vq₁⟩ ⟨n₂, Vq₂⟩,
              repeat { assumption }
            end,
          have Hb := uto'UC Jn T'b₃ ; clear Jn T'b₃,
          cases Hb with b₁ Hb,
          cases Hb with b₂ Hb,
          cases Hb with Jb Hb,
          have Q₁ := ih_1 Vq₁ Hb.1; clear ih_1,
          have Q₂ := ih_2 Vq₂ Hb.2; clear ih_2,
          apply UnivTo.cl Vq₁ Vq₂ Jm V₀ Jb Q₁ Q₂; clear Jm V₀ Jb,
        }
      }
    end

def Rel.Strongest {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {B₁ : Sep.Alg.{ℓ₂}}
    {to' : Sep.Rel A₁ B₁}
    {rel' : Sep.Rel B₁ A₂}
    (rel'eq : r = rel' ∘ to')
    (rel'DC : rel'.DownClosed)
  : Rel @rUC ≤ rel' ∘ UnivTo @rUC to' rel'
 := begin
      intro x₀,
      cases x₀ with x₀ V₀,
      induction x₀ with x₀,
      { intros y₀ Rxy,
        apply Rxy.elim ; clear Rxy,
        { intros x' Rxy E₁,
          injection E₁ with E₁'; clear E₁,
          subst E₁',
          have Rxy' : ((rel' ∘ to') x₀ y₀), from
            begin rw rel'eq at Rxy, assumption end,
          cases Rxy' with b Hb,
          existsi b,
          refine and.intro _ Hb.2,
          constructor,
          exact Hb.1
        },
        { intros m₁ m₂ Jm n₁ n₂ E₁, cases E₁ }
      },
      { intros y₀ Rxy,
        apply Rxy.elim ; clear Rxy,
        { intros x R E, cases E },
        { intros y₁ y₂ Jy x₁ x₂ E₁,
          injection E₁ with E'₁ E'₂ E'₃ E'₄ E'₅; clear E₁,
          subst E'₁, subst E'₂, subst E'₃, subst E'₄, subst E'₅,
          apply V₀.elim,
          { intros x E, cases E },
          { intros p₁ p₂ p₃ Jp q₁ q₂ Vq₁ Vq₂ Rq₁ Rq₂ E,
            injection E with E₁ E₂ E₃ E₄ E₅; clear E,
            subst E₁, subst E₂, subst E₃, subst E₄, subst E₅,
            have Q₁ := ih_1 Vq₁ Rq₁; clear ih_1,
            have Q₂ := ih_2 Vq₂ Rq₂; clear ih_2,
            cases Q₁ with b₁ Q₁,
            cases Q₁ with U₁ Rb₁,
            cases Q₂ with b₂ Q₂,
            cases Q₂ with U₂ Rb₂,
            have Q := rel'DC Rb₁ Rb₂ Jm,
            cases Q with b₃ Q,
            cases Q with Rb₃ Jb,
            existsi b₃,
            refine and.intro _ Rb₃,
            constructor, repeat { assumption }
          }
        }
      }
    end


/- Maximal extension of relations into the downards closure
 -
 -/
def {ℓ₀} Extend {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {A₀ : Sep.Alg.{ℓ₀}}
    (s : Sep.Rel A₀ A₁)
  : Sep.Rel A₀ (Alg @rUC)
 := sorry

def {ℓ₀} Extend.Weakest {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {A₀ : Sep.Alg.{ℓ₀}}
    {s : Sep.Rel A₀ A₁}
    (extend' : Sep.Rel A₀ (Alg @rUC))
    (extend'GT : r ∘ s ≤ Rel @rUC ∘ extend')
  : extend' ≤ Extend @rUC s
 := sorry

def {ℓ₀} Extend.UpClosed {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {A₀ : Sep.Alg.{ℓ₀}}
    {s : Sep.Rel A₀ A₁}
    (sUC : s.UpClosed)
  : (Extend @rUC s).UpClosed
 := sorry

def {ℓ₀} Extend.DownClosed {A₁ : Sep.Alg.{ℓ₁}} {A₂ : Sep.Alg.{ℓ₂}} {r : Sep.Rel A₁ A₂}
    (rUC : r.UpClosed)
    {A₀ : Sep.Alg.{ℓ₀}}
    {s : Sep.Rel A₀ A₁}
    (sDC : s.DownClosed)
  : (Extend @rUC s).DownClosed
 := sorry

end DownCl

end Sep
