import .basic

namespace Sep
universes ℓ

namespace Option

inductive join {A : Type.{ℓ}} (j : A → A → A → Prop)
  : option A → option A → option A → Prop
| base : ∀ {x₁ x₂ x₃} (Jx : j x₁ x₂ x₃)
         , join (option.some x₁) (option.some x₂) (option.some x₃)
| none_r : ∀ {x}, join none x x
| none_l : ∀ {x}, join x none x

def join.assoc {A : Type.{ℓ}} {j : A → A → A → Prop}
    (HJ : IsAssoc j)
  : IsAssoc (join j)
 := begin
      intros x₁ x₂ x₃ x₁₂ x₁₂₃ J₁ J₂ P C,
      cases J₁,
      { cases J₂,
        { apply HJ Jx Jx_1,
          intro a,
          refine C { x := option.some a.x, J₁ := _, J₂ := _ },
          { constructor, exact a.J₁ },
          { constructor, exact a.J₂ }
        },
        { refine C { x := option.some x₂_1, J₁ := _, J₂ := _ },
          { constructor },
          { assumption }
        }
      },
      { cases J₂,
        { refine C { x := option.some x₃_1, J₁ := _, J₂ := _ },
          { assumption },
          { constructor }
        },
        { refine C { x := x₃, J₁ := _, J₂ := _ },
          { constructor },
          { constructor }
        },
        { refine C { x := x₂, J₁ := _, J₂ := _ },
          { constructor },
          { constructor }
        }
      },
      { refine C { x := x₃, J₁ := _, J₂ := _ },
        { constructor },
        { assumption }
      }
    end

end Option

def Alg.Opt (A : Alg.{ℓ}) : Alg.{ℓ}
  := { τ := option A.τ
     , join := Option.join A.join
     , comm := λ x₁ x₂ x₃ J
               , begin
                   cases J,
                   { constructor, apply A.comm, assumption },
                   { constructor },
                   { constructor }
                 end
     , assoc := @Option.join.assoc _ _ A.assoc
     }

def Alg.Opt.Ident (A : Alg.{ℓ})
  : Alg.Ident A.Opt
 := { one := option.none
    , join_one_r
       := begin intro x, constructor end
    , join_one_uniq_r
       := begin
            intros x y H,
            cases H,
            repeat { trivial }
          end
    }

def Alg.Opt.join_none_l {A : Alg.{ℓ}}
    {x₁ x₂ : option A.τ}
    (J : A.Opt.join none x₁ x₂)
  : x₁ = x₂
 := begin
      cases J,
      repeat { trivial }
    end

def Alg.Opt.join_none_r {A : Alg.{ℓ}}
    {x₁ x₂ : option A.τ}
    (J : A.Opt.join x₁ none x₂)
  : x₁ = x₂
 := begin
      apply Alg.Opt.join_none_l,
      apply A.Opt.comm,
      assumption
    end

def Alg.Opt.join_some_r {A : Alg.{ℓ}}
    {x₁} {x₂} {x₃ : option A.τ}
    (J : A.Opt.join x₁ (some x₂) x₃)
  : ¬ x₃ = none
 := begin cases J, repeat { intro F, cases F } end

def Alg.Opt.join_some_l {A : Alg.{ℓ}}
    {x₁} {x₂} {x₃ : option A.τ}
    (J : A.Opt.join (some x₁) x₂ x₃)
  : ¬ x₃ = none
 := begin cases J, repeat { intro F, cases F } end

end Sep
