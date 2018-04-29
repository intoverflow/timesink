/- Ordered separation algebras
 -
 -/
import .rel
import ..cat.basic

namespace Sep
universes ℓ₁ ℓ₂ ℓ₃ ℓ₄

structure OrdAlg : Type.{ℓ₁ + 1}
 := (alg : Alg.{ℓ₁})
    (ord : Rel alg alg)
    (refl : ord.Refl)
    (trans : ord.Trans)
    -- (closed : ord.Closed)

def OrdAlg.ord_ord (A : OrdAlg.{ℓ₁})
  : A.ord ∘ A.ord = A.ord
 := begin
      apply funext, intro x, apply funext, intro y,
      apply iff.to_eq, apply iff.intro,
      { intro H,
        cases H with w H, cases H with H₁ H₂,
        apply A.trans, repeat { assumption }
      },
      { intro H, existsi x,
        exact and.intro (A.refl _) H
      }
    end

instance OrdAlg_has_le {A : OrdAlg.{ℓ₁}} : has_le A.alg.τ
 := { le := A.ord
    }

structure OrdRel (A : OrdAlg.{ℓ₁}) (B : OrdAlg.{ℓ₂})
 := (rel : Rel A.alg B.alg)
    (total : rel.Total)
    (action : B.ord ∘ rel ∘ A.ord = rel)

def Rel.OrdRel {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : Rel A.alg B.alg)
    (rT : r.Total)
  : OrdRel A B
 := { rel := B.ord ∘ r ∘ A.ord
    , total := λ x, begin
                      have Q := rT x,
                      cases Q with y H,
                      existsi y,
                      refine exists.intro _ (and.intro _ (B.refl _)),
                      refine exists.intro _ (and.intro (A.refl _) H)
                    end
    , action := calc B.ord ∘ (B.ord ∘ r ∘ A.ord) ∘ A.ord
                          = (B.ord ∘ B.ord) ∘ r ∘ (A.ord ∘ A.ord) : sorry
                      ... = B.ord ∘ r ∘ A.ord                     : by rw [B.ord_ord, A.ord_ord]
    }

def OrdRel.incr {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
  : ∀ x₁ x₂ y₂
      (R₂ : r.rel x₂ y₂)
      (Lx : x₁ ≤ x₂)
    , ∃ y₁, r.rel x₁ y₁ ∧ y₁ ≤ y₂
 := begin
      intros x₁ x₂ y₂ R₂ Lx,
      existsi y₂,
      refine and.intro _ (B.refl _),
      rw r.action.symm,
      refine exists.intro _ (and.intro _ (B.refl _)),
      exact exists.intro _ (and.intro Lx R₂)
    end

def OrdRel.eq {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    {r₁ r₂ : OrdRel A B}
    (E : r₁.rel = r₂.rel)
  : r₁ = r₂
 := begin cases r₁, cases r₂, simp at E, subst E end

def OrdAlg.IdRel (A : OrdAlg.{ℓ₁}) : OrdRel A A
 := { rel := A.ord
    , total := λ x, ⟨x, A.refl x⟩
    , action := eq.trans (Rel_comp.congr rfl A.ord_ord) A.ord_ord,
    }

def OrdRel_comp {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}} {C : OrdAlg.{ℓ₃}}
    (g : OrdRel B C) (f : OrdRel A B)
  : OrdRel A C
 := { rel := g.rel ∘ B.ord ∘ f.rel
    , total := λ x, begin
                      have Q := f.total x,
                      cases Q with y Hy,
                      have Q := g.total y,
                      cases Q with z Hz,
                      existsi z,
                      refine exists.intro _ (and.intro _ Hz),
                      refine exists.intro _ (and.intro Hy (B.refl _)),
                    end
    , action
       := calc C.ord ∘ (g.rel ∘ B.ord ∘ f.rel) ∘ A.ord
                   = C.ord ∘ (g.rel ∘ (B.ord ∘ B.ord ∘ B.ord) ∘ f.rel) ∘ A.ord : by repeat {rw B.ord_ord}
               ... = (C.ord ∘ g.rel ∘ B.ord) ∘ B.ord ∘ (B.ord ∘ f.rel ∘ A.ord) : sorry
               ... = g.rel ∘ B.ord ∘ f.rel     : by rw [g.action, f.action],
    }

reserve infixr ` ∘∘ ` : 100
infixr ` ∘∘ ` := λ {A₁} {A₂} {A₃}
                  (r₂₃ : OrdRel A₂ A₃) (r₁₂ : OrdRel A₁ A₂)
                , OrdRel_comp r₂₃ r₁₂

def OrdAlgCat : Cat.Cat
 := { obj := OrdAlg.{ℓ₁}
    , hom := OrdRel
    , id := OrdAlg.IdRel
    , circ := @OrdRel_comp
    , circ_id_r
       := begin
            intros A B f,
            apply OrdRel.eq,
            apply funext, intro x, apply funext, intro y,
            apply iff.to_eq, apply iff.intro,
            { intro H,
              cases H with y' H, cases H with H Ry,
              cases H with x' H, cases H with Rx Lxy,
              rw f.action.symm,
              refine exists.intro _ (and.intro _ (B.refl _)),
              refine exists.intro _ (and.intro _ Ry),
              apply A.trans,
              repeat { assumption }
            },
            { intro H,
              refine exists.intro _ (and.intro _ H),
              refine exists.intro _ (and.intro (A.refl _) (A.refl _)),
            }
          end
    , circ_id_l
       := begin
            intros A B f,
            apply OrdRel.eq,
            apply funext, intro x, apply funext, intro y,
            apply iff.to_eq, apply iff.intro,
            { intro H,
              cases H with y' H, cases H with H Ly,
              cases H with x' H, cases H with Rx Lxy,
              rw f.action.symm,
              refine exists.intro _ (and.intro _ (B.trans _ _ _ Lxy Ly)),
              refine exists.intro _ (and.intro (A.refl _) Rx)
            },
            { intro H,
              refine exists.intro _ (and.intro _ (B.refl _)),
              refine exists.intro _ (and.intro H (B.refl _)),
            }
          end
    , circ_assoc
       := begin
            intros A B C D h g f,
            apply OrdRel.eq,
            apply funext, intro x, apply funext, intro y₀,
            apply iff.to_eq, apply iff.intro,
            { intro H,
              cases H with y₁ H, cases H with H H₁₀,
              cases H with y₂ H, cases H with H H₂₁,
              cases H with y₃ H, cases H with H H₃₂,
              cases H with y₄ H, cases H with Hxy H₄₃,
              refine exists.intro y₃ (and.intro _ _),
              { refine exists.intro _ (and.intro Hxy H₄₃),
              },
              { refine exists.intro _ (and.intro _ H₁₀),
                refine exists.intro _ (and.intro H₃₂ H₂₁)
              }
            },
            { intro H,
              cases H with y₃ H, cases H with H' H,
              cases H with y₁ H, cases H with H H₁₀,
              cases H with y₂ H, cases H with H₃₂ H₂₁,
              cases H' with y₄ H', cases H' with Rxy H₄₃,
              refine exists.intro _ (and.intro _ H₁₀),
              refine exists.intro _ (and.intro _ H₂₁),
              refine exists.intro _ (and.intro _ H₃₂),
              refine exists.intro _ (and.intro Rxy H₄₃)
            }
          end
    }


-- Products of ordered algebras
def OrdAlg.ProductAlg (I : Type.{ℓ₁}) (f : I → OrdAlg.{ℓ₁})
  : OrdAlg
 := { alg := { τ := ∀ (i : I), (f i).alg.τ
             , join := λ x y z, ∀ (i : I), (f i).alg.join (x i) (y i) (z i)
             , comm := λ x y z J i, (f i).alg.comm (J i)
             , assoc := λ x₁ x₂ x₃ x₁₂ x₁₂₃ J₁₂ J₁₂₃ P C
                        , begin
                            have Q : ∃ (a : ∀ (i : I), (f i).alg.τ)
                                      , ∀ (i : I)
                                        , (f i).alg.join (x₂ i) (x₃ i) (a i)
                                        ∧ (f i).alg.join (x₁ i) (a i) (x₁₂₃ i), from
                            begin
                              have Q' : ∀ (i : I)
                                        , ∃ a
                                          , (f i).alg.join (x₂ i) (x₃ i) a
                                          ∧ (f i).alg.join (x₁ i) a (x₁₂₃ i), from
                                begin
                                  intro i,
                                  apply (f i).alg.assoc (J₁₂ i) (J₁₂₃ i),
                                  intro a,
                                  existsi a.x,
                                  exact and.intro a.J₁ a.J₂
                                end,
                              refine exists.intro _ _,
                              { intro i,
                                have Q'' := classical.indefinite_description _ (Q' i),
                                exact Q''.val
                              },
                              { intro i,
                                cases classical.indefinite_description _ (Q' i) with a Q'',
                                exact Q''
                              }
                            end,
                            cases Q with a Q,
                            refine C { x := a, J₁ := _, J₂ := _ },
                            { intro i, apply (Q i).1 },
                            { intro i, apply (Q i).2 }
                          end
             }
  , ord := λ x y, ∀ (i : I), (f i).ord (x i) (y i)
  , refl := λ x i, (f i).refl (x i)
  , trans := λ x₁ x₂ x₃ R₁₂ R₂₃ i, (f i).trans _ _ _ (R₁₂ i) (R₂₃ i)
  }

def OrdAlg.ProductProj (I : Type.{ℓ₁}) (f : I → OrdAlg.{ℓ₁})
  : ∀ (i : I), OrdRel (OrdAlg.ProductAlg I f) (f i)
 := λ i
    , { rel := λ x y, (f i).ord (x i) y
      , total := λ x
                , begin
                    existsi (x i),
                    apply (f i).refl
                  end
      , action
          := begin
              apply funext, intro x, apply funext, intro y,
              apply iff.to_eq, apply iff.intro,
              { intro H,
                cases H with y' H, cases H with H Hy,
                cases H with x' H, cases H with Hx H,
                apply (f i).trans _ _ _ (Hx i),
                apply (f i).trans _ _ _ H,
                exact Hy
              },
              { intro H,
                refine exists.intro _ (and.intro _ H),
                refine exists.intro x (and.intro _ _),
                { intro j, apply (f j).refl },
                { apply (f i).refl  }
              }
            end
      }

def OrdAlg.Prod (I : Type.{ℓ₁}) (f : I → OrdAlg.{ℓ₁})
  : OrdAlgCat.Prod I f
 := { obj := OrdAlg.ProductAlg I f
    , proj := OrdAlg.ProductProj I f
    }

def OrdAlg.Product (I : Type.{ℓ₁}) (f : I → OrdAlg.{ℓ₁})
  : OrdAlgCat.Product (OrdAlg.Prod I f)
 := { univ := λ u, { rel := λ x y, ∀ (i : I), (u.proj i).rel x (y i)
                    , total := λ x
                              , begin
                                  have Q : ∀ (i : I), {y // (u.proj i).rel x y}, from
                                    begin
                                      intro i, exact classical.indefinite_description _ ((u.proj i).total x)
                                    end,
                                  refine exists.intro _ _,
                                  { intro i, exact (Q i).val },
                                  { intro i, exact (Q i).property }
                                end
                    , action
                        := begin
                            apply funext, intro x, apply funext, intro y,
                            apply iff.to_eq, apply iff.intro,
                            { intros H i,
                              cases H with y' H, cases H with H Hy,
                              cases H with x' H, cases H with Hx H,
                              rw (u.proj i).action.symm,
                              refine exists.intro _ (and.intro _ (Hy i)),
                              refine exists.intro _ (and.intro Hx (H i))
                            },
                            { intro H,
                              refine exists.intro _ (and.intro _ (λ i, (f i).refl _)),
                              refine exists.intro _ (and.intro (u.obj.refl _) H)
                            }
                          end
                    }
    , eq := λ u i
            , begin
                apply OrdRel.eq,
                apply funext, intro x, apply funext, intro y₀,
                apply iff.to_eq, apply iff.intro,
                { intro H,
                  have Q : ∀ (j : I), {y // (u.proj j).rel x y ∧ (i = j → y == y₀)}, from
                    begin
                      intro j,
                      cases classical.prop_decidable (i = j) with E E,
                      { have Q' := classical.indefinite_description _ ((u.proj j).total x),
                        refine { val := Q'.val, property := _ },
                        apply and.intro Q'.property,
                        intro F, apply false.elim, apply E, apply F
                      },
                      { subst E,
                        refine { val := y₀, property := _ },
                        apply and.intro H,
                        intro E', apply heq.refl
                      }
                    end,
                  refine exists.intro (λ j, (Q j).val) (and.intro _ _),
                  { refine exists.intro (λ j, (Q j).val) (and.intro _ _),
                    { intro j, apply (Q j).property.1 },
                    { intro j, apply (f j).refl _ }
                  },
                  { have Q' := (Q i).property.2 rfl,
                    apply cast _ ((f i).refl (Q i).val),
                    apply congr_arg,
                    apply eq_of_heq,
                    exact Q'
                  }
                },
                { intro H,
                  cases H with y' H, cases H with H Hy,
                  cases H with x' H, cases H with Hx H,
                  dsimp at *,
                  rw (u.proj i).action.symm,
                  refine exists.intro _ (and.intro _ ((f i).trans _ _ _ (H i) Hy)),
                  refine exists.intro _ (and.intro (u.obj.refl _) (Hx i))
                }
              end
    , uniq
       := λ u h Hh
          , begin
              apply OrdRel.eq,
              apply funext, intro x, apply funext, intro y₀,
              apply iff.to_eq, apply iff.intro,
              { intros H j,
                rw (Hh j),
                refine exists.intro _ (and.intro _ ((f j).refl _)),
                refine exists.intro _ (and.intro H _),
                intro k, apply (f k).refl
              },
              { intro H, dsimp at *,
                rw h.action.symm,
                have Q' := congr_arg OrdRel.rel (@Cat.Cat.circ_assoc OrdAlgCat _ _ _ _ (OrdAlg.IdRel _) h (OrdAlg.IdRel _)),
                have Q := congr_fun (congr_fun Q'.symm x) y₀, clear Q',
                dsimp [OrdAlgCat, OrdRel_comp, OrdAlg.IdRel] at Q,
                exact sorry
              }
            end
    }

def OrdAlgCat.HasProducts
  : OrdAlgCat.{ℓ₁}.HasProducts
 := λ I f, ⟨OrdAlg.Prod I f, OrdAlg.Product I f⟩


def OrdRel.ConfinedPres {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}} (r : OrdRel A B)
  : ∀ {p : Set B.alg} (Hp : B.ord.Confined p)
    , A.ord.Confined (r.rel.FnInv p)
 := begin
      intros p Hp,
      intros a₁ H, cases H with a₂ H, cases H with H La,
      cases H with b₂ H, cases H with Hpb₂ R₂,
      have Q := r.incr _ _ _ R₂ La,
      cases Q with b₁ Q, cases Q with R₁ Lb,
      existsi b₁, exact and.intro (Hp ⟨b₂, and.intro Hpb₂ Lb⟩) R₁
    end

-- def OrdRel.LocalPres {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}} (r : OrdRel A B)
--   : Prop
--  := ∀ (p : Set B.alg) (pLocal : B.ord.Local p.Compl)
--     , A.ord.Local (r.rel.FnInv p).Compl


def OrdRel.LocallyUpClosedPres {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
  : Prop
 := ∀ (p : Set B.alg) (HS : B.ord.LocallyUpClosed p.Compl)
    , A.ord.LocallyUpClosed (r.rel.FnInv p).Compl

def OrdRel.LocallyDownClosedPres {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
  : Prop
 := ∀ (S : Set A.alg) (HS : A.ord.LocallyDownClosed S)
    , B.ord.LocallyDownClosed (r.rel.Fn S)


structure OrdRel.StrongUpClosed {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
  : Prop
 := (ord : ∀ {x₁ x₂ x₃ y₃}
             (Jx : A.alg.join x₁ x₂ x₃)
             (L₃ : x₃ ≤ y₃)
           , ∃ z₁ z₂ z₃, B.alg.join z₁ z₂ z₃ ∧ r.rel x₁ z₁ ∧ r.rel x₂ z₂ ∧ r.rel y₃ z₃)
    (rel : ∀ {x₁ x₂ x₃ y₁ y₂ y₃}
             (Jx : B.alg.join x₁ x₂ x₃)
             (R₁ : r.rel y₁ x₁)
             (R₂ : r.rel y₂ x₂)
             (R₃ : r.rel y₃ x₃)
           , ∃ z₁ z₂, A.alg.join z₁ z₂ y₃ ∧ y₁ ≤ z₁ ∧ y₂ ≤ z₂)

structure OrdRel.StrongDownClosed {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
  : Prop
 := (ord : ∀ {x₁ x₂ x₃ y₁ y₂}
             (Jx : B.alg.join x₁ x₂ x₃)
             (L₁ : y₁ ≤ x₁)
             (L₂ : y₂ ≤ x₂)
           , ∃ z₁ z₂ z₃, A.alg.join z₁ z₂ z₃ ∧ r.rel z₁ y₁ ∧ r.rel z₂ y₂ ∧ r.rel z₃ x₃)
    (rel : ∀ {x₁ x₂ x₃ y₁ y₂ y₃}
             (Jx : A.alg.join x₁ x₂ x₃)
             (R₁ : r.rel x₁ y₁)
             (R₂ : r.rel x₂ y₂)
             (R₃ : r.rel x₃ y₃)
           , ∃ (m₃ : (B.alg).τ), m₃ ≤ y₃ ∧ (B.alg).join y₁ y₂ m₃)

def OrdRel.StrongUpClosed.LocallyUpClosedPres {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    {r : OrdRel A B}
    (rUC : r.StrongUpClosed)
  : r.LocallyUpClosedPres
 := begin
      intros p Hp,
      intros s x₂ x₃ y₃ Hps J L₃,
      have Q := rUC.ord J L₃,
      cases Q with z₁ Q, cases Q with z₂ Q, cases Q with z₃ Q,
      cases Q with Jz Q, cases Q with R₁ Q, cases Q with R₂ R₃,
      exact rUC.rel Jz R₁ R₂ R₃
    end

def OrdRel.StrongDownClosed.LocallyDownClosedPres {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    {r : OrdRel A B}
    (rDC : r.StrongDownClosed)
  : r.LocallyDownClosedPres
 := begin
      intros S HS,
      intros s x₂ x₃ m₁ m₂ HSs J L₁ L₂,
      have Q := rDC.ord J L₁ L₂,
      cases Q with z₁ Q, cases Q with z₂ Q, cases Q with z₃ Q,
      cases Q with Jz Q, cases Q with R₁ Q, cases Q with R₂ R₃,
      exact rDC.rel Jz R₁ R₂ R₃
    end

structure OrdRel.PrimeRel {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
  : Prop
 := (prime : r.rel.FnPrimePres)
    (increasing : r.rel.Fn A.ord.increasing ⊆ B.ord.increasing)

structure OrdRel.JoinRel {A : OrdAlg.{ℓ₁}} {B : OrdAlg.{ℓ₂}}
    (r : OrdRel A B)
  : Prop
 := (join : r.rel.FnJoinClosedPres)
    (increasing : B.ord.increasing ⊆ r.rel.Fn A.ord.increasing)

end Sep
