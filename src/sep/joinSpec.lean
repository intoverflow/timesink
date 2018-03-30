/- The join-spectrum of a separation algebra.
 -
 -/
import .basic
import .rel
import ..top.basic
import ..extralib

namespace Sep
universes ℓ ℓ₁ ℓ₂
open Top

structure Alg.JoinSpec (A : Alg.{ℓ}) : Type.{ℓ}
 := (set : Set A)
    (join : set.JoinClosed)

def JoinSpec.eq {A : Alg.{ℓ}} (J₁ J₂ : A.JoinSpec)
  : J₁.set = J₂.set → J₁ = J₂
 := begin
      intro E,
      cases J₁ with J₁ H₁,
      cases J₂ with J₂ H₂,
      simp at E,
      subst E
    end

def JoinClosedPres.InducedMap {X : Alg.{ℓ₁}} {Y : Alg.{ℓ₂}} {r : Rel X Y}
    (rJP : r.FnJoinClosedPres)
  : X.JoinSpec → Y.JoinSpec
 := λ j, { set := r.Fn j.set
         , join := rJP j.join
         }

def JoinSpec.BasicOpen {A : Alg.{ℓ}} (S : Set A) : set A.JoinSpec
  := λ j, S ⊆ j.set

def JoinSpec.InducedMap.BasicPreImage' {X : Alg.{ℓ₁}} {Y : Alg.{ℓ₂}} (r : Rel X Y)
    (rJP : r.FnJoinClosedPres)
    (ys : Set Y)
  : PreImage (JoinClosedPres.InducedMap @rJP) (JoinSpec.BasicOpen ys)
      = set.sUnion (λ U, ∃ S, ys ⊆ r.Fn S ∧ U = JoinSpec.BasicOpen S)
 := begin
      apply funext, intro J,
      apply iff.to_eq, apply iff.intro,
      { intro H,
        existsi JoinSpec.BasicOpen J.set,
        refine exists.intro _ _,
        { existsi J.set, exact and.intro H rfl },
        { intros x Hx, exact Hx }
      },
      { intros H y Hyys,
        cases H with S H,
        cases H with H HJ,
        cases H with S H,
        cases H with H E,
        subst E,
        apply (H Hyys).elim,
        intros x Hx Rxy,
        existsi x,
        exact and.intro (HJ Hx) Rxy
      }
    end

def JoinSpec.InducedMap.BasicPreImage {X : Alg.{ℓ₁}} {Y : Alg.{ℓ₂}} (r : Rel X Y)
    (rJP : r.FnJoinClosedPres)
    (ys : Set Y)
  : PreImage (JoinClosedPres.InducedMap @rJP) (JoinSpec.BasicOpen ys)
      = set.sInter (λ U, ∃ y, y ∈ ys ∧ U = set.sUnion ((λ x, JoinSpec.BasicOpen (eq x)) <$> r.Fib y))
 := begin
      apply funext, intro J,
      apply iff.to_eq, apply iff.intro,
      { intros H O HO,
        cases HO with y Hy,
        cases Hy with Hyys E,
        subst E,
        cases H Hyys with x Hx,
        existsi JoinSpec.BasicOpen (eq x),
        refine exists.intro _ _,
        { existsi x,
          refine and.intro Hx.2 rfl,
        },
        { intros x' E,
          have E' : x = x' := E, subst E', clear E,
          exact Hx.1
        }
      },
      { intros H y Hyys,
        have Q := H (set.sUnion ((λ x, JoinSpec.BasicOpen (eq x)) <$> r.Fib y))
                    begin existsi y, exact and.intro Hyys rfl end,
        cases Q with X HX,
        cases HX with HX JX,
        cases HX with x HX,
        cases HX with Rxy E,
        have E' := E.symm, subst E', clear E,
        existsi x,
        exact and.intro (JX rfl) Rxy
      }
    end

def JoinSpec.BasicOpen.intersection {A : Alg.{ℓ}} (S₁ S₂ : Set A)
  : JoinSpec.BasicOpen S₁ ∩ JoinSpec.BasicOpen S₂ = JoinSpec.BasicOpen (S₁ ∪ S₂)
 := begin
      apply funext, intro p,
      apply iff.to_eq, apply iff.intro,
      { intros H x Hpx,
        cases Hpx with H₁ H₂,
        { apply H.1, assumption },
        { apply H.2, assumption }
      },
      { intro H, apply and.intro,
        { intros x Hpx, exact H (or.inl Hpx) },
        { intros x Hpx, exact H (or.inr Hpx) }
      }
    end


def Alg.JoinSpec.OpenBasis (A : Alg.{ℓ}) : OpenBasis A.JoinSpec
 := sorry
--  := { Open := λ U, ∃ (xs : list A.τ), U = JoinSpec.BasicOpen (λ x, x ∈ xs)
--     , Cover := begin
--                 apply funext, intro p,
--                 apply iff.to_eq,
--                 apply iff.intro,
--                 { intro T, clear T,
--                   existsi (λ x, true),
--                   apply exists.intro,
--                   { existsi list.nil,
--                     apply funext, intro p',
--                     apply iff.to_eq,
--                     apply iff.intro,
--                     { intro T, clear T,
--                       intros x Hx,
--                       cases Hx
--                     },
--                     { intro H, constructor }
--                   },
--                   { constructor }
--                 },
--                 { intro H, constructor }
--                end
--     , Ointer := begin
--                   intros U₁ U₂ H₁ H₂,
--                   cases H₁ with L₁ E₁,
--                   cases H₂ with L₂ E₂,
--                   subst E₁, subst E₂,
--                   existsi list.append L₁ L₂,
--                   apply funext, intro p,
--                   apply iff.to_eq,
--                   apply iff.intro,
--                   { intros H x Hx,
--                     have Qx : x ∈ L₁ ∨ x ∈ L₂, from set.in_append Hx,
--                     cases Qx with Qx Qx,
--                     { apply H.1 Qx },
--                     { exact H.2 Qx }
--                   },
--                   { intro H,
--                     apply and.intro,
--                     { intros x Hx,
--                       have Qx : x ∈ list.append L₁ L₂, from set.in_append_left Hx,
--                       exact H Qx
--                     },
--                     { intros x Hx,
--                       have Qx : x ∈ list.append L₁ L₂, from set.in_append_right Hx,
--                       exact H Qx
--                     }
--                   }
--                 end
--     }

def Alg.JoinSpec.Topology (A : Alg.{ℓ}) : Topology A.JoinSpec
  := (Alg.JoinSpec.OpenBasis A).Topology

def JoinClosedPres.InducedMap.Continuous {X : Alg.{ℓ₁}} {Y : Alg.{ℓ₂}} {r : Rel X Y}
    (rJP : r.FnJoinClosedPres)
  : Continuous (Alg.JoinSpec.Topology X) (Alg.JoinSpec.Topology Y)
               (JoinClosedPres.InducedMap @rJP)
 := sorry
--  := begin
--       apply OpenBasis.Continuous,
--       intros U Uopen,
--       cases Uopen with ys E, subst E,
--       induction ys with y ys,
--       { existsi (λ U, U = JoinSpec.BasicOpen (λ x, false)),
--         apply and.intro,
--         { intros O E,
--           have E' : O = JoinSpec.BasicOpen (λ x, false) := E,
--           subst E', clear E,
--           existsi list.nil,
--           trivial
--         },
--         { apply funext, intro j,
--           apply iff.to_eq,
--           apply iff.intro,
--           { intro Hj,
--             existsi (λ x, true),
--             refine exists.intro _ true.intro,
--             apply funext,
--             intro J',
--             apply iff.to_eq,
--             apply iff.intro,
--             { intro T,
--               intros x Hx,
--               exact false.elim Hx
--             },
--             { intro T, exact true.intro }
--           },
--           { intros Hj y Hy,
--             exact false.elim Hy
--           }
--         }
--       },
--       { cases ih_1 with O HO,
--         cases HO with HO E,
--         have E' : PreImage (JoinClosedPres.InducedMap @rJP) (JoinSpec.BasicOpen (λ (x : Y.τ), x ∈ y :: ys))
--                     = set.sUnion ((λ x, JoinSpec.BasicOpen (eq x)) <$> r.Fib y) ∩ set.sUnion O, from
--           begin
--             rw E.symm, clear E,
--             apply funext, intro J,
--             apply iff.to_eq,
--             apply iff.intro,
--             { intro HJ,
--               apply and.intro,
--               { have Q : y ∈ r.Fn J.set := HJ (or.inl rfl),
--                 apply Q.elim,
--                 intros x Jx Rxy,
--                 existsi JoinSpec.BasicOpen (eq x),
--                 refine exists.intro _ _,
--                 { existsi x, exact and.intro Rxy rfl },
--                 { intros x' E,
--                   have E' : x = x' := E,
--                   subst E', clear E,
--                   exact Jx
--                 }
--               },
--               { intros y' Hy,
--                 exact HJ (or.inr Hy)
--               }
--             },
--             { intros HJ y' Hy',
--               cases Hy' with Hy' Hy',
--               { subst Hy',
--                 cases HJ.1 with O HO,
--                 cases HO with HO JO,
--                 cases HO with x HO,
--                 cases HO with Rxy' E,
--                 subst E,
--                 existsi x,
--                 exact and.intro (JO rfl) Rxy',
--               },
--               { exact HJ.2 Hy' }
--             }
--           end,
--         rw E', clear E' E,
--         apply Topology.Ointer,
--         { apply Topology.Ounion,
--           intros U HU,
--           cases HU with x HU,
--           cases HU with Rxy E,
--           subst E,
--           apply OpenBasis.BaseOpen,
--           existsi (list.cons x list.nil),
--           apply congr_arg JoinSpec.BasicOpen,
--           apply funext, intro x',
--           apply iff.to_eq,
--           apply iff.intro,
--           { simp, apply eq.symm },
--           { simp, apply eq.symm }
--         },
--         { apply Topology.Ounion,
--           intros O' HO',
--           apply OpenBasis.BaseOpen,
--           exact HO HO',
--         }
--       }
--     end

end Sep
