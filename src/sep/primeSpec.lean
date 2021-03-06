/- The prime-spectrum of a separation algebra.
 -
 -/
import .basic
import .rel
import .ordalg
import ..top.basic
import ..extralib

namespace Sep
universes ℓ ℓ₁ ℓ₂
open Top

structure OrdAlg.PrimeSpec (A : OrdAlg.{ℓ}) : Type.{ℓ}
 := (set : Set A.alg)
    (prime : set.Prime)
    (locl : A.ord.FnInv set = set)

def PrimeSpec.eq {A : OrdAlg.{ℓ}} (p₁ p₂ : A.PrimeSpec)
  : p₁.set = p₂.set → p₁ = p₂
 := begin
      intro E,
      cases p₁ with p₁ H₁,
      cases p₂ with p₂ H₂,
      simp at E,
      subst E
    end

def PrimePres.InducedMap {X : OrdAlg.{ℓ₁}} {Y : OrdAlg.{ℓ₂}} {r : OrdRel X Y}
    (rPP : r.rel.PrimePres)
  : Y.PrimeSpec → X.PrimeSpec
 := λ p, { set := r.rel.FnInv p.set
         , prime := Rel.PrimePres_iff.2 @rPP p.prime
         , locl := begin
                    apply funext, intro x₁,
                    apply iff.to_eq,
                    apply iff.intro,
                    { intro H,
                      cases H with x₂ H,
                      cases H with H Lx,
                      cases H with y₂ H,
                      cases H with Hpy₂ R₂,
                      have Q := r.incr _ _ _ R₂ Lx,
                      cases Q with y₁ Q,
                      cases Q with R₁ Ly,
                      have Hpy₁ : y₁ ∈ p.set, from
                        begin
                          rw p.locl.symm,
                          existsi y₂,
                          exact and.intro Hpy₂ Ly
                        end,
                      existsi y₁,
                      exact and.intro Hpy₁ R₁
                    },
                    { intro H,
                      cases H with y₁ H,
                      cases H with Hpy₁ R₁,
                      existsi x₁,
                      refine and.intro _ (X.refl _),
                      existsi y₁,
                      exact and.intro Hpy₁ R₁
                    }
                   end
                   --r.ConfinedPres p.locl
         }

def PrimeSpec.BasicOpen {A : OrdAlg.{ℓ}} (S : Set A.alg) : set A.PrimeSpec
  := λ p, ∀ {s}, ¬ s ∈ S ∩ p.set

def PrimePres.InducedMap.BasicPreImage {X : OrdAlg.{ℓ₁}} {Y : OrdAlg.{ℓ₂}} (r : OrdRel X Y)
    (rPP : r.rel.PrimePres)
    (xs : Set X.alg)
  : PreImage (PrimePres.InducedMap @rPP) (PrimeSpec.BasicOpen xs)
      = PrimeSpec.BasicOpen (r.rel.Fn xs)
 := begin
      apply funext, intro p,
      apply iff.to_eq, apply iff.intro,
      { intros H y Hy,
        apply Hy.1.elim,
        intros x Hxxs Rxy,
        refine H (and.intro Hxxs _),
        existsi y,
        exact and.intro Hy.2 Rxy
      },
      { intros H x Hx,
        cases Hx.2 with y Hy,
        refine H (and.intro _ Hy.1),
        existsi x,
        exact and.intro Hx.1 Hy.2
      }
    end

def PrimeSpec.BasicOpen.intersection {A : OrdAlg.{ℓ}} (S₁ S₂ : Set A.alg)
  : PrimeSpec.BasicOpen S₁ ∩ PrimeSpec.BasicOpen S₂ = PrimeSpec.BasicOpen (S₁ ∪ S₂)
 := begin
      apply funext, intro p,
      apply iff.to_eq, apply iff.intro,
      { intros H x Hx, cases Hx with Sx Px,
        cases Sx with Sx Sx,
        { exact H.1 (and.intro Sx Px) },
        { exact H.2 (and.intro Sx Px) }
      },
      { intro H, apply and.intro,
        { intros x Hx, exact H (and.intro (or.inl Hx.1) Hx.2) },
        { intros x Hx, exact H (and.intro (or.inr Hx.1) Hx.2) }
      }
    end

def PrimeSpec.BasicOpen.intersection₀ {A : OrdAlg.{ℓ}} (S : set (Set A.alg))
  : set.sInter (PrimeSpec.BasicOpen <$> S)
      = PrimeSpec.BasicOpen (set.sUnion S)
 := begin
      apply funext, intro p,
      apply iff.to_eq, apply iff.intro,
      { intros H x Hx,
        cases Hx.1 with T H,
        cases H with HTS HxT,
        refine H (PrimeSpec.BasicOpen T) _ (and.intro HxT Hx.2),
        existsi T,
        exact and.intro HTS rfl
      },
      { intros H O HO,
        cases HO with T HO,
        cases HO with HTS E,
        have E' := E.symm, subst E', clear E,
        intros x Hx,
        refine H (and.intro _ Hx.2),
        existsi T,
        exact exists.intro HTS Hx.1
      }
    end

def OrdAlg.PrimeSpec.OpenBasis (A : OrdAlg.{ℓ}) : OpenBasis A.PrimeSpec
 := { OI := Set A.alg
    , Open := PrimeSpec.BasicOpen
    , Cover := begin
                apply funext, intro p,
                apply iff.to_eq,
                apply iff.intro,
                { intro T, clear T,
                  existsi (λ x, true),
                  apply exists.intro,
                  { apply exists.intro ∅,
                    apply funext, intro p',
                    apply iff.to_eq,
                    apply iff.intro,
                    { intro T, clear T,
                      intros x Hx,
                      exact Hx.1
                    },
                    { intro H, constructor }
                  },
                  { constructor }
                },
                { intro H, constructor }
               end
    , inter := λ S₁ S₂, S₁ ∪ S₂
    , Ointer := begin
                  intros U₁ U₂,
                  apply funext, intro p,
                  apply iff.to_eq, apply iff.intro,
                  { intro H,
                    apply and.intro,
                    { intros x Hx,
                      exact H (and.intro (or.inl Hx.1) Hx.2)
                    },
                    { intros x Hx,
                      exact H (and.intro (or.inr Hx.1) Hx.2)
                    }
                  },
                  { intro H,
                    cases H with H₁ H₂,
                    intros x Hx,
                    cases Hx with Hx Hxp,
                    cases Hx with Hx Hx,
                    { exact H₁ (and.intro Hx Hxp) },
                    { exact H₂ (and.intro Hx Hxp) }
                  }
                end
    }

def OrdAlg.PrimeSpec.Topology (A : OrdAlg.{ℓ}) : Topology A.PrimeSpec
  := (OrdAlg.PrimeSpec.OpenBasis A).Topology

def PrimePres.InducedMap.Continuous {X : OrdAlg.{ℓ₁}} {Y : OrdAlg.{ℓ₂}} (r : OrdRel X Y)
    (rPP : r.rel.PrimePres)
  : Continuous (OrdAlg.PrimeSpec.Topology Y) (OrdAlg.PrimeSpec.Topology X)
               (PrimePres.InducedMap @rPP)
 := begin
      let c : (OrdAlg.PrimeSpec.OpenBasis X).OI → (OrdAlg.PrimeSpec.Topology Y).OI
           := λ x y, y = r.rel.Fn x,
      apply OpenBasis.Continuous c,
      intro oix,
      apply funext, intro p,
      apply iff.to_eq, apply iff.intro,
      { intro H,
        existsi PreImage (PrimePres.InducedMap @rPP) (PrimeSpec.BasicOpen oix),
        refine exists.intro _ _,
        { existsi r.rel.Fn oix,
          apply and.intro rfl,
          rw PrimePres.InducedMap.BasicPreImage,
          trivial
        },
        { intros x Hx,
          exact H Hx
        }
      },
      { intro H,
        cases H with U H,
        cases H with H Hpu,
        cases H with V H,
        cases H with E₁ E₂,
        have E : V = r.rel.Fn oix := E₁, subst E, clear E₁,
        have E := E₂.symm, subst E, clear E₂,
        intros x Hx,
        cases Hx with Hx H,
        cases H with y H,
        apply Hpu (and.intro _ H.1),
        existsi x,
        exact and.intro Hx H.2
      }
    end


-- def Alg.PrimeSpec.OpenBasis (A : Alg.{ℓ}) : OpenBasis A.PrimeSpec
--  := { Open := λ U, ∃ (xs : list A.τ), U = PrimeSpec.BasicOpen (λ x, x ∈ xs)
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
--                       exact Hx.1
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
--                     have Qx : x ∈ L₁ ∨ x ∈ L₂, from set.in_append Hx.1,
--                     cases Qx with Qx Qx,
--                     { exact H.1 (and.intro Qx Hx.2) },
--                     { exact H.2 (and.intro Qx Hx.2) }
--                   },
--                   { intro H,
--                     apply and.intro,
--                     { intros x Hx,
--                       have Qx : x ∈ list.append L₁ L₂, from set.in_append_left Hx.1,
--                       exact H (and.intro Qx Hx.2)
--                     },
--                     { intros x Hx,
--                       have Qx : x ∈ list.append L₁ L₂, from set.in_append_right Hx.1,
--                       exact H (and.intro Qx Hx.2)
--                     }
--                   }
--                 end
--     }

-- def Alg.PrimeSpec.Topology (A : Alg.{ℓ}) : Topology A.PrimeSpec
--   := (Alg.PrimeSpec.OpenBasis A).Topology

-- def PrimePres.InducedMap.Continuous {X : Alg.{ℓ₁}} {Y : Alg.{ℓ₂}} (r : Rel X Y)
--     (rPP : r.PrimePres)
--     (rFI : r.FinIm)
--   : Continuous (Alg.PrimeSpec.Topology Y) (Alg.PrimeSpec.Topology X)
--                (PrimePres.InducedMap @rPP)
--  := begin
--       apply OpenBasis.Continuous,
--       intros U Uopen,
--       cases Uopen with xs E, subst E,
--       have Q : ∃ (ys : list Y.τ)
--                , (∀ {y}, y ∈ ys → ∃ x, x ∈ xs ∧ r x y)
--                ∧ (∀ {x y}, x ∈ xs ∧ r x y → y ∈ ys)
--              , from begin
--                       induction xs with x xs,
--                       { existsi list.nil, apply and.intro,
--                         { intros y Hy, exact false.elim Hy },
--                         { intros x y Hx, exact false.elim Hx.1 }
--                       },
--                       { cases ih_1 with ys' Hys' x xs,
--                         cases rFI x with ys Hys,
--                         existsi list.append ys ys',
--                         apply and.intro,
--                         { intros y Hy,
--                           have Hy' : y ∈ ys ∨ y ∈ ys', from set.in_append Hy,
--                           cases Hy' with Hy' Hy',
--                           { existsi x,
--                             apply and.intro,
--                             { exact or.inl rfl },
--                             { exact (Hys _).2 Hy' }
--                           },
--                           { cases Hys'.1 Hy' with x' Hx',
--                             existsi x',
--                             refine and.intro (or.inr Hx'.1) Hx'.2,
--                           }
--                         },
--                         { intros x' y Hx'y,
--                           cases Hx'y with Hx' Rx'y,
--                           cases Hx' with Hx' Hx',
--                           { subst Hx',
--                             have Q : y ∈ ys := (Hys _).1 Rx'y,
--                             exact set.in_append_left Q
--                           },
--                           { dsimp at Hx',
--                             have Q : y ∈ ys' := Hys'.2 (and.intro Hx' Rx'y),
--                             exact set.in_append_right Q
--                           }
--                         }
--                       }
--                     end,
--       cases Q with ys Hys,
--       let W : set Y.PrimeSpec := PrimeSpec.BasicOpen (λ y, y ∈ ys),
--       existsi (eq W),
--       apply and.intro,
--       { intros W' E,
--         have E' : W = W', from E, subst E',
--         existsi ys, trivial
--       },
--       { apply funext, intro p,
--         apply iff.to_eq,
--         apply iff.intro,
--         { intro H,
--           existsi W,
--           apply exists.intro rfl,
--           intros y Hy,
--           cases (Hys.1 Hy.1) with x Hx,
--           apply @H x,
--           apply and.intro Hx.1,
--           existsi y,
--           exact and.intro Hy.2 Hx.2,
--         },
--         { intros H x Hx,
--           cases H with W' H,
--           cases H with E Hp,
--           have E' : W = W', from E, subst E', clear E,
--           apply Rel.FnInv.elim Hx.2,
--           intros y Hy Rxy,
--           refine Hp (and.intro _ Hy),
--           exact Hys.2 (and.intro Hx.1 Rxy)
--         }
--       }
--     end


-- Here we allow C to be an arbitrary set, but in practice the only
-- sets worth considering are those which are intersections of prime
-- sets.
def PrimeSpec.BasicClosed {A : OrdAlg.{ℓ}} (C : Set A.alg) : set A.PrimeSpec
  := λ p, C ⊆ p.set

-- When S is finite, BasicOpen S is an open set in the sense that
-- it is a complement of a finite union of closed sets.
def PrimeSpec.BasicOpen.IsOpen {A : OrdAlg.{ℓ}} (S : Set A.alg)
  : PrimeSpec.BasicOpen S
      = set.compl (set.sUnion ((λ s, PrimeSpec.BasicClosed (eq s)) <$> S))
 := begin
      apply funext, intro p,
      apply iff.to_eq, apply iff.intro,
      { intros H Hp,
        cases Hp with T Hp,
        cases Hp with HT Hs,
        cases HT with t HT,
        refine H (and.intro HT.1 _),
        have E : T = PrimeSpec.BasicClosed (eq t) := HT.2.symm,
        subst E,
        exact Hs rfl
      },
      { intros Hp x Hx,
        apply Hp,
        existsi (PrimeSpec.BasicClosed (eq x)),
        constructor,
        { existsi x, exact and.intro Hx.1 rfl },
        { intros x' Hx',
          have E : x = x' := Hx',
          subst E,
          exact Hx.2
        }
      }
    end


-- BasicClosed I really is a closed set.
def PrimeSpec.BasicClosed.IsClosed {A : OrdAlg.{ℓ}} (I : Set A.alg)
  : PrimeSpec.BasicClosed I =
      set.compl (set.sUnion ((λ i, PrimeSpec.BasicOpen (eq i)) <$> I))
 := begin
      apply funext, intro p,
      apply iff.to_eq, apply iff.intro,
      { intros H Hp,
        cases Hp with U HU,
        cases HU with HU Hp,
        cases HU with i HU,
        cases HU with Hi E,
        subst E,
        exact Hp (and.intro rfl (H Hi)),
      },
      { intros H x Ix,
        apply classical.by_contradiction,
        intro C,
        apply H,
        existsi (PrimeSpec.BasicOpen (eq x)),
        apply exists.intro,
        { existsi x, exact and.intro Ix rfl },
        { intros x' Hx',
          refine C (cast _ Hx'.2),
          have E : x = x' := Hx'.1,
          subst E
        }
      }
    end

def PrimeSpec.BasicClosed.intersection {A : OrdAlg.{ℓ}} (I₁ I₂ : Set A.alg)
  : PrimeSpec.BasicClosed (I₁ ∪ I₂) = PrimeSpec.BasicClosed I₁ ∩ PrimeSpec.BasicClosed I₂
 := begin
      apply funext, intro p,
      apply iff.to_eq, apply iff.intro,
      { intro H, apply and.intro,
        { intros a Ha, exact H (or.inl Ha) },
        { intros a Ha, exact H (or.inr Ha) },
      },
      { intros H a Ha, cases Ha with Ha Ha,
        { exact H.1 Ha },
        { exact H.2 Ha }
      }
    end

def PrimeSpec.BasicClosed.union {A : OrdAlg.{ℓ}} (I₁ I₂ : Set A.alg)
  (I₁ideal : I₁.Ideal)
  (I₂ideal : I₂.Ideal)
  : PrimeSpec.BasicClosed I₁ ∪ PrimeSpec.BasicClosed I₂
      = PrimeSpec.BasicClosed (I₁ ∩ I₂)
          ∩ (PrimeSpec.BasicClosed (I₁ <-> I₂) ∪ PrimeSpec.BasicClosed (I₂ <-> I₁))
 := begin
      apply funext, intro p,
      apply iff.to_eq, apply iff.intro,
      { intro H,
        apply and.intro,
        { intros x Ix,
          cases H with H H,
          { exact H Ix.1 },
          { exact H Ix.2 }
        },
        { cases H with H H,
          { apply or.inl, intros x Hx, apply H, apply Hx.1 },
          { apply or.inr, intros x Hx, apply H, apply Hx.1 }
        }
      },
      { intro H, cases H with H₁ H₂,
        have Z : ¬ ((∃ x₁, x₁ ∈ set.diff I₁ p.set) ∧ (∃ x₂, x₂ ∈ set.diff I₂ p.set)), from
          begin
            intro Q, cases Q with Q₁ Q₂, cases Q₁ with x₁ Q₁, cases Q₂ with x₂ Q₂,
            cases classical.em (∃ z, A.alg.join x₁ x₂ z) with Jx Jx,
            { cases Jx with z Jx,
              have Hz : z ∈ p.set, from
                begin
                  apply H₁, apply and.intro,
                  { apply I₁ideal Q₁.1 Jx },
                  { apply I₂ideal Q₂.1 (A.alg.comm Jx) }
                end,
              cases p.prime _ _ _ Jx Hz with Z Z,
              { apply Q₁.2, assumption },
              { apply Q₂.2, assumption }
            },
            { cases H₂ with H₂ H₂,
              { apply Q₁.2, apply H₂, apply and.intro Q₁.1,
                existsi x₂, apply and.intro Q₂.1, intros z Jz,
                apply Jx, existsi z, exact Jz
              },
              { apply Q₂.2, apply H₂, apply and.intro Q₂.1,
                existsi x₁, apply and.intro Q₁.1, intros z Jz,
                apply Jx, existsi z, exact (A.alg.comm Jz)
              }
            }
          end,
        clear H₁ H₂,
        have Helper : ∀ {P Q : Prop}, ¬ (P ∧ Q) → ¬ P ∨ ¬ Q, from
          begin
            intros P Q HH,
            cases classical.em P with HP HP,
            { cases classical.em Q with HQ HQ,
              { apply false.elim, apply HH, constructor, repeat { assumption } },
              { exact or.inr HQ }
            },
            { exact or.inl HP }
          end,
        cases Helper Z with ZZ ZZ,
        { have ZZ' := forall_not_of_not_exists ZZ,
          apply or.inl, intros x Ix,
          apply classical.by_contradiction, intro Px,
          apply ZZ' x (and.intro Ix Px)
        },
        { have ZZ' := forall_not_of_not_exists ZZ,
          apply or.inr, intros x Ix,
          apply classical.by_contradiction, intro Px,
          apply ZZ' x (and.intro Ix Px)
        }
      }
    end

def OrdAlg.ZeroPt (A : OrdAlg.{ℓ}) : A.PrimeSpec
 := { set := ∅
    , prime := EmptyPrime _
    , locl := Rel.FnInv.Empty _
    }

def ZeroPt.BasisEverywhere {X : OrdAlg.{ℓ}} {S : Set X.alg}
  : X.ZeroPt ∈ (OrdAlg.PrimeSpec.OpenBasis X).Open S
 := begin
      intro z, intro F,
      cases F with F₁ F₂,
      cases F₂
    end

def ZeroPt.Everywhere {X : OrdAlg.{ℓ}} {S : Set X.alg}
  : X.ZeroPt ∈ (OrdAlg.PrimeSpec.Topology X).Open (eq S)
 := begin
      existsi (OrdAlg.PrimeSpec.OpenBasis X).Open S,
      refine exists.intro _ _,
      { existsi S, exact and.intro rfl rfl
      },
      { intro z, intro F,
        cases F with F₁ F₂,
        cases F₂
      }
    end

def OrdAlg.BigPt (A : OrdAlg.{ℓ}) (AUC : A.ord.UpClosed)
    (S : Set A.alg)
    (HS : A.ord.FnInv (JoinClosure S).Compl = (JoinClosure S).Compl)
  : A.PrimeSpec
 := { set := (JoinClosure S).Compl
    , prime := begin
                apply Set.JoinClosed.Complement_Prime,
                apply JoinClosure.JoinClosed
              end
    , locl := HS
    }

def BigPt.In {X : OrdAlg.{ℓ}} {XUC : X.ord.UpClosed} {S : Set X.alg}
    {HS : X.ord.FnInv (JoinClosure S).Compl = (JoinClosure S).Compl}
  : X.BigPt @XUC S HS ∈ (OrdAlg.PrimeSpec.Topology X).Open (eq S)
 := begin
      existsi (OrdAlg.PrimeSpec.OpenBasis X).Open S,
      refine exists.intro _ _,
      { existsi S, exact and.intro rfl rfl },
      { intros x F,
        cases F with HSx F,
        apply F, clear F,
        apply JoinClosure.gen,
        assumption
      }
    end

-- def OrdAlg.BigPt (A : OrdAlg.{ℓ}) (AUC : A.ord.UpClosed) (S : Set A.alg)
--   : A.PrimeSpec
--  := { set := A.ord.FnInv (JoinClosure (A.ord.Fn S)).Compl
--     , prime := begin
--                 apply UpClosed.PrimePres,
--                 { assumption },
--                 { apply Set.JoinClosed.Complement_Prime,
--                   apply JoinClosure.JoinClosed
--                 }
--               end
--     , locl := begin
--                 intros x H, cases H with y H,
--                 cases H with H Rxy,
--                 cases H with z H,
--                 cases H with Hz Ryz,
--                 existsi z,
--                 refine and.intro Hz _,
--                 apply A.trans,
--                 repeat { assumption }
--               end
--     }

-- def BigPt.In {X : OrdAlg.{ℓ}} {XUC : X.ord.UpClosed} {S : Set X.alg}
--   : X.BigPt @XUC S ∈ (OrdAlg.PrimeSpec.Topology X).Open (eq S)
--  := begin
--       existsi (OrdAlg.PrimeSpec.OpenBasis X).Open S,
--       refine exists.intro _ _,
--       { existsi S, exact and.intro rfl rfl },
--       { intros x F,
--         cases F with HSx F,
--         cases F with y F,
--         cases F with F Rxy,
--         apply F,
--         apply JoinClosure.gen,
--         existsi x, exact and.intro HSx Rxy
--       }
--     end

-- def OrdAlg.BigPt (A : OrdAlg.{ℓ}) (S : Set A.alg) : A.PrimeSpec
--  := { set := set.sUnion ((λ (p : OrdAlg.PrimeSpec A), p.set) <$> (PrimeSpec.BasicOpen S))
--     , prime := Prime.Union _
--                 begin
--                   intros p H,
--                   cases H with p' H,
--                   cases H with H E,
--                   subst E,
--                   exact p'.prime
--                 end
--     , locl := begin
--                 intros x H, cases H with y H,
--                 cases H with H Rxy,
--                 cases H with S H,
--                 cases H with H HSy,
--                 cases H with p H,
--                 cases H with Hp E,
--                 subst E,
--                 existsi p.set,
--                 refine exists.intro _ _,
--                 { existsi p, exact and.intro @Hp rfl },
--                 { exact p.locl ⟨_, and.intro HSy Rxy⟩ }
--               end
--     }

-- def BigPt.In {X : OrdAlg.{ℓ}} {S : Set X.alg}
--   : X.BigPt S ∈ (OrdAlg.PrimeSpec.Topology X).Open (eq S)
--  := begin
--       existsi (OrdAlg.PrimeSpec.OpenBasis X).Open S,
--       refine exists.intro _ _,
--       { existsi S, exact and.intro rfl rfl
--       },
--       { intro z, intro F,
--         cases F with F H,
--         cases H with U H,
--         cases H with H Hz,
--         cases H with p H,
--         cases H with Hp E,
--         subst E,
--         exact Hp (and.intro F Hz)
--       }
--     end

end Sep
