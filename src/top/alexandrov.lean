/- Topological spaces
 -
 -/
import .basic

namespace Top
universes ℓ ℓ₁ ℓ₂ ℓ₁₁ ℓ₂₂

structure PreOrder
  : Type.{ℓ+1}
 := (pt : Type.{ℓ})
    (rel : pt → pt → Prop)
    (refl : ∀ a, rel a a)
    (trans : ∀ a b c, rel a b → rel b c → rel a c)
    (join : ∀ x y, { z // ∀ w, rel x w ∧ rel y w ↔ rel z w})

def PreOrder.OpenBasis (A : PreOrder.{ℓ₁})
  : OpenBasis A.pt
 := { OI := A.pt
    , Open := λ x y, A.rel x y
    , Cover
       := begin
            apply funext, intro x,
            apply eq.symm, apply iff.to_eq, apply iff.intro,
            { intro H, constructor },
            { intro H, clear H,
              exact exists.intro _ (exists.intro (exists.intro _ rfl) (A.refl _))
            }
          end
    , inter := λ x y, (A.join x y).val
    , Ointer
       := λ x y
          , begin
              apply funext, intro w,
              apply iff.to_eq, apply iff.intro,
              { intro H,
                apply ((A.join x y).property _).2,
                exact H
              },
              { intro H,
                apply ((A.join x y).property _).1,
                exact H
              }
            end
    }

def PreOrder.Top (A : PreOrder.{ℓ₁})
  : Topology A.pt
 := A.OpenBasis.Topology


-- open Sep

-- structure PreOrder.Fn (A : PreOrder.{ℓ₁})
--     (alg : A.pt → OrdAlg.{ℓ₂})
--     (res : ∀ p q, A.rel q p → OrdRel (alg p) (alg q))
--     (U : A.Top.OI)
--  := (fn : ∀ (p : {p // p ∈ A.Top.Open U})
--           , (alg p.val).alg.τ)
--     (continuous : ∀ (p q : {p // p ∈ A.Top.Open U})
--                     (H : A.rel q.val p.val)
--                   , (res p.val q.val H).rel (fn p) (fn q))

-- def PreOrder.Fn.eq {A : PreOrder.{ℓ₁}}
--     {alg : A.pt → OrdAlg.{ℓ₂}}
--     {res : ∀ p q, A.rel q p → OrdRel (alg p) (alg q)}
--     {U : A.Top.OI}
--     (s t : A.Fn alg res U)
--     (E : s.fn = t.fn)
--   : s = t
--  := begin cases s, cases t, simp at E, subst E end

-- def PreOrder.Sec (A : PreOrder.{ℓ₁})
--     (alg : A.pt → OrdAlg.{ℓ₂})
--     (closed : (∀ a, (alg a).ord.UpClosed) ∨ (∀ a, (alg a).ord.DownClosed))
--     (res : ∀ p q, A.rel q p → OrdRel (alg p) (alg q))
--     (U : A.Top.OI)
--   : OrdAlg
--  := { alg :=
--           { τ := A.Fn alg res U
--           , join := λ s₁ s₂ s₃
--                     , ∀ (p : {p // p ∈ A.Top.Open U})
--                       , (alg p.val).alg.join (s₁.fn p) (s₂.fn p) (s₃.fn p)
--           , comm := λ s₁ s₂ s₃ J p
--                     , (alg p.val).alg.comm (J p)
--           , assoc := λ s₁ s₂ s₃ s₁₂ s₁₂₃ J₁₂ J₁₂₃ P C
--                     , sorry
--           }
--         , ord := λ s t, ∀ (p : {p // p ∈ A.Top.Open U})
--                         , s.fn p ≤ t.fn p
--         , refl := λ s p, (alg p.val).refl _
--         , trans := λ a b c H₁₂ H₁₂₃ p
--                    , (alg p.val).trans _ _ _ (H₁₂ p) (H₁₂₃ p)
--         , closed
--            := begin
--                 cases closed with H H,
--                 { apply or.inl,
--                   intros x₁ x₂ x₃ y₃ J R,
--                   exact sorry
--                 },
--                 { apply or.inr,
--                   exact sorry
--                 }
--               end
--         }

-- def PreOrder.ρ (A : PreOrder.{ℓ₁})
--     (alg : A.pt → OrdAlg.{ℓ₂})
--     (closed : (∀ a, (alg a).ord.UpClosed) ∨ (∀ a, (alg a).ord.DownClosed))
--     (res : ∀ p q, A.rel q p → OrdRel (alg p) (alg q))
--     (U₁ U₂ : (PreOrder.Top A).OI)
--     (HU₁U₂ : (PreOrder.Top A).Open U₂ ⊆ (PreOrder.Top A).Open U₁)
--   : OrdRel (PreOrder.Sec A alg closed res U₁) (PreOrder.Sec A alg closed res U₂)
--  := { rel := λ s t
--               , ∀ (p : {p // p ∈ A.Top.Open U₁})
--                   (q : {p // p ∈ A.Top.Open U₂})
--                   (R : A.rel q.val p.val)
--                 , (res p.val q.val R).rel (s.fn p) (t.fn q)
--     , action
--         := begin
--             apply funext, intro s, apply funext, intro t,
--             apply iff.to_eq, apply iff.intro,
--             { intro H,
--               cases H with t' H, cases H with H Rt,
--               cases H with s' H, cases H with Rs H,
--               intros p q R,
--               have Qt := Rt q,
--               have Qs := Rs p,
--               have Q₁ := H p q R, clear H,
--               rw (res (p.val) (q.val) R).action.symm,
--               refine exists.intro _ (and.intro _ Qt),
--               exact exists.intro _ (and.intro Qs Q₁)
--             },
--             { intro H,
--               existsi t,
--               refine and.intro _ _,
--               { existsi s,
--                 apply and.intro,
--                 { intro p, apply OrdAlg.refl },
--                 { intros p q R, apply H }
--               },
--               { intro p, apply OrdAlg.refl }
--             }
--           end
--     }

-- def PreOrder.Sheaf (A : PreOrder.{ℓ₁})
--     (alg : A.pt → OrdAlg.{ℓ₂})
--     (closed : (∀ a, (alg a).ord.UpClosed) ∨ (∀ a, (alg a).ord.DownClosed))
--     (res : ∀ p q, A.rel q p → OrdRel (alg p) (alg q))
--     (res_id : ∀ p H, res p p H = OrdAlg.IdRel _)
--     (glue : ∀ p q H x' x y
--             , x' ≤ x
--             → (res p q H).rel x' y
--             → (res p q H).rel x y)
--   : Sheaf A.Top
--  := { Section := A.Sec alg closed res
--     , Stalk := λ p, true.intro
--     , ρ := A.ρ alg closed res
--     , ρ_id := λ U HUU
--               , begin
--                   apply OrdRel.eq,
--                   apply funext, intro s, apply funext, intro t,
--                   apply iff.to_eq, apply iff.intro,
--                   { intros H p,
--                     have Q := (H p p (A.refl _)),
--                     rw res_id at Q,
--                     exact Q
--                   },
--                   { intros H p q R,
--                     have Q := s.continuous p q R,
--                     rw (res (p.val) (q.val) R).action.symm,
--                     refine exists.intro _ (and.intro _ (H q)),
--                     refine exists.intro _ (and.intro _ Q),
--                     apply OrdAlg.refl
--                   }
--                 end
--     , ρ_circ := λ U₁ U₂ U₃ H₂₁ H₃₂ H₃₁
--                 , begin
--                     apply OrdRel.eq, simp,
--                     apply funext, intro s, apply funext, intro t,
--                     apply iff.to_eq, apply iff.intro,
--                     { intros H p₁ p₃ R,
--                       let p₂ : {p // p ∈ (PreOrder.Top A).Open U₂}
--                              := { val := p₃.val
--                                 , property := H₃₂ p₃.property
--                                 },
--                       cases H with t' H, cases H with H Rt,
--                       cases H with s' H, cases H with Rs H,
--                       have Qt := Rt p₂ p₃ (A.refl _),
--                       have Qs := Rs p₁ p₂ R,
--                       exact sorry
--                     },
--                     { intros H,
--                       exact sorry
--                       -- refine exists.intro _ (and.intro (exists.intro _ (and.intro _ (OrdAlg.refl _ _))) _),
--                       -- { refine { fn := λ p
--                       --                  , let p' : {p // p ∈ (PreOrder.Top A).Open U₁}
--                       --                          := { val := p.val, property := H₂₁ p.property }
--                       --                    in res p' p (A.refl _) (s.fn p')
--                       --          , continuous := _
--                       --          },
--                       --   intros p q R,
--                       --   cases p with p Hp, cases q with q Hq,
--                       --   apply and.intro,
--                       --   { have Q := s.continuous { val := q, property := H₂₁ Hq }
--                       --                            { val := q, property := H₂₁ Hq }
--                       --                            (A.refl _),
--                       --     apply OrdAlg.trans _ _ _ _ Q.2, clear Q,
--                       --     have Q := s.continuous { val := p, property := H₂₁ Hp }
--                       --                            { val := q, property := H₂₁ Hq }
--                       --                            R,
--                       --     apply OrdAlg.trans _ _ _ _ Q.1, clear Q,
--                       --     apply action,
--                       --     have Q := s.continuous { val := p, property := H₂₁ Hp }
--                       --                            { val := p, property := H₂₁ Hp }
--                       --                            (A.refl _),
--                       --     exact Q.1
--                       --   },
--                       --   { have Q := s.continuous { val := q, property := H₂₁ Hq }
--                       --                            { val := q, property := H₂₁ Hq }
--                       --                            (A.refl _),
--                       --     apply OrdAlg.trans _ _ _ _ _ Q.1, clear Q,
--                       --     have Q := s.continuous { val := p, property := H₂₁ Hp }
--                       --                            { val := q, property := H₂₁ Hq }
--                       --                            R,
--                       --     apply OrdAlg.trans _ _ _ _ _ Q.2, clear Q,
--                       --     apply action,
--                       --     have Q := s.continuous { val := p, property := H₂₁ Hp }
--                       --                            { val := p, property := H₂₁ Hp }
--                       --                            (A.refl _),
--                       --     exact Q.2
--                       --   }
--                       -- },
--                       -- { intros p q R,
--                       --   simp,
--                       --   let q' : {p // p ∈ A.Top.Open U₁}
--                       --          := { val := q.val, property := H₂₁ q.property },
--                       --   have Q := s.continuous q' q' (A.refl _),
--                       --   apply OrdAlg.trans _ _ _ _ _ Q.1, clear Q,
--                       --   have Q := s.continuous p q' R,
--                       --   apply OrdAlg.trans _ _ _ _ _ Q.2, clear Q,
--                       --   apply action,
--                       --   apply OrdAlg.refl,
--                       -- },
--                       -- { intros p q R,
--                       --   simp,
--                       --   let p' : {p // p ∈ A.Top.Open U₁}
--                       --          := { val := p.val, property := H₂₁ p.property },
--                       --   let q' : {p // p ∈ A.Top.Open U₁}
--                       --          := { val := q.val, property := H₃₁ q.property },
--                       --   refine OrdAlg.trans _ _ _ _ _ (H p' q R),
--                       --   apply action,
--                       --   have Q := (s.continuous p' p' (A.refl _)),
--                       --   apply Q.2
--                       -- }
--                     }
--                   end
--    , glue := λ U cover in_cover sub_cover X loc E
--               , begin
--                   refine exists.intro
--                           { rel := λ x s,
--                             ∀ (p : {p // p ∈ A.Top.Open U})
--                             , ∃ s', (loc p).rel x s'
--                                   ∧ (A.ρ alg closed res U (cover p) (sub_cover p)).rel s s'
--                           , action := _
--                           }
--                           (and.intro _ _),
--                   { apply funext, intro x, apply funext, intro s,
--                     dsimp at *,
--                     apply iff.to_eq, apply iff.intro,
--                     { intros H p,
--                       cases H with s' H, cases H with H Rs,
--                       cases H with x' H, cases H with Rx H,
--                       have Q := H p, clear H,
--                       cases Q with t Q, cases Q with Rxt Rts,
--                       existsi t,
--                       apply and.intro,
--                       { rw (loc p).action.symm,
--                         refine exists.intro _ (and.intro _ (OrdAlg.refl _ _)),
--                         exact exists.intro _ (and.intro Rx Rxt)
--                       },
--                       { intros a b Hab,
--                         have Qa := Rs a,
--                         have Qb := Rts a b Hab,
--                         apply glue _ _ _ _ _ _ Qa Qb
--                       }
--                     },
--                     { intro H,
--                       refine exists.intro { fn := _, continuous := _ } (and.intro _ _),
--                       { intro p,
--                         have Q := classical.indefinite_description _ (H p),
--                         cases Q with s' Q,
--                         exact s'.fn { val := p, property := in_cover p }
--                       },
--                       { intros p q R,
--                         cases classical.indefinite_description _ (H p) with wp Qp,
--                         cases classical.indefinite_description _ (H q) with wq Qq,
--                         dsimp,
--                         --
--                         have Q := congr_fun (congr_fun (congr_arg OrdRel.rel (E p q)) x)
--                                     { fn := λ z, s.fn { val := z.val, property := begin apply sub_cover p, exact sorry end }
--                                     , continuous := begin intros z₁ z₂ R, exact sorry end
--                                     },
--                         --
--                         exact sorry
--                       },
--                       { exact sorry
--                       },
--                       { exact sorry
--                       }
--                     }
--                   },
--                   { exact sorry
--                   },
--                   { exact sorry
--                   }
--                 end
--    }

end Top
