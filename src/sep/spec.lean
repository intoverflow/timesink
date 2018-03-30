/- PrimeSpec and JoinSpec are homeomorphic.
 -
 -/
import .primeSpec
import .joinSpec

namespace Sep
universes ℓ ℓ₁ ℓ₂
open Top

-- def Alg.PrimeJoin (A : Alg.{ℓ}) : A.PrimeSpec → A.JoinSpec
--  := λ p
--     , { set := p.set.Compl
--       , join := p.prime.Complement_JoinClosed
--       }

-- def Alg.JoinPrime (A : Alg.{ℓ}) : A.JoinSpec → A.PrimeSpec
--  := λ J
--     , { set := J.set.Compl
--       , prime := J.join.Complement_Prime
--       }

-- def PrimeJoin_JoinPrime {A : Alg.{ℓ}}
--   : ∀ J, A.PrimeJoin (A.JoinPrime J) = J
--  := begin
--       intro J,
--       apply JoinSpec.eq,
--       apply Set.ComplCompl
--     end

-- def JoinPrime_PrimeJoin {A : Alg.{ℓ}}
--   : ∀ p, A.JoinPrime (A.PrimeJoin p) = p
--  := begin
--       intro p,
--       apply PrimeSpec.eq,
--       apply Set.ComplCompl
--     end

-- def JoinPrime.Continuous (A : Alg.{ℓ})
--   : Continuous (Alg.JoinSpec.Topology A) (Alg.PrimeSpec.Topology A)
--                A.JoinPrime
--  := sorry
-- --  := begin
-- --       apply OpenBasis.Continuous,
-- --       intros U Uopen,
-- --       cases Uopen with xs E, subst E,
-- --       existsi (λ U, U = JoinSpec.BasicOpen (λ x, x ∈ xs)),
-- --       apply and.intro,
-- --       { intros O E,
-- --         have E' : O = JoinSpec.BasicOpen (λ x, x ∈ xs) := E,
-- --         subst E', clear E,
-- --         existsi xs,
-- --         trivial
-- --       },
-- --       { apply funext,
-- --         intro J,
-- --         apply iff.to_eq,
-- --         apply iff.intro,
-- --         { intro HJ,
-- --           existsi JoinSpec.BasicOpen (λ x, x ∈ xs),
-- --           apply exists.intro rfl _,
-- --           intros x Hx,
-- --           apply classical.by_contradiction,
-- --           intro Jx,
-- --           exact @HJ x (and.intro Hx Jx)
-- --         },
-- --         { intros HJ x Hx,
-- --           cases HJ with O HO,
-- --           cases HO with E HO,
-- --           have E' : O = JoinSpec.BasicOpen (λ x, x ∈ xs) := E,
-- --           subst E', clear E,
-- --           exact Hx.2 (HO Hx.1)
-- --         }
-- --       }
-- --     end

-- def PrimeJoin.Continuous (A : Alg.{ℓ})
--   : Continuous (Alg.PrimeSpec.Topology A) (Alg.JoinSpec.Topology A)
--                A.PrimeJoin
--  := sorry
-- --  := begin
-- --       apply OpenBasis.Continuous,
-- --       intros U Uopen,
-- --       cases Uopen with xs E, subst E,
-- --       existsi (λ U, U = PrimeSpec.BasicOpen (λ x, x ∈ xs)),
-- --       apply and.intro,
-- --       { intros O E,
-- --         have E' : O = PrimeSpec.BasicOpen (λ x, x ∈ xs) := E,
-- --         subst E', clear E,
-- --         existsi xs,
-- --         trivial
-- --       },
-- --       { apply funext,
-- --         intro p,
-- --         apply iff.to_eq,
-- --         apply iff.intro,
-- --         { intro Hp,
-- --           existsi PrimeSpec.BasicOpen (λ x, x ∈ xs),
-- --           apply exists.intro rfl _,
-- --           intros x Hx,
-- --           exact Hp Hx.1 Hx.2,
-- --         },
-- --         { intros Hp x Hx Hxp,
-- --           cases Hp with O HO,
-- --           cases HO with E HO,
-- --           have E' : O = PrimeSpec.BasicOpen (λ x, x ∈ xs) := E,
-- --           subst E', clear E,
-- --           exact HO (and.intro Hx Hxp)
-- --         }
-- --       }
-- --     end


-- def Alg.Spec.Homeomorphism (A : Alg.{ℓ})
--   : Homeomorphism (Alg.PrimeSpec.Topology A) (Alg.JoinSpec.Topology A)
--                   A.PrimeJoin A.JoinPrime
--  := { cont₁ := PrimeJoin.Continuous A
--     , cont₂ := JoinPrime.Continuous A
--     , eq₁ := JoinPrime_PrimeJoin
--     , eq₂ := PrimeJoin_JoinPrime
--     }

end Sep

