/- Topological spaces
 -
 -/
namespace Top
universes ℓ ℓ₁ ℓ₂ ℓ₁₁ ℓ₂₂

structure Topology (A : Type.{ℓ})
  : Type.{ℓ+1}
 := (OI : Type.{ℓ})
    (empty : OI)
    (whole : OI)
    (inter : OI → OI → OI)
    (union : set OI → OI)
    (Open : OI → set A)
    (Empty : Open empty = ∅)
    (Whole : Open whole = set.univ)
    (Ointer : ∀ {O₁ O₂}, Open (inter O₁ O₂) = Open O₁ ∩ Open O₂)
    (Ounion : ∀ {O : set OI}, Open (union O) = set.sUnion (λ U, ∃ oi, oi ∈ O ∧ U = Open oi))

instance OpenSet_has_inter (A : Type.{ℓ}) (TA : Topology A)
  : has_inter TA.OI
 := { inter := TA.inter
    }

def Topology.Inter.Subset_l {A : Type.{ℓ}} {TA : Topology A}
    (U₁ U₂ : TA.OI)
  : TA.Open (U₁ ∩ U₂) ⊆ TA.Open U₁
 := begin
      intros x H,
      have H' : x ∈ TA.Open (TA.inter U₁ U₂) := H,
      rw TA.Ointer at H',
      exact H'.1
    end

def Topology.Inter.Subset_r {A : Type.{ℓ}} {TA : Topology A}
    (U₁ U₂ : TA.OI)
  : TA.Open (U₁ ∩ U₂) ⊆ TA.Open U₂
 := begin
      intros x H,
      have H' : x ∈ TA.Open (TA.inter U₁ U₂) := H,
      rw TA.Ointer at H',
      exact H'.2
    end

def Topology.Cover.Subset {A : Type.{ℓ}} {TA : Topology A}
    {U : TA.OI} {UU : set TA.OI}
    (Ucover : TA.Open U = set.sUnion ((λ (U : TA.OI), TA.Open U) <$> UU))
    {V : TA.OI} (H : V ∈ UU)
  : TA.Open V ⊆ TA.Open U
 := begin
      intros x Hx,
      rw Ucover,
      existsi TA.Open V,
      refine exists.intro _ Hx,
      existsi V,
      exact and.intro H rfl
    end

def Image {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
    (f : A → B)
  : set A → set B
 := λ S b, ∃ a, b = f a

def PreImage {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
    (f : A → B)
  : set B → set A
 := λ S a, f a ∈ S

def PreImage.Compl {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
    {f : A → B}
    (S : set B)
  : PreImage f S.compl = (PreImage f S).compl
 := rfl

def Continuous {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
    (TA : Topology A) (TB : Topology B)
    (f : A → B)
  : Prop
 := ∀ OB, ∃ OA, PreImage f (TB.Open OB) = TA.Open OA

structure Homeomorphism {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
    (TA : Topology A) (TB : Topology B)
    (f : A → B)
    (g : B → A)
  : Prop
 := (cont₁ : Continuous TA TB f)
    (cont₂ : Continuous TB TA g)
    (eq₁ : ∀ a, g (f a) = a)
    (eq₂ : ∀ b, f (g b) = b)


def PreImage.Intersection {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
  {f : A → B}
  (S₁ S₂ : set B)
  : PreImage f (S₁ ∩ S₂) = PreImage f S₁ ∩ PreImage f S₂
 := begin apply funext, intro a, trivial end

def PreImage.Union {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
  {f : A → B}
  (S₁ S₂ : set B)
  : PreImage f (S₁ ∪ S₂) = PreImage f S₁ ∪ PreImage f S₂
 := begin apply funext, intro a, trivial end

def PreImage.Union₀ {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
  {f : A → B}
  (S : set (set B))
  : PreImage f (set.sUnion S) = set.sUnion (λ S₀, ∃ S', S' ∈ S ∧ S₀ = PreImage f S')
 := begin
      apply funext, intro a,
      apply iff.to_eq,
      apply iff.intro,
      { intro H, cases H with S' H,
        cases H with HSS' HaS',
        existsi (PreImage f S'),
        refine exists.intro _ HaS',
        existsi S',
        exact and.intro HSS' rfl
      },
      { intro H, cases H with SA H,
        cases H with H HaS',
        cases H with S' H,
        cases H with HS'S E,
        subst E,
        existsi S',
        existsi HS'S,
        exact HaS'
      }
    end


structure OpenBasis (A : Type.{ℓ})
  : Type.{ℓ + 1}
 := (OI : Type.{ℓ})
    (Open : OI → set A)
    (Cover : set.univ = set.sUnion (λ U, ∃ oi, U = Open oi))
    (inter : OI → OI → OI)
    (Ointer : ∀ {U₁ U₂}, Open (inter U₁ U₂) = Open U₁ ∩ Open U₂)

instance OpenBasis_OpenSet_has_inter (A : Type.{ℓ}) (TA : OpenBasis A)
  : has_inter TA.OI
 := { inter := TA.inter
    }

def OpenBasis.Inter.Subset_l {A : Type.{ℓ}} {TA : OpenBasis A}
    (U₁ U₂ : TA.OI)
  : TA.Open (U₁ ∩ U₂) ⊆ TA.Open U₁
 := begin
      intros x H,
      have H' : x ∈ TA.Open (TA.inter U₁ U₂) := H,
      rw TA.Ointer at H',
      exact H'.1
    end

def OpenBasis.Inter.Subset_r {A : Type.{ℓ}} {TA : OpenBasis A}
    (U₁ U₂ : TA.OI)
  : TA.Open (U₁ ∩ U₂) ⊆ TA.Open U₂
 := begin
      intros x H,
      have H' : x ∈ TA.Open (TA.inter U₁ U₂) := H,
      rw TA.Ointer at H',
      exact H'.2
    end

def OpenBasis.Cover.Subset {A : Type.{ℓ}} {TA : OpenBasis A}
    {U : TA.OI} {UU : set TA.OI}
    (Ucover : TA.Open U = set.sUnion ((λ (U : TA.OI), TA.Open U) <$> UU))
    {V : TA.OI} (H : V ∈ UU)
  : TA.Open V ⊆ TA.Open U
 := begin
      intros x Hx,
      rw Ucover,
      existsi TA.Open V,
      refine exists.intro _ Hx,
      existsi V,
      exact and.intro H rfl
    end

def OpenBasis.Topology {A : Type.{ℓ}} (Base : OpenBasis A)
  : Topology A
 := { OI := set Base.OI
    , empty := ∅
    , whole := set.univ
    , inter := λ U₁ U₂, set.sUnion ((λ oi₁, Base.inter oi₁ <$> U₂) <$> U₁)
    , union := λ UU, λ oi, ∀ x, x ∈ Base.Open oi → ∃ U, U ∈ UU ∧ x ∈ set.sUnion (Base.Open <$> U)
    , Open := λ UU, set.sUnion (Base.Open <$> UU)
    , Empty := begin
                apply funext, intro x,
                apply iff.to_eq, apply iff.intro,
                { intro H,
                  cases H with U H,
                  cases H with F Ux,
                  cases F with oi F,
                  exact F.1
                },
                { intro H, exact false.elim H }
               end
    , Whole := begin
                apply funext, intro x,
                apply iff.to_eq, apply iff.intro,
                { intro H, exact true.intro },
                { intro H, rw Base.Cover at H,
                  cases H with U H,
                  cases H with H Hux,
                  cases H with oi E,
                  subst E,
                  existsi Base.Open oi,
                  refine exists.intro _ Hux,
                  existsi oi,
                  exact and.intro true.intro rfl
                }
               end
    , Ointer := begin
                  intros O₁ O₂,
                  apply funext, intro x,
                  apply iff.to_eq, apply iff.intro,
                  { intro H,
                    cases H with U H,
                    cases H with H Hux,
                    cases H with oi H,
                    cases H with H E,
                    have E' := E.symm, subst E', clear E,
                    cases H with U H,
                    cases H with H₁ H₂,
                    cases H₁ with oi₁ H₁,
                    cases H₁ with Hoi₁ E,
                    have E' := E.symm, subst E', clear E,
                    cases H₂ with oi₂ H₂,
                    cases H₂ with Hoi₂ E,
                    have E' := E.symm, subst E', clear E,
                    rw Base.Ointer at Hux,
                    apply and.intro,
                    { existsi Base.Open oi₁,
                      refine exists.intro _ Hux.1,
                      existsi oi₁,
                      exact and.intro Hoi₁ rfl
                    },
                    { existsi Base.Open oi₂,
                      refine exists.intro _ Hux.2,
                      existsi oi₂,
                      exact and.intro Hoi₂ rfl
                    }
                  },
                  { intro H,
                    cases H with H₁ H₂,
                    cases H₁ with U₁ H₁,
                    cases H₁ with H₁ Hxu₁,
                    cases H₁ with oi₁ H₁,
                    cases H₁ with Hoi₁ E,
                    have E' := E.symm, subst E', clear E,
                    cases H₂ with U₂ H₂,
                    cases H₂ with H₂ Hxu₂,
                    cases H₂ with oi₂ H₂,
                    cases H₂ with Hoi₂ E,
                    have E' := E.symm, subst E', clear E,
                    existsi Base.Open (Base.inter oi₁ oi₂),
                    have Hxu : x ∈ Base.Open (Base.inter oi₁ oi₂), from
                      begin
                        rw Base.Ointer,
                        exact and.intro Hxu₁ Hxu₂,
                      end,
                    refine exists.intro _ Hxu,
                    existsi Base.inter oi₁ oi₂,
                    refine and.intro _ rfl,
                    existsi Base.inter oi₁ <$> O₂,
                    refine exists.intro _ _,
                    { existsi oi₁,
                      exact and.intro Hoi₁ rfl
                    },
                    { existsi oi₂,
                      apply and.intro Hoi₂ rfl
                    }
                  }
                end
    , Ounion := begin
                  exact sorry
                end
    }

def OpenBasis.BaseOpen {A : Type.{ℓ}} (TA : OpenBasis A)
    {oi : TA.OI}
  : TA.Open oi = TA.Topology.Open (eq oi)
 := begin
      apply funext, intro x,
      apply iff.to_eq, apply iff.intro,
      { intro H,
        existsi TA.Open oi,
        refine exists.intro _ H,
        existsi oi,
        exact and.intro rfl rfl
      },
      { intro H,
        cases H with U H,
        cases H with H Hux,
        cases H with oi' H,
        cases H with E₁ E₂,
        have E₁' : oi = oi' := E₁, subst E₁', clear E₁,
        have E₂' := E₂.symm, subst E₂', clear E₂,
        exact Hux
      }
    end

def OpenBasis.Continuous {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
  {TA : Topology A} {TB : OpenBasis B}
  {f : A → B}
  (fC : TB.OI → TA.OI)
  (HfC : ∀ oib, PreImage f (TB.Open oib) = TA.Open (fC oib))
  : Continuous TA TB.Topology f
 := begin
      intro oib,
      existsi (TA.union (λ z, ∃ (z' : TB.OI), oib z' ∧ z = fC z')),
      apply funext, intro a,
      apply iff.to_eq, apply iff.intro,
      { intro H,
        cases H with b H,
        cases H with H Hfab,
        cases H with oib₀ H,
        cases H with Hoib₀ E,
        have E' := E.symm, subst E', clear E,
        rw TA.Ounion,
        existsi PreImage f (TB.Open oib₀),
        refine exists.intro _ Hfab,
        existsi fC oib₀,
        refine and.intro _ (HfC _),
        existsi oib₀,
        exact and.intro Hoib₀ rfl
      },
      { intro H,
        rw TA.Ounion at H,
        cases H with U H,
        cases H with H Hau,
        cases H with oia H,
        cases H with Hoa E,
        subst E,
        cases Hoa with oib₀ Hoa,
        cases Hoa with Hoib₀ E,
        have E' := E.symm, subst E', clear E,
        rw (HfC oib₀).symm at Hau,
        existsi TB.Open oib₀,
        refine exists.intro _ Hau,
        existsi oib₀,
        exact and.intro Hoib₀ rfl
      }
    end



end Top
