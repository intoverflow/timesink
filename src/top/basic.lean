/- Topological spaces
 -
 -/
namespace Top
universes ℓ ℓ₁ ℓ₂

structure Topology (A : Type.{ℓ}) : Type.{ℓ}
 := (Open : set (set A))
    (Empty : Open ∅)
    (Whole : Open set.univ)
    (Ointer : ∀ {O₁ O₂}, Open O₁ → Open O₂ → Open (O₁ ∩ O₂))
    (Ounion : ∀ {O}, (O ⊆ Open) → Open (set.sUnion O))

def Topology.Closed {A : Type.{ℓ}} (TA : Topology A)
  : set (set A)
 := λ C, ∃ O, TA.Open O ∧ C = O.compl

def Image {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
    (f : A → B)
  : set A → set B
 := λ S b, ∃ a, b = f a

def OpenMap {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
    (TA : Topology A) (TB : Topology B)
    (f : A → B)
  : Prop
 := ∀ S, TA.Open S → TB.Open (Image f S)

def ClosedMap {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
    (TA : Topology A) (TB : Topology B)
    (f : A → B)
  : Prop
 := ∀ S, TA.Closed S → TB.Closed (Image f S)

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
 := ∀ S, TB.Open S → TA.Open (PreImage f S)

def Continuous.Closed {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
    {TA : Topology A} {TB : Topology B}
    {f : A → B}
    (fC : Continuous TA TB f)
  : ∀ S, TB.Closed S → TA.Closed (PreImage f S)
 := begin
      intros C Cclosed,
      cases Cclosed with O H,
      cases H with Oopen E,
      subst E,
      existsi (PreImage f O),
      exact and.intro (fC _ Oopen) (PreImage.Compl _)
    end

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


structure OpenBase (A : Type.{ℓ}) : Type.{ℓ}
 := (Open : set (set A))
    (Cover : (λ x, true) = set.sUnion Open)
    (Ointer : ∀ {U₁ U₂}, Open U₁ → Open U₂ → Open (U₁ ∩ U₂))

def OpenBase.Topology {A : Type.{ℓ}} (Base : OpenBase A)
  : Topology A
 := { Open := λ O, ∃ U, U ⊆ Base.Open ∧ O = set.sUnion U
    , Empty := begin
                existsi (λ a, false),
                apply and.intro,
                { intros a H, exact false.elim H },
                { apply funext,
                  intro a,
                  apply iff.to_eq,
                  apply iff.intro,
                  { intro H, exact false.elim H },
                  { intro H, cases H with S H,
                    cases H with H₁ H₂,
                    exact false.elim H₁
                  }
                }
               end
    , Whole := begin
                existsi Base.Open,
                apply and.intro,
                { intros a H, exact H },
                { exact Base.Cover }
               end
    , Ointer := λ O₁ O₂ OpenO₁ OpenO₂
                , begin
                    cases OpenO₁ with U₁ H₁,
                    cases OpenO₂ with U₂ H₂,
                    existsi (λ (O : set A), ∃ O₁ O₂, O₁ ∈ U₁ ∧ O₂ ∈ U₂ ∧ O = O₁ ∩ O₂),
                    apply and.intro,
                    { intros S H,
                      cases H with O₁ H,
                      cases H with O₂ H,
                      cases H with U₁O₁ H,
                      cases H with U₂O₂ E,
                      subst E,
                      apply Base.Ointer,
                      { apply H₁.1, assumption },
                      { apply H₂.1, assumption }
                    },
                    { apply funext, intro x,
                      apply iff.to_eq,
                      apply iff.intro,
                      { intro H,
                        rw [H₁.2, H₂.2] at H,
                        cases H with Hx₁ Hx₂,
                        cases Hx₁ with X₁ Hx₁,
                        cases Hx₁ with UX₁ Xx₁,
                        cases Hx₂ with X₂ Hx₂,
                        cases Hx₂ with UX₂ Xx₂,
                        existsi X₁ ∩ X₂,
                        refine exists.intro _ (and.intro Xx₁ Xx₂),
                        existsi X₁, existsi X₂,
                        apply and.intro UX₁,
                        apply and.intro UX₂,
                        trivial
                      },
                      { intro H,
                        cases H with O H,
                        cases H with Q H,
                        cases Q with X₁ Q,
                        cases Q with X₂ Q,
                        rw [Q.2.2] at H,
                        rw [H₁.2, H₂.2],
                        apply and.intro,
                        { existsi X₁, existsi Q.1, exact H.1 },
                        { existsi X₂, existsi Q.2.1, exact H.2 }
                      }
                    }
                  end
    , Ounion := λ O OpenO
                , begin
                    existsi (λ U, Base.Open U ∧ ∃ O', O' ∈ O ∧ U ⊆ O'),
                    apply and.intro,
                    { intros S HS, exact HS.1 },
                    { apply funext, intro x,
                      apply iff.to_eq,
                      apply iff.intro,
                      { intro H,
                        cases H with X HX, cases HX with OX HX,
                        cases OpenO OX with U' HU',
                        cases HU' with OpenU' E,
                        subst E,
                        cases HX with V HV, cases HV with U'V Vx,
                        existsi V,
                        refine exists.intro _ Vx,
                        apply and.intro (OpenU' U'V),
                        refine exists.intro _ (and.intro OX _),
                        intros v Hv,
                        existsi V, existsi U'V, exact Hv
                      },
                      { intro H,
                        cases H with O' H,
                        cases H with Q H,
                        cases Q with OpenO' Q,
                        cases Q with X₂ Q,
                        existsi X₂,
                        existsi Q.1,
                        exact Q.2 H
                      }
                    }
                  end
    }

def OpenBase.BaseOpen {A : Type.{ℓ}} (TA : OpenBase A)
    {U : set A}
  : TA.Open U → TA.Topology.Open U
 := begin
      intro H,
      existsi (eq U),
      apply and.intro,
      { intros W E,
        have E' : U = W := E,
        subst E', clear E,
        exact H
      },
      { apply funext, intro a,
        apply iff.to_eq, apply iff.intro,
        { intro H, existsi U, existsi rfl, exact H },
        { intro H,
          cases H with U' H,
          cases H with E H,
          have E' : U = U' := E, subst E', clear E,
          exact H
        }
      }
    end

def OpenBase.Continuous {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
  (TA : Topology A) (TB : OpenBase B)
  (f : A → B)
  (fC : ∀ O, TB.Open O → TA.Open (PreImage f O))
  : Continuous TA TB.Topology f
 := begin
      intros U OpenU,
      cases OpenU with UU HUU,
      cases HUU with HUU E, subst E,
      rw [PreImage.Union₀],
      apply TA.Ounion,
      intros O HO,
      cases HO with O' HO,
      cases HO with HO'UU E,
      subst E,
      apply fC,
      apply HUU,
      exact HO'UU
    end



end Top
