------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences on pointwise equality of freely adding an infimum to a Set
------------------------------------------------------------------------
open import Relation.Binary

module Relation.Binary.Construction.Free.Infimum.Pointwise
       {k e} {Key : Set k} (_≈_ : Rel Key e) where

open import Level
open import Function
open import Function.Equivalence using (equivalence)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.Construction.Free.Infimum Key

data _≈⁺_ : Rel Key⁺ e where
  ⊥⁺≈⊥⁺ :                       ⊥⁺    ≈⁺ ⊥⁺
  []≈[] : {k l : Key} → k ≈ l → [ k ] ≈⁺ [ l ]

[]≈[]⁻¹ : ∀ {k l} → [ k ] ≈⁺ [ l ] → k ≈ l
[]≈[]⁻¹ ([]≈[] k≈l) = k≈l

≈⁺-refl : Reflexive _≈_ → Reflexive _≈⁺_
≈⁺-refl ≈-refl {⊥⁺}    = ⊥⁺≈⊥⁺
≈⁺-refl ≈-refl {[ k ]} = []≈[] ≈-refl

≈⁺-sym : Symmetric _≈_ → Symmetric _≈⁺_
≈⁺-sym ≈-sym ⊥⁺≈⊥⁺       = ⊥⁺≈⊥⁺
≈⁺-sym ≈-sym ([]≈[] x≈y) = []≈[] (≈-sym x≈y)

≈⁺-trans : Transitive _≈_ → Transitive _≈⁺_
≈⁺-trans ≈-trans ⊥⁺≈⊥⁺       ⊥⁺≈z        = ⊥⁺≈z
≈⁺-trans ≈-trans ([]≈[] x≈y) ([]≈[] y≈z) = []≈[] (≈-trans x≈y y≈z)

≈⁺-dec : Decidable _≈_ → Decidable _≈⁺_
≈⁺-dec ≈-dec ⊥⁺    ⊥⁺    = yes ⊥⁺≈⊥⁺
≈⁺-dec ≈-dec ⊥⁺    [ l ] = no (λ ())
≈⁺-dec ≈-dec [ k ] ⊥⁺    = no (λ ())
≈⁺-dec ≈-dec [ k ] [ l ] = Dec.map (equivalence []≈[] []≈[]⁻¹) (≈-dec k l)

≈⁺-irrelevance : Irrelevant _≈_ → Irrelevant _≈⁺_
≈⁺-irrelevance ≈-irrelevance ⊥⁺≈⊥⁺     ⊥⁺≈⊥⁺     = P.refl
≈⁺-irrelevance ≈-irrelevance ([]≈[] p) ([]≈[] q) = P.cong _ (≈-irrelevance p q)

≈⁺-substitutive : ∀ {ℓ} → Substitutive _≈_ ℓ → Substitutive _≈⁺_ ℓ
≈⁺-substitutive ≈-substitutive P ⊥⁺≈⊥⁺     = id
≈⁺-substitutive ≈-substitutive P ([]≈[] p) = ≈-substitutive (P ∘′ [_]) p

≈⁺-isEquivalence : IsEquivalence _≈_ → IsEquivalence _≈⁺_
≈⁺-isEquivalence isEquiv = record
  { refl  = λ {x} → ≈⁺-refl refl {x}
  ; sym   = λ {x} → ≈⁺-sym sym {x}
  ; trans = λ {x} → ≈⁺-trans trans {x}
  } where open IsEquivalence isEquiv
