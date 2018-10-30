------------------------------------------------------------------------
-- The Agda standard library
--
-- The Maybe type
------------------------------------------------------------------------

module Data.Maybe where

open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Bool.Base using (T)

open import Relation.Nullary

------------------------------------------------------------------------
-- The base type and some operations

open import Data.Maybe.Base public
open import Data.Maybe.All
open import Data.Maybe.Any

------------------------------------------------------------------------
-- Using Any and All to define Is-just and Is-nothing

Is-just : ∀ {a} {A : Set a} → Maybe A → Set
Is-just = Any (λ _ → ⊤)

Is-nothing : ∀ {a} {A : Set a} → Maybe A → Set
Is-nothing = All (λ _ → ⊥)

to-witness : ∀ {p} {P : Set p} {m : Maybe P} → Is-just m → P
to-witness (just {x = p} _) = p

to-witness-T : ∀ {p} {P : Set p} (m : Maybe P) → T (is-just m) → P
to-witness-T (just p) _  = p
to-witness-T nothing  ()

Is-just? : ∀ {a} {A : Set a} → (v : Maybe A) → Dec (Is-just v)
Is-just? nothing = no λ ()
Is-just? (just v) = yes (just ⊤.tt)

Is-Just-And : ∀ {a} {A : Set a} → (P : A → Set a) → Maybe A → Set a
Is-Just-And P = Any P

Is-Just-And? : ∀ {a} {A : Set a} → {P : A → Set a} → (v : Maybe A) → ((a : A) → Dec (P a)) → Dec (Is-Just-And P v)
Is-Just-And? (just x) d with d x
Is-Just-And? (just x) d | yes p = yes (just p)
Is-Just-And? (just x) d | no ¬p = no λ { (just px) → ¬p px }
Is-Just-And? nothing d = no (λ ())
