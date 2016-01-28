module Data.Collection.Equivalence where

open import Data.Collection.Core

open import Function using (id; _∘_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; equivalence)
open Function.Equivalence.Equivalence
open import Relation.Binary.PropositionalEquality


open import Level using (zero)

open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary

nach : ∀ {f t} {A : Set f} {B : Set t} → (A ⇔ B) → A → B
nach = _⟨$⟩_ ∘ to

von : ∀ {f t} {A : Set f} {B : Set t} → (A ⇔ B) → B → A
von = _⟨$⟩_ ∘ from


infixr 5 _≋_

_≋_ : Rel Membership _
A ≋ B = {x : Element} → x ∈ A ⇔ x ∈ B

≋-Reflexive : Reflexive _≋_
≋-Reflexive = equivalence id id

≋-Symmetric : Symmetric _≋_
≋-Symmetric z = record
    { to   = from z
    ; from = to z
    }

≋-Transitive : Transitive _≋_
≋-Transitive P≋Q Q≋R = equivalence (nach Q≋R ∘ nach P≋Q) (von P≋Q ∘ von Q≋R)

≋-IsEquivalence : IsEquivalence _≋_
≋-IsEquivalence = record
    { refl = equivalence id id
    ; sym = ≋-Symmetric
    ; trans = ≋-Transitive
    }

≋-Setoid : Setoid _ _
≋-Setoid = record
    { Carrier = Pred Element zero
    ; _≈_ = _≋_
    ; isEquivalence = ≋-IsEquivalence
    }

--------------------------------------------------------------------------------
--  Conditional Equivalence
--------------------------------------------------------------------------------

_≋[_]_ : ∀ {a} → Membership → Pred Element a → Membership → Set a
A ≋[ P ] B = {x : Element} → P x → x ∈ A ⇔ x ∈ B

-- prefix version of _≋[_]_, with the predicate being the first argument
[_]≋ : ∀ {a} → Pred Element a → Membership → Membership → Set a
[_]≋ P A B = A ≋[ P ] B

≋[]-Reflexive : ∀ {a} {P : Pred Element a} → Reflexive [ P ]≋
≋[]-Reflexive A = equivalence id id

≋[]-Symmetric : ∀ {a} {P : Pred Element a} → Symmetric [ P ]≋
≋[]-Symmetric z ∈P = record
    { to = from (z ∈P)
    ; from = to (z ∈P)
    }

≋[]-Transitive : ∀ {a} {P : Pred Element a} → Transitive [ P ]≋
≋[]-Transitive P≋Q Q≋R ∈P = equivalence (nach (Q≋R ∈P) ∘ nach (P≋Q ∈P)) (von (P≋Q ∈P) ∘ von (Q≋R ∈P))

≋[]-IsEquivalence : ∀ {a} {P : Pred Element a} → IsEquivalence [ P ]≋
≋[]-IsEquivalence {p} = record
    { refl = λ _ → equivalence id id
    ; sym = ≋[]-Symmetric
    ; trans = ≋[]-Transitive
    }
