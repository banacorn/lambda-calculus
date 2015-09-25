module Collection.Equivalence where

open import Collection.Core
open import Data.String using (String)

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

_≋_ : Rel (Pred String zero) _
A ≋ B = {x : String} → x ∈ A ⇔ x ∈ B

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
