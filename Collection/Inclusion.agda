module Collection.Inclusion where

open import Collection.Equivalence
open import Collection.Core

open import Function using (id; _∘_)
open import Function.Equivalence using (equivalence)
open import Level using (Level; suc; zero)
open import Relation.Unary hiding (_⇒_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

_⊆0_ : Pred String zero → Pred String zero → Set
_⊆0_ = _⊆_

≋⇒⊆ : _≋_ ⇒ _⊆_
≋⇒⊆ P≋Q ∈P = nach P≋Q ∈P

⊆-Transitive : ∀ {a ℓ} {A : Set a} → Transitive {_} {_} {Pred A ℓ} _⊆_
⊆-Transitive P⊆Q Q⊆R = Q⊆R ∘ P⊆Q

⊆-IsPreorder : IsPreorder _≋_ _⊆_
⊆-IsPreorder = record
    { isEquivalence = ≋-IsEquivalence
    ; reflexive = ≋⇒⊆
    ; trans = ⊆-Transitive
    }

⊆-Antisymmetric : Antisymmetric _≋_ _⊆_
⊆-Antisymmetric P⊆Q Q⊆P = equivalence P⊆Q Q⊆P

⊆-IsPartialOrder : IsPartialOrder _≋_ _⊆_
⊆-IsPartialOrder = record
    { isPreorder = ⊆-IsPreorder
    ; antisym = ⊆-Antisymmetric
    }
