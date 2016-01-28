module Data.Collection.Inclusion where

open import Data.Collection.Equivalence
open import Data.Collection.Core

open import Function using (id; _∘_)
open import Function.Equivalence using (equivalence)
open import Level using (Level; suc; zero)
open import Relation.Unary hiding (_⇒_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

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

⊆-Preorder : Preorder _ _ _
⊆-Preorder = record
    { Carrier = Pred String zero
    ; _≈_ = _≋_
    ; _∼_ = _⊆_
    ; isPreorder = ⊆-IsPreorder
    }

⊆-Antisymmetric : Antisymmetric _≋_ _⊆_
⊆-Antisymmetric P⊆Q Q⊆P = equivalence P⊆Q Q⊆P

⊆-IsPartialOrder : IsPartialOrder _≋_ _⊆_
⊆-IsPartialOrder = record
    { isPreorder = ⊆-IsPreorder
    ; antisym = ⊆-Antisymmetric
    }

⊆-Poset : Poset _ _ _
⊆-Poset = record
    { Carrier = Pred String zero
    ; _≈_ = _≋_
    ; _≤_ = _⊆_
    ; isPartialOrder = ⊆-IsPartialOrder
    }

--------------------------------------------------------------------------------
--  Conditional Inclusion
--------------------------------------------------------------------------------


_⊆[_]_ : ∀ {a ℓ₀ ℓ₁ ℓ₂} {A : Set a} → Pred A ℓ₀ → Pred A ℓ₁ → Pred A ℓ₂ → Set _
A ⊆[ P ] B = ∀ {x} → x ∈ P → x ∈ A → x ∈ B

_⊈[_]_ : ∀ {a ℓ₀ ℓ₁ ℓ₂} {A : Set a} → Pred A ℓ₀ → Pred A ℓ₁ → Pred A ℓ₂ → Set _
A ⊈[ P ] B = ∀ {x} → x ∈ P → x ∉ A → x ∉ B

-- prefix version of _⊆[_]_, with the predicate being the first argument
[_]⊆ : ∀ {a ℓ₀ ℓ₁ ℓ₂} {A : Set a} → Pred A ℓ₁ → Pred A ℓ₀ → Pred A ℓ₂ → Set _
[ P ]⊆ A B = A ⊆[ P ] B

≋[]⇒⊆[] : ∀ {a} {P : Pred Element a} → [ P ]≋ ⇒ [ P ]⊆
≋[]⇒⊆[] A≋B = nach ∘ A≋B

⊆[]-Transitive : ∀ {a ℓ} {P : Pred Element a} → Transitive {_} {_} {Pred String ℓ} [ P ]⊆
⊆[]-Transitive A⊆B B⊆C ∈P = B⊆C ∈P ∘ A⊆B ∈P

⊆[]-IsPreorder : ∀ {a} {P : Pred Element a} → IsPreorder [ P ]≋ [ P ]⊆
⊆[]-IsPreorder = record
    { isEquivalence = ≋[]-IsEquivalence
    ; reflexive = ≋[]⇒⊆[]
    ; trans = ⊆[]-Transitive
    }

⊆[]-Preorder : ∀ {a} {P : Pred Element a} → Preorder _ _ _
⊆[]-Preorder {_} {P} = record
    { Carrier = Pred String zero
    ; _≈_ = [ P ]≋
    ; _∼_ = [ P ]⊆
    ; isPreorder = ⊆[]-IsPreorder
    }

⊆[]-Antisymmetric : ∀ {a} {P : Pred Element a} → Antisymmetric [ P ]≋ [ P ]⊆
⊆[]-Antisymmetric P⊆Q Q⊆P ∈P = equivalence (P⊆Q ∈P) (Q⊆P ∈P)

⊆[]-IsPartialOrder : ∀ {a} {P : Pred Element a} → IsPartialOrder [ P ]≋ [ P ]⊆
⊆[]-IsPartialOrder = record
    { isPreorder = ⊆[]-IsPreorder
    ; antisym = ⊆[]-Antisymmetric
    }

⊆[]-Poset : ∀ {a} {P : Pred Element a} → Poset _ _ _
⊆[]-Poset {_} {P} = record
    { Carrier = Pred String zero
    ; _≈_ = [ P ]≋
    ; _≤_ = [ P ]⊆
    ; isPartialOrder = ⊆[]-IsPartialOrder
    }
