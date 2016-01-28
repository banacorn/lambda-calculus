module Data.Collection.Core where

open import Data.List public using (List; []; _∷_)
open import Data.String public using (String; _≟_)
open import Level using (zero)

open import Function using (flip)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable renaming (map to mapDec; map′ to mapDec′)
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------
--  Types
--------------------------------------------------------------------------------

Element : Set
Element = String

Collection : Set
Collection = List Element

Membership : Set _
Membership = Pred Element zero

--------------------------------------------------------------------------------
--  Membership
--------------------------------------------------------------------------------

infix 4 _∈c_ _∉c_

data _∈c_ : REL Element Collection zero where
    here  : ∀ {   x A}         → x ∈c x ∷ A
    there : ∀ {a x A} → x ∈c A → x ∈c a ∷ A

_∉c_ : REL Element Collection _
x ∉c A = ¬ x ∈c A

infixr 6 _⊈_

-- I know this notation is a bit confusing
_⊈_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊈ Q = ∀ {x} → x ∉ P → x ∉ Q

c[_] : REL Collection Element zero
c[_] = flip _∈c_

infix 4 _∈?_

_∈?_ : (x : Element) → (A : Collection) → Dec (x ∈ c[ A ])
x ∈? []       = no (λ ())
x ∈? ( a ∷ A) with x ≟ a
x ∈? (.x ∷ A) | yes refl = yes here
x ∈? ( a ∷ A) | no ¬p    = mapDec′ there (there-if-not-here ¬p) (x ∈? A)
    where
            there-if-not-here : ∀ {x a A} → x ≢ a → x ∈ c[ a ∷ A ] → x ∈ c[ A ]
            there-if-not-here x≢a here          = contradiction refl x≢a
            there-if-not-here x≢a (there x∈a∷A) = x∈a∷A

--------------------------------------------------------------------------------
--  Miscs
--------------------------------------------------------------------------------
--
-- ∷-⊆-monotone : ∀ {a A B} → c[ A ] ⊆ c[ B ] → c[ a ∷ A ] ⊆ c[ a ∷ B ]
-- ∷-⊆-monotone f here       = here
-- ∷-⊆-monotone f (there ∈A) = there (f ∈A)
