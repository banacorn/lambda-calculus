module Data.Collection.Properties where

open import Data.Collection.Core
open import Data.Collection.Equivalence
open import Data.Collection

open import Data.Sum renaming (map to mapSum)
open import Data.Product
open import Function.Equivalence using (equivalence)

-- open import Data.List public using (List; []; _∷_)
-- open import Data.String public using (String; _≟_)
-- open import Level using (zero)
--
open import Function using (id; _∘_)
open import Relation.Nullary
open import Relation.Nullary.Negation
-- open import Relation.Nullary.Decidable renaming (map to mapDec; map′ to mapDec′)
open import Relation.Unary
-- open import Relation.Binary
open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------
--  Singleton
--------------------------------------------------------------------------------

singleton-≡ : ∀ {x y} → x ∈ c[ singleton y ] → x ≡ y
singleton-≡ here = refl
singleton-≡ (there ())

--------------------------------------------------------------------------------
--  Delete
--------------------------------------------------------------------------------

-- still-∈-after-deleted : ∀ {x} y A → x ≢ y → x ∈ c[ A ] → x ∈ c[ delete y A ]
still-∈-after-deleted : ∀ y A → ∀[ _≢_ y ] c[ A ] ⊆ c[ delete y A ]
still-∈-after-deleted y []          ≢y ()
still-∈-after-deleted y (a ∷ A) {x} ≢y ∈A with y ≟ a
still-∈-after-deleted y (a ∷ A) ≢y here       | yes p = contradiction p ≢y
still-∈-after-deleted y (a ∷ A) ≢y (there ∈A) | yes p = still-∈-after-deleted y A ≢y ∈A
still-∈-after-deleted y (x ∷ A) ≢y here       | no ¬p = here
still-∈-after-deleted y (a ∷ A) ≢y (there ∈A) | no ¬p = there (still-∈-after-deleted y A ≢y ∈A)

-- still-∉-after-recovered : ∀ {x} y A → x ≢ y → x ∉c delete y A → x ∉ c[ A ]
still-∉-after-recovered : ∀ y A → ∀[ _≢_ y ] c[ delete y A ] ⊈ c[ A ]
still-∉-after-recovered y []      ≢y ∉A-y ()
still-∉-after-recovered y (a ∷ A) ≢y ∉A-y ∈a∷A with y ≟ a
still-∉-after-recovered y (a ∷ A) ≢y ∉A-y here       | yes p = contradiction p ≢y
still-∉-after-recovered y (a ∷ A) ≢y ∉A-y (there ∈A) | yes p = contradiction (still-∈-after-deleted y A ≢y ∈A) ∉A-y
still-∉-after-recovered y (a ∷ A) ≢y ∉A-y here       | no ¬p = contradiction here ∉A-y
still-∉-after-recovered y (a ∷ A) ≢y ∉A-y (there ∈A) | no ¬p = contradiction (there (still-∈-after-deleted y A ≢y ∈A)) ∉A-y

--------------------------------------------------------------------------------
--  Union
--------------------------------------------------------------------------------

in-right-union : ∀ A B → c[ B ] ⊆ c[ union A B ]
in-right-union []      B x∈B = x∈B
in-right-union (a ∷ A) B x∈B with a ∈? B
in-right-union (a ∷ A) B x∈B | yes p = in-right-union A B x∈B
in-right-union (a ∷ A) B x∈B | no ¬p = there (in-right-union A B x∈B)

in-left-union : ∀ A B → c[ A ] ⊆ c[ union A B ]
in-left-union []      B ()
in-left-union (a ∷ A) B x∈A         with a ∈? B
in-left-union (a ∷ A) B here        | yes p = in-right-union A B p
in-left-union (a ∷ A) B (there x∈A) | yes p = in-left-union A B x∈A
in-left-union (a ∷ A) B here        | no ¬p = here
in-left-union (a ∷ A) B (there x∈A) | no ¬p = there (in-left-union A B x∈A)

∪-left-identity : ∀ A → c[ [] ] ∪ c[ A ] ≋ c[ A ]
∪-left-identity A = equivalence to inj₂
    where
            to : c[ [] ] ∪ c[ A ] ⊆ c[ A ]
            to (inj₁ ())
            to (inj₂ ∈A) = ∈A

∪-right-identity : ∀ A → c[ A ] ∪ c[ [] ] ≋ c[ A ]
∪-right-identity A = equivalence to inj₁
    where
            to : c[ A ] ∪ c[ [] ] ⊆ c[ A ]
            to (inj₁ ∈A) = ∈A
            to (inj₂ ())

in-either : ∀ A B → c[ union A B ] ⊆ c[ A ] ∪ c[ B ]
in-either []      B x∈A∪B         = inj₂ x∈A∪B
in-either (a ∷ A) B x∈A∪B         with a ∈? B
in-either (a ∷ A) B x∈A∪B         | yes p = mapSum there id (in-either A B x∈A∪B)
in-either (a ∷ A) B here          | no ¬p = inj₁ here
in-either (a ∷ A) B (there x∈A∪B) | no ¬p = mapSum there id (in-either A B x∈A∪B)

not-in-left-union : ∀ A B → c[ union A B ] ⊈ c[ A ]
not-in-left-union A B ∉union ∈A = contradiction (in-left-union A B ∈A) ∉union

not-in-right-union : ∀ A B → c[ union A B ] ⊈ c[ B ]
not-in-right-union A B ∉union ∈A = contradiction (in-right-union A B ∈A) ∉union

in-neither : ∀ A B → c[ union A B ] ⊈ c[ A ] ∪ c[ B ]
in-neither A B ∉union (inj₁ ∈A) = contradiction (in-left-union A B ∈A) ∉union
in-neither A B ∉union (inj₂ ∈B) = contradiction (in-right-union A B ∈B) ∉union

-- in-neither : ∀ A B → c[ union A B ] ⊈ c[ A ] ∩ c[ B ]
-- in-neither [] B ∉union (() , ∈B)
-- in-neither (a ∷ A) B ∉union ∈both with a ∈? B
-- in-neither (a ∷ A) B ∉union (∈a∷A , ∈B) | yes p = contradiction (in-right-union A B ∈B) ∉union
-- in-neither (a ∷ A) B ∉union (∈a∷A , ∈B) | no ¬p = contradiction (there (in-right-union A B ∈B)) ∉union

-- in-neither : ∀ A B → c[ union A B ] ⊈ c[ A ] ∩ c[ B ]
-- in-neither [] B ∉union (() , ∈B)
-- in-neither (a ∷ A) B ∉union ∈both with a ∈? B
-- in-neither (a ∷ A) B ∉union (∈a∷A , ∈B) | yes p = contradiction (in-right-union A B ∈B) ∉union
-- in-neither (a ∷ A) B ∉union (∈a∷A , ∈B) | no ¬p = contradiction (there (in-right-union A B ∈B)) ∉union

∪-union : ∀ A B → c[ A ] ∪ c[ B ] ≋ c[ union A B ]
∪-union A B = equivalence to (in-either A B)
    where   to : ∀ {x} → x ∈ c[ A ] ∪ c[ B ] → x ∈ c[ union A B ]
            to (inj₁ ∈A) = in-left-union A B ∈A
            to (inj₂ ∈B) = in-right-union A B ∈B