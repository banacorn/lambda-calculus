module Data.Collection.Properties where

open import Data.Collection.Core
open import Data.Collection.Equivalence
open import Data.Collection.Inclusion
open import Data.Collection

open import Data.Sum renaming (map to mapSum)
open import Data.Product
open import Function.Equivalence using (_⇔_; equivalence)

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

singleton-≡ : ∀ {x y} → x ∈ c[ singleton y ] ⇔ x ≡ y
singleton-≡ = equivalence to from
    where   to : ∀ {x y} → x ∈ c[ singleton y ] → x ≡ y
            to here = refl
            to (there ())
            from : ∀ {x y} → x ≡ y → x ∈ c[ singleton y ]
            from refl = here

--------------------------------------------------------------------------------
--  Delete
--------------------------------------------------------------------------------

-- still-∈-after-deleted : ∀ {x} y A → x ≢ y → x ∈ c[ A ] → x ∈ c[ delete y A ]
still-∈-after-deleted : ∀ y A → c[ A ] ⊆[ _≢_ y ] c[ delete y A ]
still-∈-after-deleted y []          ≢y ()
still-∈-after-deleted y (a ∷ A) {x} ≢y ∈A with y ≟ a
still-∈-after-deleted y (a ∷ A) ≢y here       | yes p = contradiction p ≢y
still-∈-after-deleted y (a ∷ A) ≢y (there ∈A) | yes p = still-∈-after-deleted y A ≢y ∈A
still-∈-after-deleted y (x ∷ A) ≢y here       | no ¬p = here
still-∈-after-deleted y (a ∷ A) ≢y (there ∈A) | no ¬p = there (still-∈-after-deleted y A ≢y ∈A)

-- still-∉-after-recovered : ∀ {x} y A → x ≢ y → x ∉c delete y A → x ∉ c[ A ]
still-∉-after-recovered : ∀ y A → c[ delete y A ] ⊈[ _≢_ y ] c[ A ]
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

∪-union : ∀ A B → c[ A ] ∪ c[ B ] ≋ c[ union A B ]
∪-union A B = equivalence to (in-either A B)
    where   to : ∀ {x} → x ∈ c[ A ] ∪ c[ B ] → x ∈ c[ union A B ]
            to (inj₁ ∈A) = in-left-union A B ∈A
            to (inj₂ ∈B) = in-right-union A B ∈B


head-∈ : ∀ a A B → c[ a ∷ A ] ⊆ c[ B ] → a ∈ c[ B ]
head-∈ a A B ⊆B = ⊆B here

tail-⊆ : ∀ a A B → c[ a ∷ A ] ⊆ c[ B ] → c[ A ] ⊆ c[ B ]
tail-⊆ a A B ⊆B ∈A = ⊆B (there ∈A)

union-monotone : ∀ {A B C D a} (P : String → Set a) → c[ A ] ⊆[ P ] c[ C ] → c[ B ] ⊆[ P ] c[ D ] → c[ union A B ] ⊆[ P ] c[ union C D ]
union-monotone {[]}    {B} {C} {D} P A⊆C B⊆D ∈P ∈A∪B = in-right-union C D (B⊆D ∈P ∈A∪B)
union-monotone {a ∷ A} {B} {C} {D} P A⊆C B⊆D ∈P ∈A∪B with a ∈? B
union-monotone {a ∷ A}             P A⊆C B⊆D ∈P ∈A∪B         | yes p = union-monotone P (λ P A → A⊆C P (there A)) B⊆D ∈P ∈A∪B
union-monotone {a ∷ A} {B} {C} {D} P A⊆C B⊆D ∈P here         | no ¬p = in-left-union C D (A⊆C ∈P here)
union-monotone {a ∷ A}             P A⊆C B⊆D ∈P (there ∈A∪B) | no ¬p = union-monotone P (λ P₁ A₁ → A⊆C P₁ (there A₁)) B⊆D ∈P ∈A∪B
-- union-monotone {A} P A⊆C B⊆D ∈P ∈A∪B = {!   !}
-- union-monotone : ∀ A B C D → c[ A ] ⊆ c[ C ] → c[ B ] ⊆ c[ D ] → c[ union A B ] ⊆ c[ union C D ]
-- union-monotone [] ._ C D A⊆C B⊆D here = in-right-union C D (B⊆D here)
-- union-monotone [] ._ C D A⊆C B⊆D (there ∈A∪B) = in-right-union C D (B⊆D (there ∈A∪B))
-- union-monotone (a ∷ A) B C D A⊆C B⊆D ∈A∪B with a ∈? B
-- union-monotone (a ∷ A) B C D A⊆C B⊆D ∈A∪B         | yes p = union-monotone A B C D (A⊆C ∘ there) B⊆D ∈A∪B
-- union-monotone (a ∷ A) B C D A⊆C B⊆D here         | no ¬p = in-left-union C D (A⊆C here)
-- union-monotone (a ∷ A) B C D A⊆C B⊆D (there ∈A∪B) | no ¬p = union-monotone A B C D (A⊆C ∘ there) B⊆D ∈A∪B
