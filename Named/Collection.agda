module Named.Collection where

open import Data.List
open import Data.String hiding (setoid)
open import Data.List using ([]; _∷_) public
open import Data.Product
open import Data.Sum renaming (map to mapSum)
-- open import Data.Bool using (Bool; true; false; T; not)
open import Level renaming (zero to lvl0)
open import Function using (_∘_; id; flip; _on_)
open import Function.Equivalence using (_⇔_; Equivalence; equivalence)

open import Function.Equality using (_⟨$⟩_) renaming (cong to cong≈)
open import Relation.Nullary
open import Relation.Unary
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable renaming (map to mapDec; map′ to mapDec′)
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
-- open ≡-Reasoning

nach : ∀ {f t} {A : Set f} {B : Set t} → (A ⇔ B) → A → B
nach = _⟨$⟩_ ∘ Equivalence.to

von : ∀ {f t} {A : Set f} {B : Set t} → (A ⇔ B) → B → A
von = _⟨$⟩_ ∘ Equivalence.from

-- _≋_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
-- _≋_ = _,_
infixr 5 _≋_

_≋_ : Rel (Pred String lvl0) _
A ≋ B = {x : String} → x ∈ A ⇔ x ∈ B

-- I know this notation is a bit confusing
_⊈_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊈ Q = ∀ {x} → x ∉ P → x ∉ Q


⊆-IsPreorder : IsPreorder _≋_ _⊆_
⊆-IsPreorder = record
    { isEquivalence = {!   !}
    ; reflexive = {!   !}
    ; trans = {!   !}
    }

Collection : Set
Collection = List String

infix 4 _∈c_ _∉c_

data _∈c_ : REL String Collection lvl0 where
    here  : ∀ {   x A}         → x ∈c x ∷ A
    there : ∀ {a x A} → x ∈c A → x ∈c a ∷ A

c[_] : REL Collection String lvl0
c[_] = flip _∈c_

_∉c_ : REL String Collection _
x ∉c A = x ∉ c[ A ]

[]-empty : Empty c[ [] ]
[]-empty = λ x → λ ()

here-respects-≡ : ∀ {A} → (λ x → x ∈ c[ A ]) Respects _≡_
here-respects-≡ refl = id

there-respects-≡ : ∀ {x A} → (λ a → x ∈ c[ a ∷ A ]) Respects _≡_
there-respects-≡ refl = id

∈-respects-≡ : ∀ {x} → (λ P → x ∈ c[ P ]) Respects _≡_
∈-respects-≡ refl = id

there-if-not-here : ∀ {x a A} → x ≢ a → x ∈ c[ a ∷ A ] → x ∈ c[ A ]
there-if-not-here x≢a here          = contradiction refl x≢a
there-if-not-here x≢a (there x∈a∷A) = x∈a∷A

here-if-not-there : ∀ {x a A} → x ∉ c[ A ] → x ∈ c[ a ∷ A ] → x ≡ a
here-if-not-there x∉A here = refl
here-if-not-there x∉A (there x∈A) = contradiction x∈A x∉A

∷-⊆-monotone : ∀ {a A B} → c[ A ] ⊆ c[ B ] → c[ a ∷ A ] ⊆ c[ a ∷ B ]
∷-⊆-monotone f here       = here
∷-⊆-monotone f (there ∈A) = there (f ∈A)

map-¬∷ : ∀ {x a A B} → (x ∉ c[ A ] → x ∉ c[ B ]) → x ≢ a → x ∉ c[ a ∷ A ] → x ∉ c[ a ∷ B ]
map-¬∷ f x≢x x∉a∷A here = contradiction refl x≢x
map-¬∷ f x≢a x∉a∷A (there x∈B) = f (x∉a∷A ∘ there) x∈B

still-not-there : ∀ {x y} A → x ≢ y → x ∉ c[ A ] → x ∉ c[ y ∷ A ]
still-not-there [] x≢y x∉[y] here = x≢y refl
still-not-there [] x≢y x∉[y] (there ())
still-not-there (a ∷ A) x≢y x∉a∷A here = x≢y refl
still-not-there (a ∷ A) x≢y x∉a∷A (there x∈a∷A) = x∉a∷A x∈a∷A

_∈?_ : (x : String) → (A : Collection) → Dec (x ∈ c[ A ])
x ∈? [] = no (λ ())
x ∈? (a ∷ A) with x ≟ a
x ∈? (.x ∷ A) | yes refl = yes here
x ∈? (a ∷ A) | no ¬p = mapDec′ there (there-if-not-here ¬p) (x ∈? A)

--------------------------------------------------------------------------------
--  Union
--------------------------------------------------------------------------------

union : Collection → Collection → Collection
union []      B = B
union (a ∷ A) B with a ∈? B
union (a ∷ A) B | yes p = union A B
union (a ∷ A) B | no ¬p = a ∷ union A B

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

∪-union : ∀ A B → c[ A ] ∪ c[ B ] ≋ c[ union A B ]
∪-union A B = equivalence to (in-either A B)
    where   to : ∀ {x} → x ∈ c[ A ] ∪ c[ B ] → x ∈ c[ union A B ]
            to (inj₁ ∈A) = in-left-union A B ∈A
            to (inj₂ ∈B) = in-right-union A B ∈B

-- map-⊆-union : ∀ {A B C} → c[ A ] ⊆ c[ B ] → c[ B ] ⊆ c[ C ] → c[  ] ⊆ c[ union C D ]
-- map-⊆-union f g ∈union = {!   !}


union-branch-1 : ∀ {x a} A B → a ∈ c[ B ] → x ∈ c[ union (a ∷ A) B ] → x ∈ c[ union A B ]
union-branch-1 {x} {a} A B a∈B x∈union with a ∈? B
union-branch-1 A B a∈B x∈union | yes p = x∈union
union-branch-1 A B a∈B x∈union | no ¬p = contradiction a∈B ¬p

there-left-union-coherence : ∀ {x} {a} A B → x ∈ c[ a ∷ A ] → x ∈c a ∷ union A B
there-left-union-coherence A B here          = here
there-left-union-coherence A B (there x∈a∷A) = there (in-left-union A B x∈a∷A)


in-neither : ∀ {x} A B → x ∉c union A B → x ∉ c[ A ] × x ∉ c[ B ]
in-neither []      B x∉A∪B = (λ ()) , x∉A∪B
in-neither (a ∷ A) B x∉A∪B with a ∈? B
in-neither (a ∷ A) B x∉A∪B | yes a∈B = (contraposition (union-branch-1 A B a∈B ∘ in-left-union (a ∷ A) B) x∉A∪B) , (contraposition (in-right-union A B) x∉A∪B)
in-neither (a ∷ A) B x∉A∪B | no a∉B = (contraposition (there-left-union-coherence A B) x∉A∪B) , contraposition (there ∘ in-right-union A B) x∉A∪B


delete : String → Collection → Collection
delete x [] = []
delete x (a ∷ A) with x ≟ a
delete x (a ∷ A) | yes p =     delete x A -- keep deleting, because there might be many of them
delete x (a ∷ A) | no ¬p = a ∷ delete x A

∉-after-deleted : ∀ x A → x ∉ c[ delete x A ]
∉-after-deleted x [] ()
∉-after-deleted x (a ∷ A) with x ≟ a
∉-after-deleted x (a ∷ A) | yes p = ∉-after-deleted x A
∉-after-deleted x (a ∷ A) | no ¬p = still-not-there (delete x A) ¬p (∉-after-deleted x A)


still-∈-after-deleted : ∀ {x} y A → x ≢ y → x ∈ c[ A ] → x ∈ c[ delete y A ]
still-∈-after-deleted y []       x≢y ()
still-∈-after-deleted y (a  ∷ A) x≢y x∈A with y ≟ a
still-∈-after-deleted y (.y ∷ A) x≢y x∈A | yes refl = still-∈-after-deleted y A x≢y (there-if-not-here x≢y x∈A)
still-∈-after-deleted y (a  ∷ A) x≢y x∈A | no ¬p    = ∷-⊆-monotone {!   !} {! x∈A  !}
-- still-∈-after-deleted y (a  ∷ A) x≢y x∈A | no ¬p    = ∷-⊆-monotone (still-∈-after-deleted y A x≢y) x∈A

-- still-∉-after-deleted : ∀ {x} y A → x ≢ y → x ∉ c[ A ] → x ∉ c[ delete y A ]
-- still-∉-after-deleted y []       x≢y x∉A = x∉A
-- still-∉-after-deleted y (a  ∷ A) x≢y x∉A with y ≟ a
-- still-∉-after-deleted y (.y ∷ A) x≢y x∉A | yes refl = still-∉-after-deleted y A x≢y (x∉A ∘ there)
-- still-∉-after-deleted {x} y (a  ∷ A) x≢y x∉A | (no ¬p) with x ≟ a
-- still-∉-after-deleted y (x ∷ A) x≢y x∉A | no ¬p | yes refl = contradiction here x∉A
-- still-∉-after-deleted y (a ∷ A) x≢y x∉A | no ¬p | no ¬q = map-¬∷ (still-∉-after-deleted y A x≢y) ¬q x∉A
--
-- still-∉-after-recovered : ∀ {x} y A → x ≢ y → x ∉c delete y A → x ∉ c[ A ]
-- still-∉-after-recovered     y []      x≢y x∉deleted ()
-- still-∉-after-recovered     y (a  ∷ A) x≢y x∉deleted x∈a∷A with y ≟ a
-- still-∉-after-recovered     y (.y ∷ A) x≢y x∉deleted x∈a∷A | yes refl = still-∉-after-recovered y A x≢y x∉deleted (there-if-not-here x≢y x∈a∷A)
-- still-∉-after-recovered {x} y (a  ∷ A) x≢y x∉deleted x∈a∷A | no ¬p with x ≟ a
-- still-∉-after-recovered     y (x  ∷ A) x≢y x∉deleted x∈a∷A | no ¬p | yes refl = contradiction here x∉deleted
-- still-∉-after-recovered     y (a  ∷ A) x≢y x∉deleted x∈a∷A | no ¬p | no ¬q = x∉deleted (∷-⊆-monotone (still-∈-after-deleted y A x≢y) x∈a∷A)

singleton : String → Collection
singleton x = x ∷ []

singleton-≡ : ∀ {x y} → x ∈ c[ singleton y ] → x ≡ y
singleton-≡ here = refl
singleton-≡ (there ())
