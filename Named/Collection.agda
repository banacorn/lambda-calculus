module Named.Collection where

open import Data.List
open import Data.String
open import Data.List using ([]; _∷_) public
open import Data.Product
open import Data.Sum renaming (map to mapSum)
-- open import Data.Bool using (Bool; true; false; T; not)
open import Level renaming (zero to lvl0)
open import Function using (_∘_; id; flip)
-- open import Function.Equivalence using (_⇔_)
open import Relation.Nullary
open import Relation.Unary
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable renaming (map to mapDec; map′ to mapDec′)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_; refl; sym; cong; trans)

Collection : Set
Collection = List String

infix 4 _∈c_ _∉c_

data _∈c_ : REL String Collection lvl0 where
    here  : ∀ {   x A}         → x ∈c x ∷ A
    there : ∀ {a x A} → x ∈c A → x ∈c a ∷ A

c[_] = flip _∈c_

_∉c_ : REL String Collection _
x ∉c A = x ∉ c[ A ]

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


map-∷ : ∀ {x a A B} → (x ∈ c[ A ] → x ∈ c[ B ]) → x ∈ c[ a ∷ A ] → x ∈ c[ a ∷ B ]
map-∷ f here = here
map-∷ f (there x∈a∷A) = there (f x∈a∷A)

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

union : Collection → Collection → Collection
union []      B = B
union (a ∷ A) B with a ∈? B
union (a ∷ A) B | yes p = union A B
union (a ∷ A) B | no ¬p = a ∷ union A B



in-right-union : ∀ {x} A B → x ∈ c[ B ] → x ∈ c[ union A B ]
in-right-union []      B x∈B = x∈B
in-right-union (a ∷ A) B x∈B with a ∈? B
in-right-union (a ∷ A) B x∈B | yes p = in-right-union A B x∈B
in-right-union (a ∷ A) B x∈B | no ¬p = there (in-right-union A B x∈B)

in-left-union : ∀ {x} A B → x ∈ c[ A ] → x ∈ c[ union A B ]
in-left-union []      B ()
in-left-union (a ∷ A) B x∈A         with a ∈? B
in-left-union (a ∷ A) B here        | yes p = in-right-union A B p
in-left-union (a ∷ A) B (there x∈A) | yes p = in-left-union A B x∈A
in-left-union (a ∷ A) B here        | no ¬p = here
in-left-union (a ∷ A) B (there x∈A) | no ¬p = there (in-left-union A B x∈A)

in-either : ∀ {x} A B → x ∈ c[ union A B ] → x ∈ c[ A ] ⊎ x ∈ c[ B ]
in-either []      B x∈A∪B         = inj₂ x∈A∪B
in-either (a ∷ A) B x∈A∪B         with a ∈? B
in-either (a ∷ A) B x∈A∪B         | yes p = mapSum there id (in-either A B x∈A∪B)
in-either (a ∷ A) B here          | no ¬p = inj₁ here
in-either (a ∷ A) B (there x∈A∪B) | no ¬p = mapSum there id (in-either A B x∈A∪B)

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
still-∈-after-deleted y (a  ∷ A) x≢y x∈A | no ¬p    = map-∷ (still-∈-after-deleted y A x≢y) x∈A

still-∉-after-deleted : ∀ {x} y A → x ≢ y → x ∉ c[ A ] → x ∉ c[ delete y A ]
still-∉-after-deleted y []       x≢y x∉A = x∉A
still-∉-after-deleted y (a  ∷ A) x≢y x∉A with y ≟ a
still-∉-after-deleted y (.y ∷ A) x≢y x∉A | yes refl = still-∉-after-deleted y A x≢y (x∉A ∘ there)
still-∉-after-deleted {x} y (a  ∷ A) x≢y x∉A | (no ¬p) with x ≟ a
still-∉-after-deleted y (x ∷ A) x≢y x∉A | no ¬p | yes refl = contradiction here x∉A
still-∉-after-deleted y (a ∷ A) x≢y x∉A | no ¬p | no ¬q = map-¬∷ (still-∉-after-deleted y A x≢y) ¬q x∉A

still-∉-after-recovered : ∀ {x} y A → x ≢ y → x ∉c delete y A → x ∉ c[ A ]
still-∉-after-recovered     y []      x≢y x∉deleted ()
still-∉-after-recovered     y (a  ∷ A) x≢y x∉deleted x∈a∷A with y ≟ a
still-∉-after-recovered     y (.y ∷ A) x≢y x∉deleted x∈a∷A | yes refl = still-∉-after-recovered y A x≢y x∉deleted (there-if-not-here x≢y x∈a∷A)
still-∉-after-recovered {x} y (a  ∷ A) x≢y x∉deleted x∈a∷A | no ¬p with x ≟ a
still-∉-after-recovered     y (x  ∷ A) x≢y x∉deleted x∈a∷A | no ¬p | yes refl = contradiction here x∉deleted
still-∉-after-recovered     y (a  ∷ A) x≢y x∉deleted x∈a∷A | no ¬p | no ¬q = x∉deleted (map-∷ (still-∈-after-deleted y A x≢y) x∈a∷A)

singleton : String → Collection
singleton x = x ∷ []

singleton-≡ : ∀ {x y} → x ∈ c[ singleton y ] → x ≡ y
singleton-≡ here = refl
singleton-≡ (there ())
