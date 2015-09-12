module Named.Collection where

open import Data.List
open import Data.Product
open import Data.Sum renaming (map to mapSum)
open import Data.String
open import Data.Bool using (Bool; true; false; T; not)
open import Level renaming (zero to lvl0)
open import Function
open import Function.Equivalence using (_⇔_)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable renaming (map to mapDec; map′ to mapDec′)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_; refl; sym; cong; trans)

Collection : Set
Collection = List String

infix 4 _∈c_

data _∈c_ : REL String Collection lvl0 where
    here  : ∀ {   x A}         → x ∈c x ∷ A
    there : ∀ {a x A} → x ∈c A → x ∈c a ∷ A

_∉c_ : REL String Collection _
x ∉c A = ¬ x ∈c A


-- here-repects-≡ : ∀ {P} → (λ x → x ∈c P) Respects _≡_
here-repects-≡ : ∀ {x a A} → x ≡ a → x ∈c a ∷ A → a ∈c a ∷ A
here-repects-≡ refl = id

there⁻¹ : ∀ {x a A} → x ≢ a → x ∈c a ∷ A → x ∈c A
there⁻¹ x≢a here            = contradiction refl x≢a
there⁻¹ x≢a (there x∈a∷A) = x∈a∷A

_∈?_ : (x : String) → (A : Collection) → Dec (x ∈c A)
x ∈? [] = no (λ ())
x ∈? (a ∷ A) with x ≟ a
x ∈? (.x ∷ A) | yes refl = yes here
x ∈? (a ∷ A) | no ¬p = mapDec′ there (there⁻¹ ¬p) (x ∈? A)

union : Collection → Collection → Collection
union []      B = B
union (a ∷ A) B with a ∈? B
union (a ∷ A) B | yes p = union A B
union (a ∷ A) B | no ¬p = a ∷ union A B

in-right-union : ∀ {x} A B → x ∈c B → x ∈c union A B
in-right-union []      B x∈B = x∈B
in-right-union (a ∷ A) B x∈B with a ∈? B
in-right-union (a ∷ A) B x∈B | yes p = in-right-union A B x∈B
in-right-union (a ∷ A) B x∈B | no ¬p = there (in-right-union A B x∈B)

in-left-union : ∀ {x} A B → x ∈c A → x ∈c union A B
in-left-union []      B ()
in-left-union (a ∷ A) B x∈A         with a ∈? B
in-left-union (a ∷ A) B here        | yes p = in-right-union A B p
in-left-union (a ∷ A) B (there x∈A) | yes p = in-left-union A B x∈A
in-left-union (a ∷ A) B here        | no ¬p = here
in-left-union (a ∷ A) B (there x∈A) | no ¬p = there (in-left-union A B x∈A)

in-either : ∀ {x} A B → x ∈c union A B → x ∈c A ⊎ x ∈c B
in-either []      B x∈A∪B         = inj₂ x∈A∪B
in-either (a ∷ A) B x∈A∪B         with a ∈? B
in-either (a ∷ A) B x∈A∪B         | yes p = mapSum there id (in-either A B x∈A∪B)
in-either (a ∷ A) B here          | no ¬p = inj₁ here
in-either (a ∷ A) B (there x∈A∪B) | no ¬p = mapSum there id (in-either A B x∈A∪B)

union-branch-1 : ∀ {x a} A B → a ∈c B → x ∈c union (a ∷ A) B → x ∈c union A B
union-branch-1 {x} {a} A B a∈B x∈union with a ∈? B
union-branch-1 A B a∈B x∈union | yes p = x∈union
union-branch-1 A B a∈B x∈union | no ¬p = contradiction a∈B ¬p

there-left-union-coherence : ∀ {x} {a} A B → x ∈c a ∷ A → x ∈c a ∷ union A B
there-left-union-coherence A B here          = here
there-left-union-coherence A B (there x∈a∷A) = there (in-left-union A B x∈a∷A)


in-neither : ∀ {x} A B → x ∉c union A B → x ∉c A × x ∉c B
in-neither []      B x∉A∪B = (λ ()) , x∉A∪B
in-neither (a ∷ A) B x∉A∪B with a ∈? B
in-neither (a ∷ A) B x∉A∪B | yes a∈B = (contraposition (union-branch-1 A B a∈B ∘ in-left-union (a ∷ A) B) x∉A∪B) , (contraposition (in-right-union A B) x∉A∪B)
in-neither (a ∷ A) B x∉A∪B | no a∉B = (contraposition (there-left-union-coherence A B) x∉A∪B) , contraposition (there ∘ in-right-union A B) x∉A∪B

singleton : String → Collection
singleton s = s ∷ []

delete : String → Collection → Collection
delete s [] = []
delete s (x ∷ A) with s ∈? A
delete s (x ∷ A) | yes p = x ∷ A
delete s (x ∷ A) | no ¬p = s ∷ delete x A


--
-- nub : Collection → Collection
-- nub [] = []
-- nub (x ∷ A) with any (_==_ x) A
-- nub (x ∷ A) | true = A
-- nub (x ∷ A) | false = x ∷ A
--
-- -- union : Collection → Collection → Collection
-- -- union []       B = B
-- -- union (x ∷ A) [] = x ∷ A
-- -- union (x ∷ A) (y ∷ B) with x ∈c (y ∷ B)
-- -- ... | here = {! z  !}
-- -- union (x ∷ A) B | true  = union A B
-- -- union (x ∷ A) B | false = x ∷ union A B
--
--
-- -- intersection : Collection → Collection → Collection
-- -- intersection [] B = []
-- -- intersection (x ∷ A) B with any (_==_ x) B
-- -- intersection (x ∷ A) B | true = x ∷ intersection A B
-- -- intersection (x ∷ A) B | false = intersection A B
-- --
-- -- delete : String → Collection → Collection
-- -- delete s [] = []
-- -- delete s (x ∷ A) with s == x
-- -- delete s (x ∷ A) | true = A
-- -- delete s (x ∷ A) | false = x ∷ delete s A
-- --
-- -- union-right-identity : ∀ P → union P [] ≡ P
-- -- union-right-identity [] = refl
-- -- union-right-identity (x ∷ P) = cong (_∷_ x) (union-right-identity P)
-- --
-- --
-- --
-- --
-- -- trans-∉c : ∀ {x} P Q → P ≡ Q → x ∉c P → x ∉c Q
-- -- trans-∉c P .P refl x∉P x∈Q = x∉P x∈Q
-- --
-- -- a : "a" ∈c ("haha" ∷ "a" ∷ [])
-- -- a = there here
-- --
-- -- b : ¬ ("b" ∈c ("haha" ∷ "a" ∷ []))
-- -- b (there (there ()))
-- --
-- -- -- lem : ∀ {x} P Q → x ∉c (union (p ∷ P) (q ∷ Q)) → x ∉c (p ∷ P)
-- -- -- lem
-- --
-- -- -- lem : ∀ {x q} P Q → x ∈c union P (q ∷ Q) → x ∈c (p ∷ P)
-- -- -- lem P Q x∈union = ?
-- --
-- --
-- -- in-both : ∀ {x} P Q → x ∈c union P Q → x ∈c P ⊎ x ∈c Q
-- -- in-both []      Q       x∈union = inj₂ x∈union
-- -- in-both (p ∷ P) []      x∈union = inj₁ (subst-coll-∈c (union (p ∷ P) []) (p ∷ P) (union-right-identity (p ∷ P)) x∈union)
-- -- in-both (p ∷ P) (q ∷ Q) x∈union with any (_==_ p) (q ∷ Q)
-- -- in-both (p ∷ P) (q ∷ Q) x∈union | true = {!   !}
-- -- in-both (p ∷ P) (q ∷ Q) x∈union | false = {!   !}
-- --
-- -- in-neither : ∀ x P Q → x ∉c union P Q → x ∉c P × x ∉c Q
-- -- in-neither x []       Q      x∉union = (λ ()) , x∉union
-- -- in-neither x (p ∷ P) []      x∉union = trans-∉c (p ∷ union P []) (p ∷ P) (union-right-identity (p ∷ P)) x∉union , (λ ())
-- -- in-neither x (p ∷ P) (q ∷ Q) x∉union with any (_==_ p) (q ∷ Q)
-- -- in-neither x (p ∷ P) (q ∷ Q) x∉union | true = {!   !} , {!   !}
-- -- in-neither x (p ∷ P) (q ∷ Q) x∉union | false = {!   !} , {!   !}
-- --
-- -- -- = trans-∉c {!   !} {!   !} {!   !} x∉union , {!   !}
-- --
-- -- -- _∈c_ : String → Collection → Set
-- -- -- s ∈c [] = ⊥
-- -- -- s ∈c (x ∷ A) with s == x
-- -- -- s ∈c (x ∷ A) | true = ⊤
-- -- -- s ∈c (x ∷ A) | false = s ∈c A
-- -- --
-- -- -- has : Collection → Pred String _
-- -- -- has = flip _∈c_
-- -- --
-- -- -- of : Pred Collection _
-- -- -- of = λ x → (λ s → {!   !}) {!   !}
-- -- --
-- -- --
-- -- -- in-both : ∀ {x P Q} → x ∈ c[ intersection P Q ] → x ∈ c[ P ] × x ∈ c[ Q ]
-- -- -- in-both {x} {P} {Q} x∈intersection = {!   !} , {!   !}
-- -- --
-- -- -- -- in-neither : ∀ {x P Q} → x ∉ c[ union P Q ] → x ∉ c[ P ] × x ∉ c[ Q ]
-- -- -- -- in-neither {x} {P} {Q} x∉union = contradiction {!   !} x∉union , {!   !}
-- -- --
-- -- -- --
-- -- -- _∈?_ : String → Collection → Bool
-- -- -- s ∈? [] = false
-- -- -- s ∈? (x ∷ A) with s == x
-- -- -- s ∈? (x ∷ A) | true = true
-- -- -- s ∈? (x ∷ A) | false = s ∈? A
-- -- --
-- -- --
-- -- -- -- in-neither : ∀ {x P Q} → T (not (x ∈? union P Q)) → T (not (x ∈? P)) × T (not (x ∈? Q))
-- -- -- -- in-neither x∉union = {!  !}
