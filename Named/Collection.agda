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
    here  : ∀ {   x xs}           → x ∈c x ∷ xs
    there : ∀ {x' x xs} → x ∈c xs → x ∈c x' ∷ xs

_∉c_ : REL String Collection _
x ∉c xs = ¬ x ∈c xs

-- data _⊆c_ : Rel Collection lvl0 where
--     reflex : ∀ {xs}   → xs ⊆c xs
--     extend : ∀ {xs x} → xs ⊆c x ∷ xs
--
-- _⊈c_ : Rel Collection _
-- x ⊈c xs = ¬ x ⊆c xs

-- here-repects-≡ : ∀ {P} → (λ x → x ∈c P) Respects _≡_
here-repects-≡ : ∀ {s x xs} → s ≡ x → s ∈c s ∷ xs → s ∈c x ∷ xs
here-repects-≡ refl = id

there⁻¹ : ∀ {s x xs} → s ≢ x → s ∈c x ∷ xs → s ∈c xs
there⁻¹ s≢x here            = contradiction refl s≢x
there⁻¹ s≢x (there s∈x∷xs) = s∈x∷xs

_∈?_ : (s : String) → (xs : Collection) → Dec (s ∈c xs)
s ∈? [] = no (λ ())
s ∈? (x ∷ xs) with s ≟ x
s ∈? (.s ∷ xs) | yes refl = yes here
s ∈? (x ∷ xs) | no ¬p = mapDec′ there (there⁻¹ ¬p) (s ∈? xs)

union : Collection → Collection → Collection
union [] ys = ys
union (x ∷ xs) ys with x ∈? ys
union (x ∷ xs) ys | yes p = union xs ys
union (x ∷ xs) ys | no ¬p = x ∷ union xs ys

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

-- singleton : String → Collection
-- singleton s = s ∷ []
--
-- nub : Collection → Collection
-- nub [] = []
-- nub (x ∷ xs) with any (_==_ x) xs
-- nub (x ∷ xs) | true = xs
-- nub (x ∷ xs) | false = x ∷ xs
--
-- -- union : Collection → Collection → Collection
-- -- union []       ys = ys
-- -- union (x ∷ xs) [] = x ∷ xs
-- -- union (x ∷ xs) (y ∷ ys) with x ∈c (y ∷ ys)
-- -- ... | here = {! z  !}
-- -- union (x ∷ xs) ys | true  = union xs ys
-- -- union (x ∷ xs) ys | false = x ∷ union xs ys
--
--
-- -- intersection : Collection → Collection → Collection
-- -- intersection [] ys = []
-- -- intersection (x ∷ xs) ys with any (_==_ x) ys
-- -- intersection (x ∷ xs) ys | true = x ∷ intersection xs ys
-- -- intersection (x ∷ xs) ys | false = intersection xs ys
-- --
-- -- delete : String → Collection → Collection
-- -- delete s [] = []
-- -- delete s (x ∷ xs) with s == x
-- -- delete s (x ∷ xs) | true = xs
-- -- delete s (x ∷ xs) | false = x ∷ delete s xs
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
-- -- -- s ∈c (x ∷ xs) with s == x
-- -- -- s ∈c (x ∷ xs) | true = ⊤
-- -- -- s ∈c (x ∷ xs) | false = s ∈c xs
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
-- -- -- s ∈? (x ∷ xs) with s == x
-- -- -- s ∈? (x ∷ xs) | true = true
-- -- -- s ∈? (x ∷ xs) | false = s ∈? xs
-- -- --
-- -- --
-- -- -- -- in-neither : ∀ {x P Q} → T (not (x ∈? union P Q)) → T (not (x ∈? P)) × T (not (x ∈? Q))
-- -- -- -- in-neither x∉union = {!  !}
