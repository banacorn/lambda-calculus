module Named.Collection where
-- Credits to tomjack from Agda IRC

open import Data.String
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe

betterStrictTotalOrder : StrictTotalOrder _ _ _
betterStrictTotalOrder = record
    { Carrier = String
        ; _≈_ = _≡_
        ; _<_ = _<_
        ; isStrictTotalOrder = record
        { isEquivalence = PropEq.isEquivalence
        ; trans = λ { {x} {y} {z} → trans {x} {y} {z} }
        ; compare = compare'
        ; <-resp-≈ = resp'
        }
    }
    where
        open StrictTotalOrder strictTotalOrder
        import Relation.Binary.List.Pointwise as Pointwise
        open import Data.Char.Core using ( primCharToNat )
        open import Data.String.Core using ( primStringToList )
        foo : ∀ {x y} → x ≡ y → Pointwise.Rel (λ c d → primCharToNat c ≡ primCharToNat d) (primStringToList x) (primStringToList y)
        foo PropEq.refl = Pointwise.reflexive {_≈_ = _≡_}
            (PropEq.cong primCharToNat)
            (Pointwise.refl PropEq.refl)

        compare' : Trichotomous _≡_ _<_
        compare' x y with compare x y
        compare' x y | tri< a ¬b ¬c = tri< a (λ p → ¬b (foo p)) ¬c
        compare' x y | tri≈ ¬a b ¬c = tri≈ ¬a trustMe ¬c
        compare' x y | tri> ¬a ¬b c = tri> ¬a (λ p → ¬b (foo p)) c

        resp' : _<_ Respects₂ _≡_
        resp' = PropEq.resp₂ _<_

betterIsStrictTotalOrder = StrictTotalOrder.isStrictTotalOrder betterStrictTotalOrder

import Data.AVL.Sets
open module Collection = Data.AVL.Sets betterIsStrictTotalOrder public
