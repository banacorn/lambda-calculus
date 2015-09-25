module Collection.Core where

open import Data.List using (List; []; _∷_)
open import Data.String using (String)
open import Level using (zero)

open import Function using (flip)
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary


Collection : Set
Collection = List String

infix 4 _∈c_ _∉c_

data _∈c_ : REL String Collection zero where
    here  : ∀ {   x A}         → x ∈c x ∷ A
    there : ∀ {a x A} → x ∈c A → x ∈c a ∷ A

c[_] : REL Collection String zero
c[_] = flip _∈c_

_∉c_ : REL String Collection _
x ∉c A = x ∉ c[ A ]
