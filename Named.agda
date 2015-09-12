module Named where

open import Data.String
open import Data.Nat hiding (_≟_)
open import Data.Bool using (T; not)
open import Data.Product
-- open import Data.Nat.Properties using (strictTotalOrder)
-- open import Relation.Binary using (StrictTotalOrder)
-- open import Relation.Binary.Core
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Unit using (⊤)
open import Function using (_∘_)
-- open import Level renaming (zero to Lzero)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Named.Collection


Variable = String

data PreTerm : Set where
    Var : Variable → PreTerm
    App : PreTerm → PreTerm → PreTerm
    Abs : Variable → PreTerm → PreTerm

showPreTerm : PreTerm → String
showPreTerm (Var x)   = x
showPreTerm (App P Q) = "(" ++ showPreTerm P ++ " " ++ showPreTerm Q ++ ")"
showPreTerm (Abs x M) = "(λ" ++ x ++ "." ++ showPreTerm M ++ ")"

I : PreTerm
I = Abs "x" (Var "x")

S : PreTerm
S = Abs "x" (App (Var "y") (Var "x"))

FV : PreTerm → Collection
FV (Var x  ) = singleton x
FV (App f x) = union (FV f) (FV x)
FV (Abs x m) = delete x (FV m)

-- a = singleton "x" ∋ (elem "x" ∪ elem "y")


-- b = C[ singleton "x" ] ∩ C[ singleton "x" ]

-- M = FV S


-- neither∈ : ∀ {x A B} → x ∉ C[ A union B ] →

_[_≔_] : PreTerm → Variable → PreTerm → PreTerm
Var x [ v ≔ N ] with x ≟ v
Var x [ v ≔ N ] | yes p = N
Var x [ v ≔ N ] | no ¬p = Var x
App P Q [ v ≔ N ] = App (P [ v ≔ N ]) (Q [ v ≔ N ])
Abs x P [ v ≔ N ] with x ≟ v
Abs x P [ v ≔ N ] | yes p = Abs v P
Abs x P [ v ≔ N ] | no ¬p = Abs x (P [ v ≔ N ])

-- If v ∉ FV(M) then M[v≔N] is defined and M[v≔N] ≡ M
lem-1-2-5-a : ∀ M N v → v ∉ FV M → M [ v ≔ N ] ≡ M
lem-1-2-5-a (Var x) N v v∉M with x ≟ v
lem-1-2-5-a (Var x) N .x v∉M | yes refl = contradiction here v∉M
lem-1-2-5-a (Var x) N v v∉M | no ¬p = refl
lem-1-2-5-a (App P Q) N v v∉M = cong₂ App (lem-1-2-5-a P N v (proj₁ (in-neither (FV P) (FV Q) v∉M))) (lem-1-2-5-a Q N v (proj₂ (in-neither (FV P) (FV Q) v∉M)))
lem-1-2-5-a (Abs x M) N v v∉M with x ≟ v
lem-1-2-5-a (Abs x M) N v v∉M | yes p = cong (λ z → Abs z M) (sym p)
lem-1-2-5-a (Abs x M) N v v∉M | no ¬p = cong (Abs x) (lem-1-2-5-a M N v (still-∉-after-recovered x (FV M) (¬p ∘ sym) v∉M))


-- begin
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ∎

lem-1-2-5-c : (M : PreTerm) → (x : Variable) → M [ x ≔ Var x ] ≡ M
lem-1-2-5-c (Var x  ) y with x ≟ y
lem-1-2-5-c (Var x  ) y | yes p = sym (cong Var p)
lem-1-2-5-c (Var x  ) y | no ¬p = refl
lem-1-2-5-c (App P Q) y = cong₂ App (lem-1-2-5-c P y) (lem-1-2-5-c Q y)
lem-1-2-5-c (Abs x M) y  with x ≟ y
lem-1-2-5-c (Abs x M) y | yes p = cong (λ w → Abs w M) (sym p)
lem-1-2-5-c (Abs x M) y | no ¬p = cong (Abs x) (lem-1-2-5-c M y)


length : PreTerm → ℕ
length (Var x) = 1
length (App P Q) = length P + length Q
length (Abs x M) = 1 + length M


-- lem-1-2-5-c : (M : PreTerm) → (x : Variable) → (N : PreTerm) → T (not (x ∈? FV M)) → M [ x ≔ N ] ≡ M
-- lem-1-2-5-c (Var x') x N x∉M with x' ≟ x
-- lem-1-2-5-c (Var x') x N x∉M | yes p =
--     begin
--         N
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         Var x'
--     ∎
-- lem-1-2-5-c (Var x') x N x∉M | no ¬p = {!   !}
-- lem-1-2-5-c (App P Q)  x N x∉M =
--     begin
--         App (P [ x ≔ N ]) (Q [ x ≔ N ])
--     ≡⟨ refl ⟩
--         App P Q [ x ≔ N ]
--     ≡⟨ {!   !} ⟩
--         App P Q
--     ∎
-- lem-1-2-5-c (Abs x' M) x N x∉M = {!   !}


-- begin
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ∎
