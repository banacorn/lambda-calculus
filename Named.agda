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
-- open import Function using (const; flip)
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

open import Relation.Unary

-- a = singleton "x" ∋ (elem "x" ∪ elem "y")


-- b = C[ singleton "x" ] ∩ C[ singleton "x" ]

-- M = FV S


-- neither∈ : ∀ {x A B} → x ∉ C[ A union B ] →

_[_≔_] : PreTerm → Variable → PreTerm → PreTerm
Var x' [ x ≔ N ] with x' ≟ x
Var x' [ x ≔ N ] | yes p = N
Var x' [ x ≔ N ] | no ¬p = Var x'
App P Q [ x ≔ N ] = App (P [ x ≔ N ]) (Q [ x ≔ N ])
Abs x' P [ x ≔ N ] with x' ≟ x
Abs x' P [ x ≔ N ] | yes p = Abs x P
Abs x' P [ x ≔ N ] | no ¬p = Abs x' (P [ x ≔ N ])

-- If x ∉ FV(M) then M[x≔N] is defined and M[x≔N] ≡ M
lem-1-2-5-a : ∀ M N x → x ∉c FV M → M [ x ≔ N ] ≡ M
lem-1-2-5-a (Var y) N x x∉M with y ≟ x
lem-1-2-5-a (Var y) N .y x∉M | yes refl = contradiction here x∉M
lem-1-2-5-a (Var y) N x x∉M | no ¬p = refl
lem-1-2-5-a (App P Q) N x x∉M = cong₂ App (lem-1-2-5-a P N x (proj₁ (in-neither (FV P) (FV Q) x∉M))) (lem-1-2-5-a Q N x (proj₂ (in-neither (FV P) (FV Q) x∉M)))
lem-1-2-5-a (Abs y M) N x x∉M with y ≟ x
lem-1-2-5-a (Abs y M) N x x∉M | yes p = sym (cong (λ z → Abs z M) p)
lem-1-2-5-a (Abs y M) N x x∉M | no ¬p = cong (Abs y) (lem-1-2-5-a M N x {!   !})


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
