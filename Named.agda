module Named where

open import Data.String
open import Data.Nat hiding (_≟_)
open import Data.Bool using (T; not)
open import Data.Product
open import Data.Sum
-- open import Data.Nat.Properties using (strictTotalOrder)
-- open import Relation.Binary using (StrictTotalOrder)
-- open import Relation.Binary.Core
open import Function.Equivalence using (_⇔_; equivalence)

open import Relation.Nullary
open import Relation.Unary
open import Relation.Nullary.Negation
open import Data.Unit using (⊤)
open import Function using (_∘_)
-- open import Level renaming (zero to Lzero)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Data.Collection
open import Data.Collection.Properties
open import Data.Collection.Equivalence


Variable = String

data PreTerm : Set where
    Var : (w : Variable) → PreTerm
    App : (P : PreTerm) → (Q : PreTerm) → PreTerm
    Abs : (w : Variable) → (Q : PreTerm) → PreTerm

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
lem-1-2-5-a : ∀ M N v → v ∉ c[ FV M ] → M [ v ≔ N ] ≡ M
lem-1-2-5-a (Var x) N v v∉M with x ≟ v
lem-1-2-5-a (Var x) N .x v∉M | yes refl = contradiction here v∉M
lem-1-2-5-a (Var x) N v v∉M | no ¬p = refl
lem-1-2-5-a (App P Q) N v v∉M = cong₂
    App
        (lem-1-2-5-a P N v (not-in-left-union (FV P) (FV Q) v∉M))
        (lem-1-2-5-a Q N v (not-in-right-union (FV P) (FV Q) v∉M))
lem-1-2-5-a (Abs x M) N v v∉M with x ≟ v
lem-1-2-5-a (Abs x M) N v v∉M | yes p = cong (λ z → Abs z M) (sym p)
lem-1-2-5-a (Abs x M) N v v∉M | no ¬p = cong (Abs x) (lem-1-2-5-a M N v (still-∉-after-recovered x (FV M) ¬p v∉M))


-- begin
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ≡⟨ {!   !} ⟩
--     {!   !}
-- ∎

-- goal0 : ∀ {x v N} P Q → x ∈c union (FV P) (FV Q) → x ∈c union (FV (P [ v ≔ N ])) (FV (Q [ v ≔ N ]))
-- goal0 {x} {v} {N} P Q ∈∪ =

-- If M[v≔N] is defined, v ≠ x and x ∈ FV(M) iff x ∈ FV(M[v≔N])
lem-1-2-5-b-i : ∀ {x v N} M → v ≢ x → x ∈ c[ FV M ] ⇔ x ∈ c[ FV (M [ v ≔ N ]) ]
lem-1-2-5-b-i {v = v} (Var w) v≢x with w ≟ v
lem-1-2-5-b-i (Var v) v≢x | yes refl = {! v≢x  !}
lem-1-2-5-b-i (Var w) v≢x | no ¬p = {!   !}
lem-1-2-5-b-i {x} {v} {N} (App P Q) v≢x = equivalence to {!   !}
    where   open import Relation.Binary.PropositionalEquality using (setoid)
            open import Function.Equality using (_⟶_)
            to : x ∈ c[ union (FV P) (FV Q) ] → x ∈ c[ union (FV (P [ v ≔ N ])) (FV (Q [ v ≔ N ])) ]
            to = map-⊆-union {FV P} {FV Q} {FV (P [ v ≔ N ])} {FV (Q [ v ≔ N ])} (_≢_ v) {!  !} {!   !} {!   !}


lem-1-2-5-b-i (Abs w M) v≢x = {!   !}

-- lem-1-2-5-b-i : ∀ {x v N} M → v ≢ x → (x ∈ FV M) ⇔ (x ∈ FV (M [ v ≔ N ]))
-- lem-1-2-5-b-i : ∀ {x v N} M → v ≢ x → (x ∈ FV M) ≡ (x ∈ FV (M [ v ≔ N ]))
-- lem-1-2-5-b-i : ∀ {x v N} M → v ≢ x → (x ∈ c[ FV M ]) ≡ (x ∈ c[ FV (M [ v ≔ N ]) ])
-- lem-1-2-5-b-i {v = v} (Var w) v≢x with w ≟ v
-- lem-1-2-5-b-i (Var v) v≢x | yes refl = {!   !}
-- lem-1-2-5-b-i {x} (Var w) v≢x | no ¬p = refl -- cong (_∈_ x) refl
-- lem-1-2-5-b-i {x} {v} {N} (App P Q) v≢x =
--     begin
--         x ∈ c[ union (FV P) (FV Q) ]
--     ≡⟨ sym {! ∪-union  !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         {!   !}
--     ≡⟨ {!   !} ⟩
--         x ∈ c[ union (FV (P [ v ≔ N ])) (FV (Q [ v ≔ N ])) ]
--     ∎
-- lem-1-2-5-b-i (Abs w P) v≢x = {!    !}
-- lem-1-2-5-b-i {v = v} (Var w) v≢x x∈FV-M with w ≟ v
-- lem-1-2-5-b-i (Var w)   v≢x x∈FV-M | yes p = ? -- contradiction (trans (singleton-≡ x∈FV-M) p) (v≢x ∘ sym)
-- lem-1-2-5-b-i (Var w)   v≢x x∈FV-M | no ¬p = ? -- x∈FV-M
-- lem-1-2-5-b-i (App P Q) v≢x x∈FV-M = ? -- ∈-respects-≡ {!   !} x∈FV-M
-- lem-1-2-5-b-i (App P Q) v≢x x∈FV-M = ∈-respects-≡ (cong₂ union (cong FV {!   !}) (cong FV {!    !})) x∈FV-M
-- lem-1-2-5-b-i (App P Q) v≢x x∈FV-M = ∈-respects-≡ (cong₂ union ({!   !}) {!   !}) x∈FV-M
-- lem-1-2-5-b-i (Abs w P) v≢x x∈FV-M = {!   !}


-- If M[v≔N] is defined then y ∈ FV(M[v≔N]) iff either y ∈ FV(M) and v ≠ y
-- or y ∈ FV(N) and x ∈ FV(M)



-- lem-1-2-5-b-i : ∀ {x y N} M v →  y ∈ FV (M [ v ≔ N ]) → y ∈ FV M × x ≢ y ⊎ y ∈ FV N × x ∈ FV M
-- lem-1-2-5-b⇒ (Var w) v y∈Applied with w ≟ v
-- lem-1-2-5-b⇒ (Var w) v y∈Applied | yes p = {!   !}
-- lem-1-2-5-b⇒ (Var w) v y∈Applied | no ¬p = inj₁ (y∈Applied , {! singleton-≡ ∈  !})
-- lem-1-2-5-b⇒ (App P Q) v y∈Applied = {!   !}
-- lem-1-2-5-b⇒ (Abs w P) v y∈Applied = {!   !}
--
-- lem-1-2-5-b⇐ : ∀ {x y v M N} → y ∈ FV M × x ≢ y ⊎ y ∈ FV N × x ∈ FV M → y ∈ FV (M [ v ≔ N ])
-- lem-1-2-5-b⇐ = {!   !}


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
