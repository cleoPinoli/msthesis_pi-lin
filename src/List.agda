module List where

open import Data.Nat using (ℕ; zero; suc; _+_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

infixr 5 _::_

[_] : ∀{A} -> A -> List A
[_] = _:: []

length : ∀{A} -> List A -> ℕ
length [] = 0
length (_ :: Γ) = suc (length Γ)

data _#_ {A} : List A -> List A -> Set where
  #refl : ∀{Γ} -> Γ # Γ
  #tran : ∀{Γ Δ Θ} -> Γ # Δ -> Δ # Θ -> Γ # Θ
  #next : ∀{Γ Δ A} -> Γ # Δ -> (A :: Γ) # (A :: Δ)
  #here : ∀{Γ A B} -> (A :: B :: Γ) # (B :: A :: Γ)

#nil : ∀{A}{xs : List A} -> [] # xs -> xs ≡ []
#nil #refl = refl
#nil (#tran π π') rewrite #nil π | #nil π' = refl

#one : ∀{A}{x : A}{xs : List A} -> [ x ] # xs -> xs ≡ [ x ]
#one #refl = refl
#one (#tran π π') rewrite #one π | #one π' = refl
#one (#next π) rewrite #nil π = refl

