{-# OPTIONS --rewriting #-}
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.List.Base using (List; []; _∷_; [_]; _++_; map)

open import Type

Context : ℕ -> Set
Context n = List (Type n)

infix 4 _≃_+_ _≃_,_

data _≃_+_ {n} : Context n → Context n → Context n → Set where
  split-e  : [] ≃ [] + []
  split-l  : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ A ∷ Δ + Θ
  split-r  : ∀{A Γ Δ Θ} → Γ ≃ Δ + Θ → A ∷ Γ ≃ Δ + A ∷ Θ

_≃_,_ : ∀{n} -> Context n → Type n → Context n → Set
Γ ≃ A , Δ = Γ ≃ [ A ] + Δ

+-comm : ∀{n} {Γ Δ Θ : Context n} → Γ ≃ Δ + Θ → Γ ≃ Θ + Δ
+-comm split-e = split-e
+-comm (split-l p) = split-r (+-comm p)
+-comm (split-r p) = split-l (+-comm p)

+-unit-l : ∀{n} {Γ : Context n} → Γ ≃ [] + Γ
+-unit-l {_} {[]} = split-e
+-unit-l {_} {_ ∷ _} = split-r +-unit-l

+-unit-r  : ∀{n} {Γ : Context n} → Γ ≃ Γ + []
+-unit-r = +-comm +-unit-l

++≃+ : ∀{n} {Γ Δ : Context n} → Γ ++ Δ ≃ Γ + Δ
++≃+ {n} {[]} = +-unit-l {n}
++≃+ {n} {_ ∷ _} = split-l {n} (++≃+ {n})

+-assoc-r  : ∀{n} {Γ Δ Θ Δ′ Θ′ : Context n} → Γ ≃ Δ + Θ → Θ ≃ Δ′ + Θ′ →
             ∃[ Γ′ ] Γ′ ≃ Δ + Δ′ × Γ ≃ Γ′ + Θ′
+-assoc-r split-e split-e = [] , split-e , split-e
+-assoc-r (split-l p) q with +-assoc-r p q
... | _ , p′ , q′ = _ , split-l p′ , split-l q′
+-assoc-r (split-r p) (split-l q) with +-assoc-r p q
... | _ , p′ , q′ = _ , split-r p′ , split-l q′
+-assoc-r (split-r p) (split-r q) with +-assoc-r p q
... | _ , p′ , q′ = _ , p′ , split-r q′

+-assoc-l  : ∀{n} {Γ Δ Θ Δ′ Θ′ : Context n} → Γ ≃ Δ + Θ → Δ ≃ Δ′ + Θ′ →
             ∃[ Γ′ ] Γ′ ≃ Θ′ + Θ × Γ ≃ Δ′ + Γ′
+-assoc-l p q with +-assoc-r (+-comm p) (+-comm q)
... | Δ , r , p′ = Δ , +-comm r , +-comm p′

+-empty-l : ∀{n} {Γ Δ : Context n} → Γ ≃ [] + Δ → Γ ≡ Δ
+-empty-l split-e = refl
+-empty-l (split-r p) = cong (_ ∷_) (+-empty-l p)

+-sing-l : ∀{n} {A B : Type n} {Γ : Context n} → [ A ] ≃ B , Γ → A ≡ B × Γ ≡ []
+-sing-l (split-l split-e) = refl , refl

data Un {n} : Context n → Set where
  un-[]  : Un []
  un-∷   : ∀{A Γ} → Un Γ → Un (¿ A ∷ Γ)
