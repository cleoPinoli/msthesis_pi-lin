module Context where

open import Data.Nat using (ℕ; zero; suc; _+_)
import Data.Nat.Properties as NatProp
open import Data.Product using (_×_)
open import Data.Sum
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

open import List
open import Type

Context : Set
Context = List Type

infix 4 _≃_+_

data _≃_+_ : Context -> Context -> Context -> Set where
  split-e : [] ≃ [] + []
  split-l : ∀{Γ Γ₁ Γ₂ A} -> Γ ≃ Γ₁ + Γ₂ -> A :: Γ ≃ A :: Γ₁ + Γ₂
  split-r : ∀{Γ Γ₁ Γ₂ A} -> Γ ≃ Γ₁ + Γ₂ -> A :: Γ ≃ Γ₁ + A :: Γ₂

+-comm : ∀{Γ Γ₁ Γ₂} -> Γ ≃ Γ₁ + Γ₂ -> Γ ≃ Γ₂ + Γ₁
+-comm split-e = split-e
+-comm (split-l p) = split-r (+-comm p)
+-comm (split-r p) = split-l (+-comm p)

postulate +-assoc-r : ∀{Γ Γ₁ Γ₂ Δ₁ Δ₂} -> Γ ≃ Γ₁ + Γ₂ -> Γ₂ ≃ Δ₁ + Δ₂ ->
            ∃[ Δ ] (Δ ≃ Γ₁ + Δ₁) × (Γ ≃ Δ + Δ₂)
-- +-assoc-r split-e split-e = [] , split-e , split-e
-- +-assoc-r (split-l p) q = {!!}
-- +-assoc-r (split-r p) q = {!!}

+-assoc-l : ∀{Γ Γ₁ Γ₂ Δ₁ Δ₂} -> Γ ≃ Γ₁ + Γ₂ -> Γ₁ ≃ Δ₁ + Δ₂ ->
            ∃[ Δ ] (Δ ≃ Δ₂ + Γ₂) × (Γ ≃ Δ₁ + Δ)
+-assoc-l p q with +-assoc-r (+-comm p) (+-comm q)
... | Δ , r , p' = Δ , +-comm r , +-comm p'

+-unit-l : ∀{Γ} -> Γ ≃ [] + Γ
+-unit-l {[]} = split-e
+-unit-l {A :: Γ} = split-r +-unit-l

+-unit-r : ∀{Γ} -> Γ ≃ Γ + []
+-unit-r = +-comm +-unit-l

+-sing-l : ∀{A B Γ} -> [ A ] ≃ [ B ] + Γ -> A ≡ B × Γ ≡ []
+-sing-l (split-l split-e) = refl , refl

+-length : ∀{Γ Γ₁ Γ₂} -> Γ ≃ Γ₁ + Γ₂ -> length Γ ≡ length Γ₁ + length Γ₂
+-length split-e = refl
+-length (split-l p) = Eq.cong suc (+-length p)
+-length {Γ} {Γ₁} {Γ₂} (split-r {Γ'} {_} {Γ₂'} {A} p) =
  begin
    length Γ ≡⟨⟩
    suc (length Γ') ≡⟨ Eq.cong suc (+-length p) ⟩
    suc (length Γ₁ + length Γ₂') ≡⟨ Eq.cong suc (NatProp.+-comm (length Γ₁) (length Γ₂')) ⟩
    suc (length Γ₂' + length Γ₁) ≡⟨⟩
    suc (length Γ₂') + length Γ₁ ≡⟨ NatProp.+-comm (suc (length Γ₂')) (length Γ₁) ⟩
    length Γ₁ + suc (length Γ₂') ≡⟨⟩
    length Γ₁ + length Γ₂
  ∎
