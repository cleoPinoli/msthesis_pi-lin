open import Relation.Unary.Separation

module Relation.Unary.Separation.Construct.ListOf 
  {a} (A : Set a) 
  {{ r : RawSep A }}
  {{ _ : IsSep r }}
  where

open import Level
open import Data.Product
open import Data.List
open import Data.List.Properties using (++-isMonoid)
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.List.Relation.Binary.Permutation.Inductive

open import Relation.Binary.PropositionalEquality as P hiding ([_])
open import Relation.Unary hiding (_∈_; _⊢_)

open import Relation.Unary.Separation.Morphisms

private 
  Carrier = List A
  variable
    xˡ xʳ x y z : A
    xsˡ xsʳ xs ys zs : Carrier

data Split : (xs ys zs : Carrier) → Set a where
  divide   : xˡ ⊎ xʳ ≣ x → Split xs ys (xˡ ∷ xʳ ∷ zs) → Split xs ys (x ∷ zs)
  to-left  : Split xs ys zs → Split (z ∷ xs) ys (z ∷ zs)
  to-right : Split xs ys zs → Split xs (z ∷ ys) (z ∷ zs)
  []       : Split [] [] []
instance
  splits : RawSep Carrier
  RawSep._⊎_≣_ splits = Split

  split-is-sep : IsSep splits

  IsSep.⊎-comm split-is-sep (divide τ σ) = divide τ (⊎-comm σ)
  IsSep.⊎-comm split-is-sep (to-left σ)  = to-right (⊎-comm σ)
  IsSep.⊎-comm split-is-sep (to-right σ) = to-left (⊎-comm σ)
  IsSep.⊎-comm split-is-sep [] = []
  
  IsSep.⊎-assoc split-is-sep σ₁ (divide x σ₂) =
    let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂ in -, divide x σ₃ , σ₄
  IsSep.⊎-assoc split-is-sep (divide x σ₁) (to-left σ₂) = {!!}
  IsSep.⊎-assoc split-is-sep (to-left σ₁) (to-left σ₂) = {!!}
  IsSep.⊎-assoc split-is-sep (to-right σ₁) (to-left σ₂) = {!!} 
  IsSep.⊎-assoc split-is-sep σ₁ (to-right σ₂) =
    let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂ in -, to-right σ₃ , to-right σ₄
  IsSep.⊎-assoc split-is-sep [] [] = -, [] , []

