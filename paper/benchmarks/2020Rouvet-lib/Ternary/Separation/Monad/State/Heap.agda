open import Data.List
open import Data.Unit

open import Relation.Unary hiding (_∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Separation
open import Relation.Ternary.Separation.Construct.Market
open import Relation.Ternary.Separation.Monad
open import Relation.Ternary.Separation.Morphisms

module Relation.Ternary.Separation.Monad.State.Heap 
  {ℓ}

  {T : Set ℓ}

  (V : T → Pred (List T) ℓ) 
  where

open import Level hiding (Lift)
open import Function using (_∘_; case_of_)
import Relation.Binary.HeterogeneousEquality as HEq
open import Relation.Unary.PredicateTransformer hiding (_⊔_; [_])
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Ternary.Separation.Construct.Product
open import Relation.Ternary.Separation.Construct.List T
open import Relation.Ternary.Separation.Morphisms
open import Relation.Ternary.Separation.Monad
open import Relation.Ternary.Separation.Allstar

open import Data.Product
open import Data.List.Relation.Ternary.Interleaving.Propositional as I
  
module HeapOps 
  (M : Pt (Market (List T)) ℓ)
  {{monad : Monads.Monad ⊤ ℓ (λ _ _ → M) }}
  where
  Cells : Pred (List T × List T) ℓ
  Cells (Σ , Φ) = Allstar V Σ Φ

  open import Relation.Ternary.Separation.Monad.State
  open StateTransformer M public
  open Monads using (str)
  open Monads.Monad {{...}}

  newref : ∀ {a} → ∀[ V a ⇒ StateT M Cells (Just a) ]
  app (newref v) (lift st σ₁) (offerᵣ σ₂) =
    let _ , τ₁ , τ₂ = ⊎-assoc (⊎-comm σ₂) σ₁
    in return (
      inj refl
        ×⟨ offerᵣ ⊎-∙ ⟩
      lift (cons (v ×⟨ τ₂ ⟩ st)) (⊎-∙ₗ τ₁))

  read : ∀ {a} → ∀[ Just a ⇒ StateT M Cells (V a) ]
  app (read refl) (lift st σ₁) (offerᵣ σ₂) with ⊎-assoc σ₂ σ₁
  ... | _ , σ₃ , σ₄ with repartition σ₃ st
  ... | cons (v ×⟨ σ₅ ⟩ nil) ×⟨ σ₆ ⟩ st' with ⊎-id⁻ʳ σ₅ | ⊎-assoc (⊎-comm σ₆) (⊎-comm σ₄)
  ... | refl | _ , τ₁ , τ₂ = return (inj v ×⟨ offerᵣ τ₂ ⟩ lift st' (⊎-comm τ₁))

  write : ∀ {a b} → ∀[ Just b ✴ (V a) ⇒ StateT M Cells (Just a ✴ V b) ]
  app (write (refl ×⟨ σ₁ ⟩ v)) (lift st σ₂) (offerᵣ σ₃) with ⊎-assoc (⊎-comm σ₁) σ₃
  ... | _ , τ₁ , τ₂ with ⊎-assoc (⊎-comm τ₁) σ₂
  ... | _ , τ₃ , τ₄ with ⊎-assoc τ₂ τ₃
  ... | _ , τ₅ , τ₆
    with repartition τ₅ st
  ... | cons (vb ×⟨ σ₅ ⟩ nil) ×⟨ σ₆ ⟩ st' rewrite ⊎-id⁻ʳ σ₅ = 
    let 
      _ , κ₁ , κ₂ = ⊎-unassoc τ₄ (⊎-comm σ₆) 
      _ , κ₃ , κ₄ = ⊎-assoc κ₂ (⊎-comm τ₆)
    in return (
      inj (refl ×⟨ consˡ ⊎-idˡ ⟩ vb)
        ×⟨ offerᵣ (consˡ κ₄) ⟩
      lift (cons (v ×⟨ κ₁ ⟩ st')) (⊎-∙ₗ (⊎-comm κ₃)))

  update! : ∀ {a b} → ∀[ Just a ⇒ (V a ─✴ StateT M Cells (V b)) ─✴ StateT M Cells (Just b) ]
  app (update! ptr) f σ = do
    a ×⟨ σ₁ ⟩ f ← read ptr &⟨ σ ⟩ f
    b           ← app f a (⊎-comm σ₁)
    newref b
