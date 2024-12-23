{-# OPTIONS --guardedness #-}

-- contextInf ≡ context_finite, unchanged
module ContextInf where

open import Data.Product using (_×_; Σ; _,_; ∃; Σ-syntax; ∃-syntax)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import TypeInf

data Context : Set where
  []   : Context
  _::_ : Type -> Context -> Context

infixr 5 _::_

[_] : Type -> Context
[_] = _:: []

data _#_ : Context -> Context -> Set where
  #refl : ∀{Γ} -> Γ # Γ
  #tran : ∀{Γ Δ Θ} -> Γ # Δ -> Δ # Θ -> Γ # Θ
  #next : ∀{Γ Δ A} -> Γ # Δ -> (A :: Γ) # (A :: Δ)
  #here : ∀{Γ A B} -> (A :: B :: Γ) # (B :: A :: Γ)

#nil : ∀{Γ} -> [] # Γ -> Γ ≡ []
#nil #refl = refl
#nil {Γ} (#tran π π') rewrite #nil π = #nil π'

#one : ∀{A Γ} -> [ A ] # Γ -> Γ ≡ [ A ]
#one #refl = refl
#one (#tran π π') rewrite #one π | #one π' = refl
#one (#next π) rewrite #nil π = refl

-- rotation: next but make it a triple
#rot : ∀{A B C Γ} -> (A :: B :: C :: Γ) # (C :: A :: B :: Γ)
#rot = #tran (#next #here) #here

infix 4 _≃_+_


data _≃_+_ : Context -> Context -> Context -> Set where
  split-e : [] ≃ [] + []
  split-l : ∀{A Γ Δ Θ} -> Γ ≃ Δ + Θ -> A :: Γ ≃ A :: Δ + Θ
  split-r : ∀{A Γ Δ Θ} -> Γ ≃ Δ + Θ -> A :: Γ ≃ Δ + A :: Θ
  
+-comm : ∀{Γ Δ Θ} -> Γ ≃ Δ + Θ -> Γ ≃ Θ + Δ
+-comm split-e = split-e
+-comm (split-l p) = split-r (+-comm p)
+-comm (split-r p) = split-l (+-comm p)

+-assoc-r :
  ∀{Γ Δ Θ Δ' Θ'} -> Γ ≃ Δ + Θ -> Θ ≃ Δ' + Θ' -> ∃[ Γ' ] (Γ' ≃ Δ + Δ' × Γ ≃ Γ' + Θ')
+-assoc-r split-e split-e = [] , split-e , split-e
+-assoc-r (split-l p) q with +-assoc-r p q
... | _ , p' , q' = _ , split-l p' , split-l q'
+-assoc-r (split-r p) (split-l q) with +-assoc-r p q
... | _ , p' , q' = _ , split-r p' , split-l q'
+-assoc-r (split-r p) (split-r q) with +-assoc-r p q
... | _ , p' , q' = _ , p' , split-r q'

+-assoc-l :
  ∀{Γ Δ Θ Δ' Θ'} -> Γ ≃ Δ + Θ -> Δ ≃ Δ' + Θ' -> ∃[ Γ' ] (Γ' ≃ Θ' + Θ × Γ ≃ Δ' + Γ')
+-assoc-l p q with +-assoc-r (+-comm p) (+-comm q)
... | Δ , r , p' = Δ , +-comm r , +-comm p'

+-unit-l : ∀{Γ} -> Γ ≃ [] + Γ
+-unit-l {[]} = split-e
+-unit-l {_ :: _} = split-r +-unit-l

+-unit-r : ∀{Γ} -> Γ ≃ Γ + []
+-unit-r = +-comm +-unit-l

+-empty-l : ∀{Γ Δ} -> Γ ≃ [] + Δ -> Γ ≡ Δ
+-empty-l split-e = refl
+-empty-l (split-r p) = Eq.cong (_ ::_) (+-empty-l p)

+-sing-l : ∀{A B Γ} -> [ A ] ≃ [ B ] + Γ -> A ≡ B × Γ ≡ []
+-sing-l (split-l split-e) = refl , refl

#cons : ∀{A Γ Δ} -> Γ ≃ [ A ] + Δ -> (A :: Δ) # Γ
#cons (split-l p) with +-empty-l p
... | refl = #refl
#cons (split-r p) with #cons p
... | π = #tran #here (#next π)

#split : ∀{Γ Γ₁ Γ₂ Δ} -> Γ # Δ -> Γ ≃ Γ₁ + Γ₂ -> ∃[ Δ₁ ] ∃[ Δ₂ ] (Δ ≃ Δ₁ + Δ₂ × Γ₁ # Δ₁ × Γ₂ # Δ₂)
#split #refl p = _ , _ , p , #refl , #refl
#split (#tran π π') p with #split π p
... | Θ₁ , Θ₂ , p' , π₁ , π₂ with #split π' p'
... | Δ₁ , Δ₂ , q , π₁' , π₂' = Δ₁ , Δ₂ , q , #tran π₁ π₁' , #tran π₂ π₂'
#split (#next π) (split-l p) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂  = _ :: Δ₁ , Δ₂ , split-l q , #next π₁ , π₂
#split (#next π) (split-r p) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = Δ₁ , _ :: Δ₂ , split-r q , π₁ , #next π₂
#split #here (split-l (split-l p)) = _ , _ , split-l (split-l p) , #here , #refl
#split #here (split-l (split-r p)) = _ , _ , split-r (split-l p) , #refl , #refl
#split #here (split-r (split-l p)) = _ , _ , split-l (split-r p) , #refl , #refl
#split #here (split-r (split-r p)) = _ , _ , split-r (split-r p) , #refl , #here

#one+ : ∀{A Γ Γ' Δ} ->
        Γ # Δ -> Γ ≃ [ A ] + Γ' -> ∃[ Δ' ] ((Δ ≃ [ A ] + Δ') × (Γ' # Δ'))
#one+ π p with #split π p
... | Θ , Δ' , q , π₁ , π₂ rewrite #one π₁ = Δ' , q , π₂
