module List where

open import Data.Nat using (ℕ; zero; suc; _+_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Product using (_×_; Σ; _,_; ∃; Σ-syntax; ∃-syntax)

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

infix 4 _≃_+_

data _≃_+_ {A} : List A -> List A -> List A -> Set where
  split-e : [] ≃ [] + []
  split-l : ∀{x xs ys zs} -> xs ≃ ys + zs -> x :: xs ≃ x :: ys + zs
  split-r : ∀{x xs ys zs} -> xs ≃ ys + zs -> x :: xs ≃ ys + x :: zs

+-comm : ∀{A}{xs ys zs : List A} -> xs ≃ ys + zs -> xs ≃ zs + ys
+-comm split-e = split-e
+-comm (split-l p) = split-r (+-comm p)
+-comm (split-r p) = split-l (+-comm p)

+-assoc-r :
  ∀{A}{xs ys zs us vs : List A} ->
  xs ≃ ys + zs ->
  zs ≃ us + vs ->
  ∃[ ws ] (ws ≃ ys + us) × (xs ≃ ws + vs)
+-assoc-r split-e split-e = [] , split-e , split-e
+-assoc-r (split-l p) q with +-assoc-r p q
... | _ , p' , q' = _ , split-l p' , split-l q'
+-assoc-r (split-r p) (split-l q) with +-assoc-r p q
... | _ , p' , q' = _ , split-r p' , split-l q'
+-assoc-r (split-r p) (split-r q) with +-assoc-r p q
... | _ , p' , q' = _ , p' , split-r q'

+-assoc-l :
  ∀{A}{xs ys zs us vs : List A} ->
  xs ≃ ys + zs ->
  ys ≃ us + vs ->
  ∃[ ws ] (ws ≃ vs + zs) × (xs ≃ us + ws)
+-assoc-l p q with +-assoc-r (+-comm p) (+-comm q)
... | Δ , r , p' = Δ , +-comm r , +-comm p'

+-unit-l : ∀{A}{xs : List A} -> xs ≃ [] + xs
+-unit-l {_} {[]} = split-e
+-unit-l {_} {_ :: _} = split-r +-unit-l

+-unit-r : ∀{A}{xs : List A} -> xs ≃ xs + []
+-unit-r = +-comm +-unit-l

+-empty-l : ∀{A}{xs ys : List A} -> xs ≃ [] + ys -> xs ≡ ys
+-empty-l split-e = refl
+-empty-l (split-r p) = Eq.cong (_ ::_) (+-empty-l p)

+-sing-l :
  ∀{A}{x y}{xs : List A} ->
  [ x ] ≃ [ y ] + xs ->
  x ≡ y × xs ≡ []
+-sing-l (split-l split-e) = refl , refl

#cons : ∀{A}{x : A}{xs ys} -> xs ≃ [ x ] + ys -> (x :: ys) # xs
#cons (split-l p) with +-empty-l p
... | refl = #refl
#cons (split-r p) with #cons p
... | π = #tran #here (#next π)

#split : ∀{A}{xs xs₁ xs₂ ys : List A} -> xs # ys -> xs ≃ xs₁ + xs₂ -> ∃[ ys₁ ] ∃[ ys₂ ] (ys ≃ ys₁ + ys₂ × xs₁ # ys₁ × xs₂ # ys₂)
#split #refl p = _ , _ , p , #refl , #refl
#split (#tran π π') p with #split π p
... | zs₁ , zs₂ , p' , π₁ , π₂ with #split π' p'
... | ys₁ , ys₂ , q , π₁' , π₂' = ys₁ , ys₂ , q , #tran π₁ π₁' , #tran π₂ π₂'
#split (#next π) (split-l p) with #split π p
... | ys₁ , ys₂ , q , π₁ , π₂  = _ :: ys₁ , ys₂ , split-l q , #next π₁ , π₂
#split (#next π) (split-r p) with #split π p
... | ys₁ , ys₂ , q , π₁ , π₂ = ys₁ , _ :: ys₂ , split-r q , π₁ , #next π₂
#split #here (split-l (split-l p)) = _ , _ , split-l (split-l p) , #here , #refl
#split #here (split-l (split-r p)) = _ , _ , split-r (split-l p) , #refl , #refl
#split #here (split-r (split-l p)) = _ , _ , split-l (split-r p) , #refl , #refl
#split #here (split-r (split-r p)) = _ , _ , split-r (split-r p) , #refl , #here

#one+ : ∀{A}{x : A}{xs xs' ys : List A} ->
        xs # ys -> xs ≃ [ x ] + xs' -> ∃[ ys' ] (ys ≃ [ x ] + ys' × xs' # ys')
#one+ π p with #split π p
... | zs , ys' , q , π₁ , π₂ rewrite #one π₁ = ys' , q , π₂
