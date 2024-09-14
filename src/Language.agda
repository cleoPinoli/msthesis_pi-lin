
open import Data.Nat using (ℕ; zero; suc; _+_)
import Data.Nat.Properties as NatProp
open import Data.Product using (_×_)
open import Data.Sum
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

open import Relation.Nullary using (¬_)

data Type : Set where
  Zero One Bot Top : Type
  _&_ _⊕_ : Type -> Type -> Type

data Dual : Type -> Type -> Set where
  dual-zero-top : Dual Zero Top
  dual-top-zero : Dual Top Zero
  dual-one-bot  : Dual One Bot
  dual-bot-one  : Dual Bot One
  dual-with-plus : ∀{t s t' s'} -> Dual t t' -> Dual s s' -> Dual (t & s) (t' ⊕ s')
  dual-plus-with : ∀{t s t' s'} -> Dual t t' -> Dual s s' -> Dual (t ⊕ s) (t' & s')

dual-symm : ∀{A B} -> Dual A B -> Dual B A
dual-symm dual-zero-top = dual-top-zero
dual-symm dual-top-zero = dual-zero-top
dual-symm dual-one-bot = dual-bot-one
dual-symm dual-bot-one = dual-one-bot
dual-symm (dual-with-plus p q) = dual-plus-with (dual-symm p) (dual-symm q)
dual-symm (dual-plus-with p q) = dual-with-plus (dual-symm p) (dual-symm q)

BoolST : Type
BoolST = One ⊕ One

Channel : Set
Channel = ℕ

data Maybe (A : Set) : Set where
  none : Maybe A
  some : A -> Maybe A

data Context : Set where
  [] : Context
  _::_ : (A : Type) (Γ : Context) -> Context

[_] : Type -> Context
[_] = _:: []

_++_ : Context -> Context -> Context
[] ++ Δ = Δ
(mt :: Γ) ++ Δ = mt :: (Γ ++ Δ)

length : Context -> ℕ
length [] = 0
length (_ :: Γ) = suc (length Γ)

data _#_ : Context -> Context -> Set where
  #refl : ∀{Γ} -> Γ # Γ
  #tran : ∀{Γ Δ Θ} -> Γ # Δ -> Δ # Θ -> Γ # Θ
  #push : ∀{Γ Δ A} -> Γ # Δ -> (A :: Γ) # (A :: Δ)
  #swap : ∀{Γ A B} -> (A :: B :: Γ) # (B :: A :: Γ)

infixr 5 _::_ _++_
infix 4 _≃_+_

data Empty : Context -> Set where
  empty-[] : Empty []

data _≃_+_ : Context -> Context -> Context -> Set where
  split-e : [] ≃ [] + []
  split-l : ∀{Γ Γ₁ Γ₂ A} -> Γ ≃ Γ₁ + Γ₂ -> A :: Γ ≃ A :: Γ₁ + Γ₂
  split-r : ∀{Γ Γ₁ Γ₂ A} -> Γ ≃ Γ₁ + Γ₂ -> A :: Γ ≃ Γ₁ + A :: Γ₂

data Process : Context -> Set where
   close : Process [ One ]
   fail  : ∀{Γ Δ}
           (p : Γ ≃ [ Top ] + Δ)
           -> Process Γ
   wait  : ∀{Γ Δ}
           (p : Γ ≃ [ Bot ] + Δ)
           -> Process Δ
           -> Process Γ
   left  : ∀{Γ Δ A B}
           (p : Γ ≃ [ A ⊕ B ] + Δ)
           -> Process (A :: Δ)
           -> Process Γ
   right : ∀{Γ Δ A B}
           (p : Γ ≃ [ A ⊕ B ] + Δ)
           -> Process (B :: Δ)
           -> Process Γ
   case_ : ∀{Γ Δ A B}
           (p : Γ ≃ [ A & B ] + Δ)
           -> Process (A :: Δ)
           -> Process (B :: Δ)
           -> Process Γ
   cut   : ∀{Γ Γ₁ Γ₂ A B}
           (d : Dual A B)
           (p : Γ ≃ Γ₁ + Γ₂)
           -> Process (A :: Γ₁)
           -> Process (B :: Γ₂)
           -> Process Γ

+-comm : ∀{Γ Γ₁ Γ₂} -> Γ ≃ Γ₁ + Γ₂ -> Γ ≃ Γ₂ + Γ₁
+-comm split-e = split-e
+-comm (split-l p) = split-r (+-comm p)
+-comm (split-r p) = split-l (+-comm p)

+-assoc-r : ∀{Γ Γ₁ Γ₂ Δ₁ Δ₂} -> Γ ≃ Γ₁ + Γ₂ -> Γ₂ ≃ Δ₁ + Δ₂ ->
            ∃[ Δ ] (Δ ≃ Γ₁ + Δ₁) × (Γ ≃ Δ + Δ₂)
+-assoc-r split-e split-e = [] , split-e , split-e
+-assoc-r (split-l p) q = {!!}
+-assoc-r (split-r p) q = {!!}

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

#+ : ∀{Γ Γ₁ Γ₂ Δ} -> Γ # Δ -> Γ ≃ Γ₁ + Γ₂ -> ∃[ Δ₁ ] ∃[ Δ₂ ] (Δ ≃ Δ₁ + Δ₂ × Γ₁ # Δ₁ × Γ₂ # Δ₂)
#+ #refl p = _ , _ , p , #refl , #refl
#+ (#tran π π') p with #+ π p
... | Θ₁ , Θ₂ , p' , π₁ , π₂ with #+ π' p'
... | Δ₁ , Δ₂ , q , π₁' , π₂' = Δ₁ , Δ₂ , q , #tran π₁ π₁' , #tran π₂ π₂'
#+ (#push π) (split-l p) with #+ π p
... | Δ₁ , Δ₂ , q , π₁ , π₂  = _ :: Δ₁ , Δ₂ , split-l q , #push π₁ , π₂
#+ (#push π) (split-r p) with #+ π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = Δ₁ , _ :: Δ₂ , split-r q , π₁ , #push π₂
#+ #swap (split-l (split-l p)) = _ , _ , split-l (split-l p) , #swap , #refl
#+ #swap (split-l (split-r p)) = _ , _ , split-r (split-l p) , #refl , #refl
#+ #swap (split-r (split-l p)) = _ , _ , split-l (split-r p) , #refl , #refl
#+ #swap (split-r (split-r p)) = _ , _ , split-r (split-r p) , #refl , #swap

#empty : ∀{Γ} -> [] # Γ -> Γ ≡ []
#empty #refl = refl
#empty (#tran π π') rewrite #empty π | #empty π' = refl

#singleton : ∀{Γ A} -> [ A ] # Γ -> Γ ≡ [ A ]
#singleton #refl = refl
#singleton (#tran π π') rewrite #singleton π | #singleton π' = refl
#singleton (#push π) rewrite #empty π = refl

#singleton+ : ∀{Γ Γ' Δ A} -> Γ # Δ -> Γ ≃ [ A ] + Γ' -> ∃[ Δ' ] (Δ ≃ [ A ] + Δ' × Γ' # Δ')
#singleton+ π p with #+ π p
... | Θ , Δ' , q , π₁ , π₂ rewrite #singleton π₁ = Δ' , q , π₂

#process : ∀{Γ Δ} -> Γ # Δ -> Process Γ -> Process Δ
#process π close rewrite #singleton π = close
#process π (fail p) with #singleton+ π p
... | Δ' , q , π' = fail q
#process π (wait p P) with #singleton+ π p
... | Δ' , q , π' = wait q (#process π' P)
#process π (left p P) = {!!}
#process π (right p P) = {!!}
#process π ((case p) P Q) = {!!}
#process π (cut d p P Q) with #+ π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = cut d q (#process (#push π₁) P) (#process (#push π₂) Q)

data _⊒_ {Γ} : Process Γ -> Process Γ -> Set where
  s-comm : ∀{Γ₁ Γ₂ A B P Q} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
           -> cut d p P Q ⊒ cut (dual-symm d) (+-comm p) Q P

  s-assoc-r : ∀{Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B B'}
              {P : Process (A :: Γ₁)}
              {Q : Process (B :: A' :: Δ₁)}
              {R : Process (B' :: Δ₂)}
              (d : Dual A A') (e : Dual B B')
              (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₂ ≃ Δ₁ + Δ₂)
              (p' : Δ ≃ Γ₁ + Δ₁) (q' : Γ ≃ Δ + Δ₂) ->
              cut d p P (cut e (split-l q) Q R) ⊒ cut e q' (cut d (split-r p') P (#process #swap Q)) R

  s-fail : ∀{Γ₁ Γ₂ Δ A B P} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ Top ] + Δ) ->
           let _ , _ , q' = +-assoc-l p q in
           cut d p (fail (split-r q)) P ⊒ fail q'

  s-refl : {P : Process Γ} -> P ⊒ P
  s-tran : {P Q R : Process Γ} -> P ⊒ Q -> Q ⊒ R -> P ⊒ R
  s-cong : ∀{Γ₁ Γ₂ A A'}
           {P Q : Process (A :: Γ₁)}
           {R : Process (A' :: Γ₂)}
           (d : Dual A A')
           (p : Γ ≃ Γ₁ + Γ₂) ->
           P ⊒ Q -> cut d p P R ⊒ cut d p Q R

s-assoc-l : ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B B'}
            {P : Process (B :: Δ₁)}
            {Q : Process (B' :: A :: Δ₂)}
            {R : Process (A' :: Γ₂)}
            (d : Dual A A') (e : Dual B B')
            (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ Δ₁ + Δ₂)
            (p' : Δ ≃ Δ₂ + Γ₂) (q' : Γ ≃ Δ₁ + Δ) ->
            cut d p (cut e (split-r q) P Q) R ⊒ cut (dual-symm (dual-symm e)) (+-comm (+-comm q')) P (cut (dual-symm (dual-symm d)) (split-l (+-comm (+-comm p'))) (#process #swap Q) R)
s-assoc-l d e p q p' q' =
  s-tran (s-cong d p (s-comm e (split-r q)))
  (s-tran (s-comm d p)
  (s-tran (s-assoc-r (dual-symm d) (dual-symm e) (+-comm p) (+-comm q) (+-comm p') (+-comm q'))
  (s-tran (s-cong (dual-symm e) (+-comm q') (s-comm (dual-symm d) (split-r (+-comm p'))))
  (s-comm (dual-symm e) (+-comm q')))))
