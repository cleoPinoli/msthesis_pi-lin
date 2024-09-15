
open import Data.Bool using (Bool; if_then_else_)
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

data Context : Set where
  [] : Context
  _::_ : (A : Type) (Γ : Context) -> Context

[_] : Type -> Context
[_] = _:: []

length : Context -> ℕ
length [] = 0
length (_ :: Γ) = suc (length Γ)

data _#_ : Context -> Context -> Set where
  #refl : ∀{Γ} -> Γ # Γ
  #tran : ∀{Γ Δ Θ} -> Γ # Δ -> Δ # Θ -> Γ # Θ
  #next : ∀{Γ Δ A} -> Γ # Δ -> (A :: Γ) # (A :: Δ)
  #here : ∀{Γ A B} -> (A :: B :: Γ) # (B :: A :: Γ)

infixr 5 _::_
infix 4 _≃_+_

data Empty : Context -> Set where
  empty-[] : Empty []

data _≃_+_ : Context -> Context -> Context -> Set where
  split-e : [] ≃ [] + []
  split-l : ∀{Γ Γ₁ Γ₂ A} -> Γ ≃ Γ₁ + Γ₂ -> A :: Γ ≃ A :: Γ₁ + Γ₂
  split-r : ∀{Γ Γ₁ Γ₂ A} -> Γ ≃ Γ₁ + Γ₂ -> A :: Γ ≃ Γ₁ + A :: Γ₂

data Process (Γ : Context) : Set where
   Close : Γ ≃ [ One ] + [] -> Process Γ
   Link  : ∀{A B}
           (d : Dual A B)
           (p : Γ ≃ [ A ] + [ B ])
           -> Process Γ
   Fail  : ∀{Δ}
           (p : Γ ≃ [ Top ] + Δ)
           -> Process Γ
   Wait  : ∀{Δ}
           (p : Γ ≃ [ Bot ] + Δ)
           -> Process Δ
           -> Process Γ
   Select : ∀{Δ A B}
            (x : Bool)
            (p : Γ ≃ [ A ⊕ B ] + Δ)
            -> Process ((if x then A else B) :: Δ)
            -> Process Γ
   Case  : ∀{Δ A B}
           (p : Γ ≃ [ A & B ] + Δ)
           -> Process (A :: Δ)
           -> Process (B :: Δ)
           -> Process Γ
   Cut   : ∀{Γ₁ Γ₂ A B}
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

#nil : ∀{Γ} -> [] # Γ -> Γ ≡ []
#nil #refl = refl
#nil (#tran π π') rewrite #nil π | #nil π' = refl

#one : ∀{Γ A} -> [ A ] # Γ -> Γ ≡ [ A ]
#one #refl = refl
#one (#tran π π') rewrite #one π | #one π' = refl
#one (#next π) rewrite #nil π = refl

#one+ : ∀{Γ Γ' Δ A} -> Γ # Δ -> Γ ≃ [ A ] + Γ' -> ∃[ Δ' ] (Δ ≃ [ A ] + Δ' × Γ' # Δ')
#one+ π p with #split π p
... | Θ , Δ' , q , π₁ , π₂ rewrite #one π₁ = Δ' , q , π₂

#process : ∀{Γ Δ} -> Γ # Δ -> Process Γ -> Process Δ
#process π (Link d p) with #one+ π p
... | Δ' , q , π' with #one π'
... | refl = Link d q
#process π (Close p) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ with #one π₁ | #nil π₂
... | refl | refl = Close q
#process π (Fail p) with #one+ π p
... | Δ' , q , π' = Fail q
#process π (Wait p P) with #one+ π p
... | Δ' , q , π' = Wait q (#process π' P)
#process π (Select x p P) = {!!}
#process π (Case p P Q) = {!!}
#process π (Cut d p P Q) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = Cut d q (#process (#next π₁) P) (#process (#next π₂) Q)

data _⊒_ : ∀{Γ} -> Process Γ -> Process Γ -> Set where
  s-comm : ∀{Γ Γ₁ Γ₂ A B P Q} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
           -> Cut d p P Q ⊒ Cut (dual-symm d) (+-comm p) Q P

  s-assoc-r : ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B B'}
              {P : Process (A :: Γ₁)}
              {Q : Process (B :: A' :: Δ₁)}
              {R : Process (B' :: Δ₂)}
              (d : Dual A A') (e : Dual B B')
              (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₂ ≃ Δ₁ + Δ₂)
              (p' : Δ ≃ Γ₁ + Δ₁) (q' : Γ ≃ Δ + Δ₂) ->
              Cut d p P (Cut e (split-l q) Q R) ⊒ Cut e q' (Cut d (split-r p') P (#process #here Q)) R

  s-link : ∀{Γ A B}
           (d : Dual A B)
           (p : Γ ≃ [ A ] + [ B ]) ->
           Link d p ⊒ Link (dual-symm d) (+-comm p)

  s-fail : ∀{Γ Γ₁ Γ₂ Δ A B P} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ Top ] + Δ) ->
           let _ , _ , q' = +-assoc-l p q in
           Cut d p (Fail (split-r q)) P ⊒ Fail q'

  s-refl : ∀{Γ} {P : Process Γ} -> P ⊒ P
  s-tran : ∀{Γ} {P Q R : Process Γ} -> P ⊒ Q -> Q ⊒ R -> P ⊒ R
  s-cong : ∀{Γ Γ₁ Γ₂ A A'}
           {P Q : Process (A :: Γ₁)}
           {R : Process (A' :: Γ₂)}
           (d : Dual A A')
           (p : Γ ≃ Γ₁ + Γ₂) ->
           P ⊒ Q -> Cut d p P R ⊒ Cut d p Q R

s-assoc-l : ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B B'}
            {P : Process (B :: Δ₁)}
            {Q : Process (B' :: A :: Δ₂)}
            {R : Process (A' :: Γ₂)}
            (d : Dual A A') (e : Dual B B')
            (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ Δ₁ + Δ₂)
            (p' : Δ ≃ Δ₂ + Γ₂) (q' : Γ ≃ Δ₁ + Δ) ->
            Cut d p (Cut e (split-r q) P Q) R ⊒ Cut (dual-symm (dual-symm e)) (+-comm (+-comm q')) P (Cut (dual-symm (dual-symm d)) (split-l (+-comm (+-comm p'))) (#process #here Q) R)
s-assoc-l d e p q p' q' =
  s-tran (s-cong d p (s-comm e (split-r q)))
  (s-tran (s-comm d p)
  (s-tran (s-assoc-r (dual-symm d) (dual-symm e) (+-comm p) (+-comm q) (+-comm p') (+-comm q'))
  (s-tran (s-cong (dual-symm e) (+-comm q') (s-comm (dual-symm d) (split-r (+-comm p'))))
  (s-comm (dual-symm e) (+-comm q')))))
