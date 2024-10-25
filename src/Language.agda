open import Data.Bool using (Bool; if_then_else_)
open Bool using (true; false)
open import Data.Nat
import Data.Nat.Properties as NatProp
open import Data.Product using (_×_)
open import Data.Sum
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

open import Relation.Nullary using (¬_)

open import List
open import Type
open import Context

data Process (Γ : Context) : Set where
   close : Γ ≃ [ One ] + [] -> Process Γ
   link  : ∀{A B}
           (d : Dual A B)
           (p : Γ ≃ [ A ] + [ B ])
           -> Process Γ
   fail  : ∀{Δ}
           (p : Γ ≃ [ Top ] + Δ)
           -> Process Γ
   wait  : ∀{Δ}
           (p : Γ ≃ [ Bot ] + Δ)
           -> Process Δ
           -> Process Γ
   select : ∀{Δ A B}
            (x : Bool)
            (p : Γ ≃ [ A ⊕ B ] + Δ)
            -> Process ((if x then A else B) :: Δ)
            -> Process Γ
   case  : ∀{Δ A B}
           (p : Γ ≃ [ A & B ] + Δ)
           -> Process (A :: Δ)
           -> Process (B :: Δ)
           -> Process Γ
   -- fork  : ∀{Δ Γ₁ Γ₂ A B}
   --         (p : Γ ≃ [ A ⊗ B ] + Δ)
   --         (q : Δ ≃ Γ₁ + Γ₂)
   --         -> Process (A :: Γ₁)
   --         -> Process (B :: Γ₂)
   --         -> Process Γ
   -- join  : ∀{Δ A B}
   --         (p : Γ ≃ [ A ⅋ B ] + Δ)
   --         -> Process (B :: A :: Δ)
   --         -> Process Γ
   cut   : ∀{Γ₁ Γ₂ A B}
           (d : Dual A B)
           (p : Γ ≃ Γ₁ + Γ₂)
           -> Process (A :: Γ₁)
           -> Process (B :: Γ₂)
           -> Process Γ

#process : ∀{Γ Δ} -> Γ # Δ -> Process Γ -> Process Δ
#process π (link d p) with #one+ π p
... | Δ' , q , π' with #one π'
... | refl = link d q
#process π (close p) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ with #one π₁ | #nil π₂
... | refl | refl = close q
#process π (fail p) with #one+ π p
... | Δ' , q , π' = fail q
#process π (wait p P) with #one+ π p
... | Δ' , q , π' = wait q (#process π' P)
#process π (select x p P) with #one+ π p
... | Δ' , q , π' = select x q (#process (#next π') P)
#process π (case p P Q) with #one+ π p
... | Δ' , q , π' = case q (#process (#next π') P) (#process (#next π') Q)
#process π (cut d p P Q) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = cut d q (#process (#next π₁) P) (#process (#next π₂) Q)

data _⊒_ : ∀{Γ} -> Process Γ -> Process Γ -> Set where
  s-comm : ∀{Γ Γ₁ Γ₂ A B P Q} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
           -> cut d p P Q ⊒ cut (dual-symm d) (+-comm p) Q P

  s-assoc-r : ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B B'}
              {P : Process (A :: Γ₁)}
              {Q : Process (B :: A' :: Δ₁)}
              {R : Process (B' :: Δ₂)}
              (d : Dual A A') (e : Dual B B')
              (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₂ ≃ Δ₁ + Δ₂)
              (p' : Δ ≃ Γ₁ + Δ₁) (q' : Γ ≃ Δ + Δ₂) ->
              cut d p P (cut e (split-l q) Q R) ⊒ cut e q' (cut d (split-r p') P (#process #here Q)) R

  s-link : ∀{Γ A B}
           (d : Dual A B)
           (p : Γ ≃ [ A ] + [ B ]) ->
           link d p ⊒ link (dual-symm d) (+-comm p)

  s-fail : ∀{Γ Γ₁ Γ₂ Δ A B P} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ Top ] + Δ) ->
           let _ , _ , q' = +-assoc-l p q in
           cut d p (fail (split-r q)) P ⊒ fail q'

  s-wait : ∀{Γ Γ₁ Γ₂ Δ A B}
           {P : Process (A :: Δ)}
           {Q : Process (B :: Γ₂)}
           (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ Bot ] + Δ) ->
           let _ , p' , q' = +-assoc-l p q in
           cut d p (wait (split-r q) P) Q ⊒ wait q' (cut d p' P Q)

  -- (x)(case y(z){P|Q} | R) ⊒ case y(z){(x)(P|R), (x)(Q|R)} , x ≠ y,z
  s-case : ∀{Γ A B A₁ A₂ Γ₁ Γ₂ Δ}
         {P : Process (A₁ :: A :: Δ)}
         {Q : Process (A₂ :: A :: Δ)}
         {R : Process (B :: Γ₂)}
         (d : Dual A B)
         (p : Γ ≃ Γ₁ + Γ₂)
         (q : Γ₁ ≃ [ A₁ & A₂ ] + Δ) ->
         let _ , p' , q' = +-assoc-l p q in
         cut d p (case (split-r q) P Q) R ⊒
         case q' (cut d (split-l p') (#process #here P) R)
                 (cut d (split-l p') (#process #here Q) R)

  s-refl : ∀{Γ} {P : Process Γ} -> P ⊒ P
  s-tran : ∀{Γ} {P Q R : Process Γ} -> P ⊒ Q -> Q ⊒ R -> P ⊒ R
  s-cong : ∀{Γ Γ₁ Γ₂ A A'}
           {P Q : Process (A :: Γ₁)}
           {R : Process (A' :: Γ₂)}
           (d : Dual A A')
           (p : Γ ≃ Γ₁ + Γ₂) ->
           P ⊒ Q -> cut d p P R ⊒ cut d p Q R

  s-select-l :
    ∀{Γ Γ₁ Γ₂ Δ A B A₁ A₂}
    {P : Process (A₁ :: A :: Δ)}
    {Q : Process (B :: Γ₂)}
    (d : Dual A B)
    (p : Γ ≃ Γ₁ + Γ₂)
    (q : Γ₁ ≃ [ A₁ ⊕ A₂ ] + Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut d p (select true (split-r q) P) Q ⊒
    select true q' (cut d (split-l p') (#process #here P) Q)

  s-select-r :
    ∀{Γ Γ₁ Γ₂ Δ A B A₁ A₂}
    {P : Process (A₂ :: A :: Δ)}
    {Q : Process (B :: Γ₂)}
    (d : Dual A B)
    (p : Γ ≃ Γ₁ + Γ₂)
    (q : Γ₁ ≃ [ A₁ ⊕ A₂ ] + Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut d p (select false (split-r q) P) Q ⊒
    select false q' (cut d (split-l p') (#process #here P) Q)

s-assoc-l : ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B B'}
            {P : Process (B :: Δ₁)}
            {Q : Process (B' :: A :: Δ₂)}
            {R : Process (A' :: Γ₂)}
            (d : Dual A A') (e : Dual B B')
            (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ Δ₁ + Δ₂)
            (p' : Δ ≃ Δ₂ + Γ₂) (q' : Γ ≃ Δ₁ + Δ) ->
            cut d p (cut e (split-r q) P Q) R ⊒ cut (dual-symm (dual-symm e)) (+-comm (+-comm q')) P (cut (dual-symm (dual-symm d)) (split-l (+-comm (+-comm p'))) (#process #here Q) R)
s-assoc-l d e p q p' q' =
  s-tran (s-cong d p (s-comm e (split-r q)))  (s-tran (s-comm d p)
  (s-tran (s-assoc-r (dual-symm d) (dual-symm e) (+-comm p) (+-comm q) (+-comm p') (+-comm q'))
  (s-tran (s-cong (dual-symm e) (+-comm q') (s-comm (dual-symm d) (split-r (+-comm p'))))
  (s-comm (dual-symm e) (+-comm q')))))

data _~>_ : ∀{Γ} -> Process Γ -> Process Γ -> Set where
  r-link :
    ∀{Γ Δ A B}
    {P : Process (B :: Δ)}
    (d : Dual A B)
    (p : Γ ≃ [ B ] + Δ) ->
    cut d p (link d (split-l (split-r split-e))) P ~> #process (#cons p) P

  r-close :
    ∀{Γ}
    {P : Process Γ} (p : Γ ≃ [] + Γ) (q : Γ ≃ [] + Γ) ->
    cut dual-one-bot p (close (split-l split-e)) (wait (split-l q) P) ~> P

  -- (x)(select true x(y).P | case x(y){Q,R}) ~> (y)(P | Q)

  r-left :
    ∀{Γ Γ₁ Γ₂ A₁ A₂ B₁ B₂}
    {P : Process (A₁ :: Γ₁)}
    {Q : Process (B₁ :: Γ₂)}
    {R : Process (B₂ :: Γ₂)}
    (d₁ : Dual A₁ B₁) (d₂ : Dual A₂ B₂)
    (q₁ : Γ₁ ≃ [] + Γ₁) (q₂ : Γ₂ ≃ [] + Γ₂)
    (p : Γ ≃ Γ₁ + Γ₂)
    ->
    cut (dual-plus-with d₁ d₂) p (select true (split-l q₁) P) (case (split-l q₂) Q R) ~> cut d₁ p P Q

  r-right :
    ∀{Γ Γ₁ Γ₂ A₁ A₂ B₁ B₂}
    {P : Process (A₂ :: Γ₁)}
    {Q : Process (B₁ :: Γ₂)}
    {R : Process (B₂ :: Γ₂)}
    (d₁ : Dual A₁ B₁) (d₂ : Dual A₂ B₂)
    (q₁ : Γ₁ ≃ [] + Γ₁) (q₂ : Γ₂ ≃ [] + Γ₂)
    (p : Γ ≃ Γ₁ + Γ₂)
    ->
    cut (dual-plus-with d₁ d₂) p (select false (split-l q₁) P) (case (split-l q₂) Q R) ~> cut d₂ p P R

  r-cut :
    ∀{Γ Γ₁ Γ₂ A B}
    {P Q : Process (A :: Γ₁)}
    {R : Process (B :: Γ₂)}
    (d : Dual A B)
    (q : Γ ≃ Γ₁ + Γ₂)
    (r : P ~> Q) ->
    cut d q P R ~> cut d q Q R


-- provided that P ⊒ R and R ~> Q then P ~> Q
  r-cong :
    ∀{Γ}
    {P R Q : Process Γ}
    (p : P ⊒ R) (q : R ~> Q) -> P ~> Q

data _=>_ : ∀{Γ} -> Process Γ -> Process Γ -> Set where
  refl : ∀{Γ} {P : Process Γ} -> P => P
  tran : ∀{Γ} {P Q R : Process Γ} -> P ~> R -> R => Q -> P => Q

size : ∀{Γ} -> Process Γ -> ℕ
size (close _) = zero
size (link _ _) = zero
size (fail _ ) = zero
size (wait _ P) = suc (size P)
size (select _ _ P) = suc (size P)
size (case _ P Q) = suc (size P ⊔ size Q) 
size (cut _ _ P Q) = suc (size P + size Q)
-- size (fork _ _ P Q) = suc (size P + size Q)
-- size (join _ P) = suc (size P)

#size : ∀{Γ Δ} (P : Process Γ) (π : Γ # Δ) -> size (#process π P) ≡ size P
#size (close p) π with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ with #one π₁ | #nil π₂
... | refl | refl = refl
#size (link d p) π with #one+ π p
... | Δ' , _ , π' with #one π'
... | refl = refl
#size (fail p) π = refl
#size (wait p P) π with #one+ π p
... | Δ' , q , π' = cong suc (#size P π')
#size (select x p P) π with #one+ π p
... | Δ' , q , π' = cong suc (#size P (#next π'))
#size (case p P Q) π with #one+ π p
... | Δ' , q , π' = cong suc {!!} -- I'd like to make a recursive call like _⊔_ (#size P (#next π')) (#size Q (#next π'))
-- with  #process (#next π') P | #process (#next π') Q -- or convince agda that P' ≡ P and Q' ≡ Q
-- ... | P' | Q' = {!!} 
#size (cut d p P Q) π with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ with #process (#next π₁) P | #process (#next π₂) Q
... | P' | Q'  = cong suc {!!}

-- precongruence preserves process size
size-⊒ : ∀{Γ} {P Q : Process Γ} -> P ⊒ Q -> size Q ≤ size P
size-⊒ {_} {cut _ _ P Q} (s-comm d p)
  rewrite NatProp.+-comm (size P) (size Q) = NatProp.≤-refl
size-⊒ {_} {cut _ _ P (cut _ _ Q R)} (s-assoc-r d e p q p' q') = begin
  suc (suc (size P + size (#process #here Q) + size R))
    ≡⟨ cong suc (cong suc (cong (_+ size R) (cong (size P +_) ((#size Q #here))))) ⟩
  suc ((suc (size P + size Q) + size R))
    ≡⟨ cong suc (cong (_+ size R) (Eq.sym (NatProp.+-suc (size P) (size Q) ))) ⟩
  suc ((size P + suc (size Q) + size R))
    ≡⟨ cong suc ((NatProp.+-assoc (size P) (suc (size Q)) (size R)) ) ⟩
  suc (size P + suc (size Q + size R)) ∎
  where open NatProp.≤-Reasoning
size-⊒ {_} (s-link d p) = NatProp.≤-refl
size-⊒ {_} (s-fail d p q) = z≤n
size-⊒ {_} (s-wait d p q) = NatProp.≤-refl
size-⊒ {_} {cut _ _ (case _ P Q) R} (s-case d p q)
  rewrite #size P #here |
          #size Q #here |
          NatProp.+-distribʳ-⊔ ((size R)) (size P) (size Q) = NatProp.≤-refl
size-⊒ {_} s-refl = NatProp.≤-refl
size-⊒ {_} (s-tran pc₁ pc₂) = NatProp.≤-trans (size-⊒ pc₂) (size-⊒ pc₁)
size-⊒ {_} {cut _ _ P R} (s-cong d p pc) =
  s≤s (NatProp.+-monoˡ-≤ (size R) (size-⊒ pc)) -- I'd like to make a recursive call like: cong ( _+ size R) (size-⊒ pc)
size-⊒ {_} {cut _ _ (select _ _ P) Q}(s-select-l d p q)
  rewrite #size P #here = NatProp.≤-refl
size-⊒ {_} {cut _ _ (select _ _ P) Q} (s-select-r d p q)
  rewrite #size P #here = NatProp.≤-refl

-- redux always decreases process size
size-r : ∀{Γ} {P Q : Process Γ} -> P ~> Q -> size Q < size P
size-r {_} {cut _ _ (link _ _) P} (r-link d p) rewrite #size P (#cons p) = s≤s NatProp.≤-refl
size-r {_} {cut _ _ (close _) (wait _ Q)} (r-close p q) = s≤s (NatProp.n≤1+n (size Q))  
size-r {_} {cut _ _ (select true _ P) (case _ Q R)} (r-left d e p q r) = begin
  suc (suc (size P + size Q)) ≡⟨ cong suc (Eq.sym (NatProp.+-suc (size P) (size Q))) ⟩
  suc (size P + suc (size Q)) <⟨ s≤s (s≤s (NatProp.+-monoʳ-≤ (size P) (s≤s (NatProp.m≤m⊔n (size Q) (size R))))) ⟩
  suc (suc (size P + suc (size Q ⊔ size R))) ∎
  where open NatProp.≤-Reasoning
size-r (r-right d₁ d₂ q₁ q₂ p) = {!!} 
size-r {_} {cut _ _ P R} (r-cut d q red) = s≤s (NatProp.+-monoˡ-≤ (size R) (size-r red)) 
size-r (r-cong p red) = size-r {!!}

-- @@@ pieces I needed for termination @@@
data Thread : ∀{Γ} -> Process Γ -> Set where
  link :
    ∀{Γ A B}
    (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) -> Thread (link d p)
  fail :
    ∀{Γ Δ}
    (p : Γ ≃ [ Top ] + Δ) -> Thread (fail p)
  wait :
    ∀{Γ Δ} (p : Γ ≃ [ Bot ] + Δ) {P : Process Δ} -> Thread (wait p P)
  case :
    ∀{Γ Δ A B} (p : Γ ≃ [ A & B ] + Δ)
    {P : Process (A :: Δ)} {Q : Process (B :: Δ)} -> Thread (case p P Q)
-- close : Thread close overwriting of definition from process?
  select :
    ∀ {Γ Δ A B} (x : Bool) (p : Γ ≃ [ A ⊕ B ] + Δ)
    {P : Process ((if x then A else B) :: Δ)} -> Thread (select x p P)
-- join :
-- fork :

data Cut {Γ} : Process Γ -> Set where
  cut :
    ∀{Γ₁ Γ₂ A B} {P : Process (A :: Γ₁)} {Q : Process (B :: Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) -> Cut (cut d p P Q)
    

Observable : ∀{Γ} -> Process Γ -> Set
Observable P = ∃[ Q ] ((P ⊒ Q) × (Thread Q))

termination : ∀{Γ} (P : Process Γ) -> ∃[ Q ] ((P ~> Q) × (Observable Q))
termination P = {!!}
