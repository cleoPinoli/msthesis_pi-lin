open import Data.Fin using (Fin; suc)
open import Data.Nat using (ℕ; suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)

open import Type
open import Context
open import Permutations

data Process : ∀{n} -> Context n → Set where
   link      : ∀{n} {Γ : Context n} {A B : Type n} (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) → Process Γ
   fail      : ∀{n} {Γ Δ : Context n} (p : Γ ≃ ⊤ , Δ) → Process Γ
   close     : ∀{n} -> Process {n} [ 𝟙 ]
   wait      : ∀{n} {Γ Δ : Context n} (p : Γ ≃ ⊥ , Δ) → Process Δ → Process Γ
   select    : ∀{n} {A B : Type n} {Γ Δ} (x : Bool) (p : Γ ≃ A ⊕ B , Δ) →
               Process ((if x then A else B) ∷ Δ) → Process Γ
   case      : ∀{n} {A B : Type n} {Γ Δ} (p : Γ ≃ A & B , Δ) →
               Process (A ∷ Δ) → Process (B ∷ Δ) → Process Γ
   fork      : ∀{n} {A B : Type n} {Γ Δ Γ₁ Γ₂} (p : Γ ≃ A ⊗ B , Δ) (q : Δ ≃ Γ₁ + Γ₂) →
               Process (A ∷ Γ₁) → Process (B ∷ Γ₂) → Process Γ
   join      : ∀{n} {A B : Type n} {Γ Δ} (p : Γ ≃ A ⅋ B , Δ) →
               Process (B ∷ A ∷ Δ) → Process Γ
   server    : ∀{n} {A : Type n} {Γ Δ} (p : Γ ≃ ¡ A , Δ) (un : Un Δ) →
               Process (A ∷ Δ) → Process Γ
   client    : ∀{n} {A : Type n} {Γ Δ} (p : Γ ≃ ¿ A , Δ) → Process (A ∷ Δ) → Process Γ
   weaken    : ∀{n} {A : Type n} {Γ Δ} (p : Γ ≃ ¿ A , Δ) → Process Δ → Process Γ
   contract  : ∀{n} {A : Type n} {Γ Δ} (p : Γ ≃ ¿ A , Δ) → Process (¿ A ∷ ¿ A ∷ Δ) → Process Γ
   ex        : ∀{n} {A : Type (suc n)} {B C : Type n} {Γ Δ} (p : Γ ≃ $∃ A , Δ) ->
               Subst (make-subst C) A B -> Process (B ∷ Δ) -> Process Γ
   all       : ∀{n} {A : Type (suc n)} {Γ Δ : Context n} (p : Γ ≃ $∀ A , Δ) ->
               ({B C : Type n} -> Subst (make-subst C) A B -> Process (B ∷ Δ)) -> Process Γ
   cut       : ∀{n} {A B : Type n} {Γ Γ₁ Γ₂} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) →
               Process (A ∷ Γ₁) → Process (B ∷ Γ₂) → Process Γ

#process : ∀{n} {Γ Δ : Context n} → Γ # Δ → Process Γ → Process Δ
#process π (link d p) with #one+ π p
... | Δ′ , q , π′ with #singleton-inv π′
... | refl = link d q
#process π close with #singleton-inv π
... | refl = close
#process π (fail p) with #one+ π p
... | Δ′ , q , π′ = fail q
#process π (wait p P) with #one+ π p
... | Δ′ , q , π′ = wait q (#process π′ P)
#process π (select x p P) with #one+ π p
... | Δ′ , q , π′ = select x q (#process (#next π′) P)
#process π (case p P Q) with #one+ π p
... | Δ′ , q , π′ = case q (#process (#next π′) P) (#process (#next π′) Q)
#process π (fork p q P Q) with #one+ π p
... | Δ′ , p′ , π′ with #split π′ q
... | Δ₁ , Δ₂ , q′ , π₁ , π₂ = fork p′ q′ (#process (#next π₁) P) (#process (#next π₂) Q)
#process π (join p P) with #one+ π p
... | Δ′ , q , π′ = join q (#process (#next (#next π′)) P)
#process π (cut d p P Q) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = cut d q (#process (#next π₁) P) (#process (#next π₂) Q)
#process π (server p un P) with #one+ π p
... | Δ′ , q , π′ = server q (#un π′ un) (#process (#next π′) P)
#process π (client p P) with #one+ π p
... | Δ′ , q , π′ = client q (#process (#next π′) P)
#process π (weaken p P) with #one+ π p
... | Δ′ , q , π′ = weaken q (#process π′ P)
#process π (contract p P) with #one+ π p
... | Δ′ , q , π′ = contract q (#process (#next (#next π′)) P)
#process π (all p P) with #one+ π p
... | Δ' , q , π' = all q λ B → #process (#next π') (P B)
#process π (ex p σ P) with #one+ π p
... | Δ' , q , π' = ex q σ (#process (#next π') P)
