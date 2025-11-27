open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)

open import Type
open import Context
open import Permutations
open import Process

data _⊒_ {n} : ∀{Γ : Context n} → Process Γ → Process Γ → Set where
  s-comm :
    ∀{A B Γ Γ₁ Γ₂ P Q} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) →
    cut d p P Q ⊒ cut (dual-symm d) (+-comm p) Q P
  s-link :
    ∀{Γ A B}
    (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) →
    link d p ⊒ link (dual-symm d) (+-comm p)
  s-fail :
    ∀{Γ Γ₁ Γ₂ Δ A B P} (d : Dual A B)
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ ⊤ , Δ) →
    let _ , _ , q′ = +-assoc-l p q in
    cut d p (fail (split-r q)) P ⊒ fail q′
  s-wait :
    ∀{Γ Γ₁ Γ₂ Δ A B} {P : Process (A ∷ Δ)} {Q : Process (B ∷ Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ ⊥ , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut d p (wait (split-r q) P) Q ⊒ wait q′ (cut d p′ P Q)
  s-select-l :
    ∀{Γ Γ₁ Γ₂ Δ A B C D} {P : Process (C ∷ A ∷ Δ)} {Q : Process (B ∷ Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ C ⊕ D , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut d p (select true (split-r q) P) Q ⊒
    select true q′ (cut d (split-l p′) (#process #here P) Q)
  s-select-r :
    ∀{Γ Γ₁ Γ₂ Δ A B C D}
    {P : Process (D ∷ A ∷ Δ)}
    {Q : Process (B ∷ Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ C ⊕ D , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut d p (select false (split-r q) P) Q ⊒
    select false q′ (cut d (split-l p′) (#process #here P) Q)
  s-case :
    ∀{Γ A B A₁ A₂ Γ₁ Γ₂ Δ}
    {P : Process (A₁ ∷ A ∷ Δ)}
    {Q : Process (A₂ ∷ A ∷ Δ)}
    {R : Process (B ∷ Γ₂)}
    (d : Dual A B)
    (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ A₁ & A₂ , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut d p (case (split-r q) P Q) R ⊒
    case q′ (cut d (split-l p′) (#process #here P) R)
            (cut d (split-l p′) (#process #here Q) R)
  s-fork-l :
    ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A B C D}
    {P : Process (C ∷ A ∷ Δ₁)} {Q : Process (D ∷ Δ₂)} {R : Process (B ∷ Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ C ⊗ D , Δ) (r : Δ ≃ Δ₁ + Δ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    let _ , p′′ , r′ = +-assoc-l p′ r in
    let _ , q′′ , r′′ = +-assoc-r r′ (+-comm p′′) in
    cut d p (fork (split-r q) (split-l r) P Q) R ⊒
    fork q′ r′′ (cut d (split-l q′′) (#process #here P) R) Q
  s-fork-r :
    ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A B C D}
    {P : Process (C ∷ Δ₁)}
    {Q : Process (D ∷ A ∷ Δ₂)}
    {R : Process (B ∷ Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ C ⊗ D , Δ)
    (r : Δ ≃ Δ₁ + Δ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    let _ , p′′ , r′ = +-assoc-l p′ r in
    cut d p (fork (split-r q) (split-r r) P Q) R ⊒
    fork q′ r′ P (cut d (split-l p′′) (#process #here Q) R)
  s-join :
    ∀{Γ Γ₁ Γ₂ Δ A B C D}
    {P : Process (D ∷ C ∷ A ∷ Δ)}
    {Q : Process (B ∷ Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ C ⅋ D , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut d p (join (split-r q) P) Q ⊒
    join q′ (cut d (split-l (split-l p′)) (#process #rot P) Q)
  s-server :
    ∀{Γ A B C Γ₁ Γ₂ Δ₁}
    {P : Process (C ∷ ¿ A ∷ Δ₁)}
    {Q : Process (B ∷ Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ ¡ C , Δ₁) (r : Γ₂ ≃ [] + Γ₂)
    (un₁ : Un Δ₁) (un₂ : Un Γ₂) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut (d-?-! d) p (server (split-r q) (un-∷ un₁) P) (server (split-l r) un₂ Q) ⊒
    server q′ (#un+ p′ un₁ un₂) (cut (d-?-! d) (split-l p′) (#process #here P) (server (split-l r) un₂ Q))
  s-client :
    ∀{Γ A B C Γ₁ Γ₂ Δ}
    {P : Process (C ∷ A ∷ Δ)}
    {Q : Process (B ∷ Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ ¿ C , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut d p (client (split-r q) P) Q ⊒
    client q′ (cut d (split-l p′) (#process #here P) Q)
  s-weaken :
    ∀{Γ A B C Γ₁ Γ₂ Δ}
    {P : Process (A ∷ Δ)}
    {Q : Process (B ∷ Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ ¿ C , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut d p (weaken (split-r q) P) Q ⊒
    weaken q′ (cut d p′ P Q)
  s-contract :
    ∀{Γ A B C Γ₁ Γ₂ Δ}
    {P : Process (¿ C ∷ ¿ C ∷ A ∷ Δ)}
    {Q : Process (B ∷ Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ ¿ C , Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut d p (contract (split-r q) P) Q ⊒
    contract q′ (cut d (split-l (split-l p′)) (#process #rot P) Q)
  s-ex :
    ∀{Γ A B C D E Γ₁ Γ₂ Δ}
    {σ : Subst (make-subst D) C E}
    {P : Process (E ∷ A ∷ Δ)}
    {Q : Process (B ∷ Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ $∃ C , Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut d p (ex (split-r q) σ P) Q ⊒
    ex q' σ (cut d (split-l p') (#process #here P) Q)
  s-all :
    ∀{Γ A B C Γ₁ Γ₂ Δ}
    {F : {D E : Type n} -> Subst (make-subst D) C E -> Process (E ∷ A ∷ Δ)}
    {Q : Process (B ∷ Γ₂)}
    (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ $∀ C , Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut d p (all (split-r q) F) Q ⊒
    all q' λ σ → cut d (split-l p') (#process #here (F σ)) Q

  s-refl  : ∀{Γ} {P : Process Γ} → P ⊒ P
  s-tran  : ∀{Γ} {P Q R : Process Γ} → P ⊒ Q → Q ⊒ R → P ⊒ R
  s-cong  : ∀{Γ Γ₁ Γ₂ A B} {P Q : Process (A ∷ Γ₁)} {P′ Q′ : Process (B ∷ Γ₂)}
            (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) → P ⊒ Q → P′ ⊒ Q′ →
            cut d p P P′ ⊒ cut d p Q Q′
