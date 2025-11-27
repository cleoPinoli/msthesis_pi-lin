open import Data.Fin using (Fin; suc)
open import Data.Nat using (suc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_; ∃; Σ; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)
open import Data.List.Properties using (++-assoc)

open import Type
open import Context
open import Permutations
open import Process
open import Congruence

weakening : ∀{n} {Γ Γ₁ Γ₂ : Context n} (un : Un Γ₁) → Γ ≃ Γ₁ + Γ₂ → Process Γ₂ → Process Γ
weakening un p P = #process (+++# p) (aux un P)
  where
    aux : ∀{Γ₁ Γ₂} (un : Un Γ₁) → Process Γ₂ → Process (Γ₁ ++ Γ₂)
    aux un-[] P = P
    aux (un-∷ un) P = weaken (split-l +-unit-l) (aux un P)

contraction : ∀{n} {Γ Γ₁ Γ₂ : Context n} (un : Un Γ₁) → Γ ≃ Γ₁ + Γ₂ → Process (Γ₁ ++ Γ) → Process Γ
contraction un p P = #process (+++# p) (aux un (#process (#left (#sym (+++# p))) P))
  where
    aux : ∀{Γ₁ Γ₂} → Un Γ₁ → Process (Γ₁ ++ Γ₁ ++ Γ₂) → Process (Γ₁ ++ Γ₂)
    aux un-[] P = P
    aux {¿ A ∷ Γ₁} {Γ₂} (un-∷ un) P with contract (split-l +-unit-l) (#process (#shift {_} {¿ A} {¿ A ∷ Γ₁} {Γ₁ ++ Γ₂}) P)
    ... | P₁ rewrite sym (++-assoc (¿ A ∷ Γ₁) Γ₁ Γ₂) with #process (#sym (#shift {_} {¿ A} {Γ₁ ++ Γ₁})) P₁
    ... | P₂ rewrite ++-assoc Γ₁ Γ₁ (¿ A ∷ Γ₂) with aux un P₂
    ... | P₃ = #process #shift P₃

dual-subst : ∀{m n} {A A' : Type m} {B : Type n} {σ : Fin m -> Type n} -> Dual A A' -> Subst σ A B -> ∃[ B' ] Dual B B' × Subst σ A' B'
dual-subst d-𝟘-⊤ s-𝟘 = ⊤ , d-𝟘-⊤ , s-⊤
dual-subst d-𝟙-⊥ s-𝟙 = ⊥ , d-𝟙-⊥ , s-⊥
dual-subst d-⊥-𝟙 s-⊥ = 𝟙 , d-⊥-𝟙 , s-𝟙
dual-subst d-⊤-𝟘 s-⊤ = 𝟘 , d-⊤-𝟘 , s-𝟘
dual-subst (d-!-? d) (s-! s) with dual-subst d s
... | B' , d' , s' = ¿ B' , d-!-? d' , s-? s'
dual-subst (d-?-! d) (s-? s) with dual-subst d s
... | B' , d' , s' = ¡ B' , d-?-! d' , s-! s'
dual-subst (d-&-⊕ d e) (s-& s t) with dual-subst d s | dual-subst e t
... | B' , d' , s' | C' , e' , t' = (B' ⊕ C') , d-&-⊕ d' e' , s-⊕ s' t'
dual-subst (d-⊕-& d e) (s-⊕ s t) with dual-subst d s | dual-subst e t
... | B' , d' , s' | C' , e' , t' = (B' & C') , d-⊕-& d' e' , s-& s' t'
dual-subst (d-⊗-⅋ d e) (s-⊗ s t) with dual-subst d s | dual-subst e t
... | B' , d' , s' | C' , e' , t' = (B' ⅋ C') , d-⊗-⅋ d' e' , s-⅋ s' t'
dual-subst (d-⅋-⊗ d e) (s-⅋ s t) with dual-subst d s | dual-subst e t
... | B' , d' , s' | C' , e' , t' = (B' ⊗ C') , d-⅋-⊗ d' e' , s-⊗ s' t'
dual-subst (d-∃-∀ d) (s-∃ s) with dual-subst d s
... | B' , d' , s' = $∀ B' , d-∃-∀ d' , s-∀ s'
dual-subst (d-∀-∃ d) (s-∀ s) with dual-subst d s
... | B' , d' , s' = $∃ B' , d-∀-∃ d' , s-∃ s'
dual-subst d-v-o (s-r (s-var d)) = _ , d , s-r (s-ort d)
dual-subst d-o-v (s-r (s-ort d)) = _ , dual-symm d , s-r (s-var d)

data _↝_ {n} {Γ : Context n} : Process Γ → Process Γ → Set where
  r-link      : ∀{Δ A B} {P : Process (B ∷ Δ)}
                (d : Dual A B) (e : Dual A B) (p : Γ ≃ B , Δ) →
                cut d p (link e (split-l (split-r split-e))) P ↝ #process (#cons p) P
  r-close     : ∀{P : Process Γ} (p₀ : Γ ≃ [] + Γ) (q₀ : Γ ≃ [] + Γ) →
                cut d-𝟙-⊥ p₀ close (wait (split-l q₀) P) ↝ P
  r-select-l  : ∀{Γ₁ Γ₂ A A′ B B′}
                {P : Process (A ∷ Γ₁)} {Q : Process (A′ ∷ Γ₂)} {R : Process (B′ ∷ Γ₂)}
                (d : Dual A A′) (e : Dual B B′)
                (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
                cut (d-⊕-& d e) p
                    (select true (split-l p₀) P)
                    (case (split-l q₀) Q R) ↝ cut d p P Q
  r-select-r  :
    ∀{Γ₁ Γ₂ A A′ B B′}
    {P : Process (B ∷ Γ₁)} {Q : Process (A′ ∷ Γ₂)} {R : Process (B′ ∷ Γ₂)}
    (d : Dual A A′) (e : Dual B B′) (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) →
    cut (d-⊕-& d e) p
        (select false (split-l p₀) P)
        (case (split-l q₀) Q R) ↝ cut e p P R
  r-fork      :
    ∀{Γ₁ Γ₂ Γ₃ Δ A B A′ B′}
    {P : Process (A ∷ Γ₁)} {Q : Process (B ∷ Γ₂)} {R : Process (B′ ∷ A′ ∷ Γ₃)}
    (d : Dual A A′) (e : Dual B B′) (p : Γ ≃ Δ + Γ₃) (p₀ : Γ₃ ≃ [] + Γ₃)
    (q : Δ ≃ Γ₁ + Γ₂) (q₀ : Δ ≃ [] + Δ) →
    let _ , p′ , q′ = +-assoc-l p q in
    cut (d-⊗-⅋ d e) p
        (fork (split-l q₀) q P Q)
        (join (split-l p₀) R) ↝ cut d q′ P (cut e (split-r p′) Q R)
  r-client    :
    ∀{Γ₁ Γ₂ A A′}
    {P : Process (A ∷ Γ₁)} {Q : Process (A′ ∷ Γ₂)} (d : Dual A A′)
    (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) (un : Un Γ₁) →
    cut (d-!-? d) p
      (server (split-l p₀) un P)
      (client (split-l q₀) Q) ↝ cut d p P Q
  r-weaken    :
    ∀{Γ₁ Γ₂ A A′}
    {P : Process (A ∷ Γ₁)} {Q : Process Γ₂}
    (d : Dual A A′) (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) (un : Un Γ₁) →
    cut (d-!-? d) p
        (server (split-l p₀) un P)
        (weaken (split-l q₀) Q) ↝ weakening un p Q
  r-contract  :
    ∀{Γ₁ Γ₂ A A′}
    {P : Process (A ∷ Γ₁)} {Q : Process (¿ A′ ∷ ¿ A′ ∷ Γ₂)}
    (d : Dual A A′) (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) (un : Un Γ₁) →
    cut (d-!-? d) p
      (server (split-l p₀) un P)
      (contract (split-l q₀) Q) ↝
      contraction un p
        (cut (d-!-? d) ++≃+
             (server (split-l p₀) un P)
             (cut (d-!-? d) (split-r p) (server (split-l p₀) un P) Q))
  r-poly :
    ∀{A A' : Type (suc n)} {B C : Type n} {Γ₁ Γ₂ : Context n} (σ : Subst (make-subst C) A B)
    {P : Process (B ∷ Γ₁)} {F : {X Y : Type n} -> Subst (make-subst X) A' Y -> Process (Y ∷ Γ₂)}
    (d : Dual A A') (p : Γ ≃ Γ₁ + Γ₂) (p₀ : Γ₁ ≃ [] + Γ₁) (q₀ : Γ₂ ≃ [] + Γ₂) ->
    let B' , d' , σ' = dual-subst d σ in
    cut (d-∃-∀ d) p (ex (split-l p₀) σ P) (all (split-l q₀) F) ↝
    cut d' p P (F σ')
  r-cut       : ∀{Γ₁ Γ₂ A B} {P Q : Process (A ∷ Γ₁)} {R : Process (B ∷ Γ₂)}
                (d : Dual A B) (q : Γ ≃ Γ₁ + Γ₂) → P ↝ Q →
                cut d q P R ↝ cut d q Q R
  r-cong      : ∀{P R Q : Process Γ} → P ⊒ R → R ↝ Q → P ↝ Q
