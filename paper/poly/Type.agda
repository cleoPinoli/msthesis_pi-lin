open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Data.Nat
open import Data.Fin

data Type : ℕ -> Set where
  𝟘 𝟙 ⊥ ⊤          : ∀{n} -> Type n
  var ort          : ∀{n} -> Fin n -> Type n
  ¡ ¿              : ∀{n} -> Type n → Type n
  _&_ _⊕_ _⊗_ _⅋_  : ∀{n} -> Type n → Type n → Type n
  $∀ $∃            : ∀{n} -> Type (suc n) -> Type n

data Dual : ∀{n} -> Type n → Type n → Set where
  d-𝟘-⊤  : ∀{n} -> Dual {n} 𝟘 ⊤
  d-⊤-𝟘  : ∀{n} -> Dual {n} ⊤ 𝟘
  d-𝟙-⊥  : ∀{n} -> Dual {n} 𝟙 ⊥
  d-⊥-𝟙  : ∀{n} -> Dual {n} ⊥ 𝟙
  d-!-?  : ∀{n} {A B} → Dual {n} A B → Dual (¡ A) (¿ B)
  d-?-!  : ∀{n} {A B} → Dual {n} A B → Dual (¿ A) (¡ B)
  d-&-⊕  : ∀{n} {A B A′ B′} → Dual {n} A A′ → Dual B B′ → Dual (A & B) (A′ ⊕ B′)
  d-⊕-&  : ∀{n} {A B A′ B′} → Dual {n} A A′ → Dual B B′ → Dual (A ⊕ B) (A′ & B′)
  d-⊗-⅋  : ∀{n} {A B A′ B′} → Dual {n} A A′ → Dual B B′ → Dual (A ⊗ B) (A′ ⅋ B′)
  d-⅋-⊗  : ∀{n} {A B A′ B′} → Dual {n} A A′ → Dual B B′ → Dual (A ⅋ B) (A′ ⊗ B′)
  d-∀-∃  : ∀{n} {A B : Type (suc n)} -> Dual A B -> Dual ($∀ A) ($∃ B)
  d-∃-∀  : ∀{n} {A B : Type (suc n)} -> Dual A B -> Dual ($∃ A) ($∀ B)
  d-v-o  : ∀{n} {x : Fin n} -> Dual (var x) (ort x)
  d-o-v  : ∀{n} {x : Fin n} -> Dual (ort x) (var x)

dual-symm : ∀{n} {A B : Type n} → Dual A B → Dual B A
dual-symm d-𝟘-⊤ = d-⊤-𝟘
dual-symm d-⊤-𝟘 = d-𝟘-⊤
dual-symm d-𝟙-⊥ = d-⊥-𝟙
dual-symm d-⊥-𝟙 = d-𝟙-⊥
dual-symm (d-!-? p) = d-?-! (dual-symm p)
dual-symm (d-?-! p) = d-!-? (dual-symm p)
dual-symm (d-&-⊕ p q) = d-⊕-& (dual-symm p) (dual-symm q)
dual-symm (d-⊕-& p q) = d-&-⊕ (dual-symm p) (dual-symm q)
dual-symm (d-⊗-⅋ p q) = d-⅋-⊗ (dual-symm p) (dual-symm q)
dual-symm (d-⅋-⊗ p q) = d-⊗-⅋ (dual-symm p) (dual-symm q)
dual-symm (d-∀-∃ p) = d-∃-∀ (dual-symm p)
dual-symm (d-∃-∀ p) = d-∀-∃ (dual-symm p)
dual-symm d-v-o = d-o-v
dual-symm d-o-v = d-v-o

dual-inv : ∀{n} {A B C : Type n} → Dual A B → Dual B C → A ≡ C
dual-inv d-𝟘-⊤ d-⊤-𝟘 = refl
dual-inv d-⊤-𝟘 d-𝟘-⊤ = refl
dual-inv d-𝟙-⊥ d-⊥-𝟙 = refl
dual-inv d-⊥-𝟙 d-𝟙-⊥ = refl
dual-inv (d-!-? p) (d-?-! q) = cong ¡ (dual-inv p q)
dual-inv (d-?-! p) (d-!-? q) = cong ¿ (dual-inv p q)
dual-inv (d-&-⊕ p q) (d-⊕-& r s) = cong₂ _&_ (dual-inv p r) (dual-inv q s)
dual-inv (d-⊕-& p q) (d-&-⊕ r s) = cong₂ _⊕_ (dual-inv p r) (dual-inv q s)
dual-inv (d-⊗-⅋ p q) (d-⅋-⊗ r s) = cong₂ _⊗_ (dual-inv p r) (dual-inv q s)
dual-inv (d-⅋-⊗ p q) (d-⊗-⅋ r s) = cong₂ _⅋_ (dual-inv p r) (dual-inv q s)
dual-inv (d-∀-∃ p) (d-∃-∀ q) = cong $∀ (dual-inv p q)
dual-inv (d-∃-∀ p) (d-∀-∃ q) = cong $∃ (dual-inv p q)
dual-inv d-v-o d-o-v = refl
dual-inv d-o-v d-v-o = refl

dual-fun-r  : ∀{n} {A B C : Type n} → Dual A B → Dual A C → B ≡ C
dual-fun-r d e = dual-inv (dual-symm d) e

dual-fun-l  : ∀{n} {A B C : Type n} → Dual B A → Dual C A → B ≡ C
dual-fun-l d e = dual-inv d (dual-symm e)

ext : ∀{m n} -> (Fin m -> Fin n) -> Fin (suc m) -> Fin (suc n)
ext ρ zero = zero
ext ρ (suc k) = suc (ρ k)

rename : ∀{m n} -> (Fin m -> Fin n) -> Type m -> Type n
rename ρ 𝟘 = 𝟘
rename ρ 𝟙 = 𝟙
rename ρ ⊥ = ⊥
rename ρ ⊤ = ⊤
rename ρ (var x) = var (ρ x)
rename ρ (ort x) = ort (ρ x)
rename ρ (¡ A) = ¡ (rename ρ A)
rename ρ (¿ A) = ¿ (rename ρ A)
rename ρ (A & B) = rename ρ A & rename ρ B
rename ρ (A ⊕ B) = rename ρ A ⊕ rename ρ B
rename ρ (A ⊗ B) = rename ρ A ⊗ rename ρ B
rename ρ (A ⅋ B) = rename ρ A ⅋ rename ρ B
rename ρ ($∀ A) = $∀ (rename (ext ρ) A)
rename ρ ($∃ A) = $∃ (rename (ext ρ) A)

exts : ∀{m n} -> (Fin m -> Type n) -> Fin (suc m) -> Type (suc n)
exts σ zero = var zero
exts σ (suc k) = rename suc (σ k)

data Subst {m n} : (σ : Fin m -> Type n) -> Type m -> Type n -> Set where
  s-𝟘 : ∀{σ} -> Subst σ 𝟘 𝟘
  s-𝟙 : ∀{σ} -> Subst σ 𝟙 𝟙
  s-⊥ : ∀{σ} -> Subst σ ⊥ ⊥
  s-⊤ : ∀{σ} -> Subst σ ⊤ ⊤
  s-v : ∀{σ A x} -> Dual (σ x) A -> Subst σ (var x) (σ x)
  s-o : ∀{σ A x} -> Dual (σ x) A -> Subst σ (ort x) A
  s-! : ∀{σ A A'} -> Subst σ A A' -> Subst σ (¡ A) (¡ A')
  s-? : ∀{σ A A'} -> Subst σ A A' -> Subst σ (¿ A) (¿ A')
  s-& : ∀{σ A A' B B'} -> Subst σ A A' -> Subst σ B B' -> Subst σ (A & B) (A' & B')
  s-⊕ : ∀{σ A A' B B'} -> Subst σ A A' -> Subst σ B B' -> Subst σ (A ⊕ B) (A' ⊕ B')
  s-⊗ : ∀{σ A A' B B'} -> Subst σ A A' -> Subst σ B B' -> Subst σ (A ⊗ B) (A' ⊗ B')
  s-⅋ : ∀{σ A A' B B'} -> Subst σ A A' -> Subst σ B B' -> Subst σ (A ⅋ B) (A' ⅋ B')
  s-∃ : ∀{σ A A'} -> Subst (exts σ) A A' -> Subst σ ($∃ A) ($∃ A')
  s-∀ : ∀{σ A A'} -> Subst (exts σ) A A' -> Subst σ ($∀ A) ($∀ A')

make-subst : ∀{n} -> Type n -> Fin (suc n) -> Type n
make-subst A zero = A
make-subst A (suc k) = var k
