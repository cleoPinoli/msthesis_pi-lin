module Type where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong₂)

data Type : Set where
  Zero One Bot Top : Type
  _&_ _⊕_ _⊗_ _⅋_ : Type -> Type -> Type

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


-- duality is an involution (if Dual A B, and Dual B C, then A ≡ C)
dual-inv : ∀{A B C} -> Dual A B -> Dual B C -> A ≡ C
dual-inv dual-zero-top dual-top-zero = refl
dual-inv dual-top-zero dual-zero-top = refl
dual-inv dual-one-bot dual-bot-one = refl
dual-inv dual-bot-one dual-one-bot = refl
dual-inv (dual-with-plus p q) (dual-plus-with r s) = cong₂ _&_ (dual-inv p r) (dual-inv q s)
dual-inv (dual-plus-with p q) (dual-with-plus r s) = cong₂ _⊕_ (dual-inv p r) (dual-inv q s)
--dual-inv (d-⊗-⅋ p q) (d-⅋-⊗ r s) = cong₂ _⊗_ (dual-inv p r) (dual-inv q s)
--dual-inv (d-⅋-⊗ p q) (d-⊗-⅋ r s) = cong₂ _⅋_ (dual-inv p r) (dual-inv q s)



dual-fun-r : ∀{A B C} -> Dual A B -> Dual A C -> B ≡ C
dual-fun-r d e = dual-inv (dual-symm d) e

dual-fun-l : ∀{A B C} -> Dual B A -> Dual C A -> B ≡ C
dual-fun-l d e = dual-inv d (dual-symm e)
