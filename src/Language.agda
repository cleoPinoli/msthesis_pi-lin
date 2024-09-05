
open import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Data.List

data SessionType : Set where
  Zero One Bot Top : SessionType
  _&_ _⊕_ : SessionType -> SessionType -> SessionType

data Dual : SessionType -> SessionType -> Set where
  dual-zero-top : Dual Zero Top
  dual-top-zero : Dual Top Zero
  dual-one-bot  : Dual One Bot
  dual-bot-one  : Dual Bot One
  dual-with-plus : ∀{t s t' s'} -> Dual t t' -> Dual s s' -> Dual (t & s) (t' ⊕ s')
  dual-plus-with : ∀{t s t' s'} -> Dual t t' -> Dual s s' -> Dual (t ⊕ s) (t' & s')

BoolST : SessionType
BoolST = One ⊕ One

dual : SessionType -> SessionType
dual Zero = Top
dual One = Bot
dual Bot = One
dual Top = Zero
dual (t & s) = dual t ⊕ dual s
dual (t ⊕ s) = dual t & dual s

dual-inv : (t : SessionType) -> t ≡ dual (dual t)
dual-inv Zero = refl
dual-inv One = refl
dual-inv Bot = refl
dual-inv Top = refl
dual-inv (t & s) =
  begin
    (t & s)             ≡⟨ cong (_& s) (dual-inv t) ⟩
    (dual (dual t) & s) ≡⟨ cong ((dual (dual t)) &_) (dual-inv s) ⟩
    (dual (dual t) & dual (dual s))
  ∎
dual-inv (t ⊕ s) = {!!}

Context : Set
Context = List SessionType

data Empty : Context -> Set where
  empty : Empty []

-- data _~>_∘_ : Context -> Context -> Context -> Set where
--   empty : [] ~> [] ∘ []
--   left  : ∀{t Γ Δ₁ Δ₂} -> Γ ~> Δ₁ ∘ Δ₂ -> (t ∷ Γ) ~> (t ∷ Δ₁) ∘ Δ₂
--   right : ∀{t Γ Δ₁ Δ₂} -> Γ ~> Δ₁ ∘ Δ₂ -> (t ∷ Γ) ~> Δ₁ ∘ (t ∷ Δ₂)

-- data _∈_ (t : SessionType) : Context -> Set where
--   here : t ∈ (t ∷ [])

-- data _∈_~>_∈_ (t : SessionType) : Context -> SessionType -> Context -> Set where
--   here : ∀{s Γ} -> t ∈ (t ∷ Γ) ~> s ∈ (s ∷ Γ)
--   next : ∀{s u Γ Δ} -> t ∈ Γ ~> s ∈ Δ -> t ∈ (u ∷ Γ) ~> s ∈ (u ∷ Δ)

-- data _/_∈_/_ (t s : SessionType) : Context -> Context -> Set where
--   here : ∀{Γ} -> t / s ∈ (t ∷ Γ) / (s ∷ Γ)
--   next : ∀{u Γ Δ} -> t / s ∈ Γ / Δ -> t / s ∈ (u ∷ Γ) / (u ∷ Δ)

data _∈_~>_ (t : SessionType) : Context -> Context -> Set where
  here : ∀{Γ} -> t ∈ (t ∷ Γ) ~> Γ
  next : ∀{s Γ Δ} -> t ∈ Γ ~> Δ -> t ∈ (s ∷ Γ) ~> (s ∷ Δ)

data Process Γ : Set where
  close : One ∈ Γ ~> [] -> Process Γ
  wait : ∀{Δ} -> Bot ∈ Γ ~> Δ -> Process Δ -> Process Γ
  left : ∀{t s Δ} -> (t ⊕ s) ∈ Γ ~> Δ -> Process (t ∷ Δ) -> Process Γ
  right : ∀{t s Δ} -> (t ⊕ s) ∈ Γ ~> Δ -> Process (s ∷ Δ) -> Process Γ
  switch : ∀{t s Δ} -> (t & s) ∈ Γ ~> Δ -> Process (t ∷ Δ) -> Process (s ∷ Δ) -> Process Γ
  cut : ∀{t s} -> Dual t s -> Process (t ∷ Γ) -> Process (s ∷ Γ) -> Process Γ

dual-symm : ∀{t s} -> Dual t s -> Dual s t
dual-symm dual-zero-top = dual-top-zero
dual-symm dual-top-zero = {!!}

data _⊒_ {Γ} : Process Γ -> Process Γ -> Set where
  comm : ∀{t s P Q} (d : Dual t s) -> cut d P Q ⊒ cut (dual-symm d) Q P
