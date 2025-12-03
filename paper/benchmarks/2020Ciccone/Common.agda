open import Data.Nat using (suc)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; refl)

suc-≢ : ∀{m n} -> suc m ≢ suc n -> m ≢ n
suc-≢ = contraposition (cong suc)

cong₃ :
  ∀{ℓ1 ℓ2 ℓ3 ℓ4}{A : Set ℓ1}{B : Set ℓ2}{C : Set ℓ3}{D : Set ℓ4}{x x' : A}{y y' : B}{z z' : C} ->
  (f : A -> B -> C -> D) -> x ≡ x' -> y ≡ y' -> z ≡ z' -> f x y z ≡ f x' y' z'
cong₃ _ refl refl refl = refl

postulate
  extensionality :
    ∀{A B : Set} {f g : A -> B} -> (∀(x : A) -> f x ≡ g x) -> f ≡ g
  ∀-extensionality :
    ∀{ℓ ℓ'}{A : Set ℓ} {B : A -> Set ℓ'} {f g : (x : A) -> B x} ->
    (∀(x : A) -> f x ≡ g x) -> f ≡ g
