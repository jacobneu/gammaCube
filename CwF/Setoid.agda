module CwF.Setoid where

open import Prelude
open import Structures.Setoid public
open import Families.Setoid public

infixl 7 _[_]T
infixl 5 _▷_
infixl 5 _,s_


open Displayed

record SetoidSec {i}(Γ : Setoid i){j}(A : DispSetoid Γ j) : Type (i ⊔ j) where
    field
        ∣_∣t : (γ : ∣ Γ ∣C) → ∣ A ∣T γ
        ~t   : {γ γ' : ∣ Γ ∣C}(p : Γ C γ ~ γ') → A T p ⊢ (∣_∣t γ) ~ (∣_∣t γ')
    infix 4 ∣_∣t
open SetoidSec public

_▷_ : ∀{i}(Γ : Setoid i){j}(α : DispSetoid Γ j) → Setoid (i ⊔ j)
Γ ▷ α = record 
    { ∣_∣C = Σ ∣ Γ ∣C (∣ α ∣T_) 
    ; _C_~_ = λ w w' → Σp (Γ C fst w ~ fst w') λ p → α T p ⊢ snd w ~ snd w'
    ; refC = λ w → refC Γ (fst w) ,p refT α (snd w)
    ; symC = λ φ → (symC Γ (fstp φ)) ,p symT α (sndp φ)
    ; transC = λ φ ψ → (transC Γ (fstp φ) (fstp ψ)) ,p transT α (sndp φ) (sndp ψ) 
    }

_[_]T : ∀{i}{Δ Γ : Setoid i}{j} → DispSetoid Γ j → SetoidMor Δ Γ → DispSetoid Δ j
_[_]T {i}{Δ}{Γ}{j} α σ = record
  { ∣_∣T_ = λ δ → ∣ α ∣T ∣ σ ∣s δ
  ; _T_⊢_~_ = λ p x x' → α T ~s σ p ⊢ x ~ x'
  ; refT = λ x → refT α x
  ; symT = λ p → symT α p
  ; transT = λ p q → transT α p q
  }


_,s_ : ∀{i}{Δ Γ : Setoid i}{j}{α : DispSetoid Γ j} →
    (σ : SetoidMor Δ Γ) →
    SetoidSec Δ (α [ σ ]T) → 
    SetoidMor Δ (Γ ▷ α)
σ ,s s = record 
    { ∣_∣s = λ δ → (∣ σ ∣s δ) , ∣ s ∣t δ
    ; ~s = λ p → ~s σ p ,p ~t s p
    }

id : ∀{i}{Γ : Setoid i} → SetoidMor Γ Γ
id {i}{Γ} = record 
    { ∣_∣s = λ γ → γ
    ; ~s = λ p → p
    }

-- _[id]T : ∀{i}{Γ : Setoid i}{j}{α : DispSetoid Γ j} →
--     α [ id ]T ≡ α
-- _[id]T = {!   !}
id,s : ∀{i}{Γ : Setoid i}{j}{α : DispSetoid Γ j} →
    SetoidSec Γ α → 
    SetoidMor Γ (Γ ▷ α)
id,s t = record 
    { ∣_∣s = λ γ → γ , ∣ t ∣t γ
    ; ~s = λ p → p ,p ~t t p 
    }