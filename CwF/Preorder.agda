module CwF.Preorder where

open import Prelude
open import Structures.Preorder public
open import Families.Preorder public

infixl 7 _[_]T⁺
infixl 5 _▷⁺_
infixl 5 _,⁺s_


open Displayed

record PreordSec {i}(Γ : Preord i){j}(A : DispPreord Γ j) : Type (i ⊔ j) where
    field
        ∣_∣t : (γ : ∣ Γ ∣C) → ∣ A ∣T γ
        ≤t   : {γ γ' : ∣ Γ ∣C}(p : Γ C γ ≤ γ') → A T p ⊢ (∣_∣t γ) ≤ (∣_∣t γ')
    infix 4 ∣_∣t
open PreordSec public

_▷⁺_ : ∀{i}(Γ : Preord i){j}(α : DispPreord Γ j) → Preord (i ⊔ j)
Γ ▷⁺ α = record 
    { ∣_∣C = Σ ∣ Γ ∣C (∣ α ∣T_) 
    ; _C_≤_ = λ w w' → Σp (Γ C fst w ≤ fst w') λ p → α T p ⊢ snd w ≤ snd w'
    ; refC = λ w → refC Γ (fst w) ,p refT α (snd w)
    ; transC = λ φ ψ → (transC Γ (fstp φ) (fstp ψ)) ,p transT α (sndp φ) (sndp ψ) 
    }

_[_]T⁺ : ∀{i}{Δ Γ : Preord i}{j} → DispPreord Γ j → PreordMor Δ Γ → DispPreord Δ j
_[_]T⁺ {i}{Δ}{Γ}{j} α σ = record
  { ∣_∣T_ = λ δ → ∣ α ∣T ∣ σ ∣s δ
  ; ≤D = λ γ γ' p x x' → α T ≤s σ p ⊢ x ≤ x'
  ; refT = λ x → refT α x
  ; transT = λ p q → transT α p q
  }


_,⁺s_ : ∀{i}{Δ Γ : Preord i}{j}{α : DispPreord Γ j} →
    (σ : PreordMor Δ Γ) →
    PreordSec Δ (α [ σ ]T⁺) → 
    PreordMor Δ (Γ ▷⁺ α)
σ ,⁺s s = record 
    { ∣_∣s = λ δ → (∣ σ ∣s δ) , ∣ s ∣t δ
    ; ≤s = λ p → ≤s σ p ,p ≤t s p
    }

id : ∀{i}{Γ : Preord i} → PreordMor Γ Γ
id {i}{Γ} = record 
    { ∣_∣s = λ γ → γ
    ; ≤s = λ p → p
    }

_[id]T⁺ : ∀{i}{Γ : Preord i}{j} → (α : DispPreord Γ j) → α [ id ]T⁺ ≡ α
_[id]T⁺ {i}{Γ}{j} α = DispPreord-≡-intro (α [ id ]T⁺) α refl refl

id,⁺s : ∀{i}{Γ : Preord i}{j}{α : DispPreord Γ j} →
    PreordSec Γ α → 
    PreordMor Γ (Γ ▷⁺ α)
id,⁺s {i}{Γ}{j}{α} t = _,⁺s_ {i}{Γ}{Γ}{j}{α} id (tr (PreordSec Γ) (symm (α [id]T⁺)) t)