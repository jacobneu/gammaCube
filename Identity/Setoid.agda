module Identity.Setoid where

open import Prelude
open import Structures.Setoid public
open import Families.Setoid public


open Displayed

Id : ∀ {i}{Γ : Setoid i}{j}{α : DispSetoid Γ j}(s t : SetoidSec Γ α) → DispSetoid Γ j
Id {i}{Γ}{j}{α} s t = record
  { ∣_∣T_ = λ γ → ↑ps (α T refC Γ γ ⊢ ∣ s ∣t γ ~ ∣ t ∣t γ) 
  ; _T_⊢_~_ = λ _ _ _ → ⊤p' 
  ; refT = λ _ → ttp' 
  ; symT = λ _ → ttp' 
  ; transT = λ _ _ → ttp' 
  }

rfl : ∀ {i}{Γ : Setoid i}{j}{α : DispSetoid Γ j}(s : SetoidSec Γ α) → SetoidSec Γ (Id s s)
rfl {i}{Γ}{j}{α} s = record 
    { ∣_∣t = λ γ → mk↑ps (refT α (∣ s ∣t γ)) 
    ; ~t = λ _ → ttp' }