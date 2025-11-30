module Identity.Setoid where

open import Prelude
open import Structures.Setoid public
open import Families.Setoid public
open import CwF.Setoid public


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

module Fibrant where
  open Pseudo
  open psSetoidFibrancy

  trspt : ∀ {i}{Γ : Setoid i}{α : psSetoidFam Γ i}{β : psSetoidFam (Γ ▷ (fst α)) i}{s t : SetoidSec Γ (fst α)}
    (f : SetoidSec Γ (Id s t)) →
    SetoidSec Γ {i} (_[_]T (fst β) (id,s s)) →
    SetoidSec Γ {i} (_[_]T (fst β) (id,s t))
  trspt {i}{Γ}{α}{β}{s}{t} f b = record 
    { ∣_∣t = λ γ → coeT (snd β) (refC Γ γ ,p un↑ps (∣ f ∣t γ)) (∣ b ∣t γ)
    ; ~t = λ {γ} {γ'} p →  
        let 
          helper γ = (refC Γ γ) ,p un↑ps (∣ f ∣t γ)
          open Disp~Reasoning (fst β)
        in
          coeT (snd β) (helper γ) (∣ b ∣t γ) 
              ~D⟨ reverseT (cohT (snd β) (helper γ) (∣ b ∣t γ)) ⟩
          ∣ b ∣t γ 
              ~D⟨ ~t b p ⟩
          ∣ b ∣t γ'
              ~D⟨ cohT (snd β) (helper γ') (∣ b ∣t γ') ⟩
          coeT (snd β) (helper γ') (∣ b ∣t γ')    
              ~D∎
    }