module Preorder.PCwF where

open import Prelude
open import Structures.Preorder

infixl 5 _▷⁺_
infixl 7 _[_]T⁺
infixl 5 _▷⁻_
infixl 7 _[_]T⁻
infixr 6 _∘_
infixl 5 _,⁺_
infixl 8 _[_]t⁺
infixl 5 _,⁻_
infixl 8 _[_]t⁻

Con = Preord
Sub = PreordMor
Ty⁺ = PreordFam⁺
Ty⁻ = PreordFam⁻
Tm⁺ = PreordSec⁺
Tm⁻ = PreordSec⁻

• : Con lzero
∣ • ∣C = ⊤
• C _ ≤ _ = ⊤p
refC • _ = ttp
transC • _ _ = ttp


_▷⁺_ : ∀{i}(Γ : Con i){j} → Ty⁺ Γ j → Con (i ⊔ j)
_▷⁺_ Γ A = record
  { ∣_∣C   = Σ ∣ Γ ∣C ∣ A ∣T⁺_
  ; _C_≤_  = λ { (γ , α)(γ' , α') → Σp (Γ C γ ≤ γ') (A T⁺_⊢ α ≤ α') }
  ; refC   = λ { (γ , α) → refC Γ γ ,p refT⁺ A α }
  ; transC = λ { (p ,p r)(p' ,p r') → transC Γ p p' ,p transT⁺ A r r' }
  }
_▷⁻_ : ∀{i}(Γ : Con i){j} → Ty⁻ Γ j → Con (i ⊔ j)
_▷⁻_ Γ A = record
  { ∣_∣C   = Σ ∣ Γ ∣C ∣ A ∣T⁻_
  ; _C_≤_  = λ { (γ , α)(γ' , α') → Σp (Γ C γ ≤ γ') (A T⁻_⊢ α ≤ α') }
  ; refC   = λ { (γ , α) → refC Γ γ ,p refT⁻ A α }
  ; transC = λ { (p ,p r)(p' ,p r') → transC Γ p p' ,p transT⁻ A r r' }
  }


_[_]T⁺ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k} → Ty⁺ Δ k → Sub Γ Δ → Ty⁺ Γ k
A [ σ ]T⁺ = record
  { ∣_∣T⁺_   = λ γ → ∣ A ∣T⁺ (∣ σ ∣s γ)
  ; _T⁺_⊢_≤_ = λ p α α' → A T⁺ ≤s σ p ⊢ α ≤ α'
  ; refT⁺    = refT⁺ A
  ; transT⁺  = transT⁺ A
  ; coeT⁺    = λ p → coeT⁺ A (≤s σ p)
  ; cohT⁺    = λ p → cohT⁺ A (≤s σ p)
  }
_[_]T⁻ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k} → Ty⁻ Δ k → Sub Γ Δ → Ty⁻ Γ k
A [ σ ]T⁻ = record
  { ∣_∣T⁻_   = λ γ → ∣ A ∣T⁻ (∣ σ ∣s γ)
  ; _T⁻_⊢_≤_ = λ p α α' → A T⁻ ≤s σ p ⊢ α ≤ α'
  ; refT⁻    = refT⁻ A
  ; transT⁻  = transT⁻ A
  ; coeT⁻    = λ p → coeT⁻ A (≤s σ p)
  ; cohT⁻    = λ p → cohT⁻ A (≤s σ p)
  }

id : ∀{i}{Γ : Con i} → Sub Γ Γ
id = record
  { ∣_∣s = λ γ → γ
  ; ≤s   = λ p → p
  }

_∘_ : ∀{i}{Γ : Con i}{j}{Θ : Con j}{k}{Δ : Con k} → Sub Θ Δ → Sub Γ Θ → Sub Γ Δ
σ ∘ ν = record
  { ∣_∣s = λ γ → ∣ σ ∣s (∣ ν ∣s γ)
  ; ≤s   = λ p → ≤s σ (≤s ν p)
  }

ε : ∀{i}{Γ : Con i} → Sub Γ •
∣ ε ∣s _ = tt
≤s ε _ = ttp

_,⁺_ : ∀{i}{Γ : Con i}{j}{Δ : Con j}(σ : Sub Γ Δ){b}{A : Ty⁺ Δ b} → Tm⁺ Γ (A [ σ ]T⁺) → Sub Γ (Δ ▷⁺ A)
σ ,⁺ t = record { ∣_∣s = λ γ → ∣ σ ∣s γ , ∣ t ∣t⁺ γ 
                ; ≤s   = λ p →  (≤s σ p) ,p ≤t⁺ t p 
                }
_,⁻_ : ∀{i}{Γ : Con i}{j}{Δ : Con j}(σ : Sub Γ Δ){b}{A : Ty⁻ Δ b} → Tm⁻ Γ (A [ σ ]T⁻) → Sub Γ (Δ ▷⁻ A)
σ ,⁻ t = record { ∣_∣s = λ γ → ∣ σ ∣s γ , ∣ t ∣t⁻ γ 
                ; ≤s   = λ p →  (≤s σ p) ,p ≤t⁻ t p 
                }

π₁⁺ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty⁺ Δ k} → Sub Γ (Δ ▷⁺ A) →  Sub Γ Δ
π₁⁺ σ = record { ∣_∣s = λ γ → fst (∣ σ ∣s γ) ; ≤s = λ p → fstp (≤s σ p) }
π₁⁻ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty⁻ Δ k} → Sub Γ (Δ ▷⁻ A) →  Sub Γ Δ
π₁⁻ σ = record { ∣_∣s = λ γ → fst (∣ σ ∣s γ) ; ≤s = λ p → fstp (≤s σ p) } 


_[_]t⁺ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty⁺ Δ k} → Tm⁺ Δ A → (σ : Sub Γ Δ) → Tm⁺ Γ (A [ σ ]T⁺)
t [ σ ]t⁺ = record { ∣_∣t⁺ = λ γ → ∣ t ∣t⁺ (∣ σ ∣s γ) ; ≤t⁺ = λ p → ≤t⁺ t (≤s σ p) }
_[_]t⁻ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty⁻ Δ k} → Tm⁻ Δ A → (σ : Sub Γ Δ) → Tm⁻ Γ (A [ σ ]T⁻)
t [ σ ]t⁻ = record { ∣_∣t⁻ = λ γ → ∣ t ∣t⁻ (∣ σ ∣s γ) ; ≤t⁻ = λ p → ≤t⁻ t (≤s σ p) }


π₂⁺ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty⁺ Δ k}(σ : Sub Γ (Δ ▷⁺ A)) → Tm⁺ Γ (A [ π₁⁺ {A = A} σ ]T⁺)
π₂⁺ σ = record { ∣_∣t⁺ = λ γ → snd (∣ σ ∣s γ) ; ≤t⁺ = λ p → sndp (≤s σ p) }
π₂⁻ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty⁻ Δ k}(σ : Sub Γ (Δ ▷⁻ A)) → Tm⁻ Γ (A [ π₁⁻ {A = A} σ ]T⁻)
π₂⁻ σ = record { ∣_∣t⁻ = λ γ → snd (∣ σ ∣s γ) ; ≤t⁻ = λ p → sndp (≤s σ p) }
