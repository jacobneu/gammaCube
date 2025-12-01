
{-
Modified from the Agda formalization of the Setoid universe,
by Thorsten Altenkrich, Simon Boulier, Ambrus Kaposi, Christian Sattler, and Filippo Sestini.
https://bitbucket.org/taltenkirch/Setoid-univ
-}

module Structures.Preorder where

open import Prelude 


record Preord i : Type (lsuc i) where
  field
    ∣_∣C : Type i
    _C_≤_ : ∣_∣C → ∣_∣C → Prop i
    refC : ∀ γ → _C_≤_ γ γ
    transC : ∀{γ γ' γ''} → _C_≤_ γ γ' → _C_≤_ γ' γ'' → _C_≤_ γ γ''
  infix 4 ∣_∣C
  infix 5 _C_≤_
open Preord public

record PreordMor {i j}(Γ : Preord i)(Δ : Preord j) : Type (i ⊔ j) where
  field
    ∣_∣s : ∣ Γ ∣C → ∣ Δ ∣C
    ≤s   : {γ γ' : ∣ Γ ∣C} → Γ C γ ≤ γ' → Δ C (∣_∣s γ) ≤ (∣_∣s γ')
  infix 4 ∣_∣s
open PreordMor public

module PreordReasoning {i} (Γ : Preord i) where

  infixr 30 _≤⟨_⟩_
  infixl 40 _≤∎

  _≤∎ : ∀ γ → Γ C γ ≤ γ
  _≤∎ = refC Γ

  _≤⟨_⟩_ : ∀ (γ : ∣ Γ ∣C){γ' : ∣ Γ ∣C} → Γ C γ ≤ γ' → {γ'' : ∣ Γ ∣C} → Γ C γ' ≤ γ'' → Γ C γ ≤ γ''
  γ ≤⟨ p ⟩ q = transC Γ p q