{-
Taken (with minor modification) from Agda formalization of the setoid universe,
by Thorsten Altenkrich, Simon Boulier, Ambrus Kaposi, Christian Sattler, and Filippo Sestini.
https://bitbucket.org/taltenkirch/setoid-univ
-}

module Structures.Setoid where

open import Prelude 


record Setoid i : Type (lsuc i) where
  field
    ∣_∣C : Type i
    _C_~_ : ∣_∣C → ∣_∣C → Prop i
    refC : ∀ γ → _C_~_ γ γ
    symC : ∀{γ γ'} → _C_~_ γ γ' → _C_~_ γ' γ
    transC : ∀{γ γ' γ''} → _C_~_ γ γ' → _C_~_ γ' γ'' → _C_~_ γ γ''
  infix 4 ∣_∣C
  infix 5 _C_~_
open Setoid public

record SetoidMor {i j}(Γ : Setoid i)(Δ : Setoid j) : Type (i ⊔ j) where
  field
    ∣_∣s : ∣ Γ ∣C → ∣ Δ ∣C
    ~s   : {γ γ' : ∣ Γ ∣C} → Γ C γ ~ γ' → Δ C (∣_∣s γ) ~ (∣_∣s γ')
  infix 4 ∣_∣s
open SetoidMor public

module ~Reasoning {i} (Γ : Setoid i) where

  infixr 29 _⁻¹
  infixr 30 _~⟨_⟩_
  infixl 40 _~∎

  _~∎ : ∀ γ → Γ C γ ~ γ
  _~∎ = refC Γ

  _⁻¹ : ∀{γ γ'} → Γ C γ ~ γ' → Γ C γ' ~ γ
  p ⁻¹ = symC Γ p

  _~⟨_⟩_ : ∀ (γ : ∣ Γ ∣C){γ' : ∣ Γ ∣C} → Γ C γ ~ γ' → {γ'' : ∣ Γ ∣C} → Γ C γ' ~ γ'' → Γ C γ ~ γ''
  γ ~⟨ p ⟩ q = transC Γ p q