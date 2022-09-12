module EffEx where
  open import Eff

  open import Data.List
  open import Data.List.Membership.Propositional
  open import Data.Nat

  private
    variable
      R : List (Req)

  addGet : ⦃ Reader ℕ ∈ R ⦄ → ℕ → Eff R ℕ
  addGet x = do
    i ← ask
    return (i + x)

  addN : ⦃ Reader ℕ ∈ R ⦄ → ℕ → Eff R ℕ
  addN n = foldl _>=>_ return (replicate n addGet) 0
