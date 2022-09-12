open import Level renaming (zero to lzero; suc to lsuc)

module Eff {a : Level} where
  open import Data.List
  open import Data.List.Membership.Propositional
  open import Data.List.Relation.Unary.Any
  open import Data.Maybe hiding (_>>=_)
  open import Data.Nat hiding (_<_)
  open import Data.Nat.Induction
  open import Data.Nat.Properties
  open import Data.Product
  open import Data.Sum
  open import Data.Unit
  open import Function
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality

  Req : Set (lsuc a)
  Req = Set a → Set a

  private
    variable
      A B C D : Set a
      T U : Req
      R R′ : List (Req)

  data Union : List Req → Set a → Set a where
    here  : ∀ {T R A} → T A       → Union (T ∷ R) A
    there : ∀ {T R A} → Union R A → Union (T ∷ R) A

  instance
    ∈-here : T ∈ T ∷ R
    ∈-here = here refl

    ∈-there : ⦃ T ∈ R ⦄ → T ∈ U ∷ R
    ∈-there ⦃ p ⦄ = there p

  inj : ⦃ T ∈ R ⦄ → T A → Union R A
  inj ⦃ here refl ⦄ x = here x
  inj ⦃ there p   ⦄ x = there (inj ⦃ p ⦄ x)

  prj : ⦃ T ∈ R ⦄ → Union R A → Maybe (T A)
  prj ⦃ here refl ⦄ (here  x) = just x
  prj ⦃ here refl ⦄ (there x) = nothing
  prj ⦃ there p ⦄   (here  x) = nothing
  prj ⦃ there p ⦄   (there x) = prj ⦃ p ⦄ x

  decomp : Union (T ∷ R) A → Union R A ⊎ T A
  decomp (here  p) = inj₂ p
  decomp (there p) = inj₁ p

  -- The existential quantification over Set a that occurs in node and impure
  -- pushes Eff R A up a universe level into Set (lsuc a). This makes it
  -- incompatible with the Agda standard library definitions for RawMonad
  -- etc. which operate on functions of the form Set a → Set a. It might (?) be
  -- possible to solve this with indexed universes like Agda's continuation
  -- monad.
  mutual
    data Cont (R : List Req) (A B : Set a) : Set (lsuc a) where
      leaf : (A → Eff R B) → Cont R A B
      node : Cont R A C → Cont R C B → Cont R A B

    data Eff (R : List Req) (A : Set a) : Set (lsuc a) where
      pure   : A → Eff R A
      impure : Union R B → Cont R B A → Eff R A

  -- qapp does some non-structural recursion on the continuation(s) by way of
  -- tree rotation. Agda can't prove this terminates on its own, so we imbue
  -- ViewL with a proof that it strictly decreases the size of the tree.
  module ContRec where

    size : Cont R A B → ℕ
    size (leaf k)   = 1
    size (node l r) = size l + size r

    _<_ : REL (Cont R A B) (Cont R C D) _
    x < y = size x <′ size y

    data ViewL {R : List Req} {A B : Set a} (k : Cont R A B) : Set (lsuc a) where
      t1 : (A → Eff R B) → ViewL k
      t* : (A → Eff R C) → (x : Cont R C B) → x < k → ViewL k

    tviewl : (x : Cont R A B) -> ViewL x
    tviewl (leaf r) = t1 r
    tviewl (node l r) = go l r
      where
        rotate : (a : Cont R A B) → (b : Cont R B C) → (c : Cont R C D)
               → size a + (size b + size c) ≡ (size a + size b) + size c
        rotate a b c = sym $ +-assoc (size a) (size b) (size c)

        go : (l : Cont R A C) -> (r : Cont R C B) -> ViewL (node l r)
        go (leaf r) tr = t* r tr ≤′-refl
        go (node l r) tr with go l (node r tr)
        ... | t1 k = t1 k
        ... | t* k x p = t* k x (subst₂ _<′_ refl (rotate l r tr) p)

    qapp : (q : Cont R B A) → Acc _<′_ (size q) → B → Eff R A
    qapp q (acc rs) x = case tviewl q of λ where
      (t1 k)     → k x
      (t* k t p) → case k x of λ where
        (pure y)     → qapp t (rs _ p) y
        (impure m f) → impure m (node f t)

  qapp : Cont R B A → B → Eff R A
  qapp q x = ContRec.qapp q (<′-wellFounded _) x

  qcomp : Cont R A B → (Eff R B → Eff R′ C) → (A → Eff R′ C)
  qcomp g h a = h (qapp g a)

  fmap : (A → B) → Eff R A → Eff R B
  fmap f (pure x) = pure (f x)
  fmap f (impure m g) = impure m (node g (leaf (pure ∘ f)))

  return : A → Eff R A
  return = pure

  infixl 1 _>>=_ _>>_ _>=>_
  _>>=_ : Eff R A → (A → Eff R B) → Eff R B
  pure x >>= f = f x
  impure m g >>= f = impure m (node g (leaf f))

  _>>_ : Eff R A → Eff R B → Eff R B
  x >> y = x >>= λ _ → y

  _>=>_ : (A → Eff R B) → (B → Eff R C) → (A → Eff R C)
  f >=> g = λ a → f a >>= g

  send : ⦃ T ∈ R ⦄ → T A → Eff R A
  send t = impure (inj t) (leaf pure)

  run : Eff [] A → A
  run (pure x) = x

  -- I'm not particularly convinced this is actually true, but constructing the
  -- appropriate recursion scheme is really hard.
  {-# TERMINATING #-}
  handle-relay : (A → Eff R B)
               → (∀ {X} → T X → (X → Eff R B) → Eff R B)
               → Eff (T ∷ R) A → Eff R B
  handle-relay ret h (pure x) = ret x
  handle-relay ret h (impure m f) with decomp m | qcomp f (handle-relay ret h)
  ... | inj₁ x | k = impure x (leaf k)
  ... | inj₂ x | k = h x k

  data Reader (A : Set a) : Set a → Set a where
    get : Reader A A

  ask : ⦃ Reader A ∈ R ⦄ → Eff R A
  ask = send get

  runReader : A → Eff (Reader A ∷ R) B → Eff R B
  runReader i = handle-relay return λ where get k → k i

  data Writer (A : Set a) : Set a → Set a where
    put : A → Writer A (Lift _ ⊤)

  tell : ⦃ Writer A ∈ R ⦄ → A → Eff R _
  tell o = send (put o)

  runWriter : Eff (Writer A ∷ R) B → Eff R (B × List A)
  runWriter = handle-relay (λ x → return (x , []))
    λ where (put o) k → do
      (x , l) ← k _
      return (x , o ∷ l)
