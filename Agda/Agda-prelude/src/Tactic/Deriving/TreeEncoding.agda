
-- Deriving TreeEncoding. Note: only for non-dependent datatypes.

module Tactic.Deriving.TreeEncoding where

open import Prelude
open import Tactic.Reflection
open import Tactic.Deriving
open import Tactic.Reflection
open import Tactic.Reflection.Quote
open import Data.TreeRep
open import Container.Traversable

private
  mapIx : ∀ {a b} {A : Set a} {B : Set b} → (Nat → A → B) → List A → List B
  mapIx f []       = []
  mapIx f (x ∷ xs) = f 0 x ∷ mapIx (f ∘ suc) xs

  -- encode (ci x₁ .. xn) = node i (treeEncode x₁) .. (treeEncode xn)
  encodeClause : Nat → Nat → Name → TC Clause
  encodeClause np i c = do
    args ← drop np <$> argTel c
    let xs = reverse (mapIx const args)
    return (clause [ vArg (con c (map (var "x" <$_) args)) ]
                   (con₂ (quote node)
                         (lit (nat i))
                         (quoteList (map (λ i → def₁ (quote treeEncode) (var i [])) xs))))

  quoteListP : List Pattern → Pattern
  quoteListP = foldr (λ p ps → con₂ (quote List._∷_) p ps) (con₀ (quote List.[]))

  qAp : Term → Term → Term
  qAp f x = def₂ (quote _<*>′_) f x

  -- decode (node i x₁ .. xn) = ⦇ cᵢ (treeDecode x₁) .. (treeDecode xn) ⦈
  decodeClause : Nat → Nat → Name → TC Clause
  decodeClause np i c = do
    args ← drop np <$> argTel c
    let xs = reverse (mapIx const args)
    pure (clause [ vArg (con₂ (quote node) (lit (nat i)) (quoteListP (map (λ _ → var "x") args))) ]
                 (foldl qAp (con₁ (quote just) (con₀ c))
                            (map (λ i → def₁ (quote treeDecode) (var i [])) xs)))

  encodeClauses : Name → TC (List Clause)
  encodeClauses d = do
    cs ← getConstructors d
    np ← getParameters d
    traverse id (mapIx (encodeClause np) cs)

  decodeClauses : Name → TC (List Clause)
  decodeClauses d = do
    cs ← getConstructors d
    np ← getParameters d
    cs ← traverse id (mapIx (decodeClause np) cs)
    pure (cs ++ clause (vArg (var "_") ∷ []) (con₀ (quote nothing)) ∷ [])

  proofClause : Nat → Nat → Name → TC Clause
  proofClause np i c = do
    args ← drop np <$> argTel c
    let xs = reverse (mapIx const args)
    pure (clause [ vArg (con c (map (var "x" <$_) args)) ]
                 (foldl (λ eq eq₁ → def₂ (quote _=*=′_) eq eq₁)
                        (con₀ (quote refl))
                        (map (λ i → def₁ (quote isTreeEmbedding) (var i [])) xs)))

  proofClauses : Name → TC (List Clause)
  proofClauses d = do
    cs ← getConstructors d
    np ← getParameters d
    traverse id (mapIx (proofClause np) cs)

  makeProjection : Name → Clause → Clause
  makeProjection f (clause ps b)      = clause (vArg (proj f) ∷ ps) b
  makeProjection f (absurd-clause ps) = absurd-clause (vArg (proj f) ∷ ps)

  instanceClauses : Name → TC (List Clause)
  instanceClauses d = do
    enc ← encodeClauses d
    dec ← decodeClauses d
    prf ← proofClauses d
    pure (map (makeProjection (quote TreeEncoding.treeEncode)) enc ++
          map (makeProjection (quote TreeEncoding.treeDecode)) dec ++
          map (makeProjection (quote TreeEncoding.isTreeEmbedding)) prf)

deriveTreeEncoding : Name → Name → TC ⊤
deriveTreeEncoding iname dname = do
  declareDef (iArg iname) =<< instanceType dname (quote TreeEncoding)
  defineFun iname =<< instanceClauses dname

-- unquoteDecl EncodeList = deriveTreeEncoding EncodeList (quote List)
