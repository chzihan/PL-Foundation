------------------------------------------------------------------------
-- The Agda standard library
--
-- The sublist relation over propositional equality.
------------------------------------------------------------------------

module Data.List.Relation.Sublist.Propositional {a} {A : Set a} where

import Data.List.Relation.Sublist.Setoid as SetoidSublist
open import Relation.Binary.PropositionalEquality using (setoid)

------------------------------------------------------------------------
-- Re-export parameterised definitions from setoid sublists

open SetoidSublist (setoid A) public
