{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
module Generics.SOP.DMapUtilities where

import           Generics.SOP
import           Generics.SOP.NP
import           Generics.SOP.NS    (ap_NS)

import qualified Data.Dependent.Map as DM
import           Data.Dependent.Sum (DSum ((:=>)))
import qualified Data.Dependent.Sum as DS
import           Data.GADT.Compare  ((:~:) (..), GCompare (..), GEq (..),
                                     GOrdering (..))

--import           Data.Type.List (Map)


-- some preliminaries for type-level tags for the constructors of sum types
data TypeListTag (xs :: [k]) (x :: k) where -- x is in xs
  Here  :: TypeListTag (x ': xs) x          -- x begins xs
  There :: TypeListTag xs x -> TypeListTag (y ': xs) x -- given that x is in xs, x is also in (y ': xs)

instance GEq (TypeListTag xs) where
  geq Here      Here      = Just Refl
  geq (There x) (There y) = geq x y
  geq _         _         = Nothing


instance All2 (Compose Eq FieldInfo) xss=> DS.EqTag (TypeListTag xss) ConstructorInfo where
  eqTagged Here      Here      = (==)

instance GCompare (TypeListTag xs) where
  gcompare Here Here = GEQ
  gcompare Here (There _) = GLT
  gcompare (There _) Here = GGT
  gcompare (There x) (There y) = gcompare x y

instance (All2 (Compose Eq FieldInfo) xss
         ,All2 (Compose Ord FieldInfo) xss)=>DS.OrdTag (TypeListTag xss) ConstructorInfo where
  compareTagged Here Here = compare

-- This was tricky!
-- It inserts into a DMap on a shorter type-list, np'
-- The DMap from the shorter list (np') has proofs that the various x are in the shorter list
-- adding a "There" proves that x's are in the list which is one element longer, thus making the
-- new DMap have proofs on the correct list
npToDMap::NP f xs -> DM.DMap (TypeListTag xs) f
npToDMap Nil = DM.empty
npToDMap (fx :* np') = DM.insert Here fx $ DM.mapKeysMonotonic There $ npToDMap np'

type family AddFunctor (f :: * -> *) (xs :: [*]) where
  AddFunctor f '[] = '[]
  AddFunctor f (x ': xs) = f x ': AddFunctor f xs

npUnCompose::SListI xs=>NP (f :.: g) xs -> NP f (AddFunctor g xs)
npUnCompose np = go np where
  go::NP (f :.: g) ys -> NP f (AddFunctor g ys)
  go Nil = Nil
  go (fgx :* np') = unComp fgx :* go np'

{-
type family RemoveFunctor (f :: * -> *) (xs :: [*]) where
  RemoveFunctor f '[] = '[]
  RemoveFunctor f (f x ': xs) = x ': RemoveFunctor f xs

npRecompose::SListI gxs=>NP f gxs -> NP (f :.: g) (RemoveFunctor g gxs)
npRecompose np = go np where
  go::NP f gys -> NP (f :.: g) (RemoveFunctor g gys)
  go Nil = Nil
  go (fgx :* np') = Comp fgx :* go np'
-}

makeTypeListTagNP::SListI xs=>NP (TypeListTag xs) xs
makeTypeListTagNP = go sList where
  go::forall ys.SListI ys=>SList ys->NP (TypeListTag ys) ys
  go SNil = Nil
  go SCons = Here :* hmap There (go sList)


--NB: This can fail since there is no guarantee that the DMap has entries for every tag
--But, the length check is enough since the NP has to be the right length and the DMap entries are
--one per tag
dMapToNP::forall xs f.SListI xs=>DM.DMap (TypeListTag xs) f -> Maybe (NP f xs)
dMapToNP dm = sequence'_NP $ hmap (\tag -> Comp $ DM.lookup tag dm) makeTypeListTagNP

nsToDSum::SListI xs=>NS f xs -> DS.DSum (TypeListTag xs) f
nsToDSum ns =
  let nsFToNSDSum::SListI xs=>NS f xs -> NS (K (DS.DSum (TypeListTag xs) f)) xs
      nsFToNSDSum ns = ap_NS (tagsToFs makeTypeListTagNP) ns
      tagsToFs::SListI xs=>NP (TypeListTag xs) xs -> NP (f -.-> K (DS.DSum (TypeListTag xs) f)) xs
      tagsToFs = hmap (\tag -> (Fn $ \val -> K (tag :=> val)))
  in hcollapse $ nsFToNSDSum ns

dSumToNS::SListI xs=>DS.DSum (TypeListTag xs) f -> NS f xs
dSumToNS (tag :=> fa) = go tag fa where
  go::TypeListTag ys y->f y->NS f ys
  go Here fy = Z fy
  go (There tag') fy = S (go tag' fy)
