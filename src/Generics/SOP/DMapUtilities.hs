{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

{-# LANGUAGE DeriveGeneric #-}
{-|
Module           : Generics.SOP.DMapUtilities
Description      : Utilities for converting between the NS/NP types of generics-sop and Dependent Maps.
Copyright        : Adam Conner-Sax, 2017
License          : BSD-style (see LICENSE)
Maintainer       : Adam Conner-Sax (adam_conner_sax@yahoo.com)
Stability        : Experimental
-}

module Generics.SOP.DMapUtilities
  (
    -- * Type Functions
    FunctorWrapTypeList
  , FunctorWrapTypeListOfLists
  , TypeListContains
  , TypeListConstructs
  
    -- * Tags
  , TypeListTag (..)
  , makeTypeListTagNP
  , makeProductOfAllTypeListTags
  
    -- * Conversions
    -- ** 'NP' \<-\> 'DM.DMap'
  , npToDMap
  , dMapToNP
    -- ** 'NS' \<-\> 'DSum'
  , nsToDSum
  , dSumToNS
  
  -- * Functor wrapping/unwrapping utilities for 'NP' 
  , npUnCompose
  , nsUnCompose
  , nsOfnpUnCompose
  , npReCompose
  , nsReCompose
  , nsOfnpReCompose
  
  -- * Utilities
  , npSequenceViaDMap
  , selectTypedFromNP
  
  -- * Proofs
  , functorWrappedSListIsSList
  ) where

import           Generics.SOP          (hmap, hcollapse, NS(..), NP(..), SListI(..)
                                       ,SListI2, SList(..), All2, Compose
                                       ,FieldInfo, ConstructorInfo, K(..), I (I), unI, Code (..), hliftA
                                       , type (-.->)(Fn), (:.:)(Comp), unComp, Proxy(..), SOP (SOP), unSOP)
import           Generics.SOP.NP       (sequence'_NP)
import           Generics.SOP.NS       (ap_NS)
import           Generics.SOP.Dict     (Dict(Dict),withDict)

import qualified Data.Dependent.Map as DM
import           Data.Dependent.Map    (DMap)
import           Data.Dependent.Sum    (DSum ((:=>)))
import qualified Data.Dependent.Sum as DS

import           Data.GADT.Compare     ((:~:) (..), GCompare (..), GEq (..),
                                        GOrdering (..))
import qualified Data.Type.Bool as B
import qualified Data.Type.Equality as B
import           Data.Proxy (Proxy (..))

import Data.Functor.Identity           (Identity(Identity,runIdentity))

import qualified GHC.Generics as GHCG
import Generics.SOP (Generic)

-- |A Tag type for making a 'DM.DMap' keyed by a type-level list
data TypeListTag (xs :: [k]) (x :: k) where -- x is in xs
  TLHead  :: TypeListTag (x ': xs) x          -- x begins xs
  TLTail :: TypeListTag xs x -> TypeListTag (y ': xs) x -- given that x is in xs, x is also in (y ': xs)

instance GEq (TypeListTag xs) where
  geq TLHead      TLHead      = Just Refl
  geq (TLTail x) (TLTail y) = geq x y
  geq _         _         = Nothing

instance GCompare (TypeListTag xs) where
  gcompare TLHead TLHead = GEQ
  gcompare TLHead (TLTail _) = GLT
  gcompare (TLTail _) TLHead = GGT
  gcompare (TLTail x) (TLTail y) = gcompare x y

-- |Convert an 'NP' indexed by typelist xs into a 'DM.DMap' indexed by 'TypeListTag' xs
npToDMap::NP f xs -> DM.DMap (TypeListTag xs) f
npToDMap Nil = DM.empty
npToDMap (fx :* np') = DM.insert TLHead fx $ DM.mapKeysMonotonic TLTail $ npToDMap np'

-- |Convert a 'DM.DMap' indexed by 'TypeListTag' xs to an 'NP'
-- |NB: This can fail since there is no guarantee that the 'DM.DMap' has entries for every tag. Hence it returns a 'Maybe'
dMapToNP::forall xs f.SListI xs=>DM.DMap (TypeListTag xs) f -> Maybe (NP f xs)
dMapToNP dm = sequence'_NP $ hmap (\tag -> Comp $ DM.lookup tag dm) makeTypeListTagNP

-- |Convert a 'NS' indexed by a typelist xs to a 'DS.DSum' indexed by 'TypeListTag' xs 
nsToDSum::SListI xs=>NS f xs -> DS.DSum (TypeListTag xs) f
nsToDSum ns =
  let nsFToNSDSum::SListI xs=>NS f xs -> NS (K (DS.DSum (TypeListTag xs) f)) xs
      nsFToNSDSum ns' = ap_NS (tagsToFs makeTypeListTagNP) ns'
      tagsToFs::SListI xs=>NP (TypeListTag xs) xs -> NP (f -.-> K (DS.DSum (TypeListTag xs) f)) xs
      tagsToFs = hmap (\tag -> (Fn $ \val -> K (tag :=> val)))
  in hcollapse $ nsFToNSDSum ns

-- |Convert a 'DS.DSum' indexed by 'TypeListTag' xs into a 'NS' indexed by xs
dSumToNS::SListI xs=>DS.DSum (TypeListTag xs) f -> NS f xs
dSumToNS (tag :=> fa) = go tag fa where
  go::TypeListTag ys y->f y->NS f ys
  go TLHead fy = Z fy
  go (TLTail tag') fy = S (go tag' fy)

toPerConstructorDSum :: Generic a => a -> DS.DSum (TypeListTag (Code a)) (NP I)
toPerConstructorDSum = nsToDSum . unSOP . from

fromPerConstructorDSum :: Generic a => DS.DSum (TypeListTag (Code a)) (NP I) -> a
fromPerConstructorDSum = to . SOP . dSumToNS

toPerConstructorIdentityDSum :: forall a. Generic a => a -> DS.DSum (TypeListTag (FunctorWrapTypeList (NP I) (Code a))) Identity
toPerConstructorIdentityDSum =
  withDict (functorWrappedSListIsSList (Proxy :: Proxy (NP I)) (sList :: SList (Code a))) $
  nsToDSum . nsUnCompose . hmap (Comp . Identity) . unSOP . from

fromPerConstructorIdentityDSum :: forall a. Generic a => DS.DSum (TypeListTag (FunctorWrapTypeList (NP I) (Code a))) Identity -> a
fromPerConstructorIdentityDSum =
  withDict (functorWrappedSListIsSList (Proxy :: Proxy (NP I)) (sList :: SList (Code a))) $
  to . SOP . hmap (runIdentity . unComp) . nsReCompose . dSumToNS


-- | Make an NP of TypeListTag xs for a typelist xs. 
makeTypeListTagNP::SListI xs=>NP (TypeListTag xs) xs
makeTypeListTagNP = go sList where
  go::forall ys.SListI ys=>SList ys->NP (TypeListTag ys) ys
  go SNil = Nil
  go SCons = TLHead :* hmap TLTail (go sList)

-- these are here to allow moving functors in and out of typelists
type family FunctorWrapTypeList (f :: k1 -> k2) (xs :: [k1]) :: [k2] where
  FunctorWrapTypeList f '[] = '[]
  FunctorWrapTypeList f (x ': xs) = f x ': FunctorWrapTypeList f xs

type family FunctorWrapTypeListOfLists (f :: k1 -> k2) (xss :: [[k1]]) :: [[k2]] where
  FunctorWrapTypeListOfLists f '[] = '[]
  FunctorWrapTypeListOfLists f (xs ': xss') = FunctorWrapTypeList f xs ': FunctorWrapTypeListOfLists f xss'

-- | Transform a type-list indexed product of composed functorial values into a type-list indexed product of functorial values where the inner part of the functor
-- composition has been moved to the type-list.  The values in the product remain the same (up to types representing composition of the functors). E.g.,
--
-- > (f :.: g) 2 :* (f :.: g) 3.0 :* 'Nil :: NP (f :.: g) '[Int,Double] -> f (g 2) :* f (g 3.0) :* 'Nil :: NP f '[g Int, g Double]
npUnCompose :: forall f g (xs :: [k]) . SListI xs=>NP (f :.: g) xs -> NP f (FunctorWrapTypeList g xs)
npUnCompose np = go np where
  go::NP (f :.: g) ys -> NP f (FunctorWrapTypeList g ys)
  go Nil = Nil
  go (fgx :* np') = unComp fgx :* go np'

nsUnCompose :: forall f g (xs :: [k]). SListI xs => NS (f :.: g) xs -> NS f (FunctorWrapTypeList g xs)
nsUnCompose = go sList where
  go :: forall ys. SListI ys => SList ys -> NS (f :.: g) ys -> NS f (FunctorWrapTypeList g ys)
  go SNil _ = error "An NS cannot be empty"
  go SCons (Z fgx) = Z $ unComp fgx
  go SCons (S ns') = S $ go sList ns'

  
nsOfnpUnCompose :: forall f g xss. (SListI xss, SListI2 xss)=>NS (NP (f :.: g)) xss -> NS (NP f) (FunctorWrapTypeListOfLists g xss)
nsOfnpUnCompose = go sList where
  go::forall yss. (SListI yss, SListI2 yss) => SList yss -> NS (NP (f :.: g)) yss -> NS (NP f) (FunctorWrapTypeListOfLists g yss)
  go SNil _ = error "An NS cannot be empty"
  go SCons (Z np) = Z (npUnCompose np)
  go SCons (S ns') = S (go sList ns') 

-- | The inverse of 'npUnCompose'.  Given a type-list indexed product where all the types in the list are applications of the same functor,
-- remove that functor from all the types in the list and put it in the functor parameter of the 'NP'.  The values in the product itself remain the same up
-- to types representing composition of the functors.
npReCompose :: forall f g (xs :: [k]). SListI xs=>NP f (FunctorWrapTypeList g xs) -> NP (f :.: g) xs -- (RemoveFunctor g (AddFunctor g xs))
npReCompose = go sList where
  go :: forall ys. SListI ys=>SList ys ->  NP f (FunctorWrapTypeList g ys) -> NP (f :.: g) ys
  go SNil Nil = Nil
  go SCons (fgx :* np') = Comp fgx :* go sList np'

nsReCompose :: forall f g (xs :: [k]). SListI xs => NS f (FunctorWrapTypeList g xs) -> NS (f :.: g) xs
nsReCompose = go sList
  where
    go :: forall ys. SListI ys => SList ys -> NS f (FunctorWrapTypeList g ys) -> NS (f :.: g) ys
    go SNil _ = error "NS can't be empty (in nsReCompose)."
    go SCons (Z fgx) = Z $ Comp fgx
    go SCons (S ns') = S $ go sList ns'

-- | ReCompose all the 'NP's in an "NS (NP f) xss".
nsOfnpReCompose :: forall f g xss. (SListI xss, SListI2 xss)=>NS (NP f) (FunctorWrapTypeListOfLists g xss) -> NS (NP (f :.: g)) xss
nsOfnpReCompose = go sList
  where
    go::forall yss.(SListI2 yss, SListI yss)=>SList yss->NS (NP f) (FunctorWrapTypeListOfLists g yss) -> NS (NP (f :.: g)) yss
    go SNil _ = undefined -- this shouldn't' happen since an NS can't be empty
    go SCons (Z np) = Z (npReCompose np)
    go SCons (S ns') = S (go sList ns')

-- | Prove that "SListI xs=>(FunctorWrapTypeList f xs)" is also an instance of SListI
functorWrappedSListIsSList :: forall f xs . SListI xs=>Proxy f -> SList xs -> Dict SListI (FunctorWrapTypeList f xs)
functorWrappedSListIsSList pf SNil  = Dict
functorWrappedSListIsSList pf SCons = goCons (sList :: SList xs)
  where
    goCons :: forall y ys . SList (y ': ys) -> Dict SListI (FunctorWrapTypeList f (y ': ys))
    goCons SCons = withDict (functorWrappedSListIsSList  pf (sList :: SList ys)) Dict

-- | sequence (in the sense of 'Data.Traversable.sequenceA') a functor f inside an 'NP' using a function defined over a 'DM.DMap' indexed by the same type-level-list.
-- This is useful in cases where an efficient general solution exists for DMaps.
-- This can be done more simply for Applicative f but the efficiency will depend on the particular functor and given function over 'DM.DMap'.
npSequenceViaDMap::forall k (f:: * -> *)  (g:: * -> *) (xs::[*]).(Functor f
                                                                 , SListI xs
                                                                 , DM.GCompare k
                                                                 , k ~ TypeListTag (FunctorWrapTypeList g xs))
  =>(DM.DMap k f -> f (DM.DMap k Identity))->NP (f :.: g) xs -> f (NP g xs)
npSequenceViaDMap sequenceDMap =
  withDict (functorWrappedSListIsSList (Proxy :: Proxy g) (sList :: SList xs)) $
  fmap (hmap (runIdentity . unComp) . npReCompose . (\(Just x)->x) . dMapToNP) .  sequenceDMap . npToDMap . npUnCompose
-- NB: THe (\Just x -> x) in there is safe!
-- dMapToNP has to return Maybe NP since the DMap could be incomplete.
-- But since we built this DMap from an NP, we know it's complete and dMapToNp will return a Just.  

--

type family TypeListContains (xs :: [k]) (x :: k) :: Bool where
  TypeListContains '[] _ = False
  TypeListContains (y ': ys) x = (x B.== y) B.|| TypeListContains ys x

type family TypeListConstructs (a :: k) :: [k] where
  TypeListConstructs a = a ': '[]

selectTypedFromNP :: (Functor g, Generic a, Code a ~ TypeListConstructs xs, SListI xs, SListI2 xss) => NP (g :.: NP I) xss -> TypeListTag xss xs -> g a
selectTypedFromNP np tag = to . SOP . Z <$> selectFromNP np tag

selectFromNP :: forall g xss xs. (Functor g, SListI2 xss, SListI xs) => NP (g :.: NP I) xss -> TypeListTag xss xs -> g (NP I xs)
selectFromNP np tag = go np tag
  where
    go :: NP (g :.: NP I) yss -> TypeListTag yss ys -> g (NP I ys)
    go Nil _ = error "Reached the end of typelist before the tag was satified."
    go (gy :* _) TLHead = unComp gy
    go (_ :* npTail) (TLTail tailTag) = go npTail tailTag


-- | make the product of all tags for b and then put them into a type, a, isomorphic to that product. Probably a tuple.
makeProductOfAllTypeListTags :: forall a b. ( Generic b
                                            , Generic a
                                            , (Code a) ~ TypeListConstructs (FunctorWrapTypeList (TypeListTag (Code b)) (Code b))
                                            ) => Proxy b -> a
makeProductOfAllTypeListTags _ =
  let tags :: NP (TypeListTag (Code b)) (Code b)
      tags = makeTypeListTagNP
  in to . SOP . Z $ npUnCompose $ hliftA (Comp . I) tags



-- this compiles without the TypeListContains constraint but that seems bad.  Unless:
-- does TypeListTag (Code b) (Constructs a) only exist if TLContains (Code b) (Constructs a) ~ True ??
wrapOne :: ( Generic b
           , TypeListContains (Code b) (TypeListConstructs a) ~ True
           ) => TypeListTag (Code b) (TypeListConstructs a) -> a -> b
wrapOne tag = to . SOP . matchNS tag  
  where
    matchNS :: TypeListTag xss (TypeListConstructs a) -> a -> NS (NP I) xss 
    matchNS TLHead x = Z $ I x :* Nil 
    matchNS (TLTail tagTail) x = S $ matchNS tagTail x

wrapLikeFields :: ( Generic b
                  , Generic a
                  , Code a ~ TypeListConstructs c
                  , TypeListContains (Code b) c ~ True
                  )=> TypeListTag (Code b) c -> a -> b
wrapLikeFields tag = to . SOP . matchNS tag . stripNS . unSOP . from 
  where
    stripNS :: NS (NP I) (ys ': yss) -> NP I ys
    stripNS (Z np) = np
    stripNS _ = error "Impossible case in wrapLikeFields!"
    matchNS :: TypeListTag xss xs -> NP I xs -> NS (NP I) xss 
    matchNS TLHead = Z
    matchNS (TLTail tagTail) = S . matchNS tagTail


-- for example
data Example = A1 A | A2 B | A3 Int | A4 Int String deriving (GHCG.Generic)
instance Generic Example

(a1Tag, a2Tag, a3Tag, a4Tag) = makeProductOfAllTypeListTags (Proxy :: Proxy Example)

data A = A Int
data B = B String

ex1 :: Example
ex1 = wrapOne a1Tag (A 2)

ex2 :: Example
ex2 = wrapOne a2Tag (B "Hello")

ex3 :: Example
ex3 = wrapOne a3Tag 2

ex4 :: Example
ex4 = wrapLikeFields a4Tag (2,"Hello")


{-
-- This fails.  We need a different function here.  See above.
ex4 :: Example
ex4 = wrapOne (TLTail $ TLTail $ TLTail TLHead) (2,"Hello")

but...
-}


--




