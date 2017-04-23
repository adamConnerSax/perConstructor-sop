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
module Generics.SOP.DMapUtilities where

import           Generics.SOP    (hmap,hcollapse,NS(..),NP(..),SListI(..)
                                 ,SListI2,SList(..),All2,Compose
                                 ,FieldInfo,ConstructorInfo,K(..)
                                 , type (-.->)(Fn), (:.:)(Comp),unComp,Proxy(..))
import           Generics.SOP.NP (sequence'_NP)
import           Generics.SOP.NS    (ap_NS)
import           Generics.SOP.Dict  (Dict(Dict),withDict)
import qualified Data.Dependent.Map as DM
import           Data.Dependent.Sum (DSum ((:=>)))
import qualified Data.Dependent.Sum as DS
import           Data.GADT.Compare  ((:~:) (..), GCompare (..), GEq (..),
                                     GOrdering (..))


import Data.Functor.Identity         (Identity(Identity,runIdentity))
import Data.Maybe (fromJust)


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

npToDMap::NP f xs -> DM.DMap (TypeListTag xs) f
npToDMap Nil = DM.empty
npToDMap (fx :* np') = DM.insert Here fx $ DM.mapKeysMonotonic There $ npToDMap np'

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


-- these are here to allow moving functors in and out of typelists
type family FunctorWrapTypeList (f :: * -> *) (xs :: [*]) :: [*] where
  FunctorWrapTypeList f '[] = '[]
  FunctorWrapTypeList f (x ': xs) = f x ': FunctorWrapTypeList f xs

type family FunctorWrapTypeListOfLists (f :: * -> *) (xss :: [[*]]) :: [[*]] where
  FunctorWrapTypeListOfLists f '[] = '[]
  FunctorWrapTypeListOfLists f (xs ': xss') = FunctorWrapTypeList f xs ': FunctorWrapTypeListOfLists f xss'

npUnCompose::forall f g xs.SListI xs=>NP (f :.: g) xs -> NP f (FunctorWrapTypeList g xs)
npUnCompose np = go np where
  go::NP (f :.: g) ys -> NP f (FunctorWrapTypeList g ys)
  go Nil = Nil
  go (fgx :* np') = unComp fgx :* go np'


npRecompose::forall f g xs.SListI xs=>NP f (FunctorWrapTypeList g xs) -> NP (f :.: g) xs -- (RemoveFunctor g (AddFunctor g xs))
npRecompose = go sList where
  go::forall ys.SListI ys=>SList ys ->  NP f (FunctorWrapTypeList g ys) -> NP (f :.: g) ys
  go SNil Nil = Nil
  go SCons (fgx :* np') = Comp fgx :* go sList np'

nsOfnpRecompose::forall f g xss.(SListI xss, SListI2 xss)=>NS (NP f) (FunctorWrapTypeListOfLists g xss) -> NS (NP (f :.: g)) xss
nsOfnpRecompose = go sList
  where
    go::forall yss.(SListI2 yss, SListI yss)=>SList yss->NS (NP f) (FunctorWrapTypeListOfLists g yss) -> NS (NP (f :.: g)) yss
    go SNil _ = undefined
    go SCons (Z np) = Z (npRecompose np)
    go SCons (S ns') = S (go sList ns')

makeTypeListTagNP::SListI xs=>NP (TypeListTag xs) xs
makeTypeListTagNP = go sList where
  go::forall ys.SListI ys=>SList ys->NP (TypeListTag ys) ys
  go SNil = Nil
  go SCons = Here :* hmap There (go sList)


-- required to prove the wrapped typelist is an instance of SListI
functorWrappedSListIsSList :: forall f xs . SListI xs=>Proxy f -> SList xs -> Dict SListI (FunctorWrapTypeList f xs)
functorWrappedSListIsSList pf SNil  = Dict
functorWrappedSListIsSList pf SCons = goCons (sList :: SList xs)
  where
    goCons :: forall y ys . SList (y ': ys) -> Dict SListI (FunctorWrapTypeList f (y ': ys))
    goCons SCons = withDict (functorWrappedSListIsSList  pf (sList :: SList ys)) Dict


npSequenceViaDMap::forall k (f:: * -> *)  (g:: * -> *) (xs::[*]).(Functor f
                                                                 , SListI xs
                                                                 , DM.GCompare k
                                                                 , k ~ TypeListTag (FunctorWrapTypeList g xs))
  =>(DM.DMap k f -> f (DM.DMap k Identity))->NP (f :.: g) xs -> f (NP g xs)
npSequenceViaDMap sequenceDMap = withDict (functorWrappedSListIsSList (Proxy :: Proxy g) (sList :: SList xs)) $ fmap (hmap (runIdentity . unComp) . npRecompose . fromJust . dMapToNP) .  sequenceDMap . npToDMap . npUnCompose
