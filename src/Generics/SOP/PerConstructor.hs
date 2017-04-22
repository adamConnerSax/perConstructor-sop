{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE TypeOperators              #-}
module Generics.SOP.PerConstructor
  (
    MapFieldsAndSequence
  , mapFieldsAndSequence
  , mapFieldsFromConstraintAndCustomSequence
  , mapFieldsFromConstraintAndSequence
--  , NatAt(..)
  , TransformEach
  , functorToPerConstructorNP
  , functorToPerConstructorList
  , functorToPerConstructorList'
  , functorDoPerConstructor
  , functorDoPerConstructor'
  , functorDoPerConstructorWithNames
  , functorDoPerConstructorWithNames'  
  , toPerConstructorNP
  , toPerConstructorList
  , toPerConstructorList'
  , doPerConstructor
  , doPerConstructor'
  , doPerConstructorWithNames
  , doPerConstructorWithNames'
  -- metadata utils
  , constructorNameList
  , getFieldNames
  , maybeFieldNamePOP
  , constructorData
  -- re-exports from generics-sop
  , Generic
  , HasDatatypeInfo
  , ConstructorName
  , (:.:)(Comp)
  , unComp
  , I(..)
  , Code
  , All2
  , Dict(..)
  ) where

import           Generics.SOP.Distribute

import           Generics.SOP hiding (Compose)
import           Generics.SOP.Dict   (Dict,pureAll2)

import           Control.Arrow (first, (&&&))
import           Data.Proxy (Proxy(Proxy))


type MapFieldsAndSequence f h xss = POP f xss -> NP (h :.: NP I) xss

mapFieldsAndSequence::(Applicative h, SListI2 xss)=>(forall a.f a->h a) -> MapFieldsAndSequence f h xss
mapFieldsAndSequence q = mapFieldsFromConstraintAndCustomSequence pureAll2 q hsequence

mapFieldsFromConstraintAndSequence::forall c f h xss.(Applicative h, SListI2 xss)
  =>Dict (All2 c) xss -- constraint for the field mappings
  ->(forall a.c a=>f a -> h a) -- function for the field mappings
  ->(forall xs.SListI xs=>NP h xs -> h (NP I xs)) -- sequencing function
  ->MapFieldsAndSequence f h xss
mapFieldsFromConstraintAndSequence dict fn sequence = mapFieldsFromConstraintAndCustomSequence dict fn hsequence


{-
{- Higher-kinded Natural Transformation at the type a -}
class NatAt (f :: k -> *) (h :: k -> *) (a :: k) where
  eta::f a -> h a
-}

--mapFieldsAndSequence'::forall f h xss.(Applicative h, SListI2 xss, All2 (NatAt f h) xss)=>MapFieldsAndSequence f h xss
--mapFieldsAndSequence' = mapFieldsAndCustomSequence hsequence

mapFieldsFromConstraintAndCustomSequence::forall c f h xss.SListI2 xss
  =>Dict (All2 c) xss -- constraint for the field mappings
  ->(forall a.c a=>f a -> h a) -- function for the field mappings
  ->(forall xs.SListI xs=>NP h xs -> h (NP I xs)) -- sequencing function
  ->MapFieldsAndSequence f h xss
mapFieldsFromConstraintAndCustomSequence dict fn sequence = 
  let sListIC = Proxy :: Proxy SListI
  in hcliftA sListIC (Comp . sequence) . unPOP . mapFieldsFromConstraint dict fn

mapFieldsFromConstraint::forall c f h xss.SListI2 xss=>Dict (All2 c) xss -> (forall a.c a=>f a -> h a) -> POP f xss -> POP h xss
mapFieldsFromConstraint d fn = hap (functionPOPFromClass d fn) 


{-
mapFieldsAndCustomSequence::forall f h xss.(Applicative h, SListI2 xss, All2 (NatAt f h) xss)=>(forall xs.SListI xs=>NP h xs -> h (NP I xs))->MapFieldsAndSequence f h xss
mapFieldsAndCustomSequence customSequence =
  let sListIC = Proxy :: Proxy SListI
      mapIC = Proxy :: Proxy (NatAt f h)
  in hcliftA sListIC (Comp . customSequence) . unPOP . hcliftA mapIC eta
-}


{-
This is the heart of it.  Take a functorial value (Functor g=>g a) and a (possibly restricted?) natural transformation,
(g :.: Maybe) ~> h, and you get a list of [Functor h=>h a], one per constructor of a.
-}
type TransformEach g h xss = NP ((g :.: Maybe) :.: NP I) xss -> NP (h :.: NP I) xss

functorToPerConstructorNP::(Generic a, Functor g, Functor h)=>TransformEach g h (Code a)->g a->NP (K (h a)) (Code a)
functorToPerConstructorNP transform = reconstructA . transform . reAssociateNP . functorToNP

functorToPerConstructorList::(Generic a, Functor g, Functor h)=>TransformEach g h (Code a)->g a->[h a]  -- one per constructor
functorToPerConstructorList transform = hcollapse . functorToPerConstructorNP transform

functorToPerConstructorList'::(Generic a, Functor g, Functor h)=>TransformEach g h (Code a)->g a->[(g (Maybe a), h a)]  -- one per constructor
functorToPerConstructorList' transform ga =
  let origSplit = unComp <$> (hcollapse $ functorToPerConstructorNP id ga)
      transformed = hcollapse $ functorToPerConstructorNP transform ga
  in zip origSplit transformed

functorDoPerConstructor::(Generic a, Functor g, Applicative h)=>MapFieldsAndSequence (g :.: Maybe) h (Code a)->g a->[h a]  -- one per constructor
functorDoPerConstructor mapFsAndS = functorToPerConstructorList (mapFsAndS . distributeToFields)

functorDoPerConstructor'::(Generic a, Functor g, Applicative h)=>MapFieldsAndSequence (g :.: Maybe) h (Code a)->g a->[(g (Maybe a), h a)]  
functorDoPerConstructor' mapFsAndS = functorToPerConstructorList' (mapFsAndS . distributeToFields)

functorDoPerConstructorWithNames::forall a g h.(Generic a, HasDatatypeInfo a, Functor g, Applicative h)
    =>MapFieldsAndSequence (g :.: Maybe) h (Code a)
    ->g a
    ->[(ConstructorName,h a)]  -- one per constructor
functorDoPerConstructorWithNames mapFsAndS ga =
  let conNames = constructorNameList (Proxy :: Proxy a)-- hcollapse . hliftA (K . constructorName) . constructorInfo $ datatypeInfo (Proxy :: Proxy a)  -- [ConstructorName]
  in zip conNames (functorDoPerConstructor mapFsAndS ga)

functorDoPerConstructorWithNames'::forall a g h.(Generic a, HasDatatypeInfo a, Functor g, Applicative h)
    =>MapFieldsAndSequence (g :.: Maybe) h (Code a)
    ->g a
    ->[(ConstructorName,g (Maybe a), h a)]  -- one per constructor
functorDoPerConstructorWithNames' mapFsAndS ga =
  let conNames = constructorNameList (Proxy :: Proxy a)-- hcollapse . hliftA (K . constructorName) . constructorInfo $ datatypeInfo (Proxy :: Proxy a)  -- [ConstructorName]
  in zipWith (\name (o,t) -> (name,o,t)) conNames (functorDoPerConstructor' mapFsAndS ga)

toPerConstructorNP::(Generic a, Functor h)=>TransformEach I h (Code a)->a->NP (K (h a)) (Code a)
toPerConstructorNP t a = functorToPerConstructorNP t (I a)

toPerConstructorList::(Generic a, Functor h)=>TransformEach I h (Code a)->a->[h a]  -- one per constructor
toPerConstructorList t a = functorToPerConstructorList t (I a)

toPerConstructorList'::(Generic a, Functor h)=>TransformEach I h (Code a)->a->[(Maybe a, h a)]  -- one per constructor
toPerConstructorList' t a = first unI <$> functorToPerConstructorList' t (I a)

doPerConstructor::(Generic a, Applicative h)=>MapFieldsAndSequence (I :.: Maybe) h (Code a)->a->[h a]  -- one per constructor
doPerConstructor mfs a = functorDoPerConstructor mfs (I a)

doPerConstructor'::(Generic a, Applicative h)=>MapFieldsAndSequence (I :.: Maybe) h (Code a)->a->[(Maybe a, h a)]  -- one per constructor
doPerConstructor' mfs a = first unI <$> functorDoPerConstructor' mfs (I a)

doPerConstructorWithNames::forall a h.(Generic a, HasDatatypeInfo a, Applicative h)
  =>MapFieldsAndSequence (I :.: Maybe) h (Code a)
  ->a
  ->[(ConstructorName,h a)]  -- one per constructor
doPerConstructorWithNames mapFsAndS a = functorDoPerConstructorWithNames mapFsAndS (I a)

doPerConstructorWithNames'::forall a h.(Generic a, HasDatatypeInfo a, Applicative h)
  =>MapFieldsAndSequence (I :.: Maybe) h (Code a)
  ->a
  ->[(ConstructorName,Maybe a, h a)]  -- one per constructor
doPerConstructorWithNames' mapFsAndS a =
  let f (n,io,t) = (n,unI io,t)
  in f <$> functorDoPerConstructorWithNames' mapFsAndS (I a)


-- metadata utils
npConInfo::forall a.(Generic a, HasDatatypeInfo a)=>Proxy a->NP ConstructorInfo (Code a)
npConInfo = constructorInfo . datatypeInfo

constructorNameList::forall a.(Generic a, HasDatatypeInfo a)=>Proxy a->[ConstructorName]
constructorNameList = hcollapse . hliftA (K . constructorName) . npConInfo 

getFieldNames::SListI xs=>ConstructorInfo xs -> NP (K (Maybe FieldName)) xs
getFieldNames ci = case ci of
                     Record _ npfi -> hmap (\(FieldInfo name) -> K (Just name)) npfi
                     _             -> hpure (K Nothing)

maybeFieldNamePOP::(Generic a, HasDatatypeInfo a)=>Proxy a->POP (K (Maybe FieldName)) (Code a)  
maybeFieldNamePOP proxy =
  let sListIC = Proxy :: Proxy SListI
  in POP $ hcliftA sListIC getFieldNames (npConInfo proxy) -- POP (K (Maybe FieldName)) (Code a)

constructorData::(Generic a, HasDatatypeInfo a)=>Proxy a -> ([ConstructorName],POP (K (Maybe FieldName)) (Code a))                        
constructorData proxy =
  let npci = npConInfo proxy
      sListIC = Proxy :: Proxy SListI
      conList = hcollapse $ hliftA (K . constructorName)  npci
      mFieldNamePOP = POP $ hcliftA sListIC getFieldNames npci -- POP (K (Maybe FieldName)) (Code a)
  in (conList, mFieldNamePOP)
