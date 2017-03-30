{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
module Generics.SOP.PerConstructor
  (
    MapFieldsAndSequence
  , mapFieldsAndSequence
  , mapFieldsAndSequence'
  , NatAt
  , TransformEach
  , constructorNameList
  , functorToPerConstructorNP
  , functorToPerConstructorList
  , functorDoPerConstructor
  , functorDoPerConstructorWithNames
  , toPerConstructorNP
  , toPerConstructorList
  , doPerConstructor
  , doPerConstructorWithNames
  -- re-exports from generics-sop
  , (:.:)
  , NP
  , K(..)
  , I(..)

  ) where

import           Generics.SOP hiding (Compose)

expand::forall (f :: [k] -> *) xs.(SListI xs)=>NS f xs -> NP (Maybe :.: f) xs
expand ns = go sList (Just ns) where
  go::forall ys.SListI ys => SList ys -> Maybe (NS f ys) -> NP (Maybe :.: f) ys
  go SNil _ = Nil
  go SCons mNS = case mNS of
    Nothing -> Comp Nothing :* go sList Nothing -- after Z
    Just ms -> case ms of
      Z fx -> Comp (Just fx) :* go sList Nothing -- at Z
      S ms' -> Comp Nothing :* go sList (Just ms') -- before Z


expandA::Generic a=>a->NP (Maybe :.: NP I) (Code a)
expandA = expand . unSOP . from

type WrappedProjection (g :: * -> *) (f :: k -> *) (xs :: [k]) = K (g (NP f xs)) -.-> g :.: f

wrappedProjections::forall xs g f.(Functor g,SListI xs) => NP (WrappedProjection g f xs) xs
wrappedProjections = case sList :: SList xs of
  SNil -> Nil
  SCons -> fn (Comp . fmap hd . unK) :* hliftA shiftWrappedProjection wrappedProjections

shiftWrappedProjection :: Functor g=>WrappedProjection g f xs a -> WrappedProjection g f (x ': xs) a
shiftWrappedProjection (Fn f) = Fn $ f . K . fmap tl . unK

type WrappedInjection (g :: * -> *) (f :: k -> *) (xs :: [k]) = g :.: f -.-> K (g (NS f xs))

wrappedInjections::forall xs g f. (Functor g, SListI xs) => NP (WrappedInjection g f xs) xs
wrappedInjections = case sList :: SList xs of
  SNil   -> Nil
  SCons  -> fn (K . fmap Z . unComp) :* hliftA shiftWrappedInjection wrappedInjections

shiftWrappedInjection:: Functor g=>WrappedInjection g f xs a -> WrappedInjection g f (x ': xs) a
shiftWrappedInjection (Fn f) = Fn $ K . fmap S . unK . f

-- NB: For applicative h, this is an inverse of hsequence.  If h is not applicative, then this is not invertible.
distribute::(Functor h, SListI xs)=>h (NP g xs) -> NP (h :.: g) xs
distribute x = hap wrappedProjections (hpure $ K x)

distributeI::(Functor h, SListI xs)=>h (NP I xs) -> NP h xs
distributeI = hmap (fmap unI . unComp) . distribute

functorToNP::forall g a.(Functor g,Generic a)=>g a -> NP (g :.: (Maybe :.: NP I)) (Code a)
functorToNP ga = hap wrappedProjections (hpure $ K (expandA <$> ga))

reAssociate::Functor g=>(g :.: (f :.: h)) a -> ((g :.: f) :.: h) a
reAssociate = Comp . Comp . fmap unComp . unComp

reAssociateNP::(Functor g, SListI xss)=>NP (g :.: (f :.: h)) xss->NP ((g :.: f) :.: h) xss
reAssociateNP = hmap reAssociate

distributeToFields::(Functor g, SListI2 xss)=>NP ((g :.: Maybe) :.: NP I) xss -> POP (g :.: Maybe) xss
distributeToFields =
  let proxyC = Proxy :: Proxy SListI
  in POP . hcliftA proxyC (distributeI . unComp)

reconstructA::(Functor h, Generic a) => NP (h :.: NP I) (Code a) -> NP (K (h a)) (Code a)
reconstructA = hliftA (K . fmap (to . SOP) . unK) . hap wrappedInjections

type MapFieldsAndSequence f h xss = POP f xss -> NP (h :.: NP I) xss

mapFieldsAndSequence::(Applicative h, SListI2 xss)=>(forall a.f a->h a) -> MapFieldsAndSequence f h xss
mapFieldsAndSequence q =
  let sListIC = Proxy :: Proxy SListI
  in hcliftA sListIC (Comp . hsequence) . unPOP . hliftA q

{- Higher-kinded Natural Transformation at the type a -}
class NatAt (f :: k -> *) (h :: k -> *) (a :: k) where
  eta::f a -> h a

mapFieldsAndSequence'::forall f h xss.(Applicative h, SListI2 xss, All2 (NatAt f h) xss)=>MapFieldsAndSequence f h xss
mapFieldsAndSequence' =
  let sListIC = Proxy :: Proxy SListI
      mapIC = Proxy :: Proxy (NatAt f h)
  in hcliftA sListIC (Comp . hsequence) . unPOP . hcliftA mapIC eta


{-
This is the heart of it.  Take a functorial value (Functor g=>g a) and a (possibly restricted?) natural transformation,
(g :.: Maybe) ~> h, and you get a list of [Functor h=>h a], one per constructor of a.
-}
type TransformEach g h xss = NP ((g :.: Maybe) :.: NP I) xss -> NP (h :.: NP I) xss

constructorNameList::forall a.(Generic a, HasDatatypeInfo a)=>Proxy a->[ConstructorName]
constructorNameList = hcollapse . hliftA (K . constructorName) . constructorInfo . datatypeInfo

functorToPerConstructorNP::(Generic a, Functor g, Functor h)=>TransformEach g h (Code a)->g a->NP (K (h a)) (Code a)
functorToPerConstructorNP transform = reconstructA . transform . reAssociateNP . functorToNP

functorToPerConstructorList::(Generic a, Functor g, Functor h)=>TransformEach g h (Code a)->g a->[h a]  -- one per constructor
functorToPerConstructorList transform = hcollapse . functorToPerConstructorNP transform

functorDoPerConstructor::(Generic a, Functor g, Applicative h)=>MapFieldsAndSequence (g :.: Maybe) h (Code a)->g a->[h a]  -- one per constructor
functorDoPerConstructor mapFsAndS = functorToPerConstructorList (mapFsAndS . distributeToFields)

functorDoPerConstructorWithNames::forall a g h.(Generic a, HasDatatypeInfo a, Functor g, Applicative h)
    =>MapFieldsAndSequence (g :.: Maybe) h (Code a)
    ->g a
    ->[(ConstructorName,h a)]  -- one per constructor
functorDoPerConstructorWithNames mapFsAndS ga =
  let conNames = constructorNameList (Proxy :: Proxy a)-- hcollapse . hliftA (K . constructorName) . constructorInfo $ datatypeInfo (Proxy :: Proxy a)  -- [ConstructorName]
  in zip conNames (functorDoPerConstructor mapFsAndS ga)


toPerConstructorNP::(Generic a, Functor h)=>TransformEach I h (Code a)->a->NP (K (h a)) (Code a)
toPerConstructorNP t a = functorToPerConstructorNP t (I a)

toPerConstructorList::(Generic a, Functor h)=>TransformEach I h (Code a)->a->[h a]  -- one per constructor
toPerConstructorList t a = functorToPerConstructorList t (I a)

doPerConstructor::(Generic a, Applicative h)=>MapFieldsAndSequence (I :.: Maybe) h (Code a)->a->[h a]  -- one per constructor
doPerConstructor mfs a = functorDoPerConstructor mfs (I a)


doPerConstructorWithNames::forall a h.(Generic a, HasDatatypeInfo a, Applicative h)
  =>MapFieldsAndSequence (I :.: Maybe) h (Code a)
  ->a
  ->[(ConstructorName,h a)]  -- one per constructor
doPerConstructorWithNames mapFsAndS a = functorDoPerConstructorWithNames mapFsAndS (I a)