{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
module Generics.SOP.Aeson where

import           Generics.SOP               ((:.:) (Comp), All, All2, Code,
                                             Generic, I (I), K (K),
                                             NP ((:*), Nil), NS (S, Z),
                                             Proxy (Proxy), SList (SCons, SNil),
                                             SListI (sList), SListI2, SOP (SOP),
                                             hcmap, hcollapse, hmap, hsequence,
                                             unComp, unI, unK, unSOP)
import           Generics.SOP.Dict          (withDict)
import           Generics.SOP.NS            (collapse_NS, index_NS)

import qualified Data.Dependent.Sum         as DS

import           Generics.SOP.Distribute    (expandA)
import           Generics.SOP.DMapUtilities (FunctorWrapTypeList,
                                             TypeListConstructs,
                                             TypeListTag (..), dSumToNS,
                                             functorWrappedSListIsSList,
                                             nsReCompose, nsToDSum, nsUnCompose,
                                             selectTypedFromNP)

import           Data.Aeson                 (FromJSON (..), ToJSON (..), Value,
                                             object, pairs, withObject, (.:),
                                             (.=))
import           Data.Aeson.Types           (Parser)
import           Data.Functor.Identity      (Identity (Identity), runIdentity)
import           Data.Monoid                ((<>))

instance All ToJSON xs => ToJSON (NP I xs) where
  toJSON = toJSON . hcollapse . hcmap (Proxy :: Proxy ToJSON) (K . toJSON . unI)
  toEncoding = toEncoding . hcollapse . hcmap (Proxy :: Proxy ToJSON) (K . toJSON . unI)

instance All FromJSON xs => FromJSON (NP I xs) where
  parseJSON v = do
    valList <- parseJSONList v
    case buildNPKFromList valList of
      Just npVal -> hsequence $ hcmap (Proxy :: Proxy FromJSON) (parseJSON . unK) npVal
      Nothing -> fail "parsed list too short in FromJSON (NP I xs)"

instance All ToJSON xs => ToJSON (NS I xs) where
  toJSON ns =
    let index = index_NS ns
        val = collapse_NS $ hcmap (Proxy :: Proxy ToJSON) (K . toJSON . unI) ns
    in  object ["tag" .= index, "value" .= val]

  toEncoding ns =
    let index = index_NS ns
        val = collapse_NS $ hcmap (Proxy :: Proxy ToJSON) (K . toJSON . unI) ns
    in  pairs ("tag" .= index <> "value" .= val)

instance All FromJSON xs => FromJSON (NS I xs) where
  parseJSON = withObject "NS I" $ \v -> do
    tag <- v .: "tag"
    value <- v .: "value" -- remains unparsed here
    case indexToNS tag value of
      Just ns -> hsequence $ hcmap (Proxy :: Proxy FromJSON) (parseJSON . unK) ns
      Nothing -> fail $ "index (" ++ show tag ++ ") indexToNS failed while parsing (NS I xs)."

instance (SListI2 xss, All2 ToJSON xss) => ToJSON (SOP I xss) where
  toJSON sop =
    let val = hcollapse $ hcmap (Proxy :: Proxy ToJSON) (K . toJSON . unI) sop
        index = index_NS $ unSOP sop
    in object ["tag" .= index, "value" .= val]

  toEncoding sop =
    let val = hcollapse $ hcmap (Proxy :: Proxy ToJSON) (K . toJSON . unI) sop
        index = index_NS $ unSOP sop
    in pairs ("tag" .= index <> "value" .= val)

instance (SListI2 xss, All2 FromJSON xss) => FromJSON (SOP I xss) where
  parseJSON = withObject "SOP I xss" $ \v -> do
    index <- v .: "tag"
    listOfVals <- v .: "value"
    case indexToSOP index listOfVals of
      Nothing -> fail "Error in indexToSOP.  Could be bad index or val list too short."
      Just sopVal -> hsequence $ hcmap (Proxy :: Proxy FromJSON) (parseJSON . unK) sopVal

instance (All2 ToJSON xss, SListI2 xss) => ToJSON (DS.DSum (TypeListTag xss) (NP I)) where
  toJSON = toJSON . SOP . dSumToNS

instance (All2 FromJSON xss, SListI2 xss) => FromJSON (DS.DSum (TypeListTag xss) (NP I)) where
  parseJSON = fmap (nsToDSum . unSOP) . parseJSON

{-
newtype WrappedTypeList f xss = WrappedTypeList (FunctorWrapTypeList f xss)

instance (All2 ToJSON xss, SListI2 xss) => ToJSON (DS.DSum (TypeListTag yss) Identity) where
  toJSON =
    withDict (functorWrappedSListIsSList (Proxy :: Proxy (NP I)) (sList :: SList xss)) $
    toJSON . SOP . hmap (runIdentity . unComp) . nsReCompose . dSumToNS

instance (All2 FromJSON xss, SListI2 xss, yss ~ (FunctorWrapTypeList (NP I) xss)) => FromJSON (DS.DSum (TypeListTag yss) Identity) where
  parseJSON =
    withDict (functorWrappedSListIsSList (Proxy :: Proxy (NP I)) (sList :: SList xss)) $
    fmap (nsToDSum . nsUnCompose . hmap (Comp. Identity) . unSOP) . parseJSON
-}

-- NB: This can fail if the index is >= length of the type-list, hence the Maybe return type
-- NB: This can fail if the list [a] is shorter then the type-list for the NP
indexToSOP :: SListI2 xss => Int -> [a] -> Maybe (SOP (K a) xss)
indexToSOP n xs = SOP <$> go sList n xs
  where
    go :: SListI2 yss => SList yss -> Int -> [a] -> Maybe (NS (NP (K a)) yss)
    go SNil _ _   = Nothing -- "Bad index in indexToNS"
    go SCons 0 xs = buildNPKFromList xs >>= Just . Z
    go SCons n xs = go sList (n-1) xs >>= Just . S

-- NB: This can fail if the list [a] is shorter then the type-list for the NP
buildNPKFromList :: SListI xs => [a] -> Maybe (NP (K a) xs)
buildNPKFromList as = go sList as
  where
    go :: SListI ys => SList ys -> [a] -> Maybe (NP (K a) ys)
    go SNil _  = Just Nil
    go SCons [] = Nothing
    go SCons (a : as') = case go sList as' of
      Just npTail -> Just $ K a :* npTail
      Nothing     -> Nothing

-- NB: This can fail if the index is >= length of the type-list, hence the Maybe return type
indexToNS :: SListI xs => Int -> a -> Maybe (NS (K a) xs)
indexToNS n x = go sList n x
  where
    go :: SListI ys => SList ys -> Int -> a -> Maybe (NS (K a) ys)
    go SNil _ _  = Nothing -- "Bad index in indexToNS"
    go SCons 0 x = Just $ Z $ K x
    go SCons n x = go sList (n-1) x >>= Just . S

---

selectUnary :: (Generic a, Generic b, Code b ~ TypeListConstructs xb) => TypeListTag (Code a) xb -> a -> Maybe b
selectUnary tag = flip selectTypedFromNP tag . expandA

{-
type Requests = Req1 Int | Req2 Double | Req3 Bool
type Responses = Resp1 Bool | Resp2 Double | Resp3 String

type family ResponseTagArg where
  ResponseTagArg

type Server m a b = a -> m b



(reqTag1, reqTag2, reqTag3) = makeProductOfAllTypeListTags (Proxy :: Proxy Requests)
(respTag1, respTag2, respTag3) = makeProductOfAllTypeListTags (Proxy :: Proxy Responses)

responseTag :: TypeListTag (Code Requests) xa -> TypeListTag (Code Responses) xb
responseTag reqTag1 = respTag1
responseTag reqTag2 = respTag2
responseTag reqTag3 = respTag3

doRequest :: (Code a ~ TypeListConstructs xa) => Server m req resp -> TypeListTag (Code req) xa -> a -> m b



class IsOf adt a where
  selectFrom :: adt -> Maybe a
  wrapInto :: a -> adt

--newtype GenericHolder = GenericHolder ( unGenericHolder :: a }

--instance Generic a =>


class Generic a => HasResponse a where
  type RequestADT Int = Requests
  type ResponseADT Int = Responses
  type Response a :: *
  requestTag :: TypeListTag (Code RequestADT) -- this could just as easily be (Requests -> Maybe a, a -> Requests) or a Prism...
  responseTag :: TypeListTag (Code ResponseADT) -- Ditto, with Response a and Responses

instance HasResponse Int where
  type RequestADT Int = Requests
  type ResponseADT Int = Responses
  type Response Int = Bool
  requestTag = reqTag1
  responseTag = respTag1

instance HasResponse Requests Responses Double where
  type RequestADT Int = Requests
  type ResponseADT Int = Responses
  type Response Double = Double
  requestTag = reqTag2
  responseTag = respTag2

instance HasResponse Requests Responses Bool where
  type RequestADT Int = Requests
  type ResponseADT Int = Responses
  type Response Bool = String
  requestTag = reqTag3
  responseTag = respTag3


requestToDSum :: HasResponse a => a -> DS.DSum (TypeListTag (Code RequestADT)) (NP I)
requestToDSum = toPerConstructorDSum . wrapOne requestTag

-- why use DSum here at all??
encodeRequest :: HasResponse a => a -> LB.ByteString
encodeRequest = encode . requestToDSum

decodeRequestGeneral :: ByteString -> Parser Requests
decodeRequestGeneral = fmap fromPerConstructorDSum . decode

decodeRequestSpecific :: HasResponse a => Requests -> Maybe a
decodeRequestSpecific = selectUnary requestTag

testServer :: Server Requests Responses IO
testServer req = do
  case req of
    Req1 x = respondInt x
    Req2 x = respondDouble x
    Req3 x = respondBool x

respondInt x = if x :: Int  > 0 then True else False
respondDouble x = x * (2.0 :: Double)
respondBool b = if b then -1 :: Int else 1 :: Int

responseToDSum :: HasResponse a => Response a -> DS.DSum (TypeListTag (Code RequestADT)) (NP I)
responseToDSum = toPerConstructorDSum . wrapOne requestTag


-- why use DSum here at all ?
encodeResponse :: HasResponse a => Response a -> LB.ByteString
encodeResponse = encode . responseToDSum

decodeResponseGeneral :: HasResponse a => LB.ByteString -> Parser Responses
decodeResponseGeneral = fmap fromPerConstructorDSum . decode

decodeResponseSpecific :: HasResponse a => Reponses -> Response a
decodeResponseSpecific = selectUnary responseTag

example :: Int -> Bool
example =


-}
