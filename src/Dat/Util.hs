
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Dat.Util where

import Data.Kind (Type)
import GHC.TypeLits
import Data.Proxy
import GHC.Generics (M1, (:+:) , (:*:) , Generic (Rep), Meta , C1, S1, Rec0, U1, K1
  , D1, Constructor (conName), Datatype (datatypeName) )
import Data.Typeable (typeRep )

-- | Max Width (max number of fields of any product)
class                    MW (f :: Type -> Type) where mW :: Proxy f -> Int
instance (MW f, MW g) => MW (f :+: g)           where mW _ = max (mW (Proxy @f)) (mW (Proxy @g))
instance (MW f, MW g) => MW (f :*: g)           where mW _ = mW (Proxy @f) + mW (Proxy @g)
instance                 MW (K1 i c)            where mW _ = 1
instance MW f         => MW (M1 i t f)          where mW _ = mW (Proxy @f)
instance                 MW U1                  where mW _ = 0

-- | Height (number of constructors in a sum type)
class H (f :: Type -> Type)        where h :: Proxy f -> Int
instance (H f, H g) => H (f :+: g) where h _ = h (Proxy @f) + h (Proxy @g)
instance H (f :*: g)               where h _ = 1
instance H (K1 i c)                where h _ = 1
instance (H f) => H (M1 i t f)     where h _ = h (Proxy @f)
instance H U1                      where h _ = 1

-- | Name of the type
class TypNm (a :: Type) where typNm :: Proxy a -> String
instance TypNm Bool   where typNm _ = show $ typeRep (Proxy @Bool)
instance TypNm Int    where typNm _ = show $ typeRep (Proxy @Int)
instance TypNm Float  where typNm _ = show $ typeRep (Proxy @Float)
instance TypNm Double where typNm _ = show $ typeRep (Proxy @Double)
instance TypNm String where typNm _ = show $ typeRep (Proxy @String)
instance {-# OVERLAPS #-} TypNm a => TypNm [a] where typNm _ = "[" <> typNm (Proxy @a) <> "]"
instance {-# OVERLAPPABLE #-} (Generic a, GTypNm (Rep a)) => TypNm a where typNm _ = gTypNm (Proxy @(Rep a))


-- | Show type (more than just name)
class TypNm a => SH (a :: Type) where sh :: [String] -> Int -> Proxy a -> String
instance SH Bool   where sh _ d _ = tab d <> typNm (Proxy @Bool)
instance SH Int    where sh _ d _ = tab d <> typNm (Proxy @Int)
instance SH Float  where sh _ d _ = tab d <> typNm (Proxy @Float)
instance SH Double where sh _ d _ = tab d <> typNm (Proxy @Double)
instance SH String where sh _ d _ = tab d <> typNm (Proxy @String)
instance {-# OVERLAPS #-} SH a => SH [a] where sh us d _ = tab d <> "[" <> sh us d (Proxy @a) <> "]"
instance {-# OVERLAPPABLE #-} (Generic a, GSH (Rep a)) => SH a where sh us d _ = gSH us d (Proxy @(Rep a))

-- | Generic representation variant of SH
-- Typeclass "GSH(Generic Show)" whose instances (generic representations) can be shown
-- List of TypNms already shown types is passed down in order to avoid infinite recursion
class GTypNm f => GSH (f :: Type -> Type)     where gSH :: [String] -> Int -> Proxy f -> String
instance (GSHΣ f, Datatype m) => GSH (D1 m f) where gSH us d _ = gSHΣ (gTypNm (Proxy @(D1 m f)):("["<>gTypNm (Proxy @(D1 m f))<>"]"):us) d (Proxy @f)

tab :: Int -> String
tab d = "\n" <> concat (replicate d "   ")

-- | "Generic Show" logic on generic sum type
class GSHΣ (f :: Type -> Type)              where gSHΣ :: [String] -> Int -> Proxy f -> String
instance (GSHΣ f, GSHΣ g) => GSHΣ (f :+: g) where gSHΣ us d _ = tab d <> gSHΣ us (succ d) (Proxy @f)
                                                             <> tab d <> "+" <> show d <> "+"  <> gSHΣ us (succ d) (Proxy @g)

instance (GSHπ f, Constructor m) => GSHΣ (C1 m f)  where gSHΣ us d _ = tab d <> conName @m Dummy  <> gSHπ us d (Proxy @f)

-- Constraints aliases for brevity
--
-- | "Generic Parser" logic on generic product type
class GSHπ (f :: Type -> Type)                    where gSHπ :: [String] -> Int -> Proxy f -> String
instance (GSHπ f, GSHπ g) => GSHπ (f :*: g)       where gSHπ us d _ = tab d <> gSHπ us (succ d) (Proxy @f)
                                                                   <> tab d <> "*" <> show d <> "*"  <> gSHπ us (succ d) (Proxy @g)
instance (SH a, TypNm a) => GSHπ (S1 m (Rec0 a)) where gSHπ us d _ = if typNm (Proxy @a) `elem` us
                                                                     then tab d <> "{" <> typNm (Proxy @a) <> "}"
                                                                     else sh (typNm (Proxy @a):us) d (Proxy @a)
instance GSHπ U1                                 where gSHπ _ _ _ = ""

data Dummy (t :: Meta) (c :: Type -> Type) f = Dummy

-- | Generic representation variant of TypNm
class GTypNm (f :: Type -> Type)         where gTypNm :: Proxy f -> String
instance (Datatype m) => GTypNm (D1 m f) where gTypNm _ = datatypeName @m Dummy

-- Type family helpers
--
type family HalfLen (as :: [k]) :: Nat where
  HalfLen as = Div (Length as) 2

type family Take (n :: Nat) (as :: [k]) :: [k] where
  Take n '[]       = '[]
  Take 0 as        = '[]
  Take n (a ': as) = a ': Take (n - 1) as

type family TakeHalf (as :: [k]) :: [k] where
  TakeHalf as = Take (Div (Length as) 2) as

type family Drop (n :: Nat) (as :: [k]) :: [k] where
  Drop n '[]       = '[]
  Drop 0 as        = as
  Drop n (a ': as) = Drop (n - 1) as

type family DropHalf (as :: [k]) :: [k] where
  DropHalf as = Drop (Div (Length as) 2) as

type family If (p :: Bool) (a :: k) (b :: k) :: k where
  If 'True  a b = a
  If 'False a b = b

-- | Length of type-level list
type family Length (as :: [k]) :: Nat where
  Length as = Length' as 0
-- | Local helper type family for Length type family
type family Length' (as :: [k]) (i :: Nat) :: Nat where
  Length' '[]       i = i
  Length' (a ': as) i = Length' as (i + 1)

-- | Type level list concatenation
type family LCat (as :: [k]) (bs :: [k]) :: [k] where
  LCat '[] bs = bs
  LCat (a ': as) bs = a ': LCat as bs

-- | Length of type-level list from proxy
class Len as where len :: Proxy as -> Int
instance Len' as Int =>  Len as where len p = len' p 0
-- | Local helper typeclass for Len typeclass
class Len' as r where len' :: Proxy as -> r -> r
instance                        Len' '[] r       where len' _ l = l
instance (Enum r, Len' as r) => Len' (a ': as) r where len' _ l = len' (Proxy @as) (succ l)

eqNm :: (KnownSymbol nm, KnownSymbol n') => Proxy nm -> Proxy n' -> Bool
eqNm p p' = symbolVal p == symbolVal p'
