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

module Dat.Core where

import Data.Kind (Type)
import GHC.TypeLits
import Data.Proxy
import GHC.Generics (M1 (..), (:+:) (..), (:*:) ((:*:)), Generic (from, Rep), Meta (..), D, C, C1, S1, Rec0, U1(U1), K1(K1), D1, to, Constructor (conName), Datatype (datatypeName), Selector (selName), FixityI(PrefixI), SourceUnpackedness(..), SourceStrictness(..), DecidedStrictness(..) )
import Data.Typeable (typeRep, Typeable)
import Data.Function ((&))
import Unsafe.Coerce (unsafeCoerce)
import Data.Bool
import Numeric (showIntAtBase)
import Data.Char (intToDigit)

import Dat.Util
import Test.QuickCheck (Arbitrary)


-- Dat type
--
-- | Generic data type with type level info
newtype Dat (dNm :: Symbol) c = DatVal { dCon :: c } deriving (Show, Generic, Eq )

-- | Lifted to kind KPair with type constructor ::> representing sum type constructor selection
data KPair = Symbol ::> Type

-- | Lookup constructor argument types by constructor name (Symbol)
type family Lookup (nm :: Symbol) (cs :: [KPair]) :: Type where
  Lookup nm (nm ::> t ': cs) = t
  Lookup nm (nm' ::> t ': cs) = Lookup nm cs

-- | Get Index of selected constructor
class CIx cs                                              where cIx :: Con cs -> Int
instance CIx '[]                                          where cIx (ConVal _ _) = 0
instance (CIx cs, KnownSymbol nm) => CIx (nm ::> t ': cs) where cIx cv@(ConVal p  _) = 1 + (eqNm p (Proxy @nm) & bool (cIx @cs (unsafeCoerce cv :: Con cs)) (-1))

-- | Generic product operator
infixr 7 :&
data (:&) s ss = s :& ss deriving (Show)

type family Inject a b where
  Inject (a :& b) c = a :& Inject b c
  Inject End a = a

class DoInject a b                           where doInject :: a -> b -> Inject a b
instance DoInject b c => DoInject (a :& b) c where doInject (x :& y) z = x :& doInject y z
instance                 DoInject End a      where doInject EndVal x = x

-- | Type and value representing end of list
data End = EndVal deriving Show

type NmCst nm cs = (KnownSymbol nm, Show (Lookup nm cs))

-- | Constructors typed list
data Con (cs :: [KPair]) = forall nm. NmCst nm cs  => ConVal { cNm :: Proxy nm, cT :: Lookup nm cs }

instance                                         Eq (Con '[])                 where a == b = False
instance (KnownSymbol nm, Eq (Con cs), Eq sl) => Eq (Con ((nm ::> sl) ': cs)) where ConVal p0 t0 == ConVal p1 t1 =  eqNm p0 (Proxy @nm)
                                                                                                 && eqNm p1 (Proxy @nm)
                                                                                                 && (unsafeCoerce t0 :: sl) == (unsafeCoerce t1 :: sl )

instance Show (Con cs) where
  show (ConVal (Proxy :: Proxy nm) l) = symbolVal (Proxy @nm) <> " (" <> show l <> ")"

-- | Con type concatenation
type family CCat a b where
  CCat (Con as) (Con bs) = Con (LCat as bs)


-- Conversion between Dat and Generic representation


-- G --> Dat
--
-- | Type level conversion Generic.D1 --> Dat -
type family FToD (f :: Type -> Type) :: Type where
  FToD (D1 ('MetaData dn m p nt) f) = Dat dn (FToC f)

-- | Type level conversion Generic.:+: --> Con
type family FToC (f :: Type -> Type) :: Type where
  FToC (f :+: g) = CCat (FToC f) (FToC g)
  FToC (C1 ('MetaCons nm fx s) f) = Con '[ nm ::> FToS f ]

-- | Type level conversion Generic.:*: --> Sel(:&)
type family FToS (f :: Type -> Type) where
  FToS (f :*: g) = Inject (FToS f) (FToS g)
  FToS (S1 ('MetaSel 'Nothing i j k) (Rec0 a)) = a :& End
  FToS (S1 ('MetaSel ('Just r) i j k) (Rec0 a)) = a :& End
  FToS U1 = End


-- | Generic.D1 --> DatVal
class GToD (f :: Type -> Type)                       where gToD :: f p -> FToD f
instance GToC f => GToD (D1 ('MetaData dn m p nt) f) where gToD (M1 x) = DatVal @dn $ gToC @f x

-- | Generic.:+:  --> ConVal
class GToC (f :: Type -> Type)                   where gToC :: f p -> FToC f
instance (GToC fL, GToC fR) => GToC (fL :+: fR)  where gToC x  = case x of L1 y -> unsafeCoerce $ gToC @fL y; R1 y -> unsafeCoerce $ gToC @fR y
instance (GToS f, KnownSymbol nm, Show (FToS f))
              => GToC (C1 ('MetaCons nm fx s) f) where gToC (M1 x) = ConVal (Proxy @nm) $ gToS @f x

-- | Generic.:*:  --> SelVal(:&)
class GToS (f :: Type -> Type)                                          where gToS :: f p -> FToS f
instance (GToS f, GToS g, DoInject (FToS f) (FToS g)) => GToS (f :*: g) where gToS (x:*:y) = doInject (gToS @f x) (gToS @g y)
instance TypNm a => GToS (S1 ('MetaSel 'Nothing i j k) (Rec0 a))        where gToS (M1 (K1 x)) = x :& EndVal
instance TypNm a => GToS (S1 ('MetaSel ('Just r) i j k) (Rec0 a))       where gToS (M1 (K1 x)) = x :& EndVal
instance GToS U1                                                        where gToS _ = EndVal

-- Dat --> G
--
-- | Type level conversion Dat --> Generic.D1
type family DToF (dat :: Type) :: Type -> Type where
  DToF (Dat dn (Con cs)) = (D1 ('MetaData dn "Ghostwork.Core" "main" False) (CToF (Con cs)))

-- | Type level conversion Con --> Generic.:+:
type family CToF (con :: Type) :: Type -> Type where
  CToF (Con '[nm' ::> sl]) = C1 ('MetaCons nm' PrefixI False) (SToF sl)
  CToF (Con cs)            = CToF (Con (TakeHalf cs)) :+: CToF (Con (DropHalf cs))

-- | Type level conversion Sel(&:) --> Generic.:*:
type family SToF (sel :: Type) :: Type -> Type where
  SToF (a :& End) = S1 ('MetaSel 'Nothing NoSourceUnpackedness NoSourceStrictness DecidedLazy) (Rec0 a)
  SToF (a :& as) = SToF (a :& End) :*: SToF as
  SToF End = U1

-- | DatVal --> Generic.D1
class DToG  (d :: Type)                                            where dToG :: d -> DToF d p
instance (CToG (Con cs), CIx cs, Len cs) => DToG (Dat dn (Con cs)) where dToG (DatVal cv@(ConVal p _)) = M1 $ cToG @(Con cs) (cIx @cs cv) cv

-- | ConVal --> Generic.:+:
class    CToG (con :: Type)              where cToG :: Int -> con -> CToF con p
instance {-# OVERLAPS #-} SToG sl
  => CToG (Con '[ nm ::> sl ])           where cToG _ cv@(ConVal p slVal) = M1 $ sToG (unsafeCoerce slVal :: sl)
instance {-# OVERLAPPING #-}
         ( CToG (Con (TakeHalf cs))
         , CToG (Con (DropHalf cs))
         , KnownNat (Div (Length cs) 2)
         , Len cs)
  => CToG (Con cs)                       where cToG i cv@(ConVal p sl) = if i < len (Proxy @cs) `div` 2
                                                                         then unsafeCoerce $ L1 $ cToG i                                                 (unsafeCoerce cv :: Con (TakeHalf cs))
                                                                         else unsafeCoerce $ R1 $ cToG (i - fromIntegral (natVal (Proxy @(HalfLen cs)))) (unsafeCoerce cv :: Con (DropHalf cs))

-- | SelVal(:&) --> Generic.:*:
class SToG (s :: Type)                                   where sToG :: s -> SToF s p
instance {-# OVERLAPS #-}                SToG End        where sToG EndVal =  U1
instance {-# OVERLAPS #-}                SToG (a :& End) where sToG (x :& EndVal) =  M1 $ K1 x
instance {-# OVERLAPPABLE #-} SToG as => SToG (a :& as)  where sToG (x :& xs) = unsafeCoerce $ M1 (K1 x) :*: sToG xs


-- | Convert a type to Dat type representation
type family ToDat a where
  ToDat a = FToD (Rep a)

-- | Analogous to Genercs.from that works on Dat
dFrom :: (Generic a, GToD (Rep a)) => a -> ToDat a
dFrom = gToD . from

-- | Analogous to Genercs.to that works on Dat
dTo :: (Generic a, DToG (FToD (Rep a))) => ToDat a -> a
dTo = to . unsafeCoerce . dToG
