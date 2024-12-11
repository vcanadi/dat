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
{-# LANGUAGE GADTs #-}

module Dat.Core where

import Data.Kind (Type)
import GHC.TypeLits
import Data.Proxy
import GHC.Generics (M1 (..), (:+:) (..), (:*:) ((:*:)), Generic (from, Rep), Meta (..),  C1, S1, Rec0, U1(U1), K1(K1), D1, to, FixityI(PrefixI), SourceUnpackedness(..), SourceStrictness(..), DecidedStrictness(..) )
import Data.Function ((&))
import Unsafe.Coerce (unsafeCoerce)
import Data.Bool

import Dat.Util

-- | Lifted to kind CPair with type constructor ::> representing sum type constructor selection
data CPair = Symbol ::> Type

-- | Lookup constructor argument types by constructor name (Symbol)
type family Lookup (nm :: Symbol) (cs :: [CPair]) :: Type where
  Lookup nm (nm ::> t ': cs) = t
  Lookup nm (nm' ::> t ': cs) = Lookup nm cs

-- | Get Index of selected constructor
class CIx cs               where cIx :: C cs -> Int
instance CIx' cs => CIx cs where cIx = cIx' 0
-- | Helper type-class for CIx
class CIx' cs                                               where cIx' :: Int -> C cs -> Int
instance CIx' '[]                                           where cIx' ix (CV _ _) = ix
instance (CIx' cs, KnownSymbol nm) => CIx' (nm ::> t ': cs) where cIx' ix cv@(CV p  _) = eqNm p (Proxy @nm) & bool (cIx' @cs (succ ix) (unsafeCoerce cv :: C cs)) ix

type NmCst nm cs = (KnownSymbol nm, Show (Lookup nm cs))

-- Dat type
--
-- | Generic data type with type-level info
newtype D (dNm :: Symbol) c = DV { dC :: c } deriving (Show, Generic, Eq )

-- | Sum representation. Generic constructor with type-level list of constructors
data C (cs :: [CPair]) = forall nm. NmCst nm cs  => CV { cNm :: Proxy nm, cT :: Lookup nm cs }



-----------------------------------------------------------------------------
data PR as where
  PRE :: PR '[]
  (::&) ::  a -> PR as -> PR (a ': as)

instance {-# OVERLAPS #-}                              Show (PR '[])       where show PRE = "PRE"
instance {-# OVERLAPPING #-} (Show a, Show (PR as)) => Show (PR (a ': as)) where show (x ::& pr) = show x <> " ::& " <> show pr

class PRTake n as                              where prTake :: PR as -> PR (Take n as)
instance PRTake n '[]                          where prTake PRE = PRE
instance PRTake 0 (a ': as)                    where prTake _ = PRE
instance PRTake (n-1) as => PRTake n (a ': as) where prTake (x ::& pr) = unsafeCoerce $ x ::& prTake @(n - 1) pr


class PRDrop n as                              where prDrop :: PR as -> PR (Drop n as)
instance PRDrop n '[]                          where prDrop PRE = PRE
instance PRDrop 0 (a ': as)                    where prDrop pr = pr
instance PRDrop (n-1) as => PRDrop n (a ': as) where prDrop (x ::& pr) = unsafeCoerce $ prDrop @(n - 1) pr

prLen :: PR as -> Int
prLen PRE = 0
prLen (_ ::& xs) = succ (prLen xs)

prTakeHalf :: forall as. PRTake (HalfLen as) as => PR as -> PR (TakeHalf as)
prTakeHalf = prTake @(HalfLen as)

prDropHalf :: forall as. PRDrop (HalfLen as) as => PR as -> PR (DropHalf as)
prDropHalf = prDrop  @(HalfLen as)

type family LInject as bs where
  LInject (as ': bs) cs = as ': LInject bs cs
  LInject '[] as = as

prInject :: PR as -> PR bs -> PR (LInject as bs)
prInject (x ::& ys) zs = x ::& prInject ys zs
prInject PRE pr = pr

------------------------------------------------------------------------------------------------------------


-- | Generic product operator
infixr 7 :&
data (:&) s ss = s :& ss

instance {-# OVERLAPS #-}               Show a => Show (a :& E)  where show (x :& EV) = show x <> " :& EV"
instance {-# OVERLAPPING #-} (Show a, Show as) => Show (a :& as) where show (x :& xs) = show x <> " :& " <> show xs

class PTaken as (n :: Nat)                       where pTake :: as -> PTake n as
instance {-# OVERLAPS #-}     PTaken E n         where pTake EV = EV
instance {-# OVERLAPPING #-}  PTaken (a :& as) 0 where pTake _ = EV
instance PTaken as (n - 1) => PTaken (a :& as) n where pTake (x :& xs) = unsafeCoerce $ x :& pTake @as @(n - 1) xs

class PDropped a (n :: Nat)                          where pDrop ::  a -> PDrop n a
instance {-# OVERLAPS #-}       PDropped E n         where pDrop EV = EV
instance {-# OVERLAPPING #-}    PDropped (a :& as) 0 where pDrop xs = xs
instance PDropped as (n - 1) => PDropped (a :& as) n where pDrop (_ :& xs) = unsafeCoerce $ pDrop @as @(n - 1) xs

class PLen a                       where pLen :: a -> Int
instance PLen E                    where pLen EV = 0
instance PLen as => PLen (a :& as) where pLen (_ :& xs) = succ (pLen xs)

pTakeHalf :: forall as. (PTaken as (Div (PLength as) 2)) => as -> PTakeHalf as
pTakeHalf = pTake @as @(Div (PLength as) 2)

pDropHalf :: forall a. (PDropped a (Div (PLength a) 2)) => a -> PDropHalf a
pDropHalf = pDrop @a @(Div (PLength a) 2)

-- | Length of type-level list
type family PLength as :: Nat where
  PLength as = PLength' as 0
-- | Local helper type family for PLength type family
type family PLength' as (i :: Nat) :: Nat where
  PLength' E         i = i
  PLength' (a :& as) i = PLength' as (i + 1)

type family PTake (n :: Nat) as where
  PTake n E         = E
  PTake 0 as        = E
  PTake n (a :& as) = a :& PTake (n - 1) as

type family PTakeHalf as where
  PTakeHalf as = PTake (Div (PLength as) 2) as

type family PDrop (n :: Nat) as where
  PDrop n E         = E
  PDrop 0 as        = as
  PDrop n (a :& as) = PDrop (n - 1) as

type family PDropHalf as where
  PDropHalf as = PDrop (Div (PLength as) 2) as

type family Inject a b where
  Inject (a :& b) c = a :& Inject b c
  Inject E a = a

class DoInject a b                           where doInject :: a -> b -> Inject a b
instance DoInject b c => DoInject (a :& b) c where doInject (x :& y) z = x :& doInject y z
instance                 DoInject E a        where doInject EV x = x

-- | Type and value representing end of list
data E = EV deriving Show

instance                                       Eq (C '[])                 where _ == _ = False
instance (KnownSymbol nm, Eq (C cs), Eq sl) => Eq (C ((nm ::> sl) ': cs)) where CV p0 t0 == CV p1 t1 = eqNm p0 (Proxy @nm)
                                                                                                    && eqNm p1 (Proxy @nm)
                                                                                                    && (unsafeCoerce t0 :: sl)
                                                                                                    == (unsafeCoerce t1 :: sl )

instance Show (C cs) where
  show (CV (Proxy :: Proxy nm) l) = symbolVal (Proxy @nm) <> " ( " <> show l <> " ) "

-- | C type concatenation
type family CCat a b where
  CCat (C as) (C bs) = C (LCat as bs)


-- Conversion between D and Generic representation


-- G --> D

-- Type level transformation
--
-- | Type level conversion Generic.D1 --> D -
type family FToD (f :: Type -> Type) :: Type where
  FToD (D1 ('MetaData dn m p nt) f) = D dn (FToC f)

-- | Type level conversion Generic.:+: --> C
type family FToC (f :: Type -> Type) :: Type where
  FToC (f :+: g) = CCat (FToC f) (FToC g)
  FToC (C1 ('MetaCons nm fx s) f) = C '[ nm ::> FToPR f ]

-- | Type level conversion Generic.:*: --> PR(:&)
type family FToPR (f :: Type -> Type) where
  FToPR (f :*: g) = Inject (FToPR f) (FToPR g)
  FToPR (S1 ('MetaSel 'Nothing i j k) (Rec0 a)) = a :& E
  FToPR (S1 ('MetaSel ('Just r) i j k) (Rec0 a)) = a :& E
  FToPR U1 = E

-- Value level transformation

-- | Generic.D1 --> DV
class GToD (f :: Type -> Type)                        where gToD :: f p -> FToD f
instance GToC f => GToD (D1 ('MetaData dn m p nt) f) where gToD (M1 x) = DV @dn $ gToC @f x

-- | Generic.:+:  --> CV
class GToC (f :: Type -> Type)                    where gToC :: f p -> FToC f
instance (GToC fL, GToC fR) => GToC (fL :+: fR) where gToC x  = case x of L1 y -> unsafeCoerce $ gToC @fL y; R1 y -> unsafeCoerce $ gToC @fR y
instance (GToPR f, KnownSymbol nm, Show (FToPR f))
              => GToC (C1 ('MetaCons nm fx s) f)  where gToC (M1 x) = CV (Proxy @nm) $ gToS @f x

-- | Generic.:*:  --> PRV(:&)
class GToPR (f :: Type -> Type)                                              where gToS :: f p -> FToPR f
instance (GToPR f, GToPR g, DoInject (FToPR f) (FToPR g)) => GToPR (f :*: g) where gToS (x:*:y) = doInject (gToS @f x) (gToS @g y)
instance TypNm a => GToPR (S1 ('MetaSel 'Nothing i j k) (Rec0 a))            where gToS (M1 (K1 x)) = x :& EV
instance TypNm a => GToPR (S1 ('MetaSel ('Just r) i j k) (Rec0 a))           where gToS (M1 (K1 x)) = x :& EV
instance GToPR U1                                                            where gToS _ = EV


-- D --> G

-- Type level transformation
--
-- | Type level conversion D --> Generic.D1
type family DToF (dat :: Type) :: Type -> Type where
  DToF (D dn (C cs)) = (D1 ('MetaData dn "Dat.CoreSpec" "main" False) (CToF (C cs)))

-- | Type level conversion C --> Generic.:+:
type family CToF (c :: Type) :: Type -> Type where
  CToF (C '[nm' ::> sl]) = C1 ('MetaCons nm' PrefixI False) (SToF sl)
  CToF (C cs)            = CToF (C (TakeHalf cs)) :+: CToF (C (DropHalf cs))

-- | Type level conversion PR(&:) --> Generic.:*:
type family SToF (sel :: Type) :: Type -> Type where
  SToF E = U1
  SToF (a :& E) = S1 ('MetaSel 'Nothing NoSourceUnpackedness NoSourceStrictness DecidedLazy) (Rec0 a)
  SToF as = SToF (PTakeHalf as) :*: SToF (PDropHalf as)

-- Value level transformation

-- | DV --> Generic.D1
class DToG  (d :: Type)                                          where dToG :: d -> DToF d p
instance (CToG (C cs), CIx cs, Len cs) => DToG (D dn (C cs)) where dToG (DV cv@(CV _ _)) = M1 $ cToG @(C cs) (cIx @cs cv) cv

-- | CV --> Generic.:+:
class    CToG (c :: Type)               where cToG :: Int -> c -> CToF c p
instance {-# OVERLAPS #-} PRToG sl
  => CToG (C '[ nm ::> sl ])           where cToG _ (CV _ slVal) = M1 $ sToG (unsafeCoerce slVal :: sl)
instance {-# OVERLAPPING #-}
         ( CToG (C (TakeHalf cs))
         , CToG (C (DropHalf cs))
         , KnownNat (Div (Length cs) 2)
         , Len cs)
  => CToG (C cs)                       where cToG cIx cv@(CV _ _) = if cIx < len (Proxy @cs) `div` 2
                                                                       then unsafeCoerce $ L1 $ cToG cIx                                                 (unsafeCoerce cv :: C (TakeHalf cs))
                                                                       else unsafeCoerce $ R1 $ cToG (cIx - fromIntegral (natVal (Proxy @(HalfLen cs)))) (unsafeCoerce cv :: C (DropHalf cs))

-- | PRV(:&) --> Generic.:*:
class PRToG (s :: Type)                      where sToG :: s -> SToF s p
instance                      PRToG E        where sToG _         = U1
instance {-# OVERLAPS #-}     PRToG (a :& E) where sToG (x :& EV) = M1 $ K1 x
instance {-# OVERLAPPABLE #-}
         ( PRToG (PTakeHalf as)
         , PRToG (PDropHalf as)
         , PTaken as (Div (PLength as) 2)
         , PDropped as (Div (PLength as) 2))
  => PRToG as                                where sToG xs = unsafeCoerce $ sToG (pTakeHalf xs) :*: sToG (pDropHalf xs)


-- | Convert a type to D type representation
type family ToDat a where
  ToDat a = FToD (Rep a)

-- | Analogous to Genercs.from that works on D
dFrom :: (Generic a, GToD (Rep a)) => a -> ToDat a
dFrom = gToD . from

-- | Analogous to Genercs.to that works on D
dTo :: (Generic a, DToG (FToD (Rep a))) => ToDat a -> a
dTo = to . unsafeCoerce . dToG

class Dat a where
  type family DRep a
  datTo :: DRep a -> a
  datFrom :: a -> DRep a

instance (Generic a, GToD (Rep a), DToG (FToD (Rep a))) => Dat a where
  type DRep a = FToD (Rep a)
  datTo = dTo
  datFrom = dFrom
