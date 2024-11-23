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
import GHC.Generics (M1 (..), (:+:) (..), (:*:) ((:*:)), Generic (from, Rep), Meta (..),  C1, S1, Rec0, U1(U1), K1(K1), D1, to, Constructor (conName), Datatype (datatypeName), Selector (selName), FixityI(PrefixI), SourceUnpackedness(..), SourceStrictness(..), DecidedStrictness(..) )
import Data.Typeable (typeRep, Typeable)
import Data.Function ((&))
import Unsafe.Coerce (unsafeCoerce)
import Data.Bool
import Numeric (showIntAtBase)
import Data.Char (intToDigit)

import Dat.Util
import Test.QuickCheck (Arbitrary)


-- | Lifted to kind CPair with type constructor ::> representing sum type constructor selection
data CPair = Symbol ::> Type

-- | Lookup constructor argument types by constructor name (Symbol)
type family Lookup (nm :: Symbol) (cs :: [CPair]) :: Type where
  Lookup nm (nm ::> t ': cs) = t
  Lookup nm (nm' ::> t ': cs) = Lookup nm cs

-- | Get Index of selected constructor
class SmIx cs                where smIx :: SM cs -> Int
instance SmIx' cs => SmIx cs where smIx = smIx' 0
-- | Helper type-class for SmIx
class SmIx' cs                                                where smIx' :: Int -> SM cs -> Int
instance SmIx' '[]                                            where smIx' cIx (SMV _ _) = cIx
instance (SmIx' cs, KnownSymbol nm) => SmIx' (nm ::> t ': cs) where smIx' cIx cv@(SMV p  _) = eqNm p (Proxy @nm) & bool (smIx' @cs (succ cIx) (unsafeCoerce cv :: SM cs)) cIx

type NmCst nm cs = (KnownSymbol nm, Show (Lookup nm cs))

-- Dat type
--
-- | Generic data type with type-level info
newtype D (dNm :: Symbol) c = DV { dSm :: c } deriving (Show, Generic, Eq )

-- | Sum representation. Generic constructor with type-level list of constructors
data SM (cs :: [CPair]) = forall nm. NmCst nm cs  => SMV { smNm :: Proxy nm, smT :: Lookup nm cs }

-- | Generic product operator
infixr 7 :&
data (:&) s ss = s :& ss deriving (Show)

class PTaken as (n :: Nat)                        where pTake :: as -> PTake n as
instance {-# OVERLAPS #-} PTaken E n              where pTake EV = EV
instance {-# OVERLAPPING #-} PTaken (a :& as) 0   where pTake xs = EV
instance PTaken as (n - 1) => PTaken (a :& as) n  where pTake (x :& xs) = unsafeCoerce $ x :& pTake @as @(n - 1) xs

class PDropped a (n :: Nat)                          where pDrop ::  a -> PDrop n a
instance {-# OVERLAPS #-}PDropped E n                                where pDrop EV = EV
instance {-# OVERLAPPING #-}PDropped (a :& as) 0                        where pDrop xs = xs
instance PDropped as (n - 1) => PDropped (a :& as) n where pDrop (x :& xs) = unsafeCoerce $ pDrop @as @(n - 1) xs

class PLen a                       where pLen :: a -> Int
instance PLen E                    where pLen EV = 0
instance PLen as => PLen (a :& as) where pLen (x :& xs) = succ (pLen xs)

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

instance                                        Eq (SM '[])                 where a == b = False
instance (KnownSymbol nm, Eq (SM cs), Eq sl) => Eq (SM ((nm ::> sl) ': cs)) where SMV p0 t0 == SMV p1 t1 = eqNm p0 (Proxy @nm)
                                                                                                        && eqNm p1 (Proxy @nm)
                                                                                                        && (unsafeCoerce t0 :: sl)
                                                                                                        == (unsafeCoerce t1 :: sl )

instance Show (SM cs) where
  show (SMV (Proxy :: Proxy nm) l) = symbolVal (Proxy @nm) <> " " <> show l

-- | SM type concatenation
type family SmCat a b where
  SmCat (SM as) (SM bs) = SM (LCat as bs)


-- Conversion between D and Generic representation


-- G --> D
--
-- | Type level conversion Generic.D1 --> D -
type family FToD (f :: Type -> Type) :: Type where
  FToD (D1 ('MetaData dn m p nt) f) = D dn (FToSM f)

-- | Type level conversion Generic.:+: --> SM
type family FToSM (f :: Type -> Type) :: Type where
  FToSM (f :+: g) = SmCat (FToSM f) (FToSM g)
  FToSM (C1 ('MetaCons nm fx s) f) = SM '[ nm ::> FToPR f ]

-- | Type level conversion Generic.:*: --> PR(:&)
type family FToPR (f :: Type -> Type) where
  FToPR (f :*: g) = Inject (FToPR f) (FToPR g)
  FToPR (S1 ('MetaSel 'Nothing i j k) (Rec0 a)) = a :& E
  FToPR (S1 ('MetaSel ('Just r) i j k) (Rec0 a)) = a :& E
  FToPR U1 = E


-- | Generic.D1 --> DV
class GToD (f :: Type -> Type)                        where gToD :: f p -> FToD f
instance GToSM f => GToD (D1 ('MetaData dn m p nt) f) where gToD (M1 x) = DV @dn $ gToSm @f x

-- | Generic.:+:  --> SMV
class GToSM (f :: Type -> Type)                    where gToSm :: f p -> FToSM f
instance (GToSM fL, GToSM fR) => GToSM (fL :+: fR) where gToSm x  = case x of L1 y -> unsafeCoerce $ gToSm @fL y; R1 y -> unsafeCoerce $ gToSm @fR y
instance (GToPR f, KnownSymbol nm, Show (FToPR f))
              => GToSM (C1 ('MetaCons nm fx s) f)  where gToSm (M1 x) = SMV (Proxy @nm) $ gToS @f x

-- | Generic.:*:  --> PRV(:&)
class GToPR (f :: Type -> Type)                                              where gToS :: f p -> FToPR f
instance (GToPR f, GToPR g, DoInject (FToPR f) (FToPR g)) => GToPR (f :*: g) where gToS (x:*:y) = doInject (gToS @f x) (gToS @g y)
instance TypNm a => GToPR (S1 ('MetaSel 'Nothing i j k) (Rec0 a))            where gToS (M1 (K1 x)) = x :& EV
instance TypNm a => GToPR (S1 ('MetaSel ('Just r) i j k) (Rec0 a))           where gToS (M1 (K1 x)) = x :& EV
instance GToPR U1                                                            where gToS _ = EV





-- D --> G
--
-- | Type level conversion D --> Generic.D1
type family DToF (dat :: Type) :: Type -> Type where
  DToF (D dn (SM cs)) = (D1 ('MetaData dn "Dat.CoreSpec" "main" False) (SmToF (SM cs)))

-- | Type level conversion SM --> Generic.:+:
type family SmToF (c :: Type) :: Type -> Type where
  SmToF (SM '[nm' ::> sl]) = C1 ('MetaCons nm' PrefixI False) (SToF sl)
  SmToF (SM cs)            = SmToF (SM (TakeHalf cs)) :+: SmToF (SM (DropHalf cs))

-- | Type level conversion PR(&:) --> Generic.:*:
type family SToF (sel :: Type) :: Type -> Type where
  SToF (a :& E) = S1 ('MetaSel 'Nothing NoSourceUnpackedness NoSourceStrictness DecidedLazy) (Rec0 a)
  SToF as = SToF (PTakeHalf as) :*: SToF (PDropHalf as)

-- | DV --> Generic.D1
class DToG  (d :: Type)                                          where dToG :: d -> DToF d p
instance (SMToG (SM cs), SmIx cs, Len cs) => DToG (D dn (SM cs)) where dToG (DV cv@(SMV p _)) = M1 $ cToG @(SM cs) (smIx @cs cv) cv

-- | SMV --> Generic.:+:
class    SMToG (c :: Type)               where cToG :: Int -> c -> SmToF c p
instance {-# OVERLAPS #-} PRToG sl
  => SMToG (SM '[ nm ::> sl ])           where cToG _ cv@(SMV p slVal) = M1 $ sToG (unsafeCoerce slVal :: sl)
instance {-# OVERLAPPING #-}
         ( SMToG (SM (TakeHalf cs))
         , SMToG (SM (DropHalf cs))
         , KnownNat (Div (Length cs) 2)
         , Len cs)
  => SMToG (SM cs)                       where cToG cIx cv@(SMV p sl) = if cIx < len (Proxy @cs) `div` 2
                                                                      then unsafeCoerce $ L1 $ cToG cIx                                                 (unsafeCoerce cv :: SM (TakeHalf cs))
                                                                      else unsafeCoerce $ R1 $ cToG (cIx - fromIntegral (natVal (Proxy @(HalfLen cs)))) (unsafeCoerce cv :: SM (DropHalf cs))

-- | PRV(:&) --> Generic.:*:
class PRToG (s :: Type)                                                                  where sToG :: s -> SToF s p
instance {-# OVERLAPS #-}                                                 PRToG (a :& E) where sToG (x :& EV) = M1 $ K1 x
instance {-# OVERLAPPABLE #-} (PRToG (PTakeHalf as), PRToG (PDropHalf as)
  , PTaken as (Div (PLength as) 2), PDropped as (Div (PLength as) 2))  => PRToG as       where sToG xs =  unsafeCoerce $ sToG (pTakeHalf xs) :*: sToG (pDropHalf xs)


-- | Smonvert a type to D type representation
type family ToDat a where
  ToDat a = FToD (Rep a)

-- | Analogous to Genercs.from that works on D
dFrom :: (Generic a, GToD (Rep a)) => a -> ToDat a
dFrom = gToD . from

-- | Analogous to Genercs.to that works on D
dTo :: (Generic a, DToG (FToD (Rep a))) => ToDat a -> a
dTo = to . unsafeCoerce . dToG
