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

module Dat.CoreSpec ( spec) where

import Test.Hspec
import GHC.Generics (Generic (..))
import Test.Hspec.QuickCheck (prop)
import Dat.Core
import Data.Proxy (Proxy(Proxy))
import Test.QuickCheck.Property ((===))
import Test.QuickCheck (Arbitrary (..))
import Generic.Random
import Dat.Util (TypNm(typNm), GTypNm)
import Test.QuickCheck.Gen (chooseEnum)

data X1  = X10                                                                                     deriving(Eq, Generic, Show, Enum, Bounded)
data X2  = X20 | X21                                                                               deriving(Eq, Generic, Show, Enum, Bounded)
data X3  = X30 | X31 | X32                                                                         deriving(Eq, Generic, Show, Enum, Bounded)
data X4  = X40 | X41 | X42 | X43                                                                   deriving(Eq, Generic, Show, Enum, Bounded)
data X5  = X50 | X51 | X52 | X53 | X54                                                             deriving(Eq, Generic, Show, Enum, Bounded)
data X6  = X60 | X61 | X62 | X63 | X64 | X65                                                       deriving(Eq, Generic, Show, Enum, Bounded)
data X7  = X70 | X71 | X72 | X73 | X74 | X75 | X76                                                 deriving(Eq, Generic, Show, Enum, Bounded)
data X8  = X80 | X81 | X82 | X83 | X84 | X85 | X86 | X87                                           deriving(Eq, Generic, Show ,Enum, Bounded)
data X9  = X90 | X91 | X92 | X93 | X94 | X95 | X96 | X97 | X98                                     deriving(Eq, Generic, Show ,Enum, Bounded)
data XA  = XA0 | XA1 | XA2 | XA3 | XA4 | XA5 | XA6 | XA7 | XA8 | XA9                               deriving(Eq, Generic, Show ,Enum, Bounded)
data XB  = XB0 | XB1 | XB2 | XB3 | XB4 | XB5 | XB6 | XB7 | XB8 | XB9 | XBA                         deriving(Eq, Generic, Show ,Enum, Bounded)
data XC  = XC0 | XC1 | XC2 | XC3 | XC4 | XC5 | XC6 | XC7 | XC8 | XC9 | XCA | XCB                   deriving(Eq, Generic, Show ,Enum, Bounded)
data XD  = XD0 | XD1 | XD2 | XD3 | XD4 | XD5 | XD6 | XD7 | XD8 | XD9 | XDA | XDB | XDC             deriving(Eq, Generic, Show ,Enum, Bounded)
data XE  = XE0 | XE1 | XE2 | XE3 | XE4 | XE5 | XE6 | XE7 | XE8 | XE9 | XEA | XEB | XEC | XED       deriving(Eq, Generic, Show ,Enum, Bounded)
data XF  = XF0 | XF1 | XF2 | XF3 | XF4 | XF5 | XF6 | XF7 | XF8 | XF9 | XFA | XFB | XFC | XFD | XFE deriving(Eq, Generic, Show ,Enum, Bounded)

data Y
  = Y0
  | Y1 Int
  | Y2 String Bool
  | Y3 Float Double [String]
  | Y4 Float Double [String] Bool
  deriving (Show, Generic, Eq)

data ZX = ZX1 X1
        | ZX2 X2 X3
        | ZX3 X4 X5 X6
        deriving (Show, Eq, Generic)

data Act = Sp Int String Bool
         | Rm Int
         | Mv Int (Int,Int)
         | Clr
         deriving (Show, Eq, Generic )

instance Arbitrary X1 where arbitrary = genericArbitraryU
instance Arbitrary X2 where arbitrary = genericArbitraryU
instance Arbitrary X3 where arbitrary = genericArbitraryU
instance Arbitrary X4 where arbitrary = genericArbitraryU
instance Arbitrary X5 where arbitrary = genericArbitraryU
instance Arbitrary X6 where arbitrary = genericArbitraryU
instance Arbitrary X7 where arbitrary = genericArbitraryU
instance Arbitrary X8 where arbitrary = genericArbitraryU
instance Arbitrary X9 where arbitrary = genericArbitraryU
instance Arbitrary XA where arbitrary = genericArbitraryU
instance Arbitrary XB where arbitrary = genericArbitraryU
instance Arbitrary XC where arbitrary = genericArbitraryU
instance Arbitrary XD where arbitrary = genericArbitraryU
instance Arbitrary XE where arbitrary = genericArbitraryU
instance Arbitrary XF where arbitrary = genericArbitraryU
instance Arbitrary ZX where arbitrary = genericArbitraryU
instance Arbitrary Y where arbitrary = genericArbitraryU
instance Arbitrary Act where arbitrary = genericArbitraryU

-- type DatAct
--   = D "Act"
--     ( SM '[ "Sp"  ::> (Int :& String :& Bool :& E )
--          , "Rm"  ::> (Int :& E)
--          , "Mv"  ::> (Int :& (Int,Int) :& E )
--          , "Clr" ::> E
--          ]
--     )

-- dats :: [DatAct]
-- dats = [ DV $ SMV (Proxy @"Rm") $ 1 :& EV
--        , DV $ SMV (Proxy @"Sp") $ 1 :& "bla" :& True :& EV
--        , DV $ SMV (Proxy @"Clr") EV
--        ]

-- dats2  :: [ D "Act"
--            (  SM  '[ "Sp"  ::> (Int :& String :& Bool :& E )
--                    , "Rm"  ::> (Int :& E)
--                    ]
--            )
--          ]
-- dats2 = [ DV $ SMV (Proxy @"Rm") $ 1 :& EV
--         , DV $ SMV (Proxy @"Sp") $ 1 :& "bal" :& True :& EV
--         ]

data BTree = BLeaf | BNode Int BTree BTree deriving (Eq,Generic, Show)
instance Arbitrary BTree where arbitrary = genericArbitraryU

newtype Tree = Node [Tree] deriving (Eq,Generic, Show)
instance Arbitrary Tree where
  arbitrary = do
    n <- chooseEnum (0,2)
    Node . take n <$> sequence (repeat arbitrary)

data Lst = LstEnd |  LstCon Int Lst deriving (Eq,Generic, Show)
instance Arbitrary Lst where arbitrary = genericArbitraryU

newtype Wrap a = Wrap a deriving (Eq,Generic, Show)
instance Arbitrary a => Arbitrary (Wrap a) where arbitrary = genericArbitraryU

-- | 'datTo . datFrom == id' test on multiple types
class IdDatSpec as               where idDatSpec :: Spec
instance IdDatSpec '[]           where idDatSpec = pure ()
instance ( Show a, Arbitrary a
         , Generic a, Eq a
         , Dat a, GTypNm (Rep a)
         , IdDatSpec as)
         => IdDatSpec (a ': as)  where idDatSpec = do
                                         prop ("datTo . datFrom == id on " <> typNm (Proxy @a)) $ \(t :: a) ->
                                           t === datTo @a (datFrom t)
                                         idDatSpec @as

idDSpec :: Spec
idDSpec = do
  describe "datTo . datFrom id examples" $
    idDatSpec @'[Act, X1, X2, X3, X4, X5, X6, X7, X8, X9, XA, XB, XC, XD, XE, XF, Y, ZX, Lst, Wrap Int, Wrap String, BTree, Tree]

spec :: Spec
spec = describe "Dat tests:" $ do
  idDSpec
