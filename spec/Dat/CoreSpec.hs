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
import Dat.Core
import GHC.Generics
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck ((===))


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
  deriving (Show, Generic)

type DatSmpl0 =  Dat "Act"
           (  Con   '[ "Sp"  ::> (Int :& String :& Bool :& End )
                     , "Rm"  ::> (Int :& End)
                     , "Mv"  ::> (Int :& (Int,Int) :& End )
                     , "Clr" ::> End
                     ]
           )

-- dats :: DatSmpl0
-- dats = [ DatVal $ ConVal (Proxy @"Rm") $ 1 :& EndVal
--        , DatVal $ ConVal (Proxy @"Sp") $ 1 :& "bal" :& True :& EndVal
--        , DatVal $ ConVal (Proxy @"Clr") $ EndVal
--        ]

-- dats2  :: [ Dat "Act"
--            (  Con   '[ "Sp"  ::> (Int :& String :& Bool :& End )
--                      , "Rm"  ::> (Int :& End)
--                      ]
--            )
--          ]
-- dats2 = [ DatVal $ ConVal (Proxy @"Rm") $ 1 :& EndVal
--        , DatVal $ ConVal (Proxy @"Sp") $ 1 :& "bal" :& True :& EndVal
--        ]




spec :: Spec
spec = describe "All specs:" $ do
  pure () -- idDSpec

-- idDSpec :: Spec
-- idDSpec = do
--   describe "dToG >>> gToD identity spec" $
--     prop "atEnd maches segment atEnd" $ \(d :: DatSmpl0 ) ->
--       d === d


-- | Generate tests like:
-- X10 `shouldDesSerTo` [0,0,0,0]
-- X20 `shouldDesSerTo` [0,0,0,0]
-- X21 `shouldDesSerTo` [1,0,0,0]
-- X30 `shouldDesSerTo` [0,0,0,0]
-- X31 `shouldDesSerTo` [1,0,0,0]
-- X32 `shouldDesSerTo` [2,0,0,0]
-- ...
-- i.e. Xnk `shouldDesSerTo` [k,0,0,0]
-- For all Xnk (0 <= k < n) constructors of all Xn types
-- specGenerics :: Spec
-- specGenerics = describe "Xnk" $ do
--   zipWithM_ shouldSerDesTo (allVals @X2) (ixsLessThan 2 )
--   zipWithM_ shouldSerDesTo (allVals @X3) (ixsLessThan 3 )
--   zipWithM_ shouldSerDesTo (allVals @X4) (ixsLessThan 4 )
--   zipWithM_ shouldSerDesTo (allVals @X5) (ixsLessThan 5 )
--   zipWithM_ shouldSerDesTo (allVals @X6) (ixsLessThan 6 )
--   zipWithM_ shouldSerDesTo (allVals @X7) (ixsLessThan 7 )
--   zipWithM_ shouldSerDesTo (allVals @X8) (ixsLessThan 8 )
--   zipWithM_ shouldSerDesTo (allVals @X9) (ixsLessThan 9 )
--   zipWithM_ shouldSerDesTo (allVals @XA) (ixsLessThan 10)
--   zipWithM_ shouldSerDesTo (allVals @XB) (ixsLessThan 11)
--   zipWithM_ shouldSerDesTo (allVals @XC) (ixsLessThan 12)
--   zipWithM_ shouldSerDesTo (allVals @XD) (ixsLessThan 13)
--   zipWithM_ shouldSerDesTo (allVals @XE) (ixsLessThan 14)
--   zipWithM_ shouldSerDesTo (allVals @XF) (ixsLessThan 15)
--     where
--       ixsLessThan :: Word8 -> [[Word8]]
--       ixsLessThan n = [[2,0,0,0 ,i,0,0,0] | i <- [0..pred n]]

--       allVals :: (Enum a, Bounded a) => [a]
--       allVals = [minBound..maxBound]

