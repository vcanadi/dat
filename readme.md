## dat
Alternative generic representation of Haskell types

### Utility
Easier specification and inspection of some type's values in generic way.
Difference between `GHC.Generics`' (`:+:`, `:*:`, `D1`, `C1`, `S1`) combinators and `Dat`'s type `D` is that Dat's generic represenatation of both sum (constructors) and product (fields) elements is linear (i.e. list) instead of tree.
This enables nicer overview.

Generic translation between GHC.Generics' types enables conversion between any type with `Generic` instance using functions `toDat` and `fromDat`

### Examples
Try test examples in `CoreSpec`
```
ghci -isrc -ispec spec/Dat/CoreSpec.hs
```
```
:m + Data.Proxy Data.Typeable Dat.Core
:set -XDataKinds
```


Convert generic representation to Act type
```
datTo @Act $ DV $ CV (Proxy @"Sp") $ 1 :& "bla" :& True :& EV
Sp 1 "bla" True
```

Convert Act's Sp constructor to generic representation
```
datFrom $ Sp 1 "bla" False
DV {dC = Sp ( 1 :& "bla" :& False :& EV ) }
```

Check the type
```
:t datFrom $ Sp 1 "bla" False
D "Act"
   (C '[ "Sp" '::> (Int :& ([Char] :& (Bool :& E)))
       , "Rm" '::> (Int :& E)
       , "Mv" '::> (Int :& ((Int, Int) :& E))
       , "Clr" '::> E]
   )
```

