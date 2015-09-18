{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

import Generics.BiGUL
import THAST

type SBook = (String, ([String], (Double, Int)))
type VBook = (String, Double)

s :: [SBook]
s = [("Real World Haskell is Not GOOD!", (["zantao"], (30.0, 2015)))]

v :: [VBook]
v = [("Real World Haskell is Not GOOD!", 10.0), ("Learn You Haskell is GOOD!", 20.0)]

bookstore :: MonadError' ErrorInfo m => BiGUL m [SBook] [VBook]
bookstore =
  Align (\_ -> return True)
        (\(stitle, _) (vtitle, _) -> return $ stitle == vtitle)
        ($(rearrTH =<< [| \(x, y) -> (x, (), y, ()) |])
          -- Rearr (RProd RVar RVar)
          --       (EProd (EDir (DLeft DVar)) (EProd (EConst ()) (EProd (EDir (DRight DVar)) (EConst ()))))
               (Update (UProd (UVar Replace) (UProd (UVar Skip) (UProd (UVar Replace) (UVar Skip))))))
        (\(vtitle, vprice) -> return (vtitle, ([], (vprice, 2012))))
        (\_ -> return Nothing)
