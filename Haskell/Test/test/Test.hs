{-# LANGUAGE DeriveGeneric #-}
import GHC.Generics

data A = A [Either String Int]
  deriving (Generic, Show)
