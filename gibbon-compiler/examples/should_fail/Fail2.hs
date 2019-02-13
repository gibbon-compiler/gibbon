module Fail2 where

data Maybe a = Nothing | Just a

fmapMaybe :: (a -> b) -> Maybe a -> Maybe b
fmapMaybe f mb =
  case mb of
    Nothing -> Nothing
    Just x  -> Just x
