module Gibbon.Language.Constants where

import Data.List

import Gibbon.Language.Syntax
import Gibbon.Common

--------------------------------------------------------------------------------

redirectionSize :: Int
redirectionSize = 9

redirectionTag :: DataCon
redirectionTag = "REDIRECTION"

redirectionAlt :: Num a => a
redirectionAlt = 100

indirectionTag :: DataCon
indirectionTag = "INDIRECTION"

isIndirectionTag :: DataCon -> Bool
isIndirectionTag = isPrefixOf indirectionTag

indirectionAlt :: Num a => a
indirectionAlt = 90

toIndrDataCon :: DataCon -> DataCon
toIndrDataCon dcon = dcon ++ "^"

fromIndrDataCon :: DataCon -> DataCon
fromIndrDataCon = init

isIndrDataCon :: DataCon -> Bool
isIndrDataCon = isSuffixOf "^"

-- | Map a DataCon onto the name of the generated unpack function.
mkUnpackerName :: TyCon -> Var
mkUnpackerName tyCons = toVar $ "unpack_" ++ tyCons

-- | Map a DataCon onto the name of the generated print function.
mkPrinterName :: DataCon -> Var
mkPrinterName tyCons = toVar $ "print_" ++ tyCons

mkCopyFunName :: DataCon -> Var
mkCopyFunName dcon = "copy_" `varAppend` (toVar dcon)

isCopyFunName :: Var -> Bool
isCopyFunName = isPrefixOf "copy_" . fromVar

mkTravFunName :: DataCon -> Var
mkTravFunName dcon = "_traverse_" `varAppend` (toVar dcon)
