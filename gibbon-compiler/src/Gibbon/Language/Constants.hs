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

toRANDataCon :: DataCon -> DataCon
toRANDataCon dcon = dcon ++ "^"

fromRANDataCon :: DataCon -> DataCon
fromRANDataCon = init

isRANDataCon :: DataCon -> Bool
isRANDataCon = isSuffixOf "^"

-- | Map a DataCon onto the name of the generated unpack function.
mkUnpackerName :: TyCon -> Var
mkUnpackerName tyCons = toVar $ "_unpack_" ++ tyCons

isUnpackerName :: Var -> Bool
isUnpackerName v = isPrefixOf "_unpack_" (fromVar v)

-- | Map a DataCon onto the name of the generated print function.
mkPrinterName :: DataCon -> Var
mkPrinterName tyCons = toVar $ "_print_" ++ tyCons

isPrinterName :: Var -> Bool
isPrinterName v = isPrefixOf "_print_" (fromVar v)

mkCopyFunName :: DataCon -> Var
mkCopyFunName dcon = "_copy_" `varAppend` (toVar dcon)

isCopyFunName :: Var -> Bool
isCopyFunName = isPrefixOf "_copy_" . fromVar

mkTravFunName :: DataCon -> Var
mkTravFunName dcon = "_traverse_" `varAppend` (toVar dcon)
