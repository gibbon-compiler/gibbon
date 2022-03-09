module Gibbon.Language.Constants where

import qualified Data.List as L

import Gibbon.Language.Syntax
import Gibbon.Common

--------------------------------------------------------------------------------

redirectionSize :: Int
redirectionSize = 9

redirectionTag :: DataCon
redirectionTag = "REDIRECTION"

redirectionAlt :: Num a => a
redirectionAlt = 255

indirectionTag :: DataCon
indirectionTag = "INDIRECTION"

isIndirectionTag :: DataCon -> Bool
isIndirectionTag = L.isPrefixOf indirectionTag

indirectionAlt :: Num a => a
indirectionAlt = 254

toAbsRANDataCon :: DataCon -> DataCon
toAbsRANDataCon dcon = dcon ++ "^"

isAbsRANDataCon :: DataCon -> Bool
isAbsRANDataCon = L.isSuffixOf "^"

toRelRANDataCon :: DataCon -> DataCon
toRelRANDataCon dcon = dcon ++ "*"

isRelRANDataCon :: DataCon -> Bool
isRelRANDataCon = L.isSuffixOf "*"

fromRANDataCon :: DataCon -> DataCon
fromRANDataCon = init

--------------------------------------------------------------------------------

-- | Map a DataCon onto the name of the generated unpack function.
mkUnpackerName :: TyCon -> Var
mkUnpackerName tyCons = toVar $ "_unpack_" ++ tyCons

isUnpackerName :: Var -> Bool
isUnpackerName v = L.isPrefixOf "_unpack_" (fromVar v)

-- | Map a DataCon onto the name of the generated print function.
mkPrinterName :: TyCon -> Var
mkPrinterName tyCons = toVar $ "_print_" ++ tyCons

isPrinterName :: Var -> Bool
isPrinterName v = L.isPrefixOf "_print_" (fromVar v)

mkCopyFunName :: TyCon -> Var
mkCopyFunName dcon = "_copy_" `varAppend` (toVar dcon)

isCopyFunName :: Var -> Bool
isCopyFunName = L.isPrefixOf "_copy_" . fromVar

mkCopySansPtrsFunName :: TyCon -> Var
mkCopySansPtrsFunName dcon = "_copy_without_ptrs_" `varAppend` (toVar dcon)

isCopySansPtrsFunName :: Var -> Bool
isCopySansPtrsFunName = L.isPrefixOf "_copy_without_ptrs_" . fromVar

mkTravFunName :: TyCon -> Var
mkTravFunName dcon = "_traverse_" `varAppend` (toVar dcon)

isTravFunName :: Var -> Bool
isTravFunName = L.isPrefixOf "_traverse_" . fromVar

mkRelOffsetsFunName :: DataCon -> Var
mkRelOffsetsFunName dcon = "_add_size_and_rel_offsets_" `varAppend` (toVar dcon)

isRelOffsetsFunName :: Var -> Bool
isRelOffsetsFunName = L.isPrefixOf "_add_size_and_rel_offsets_" . fromVar
