module Gibbon.Language.Constants where

import qualified Data.List as L

import Gibbon.Language.Syntax
import Gibbon.Common

--------------------------------------------------------------------------------

redirectionSize :: Int
redirectionSize = 9

redirectionTag :: DataCon
redirectionTag = "REDIRECTION"

isRedirectionTag :: DataCon -> Bool
isRedirectionTag = L.isPrefixOf redirectionTag

redirectionAlt :: Num a => a
redirectionAlt = 255

indirectionTag :: DataCon
indirectionTag = "INDIRECTION"

isIndirectionTag :: DataCon -> Bool
isIndirectionTag = L.isPrefixOf indirectionTag

indirectionAlt :: Num a => a
indirectionAlt = 254

selectiveIndirectionAlt :: Num a => a
selectiveIndirectionAlt = 249

-- | Bytes a selective-indirection wrapper occupies.
--
-- Tag, the pointer, the pointee's end, and the share bitmask.  The cursor
-- advances by exactly this much, so a writer must have this much room.
selectiveIndirectionSize :: Num a => a
selectiveIndirectionSize = 25

-- | Where random-access datacon tags start.
--
-- A tag is one byte and the space is split three ways: @[0, ranTagBase)@ are
-- ordinary constructors, @[ranTagBase, selectiveIndirectionAlt)@ are the
-- random-access variants -- which a reader identifies by the tag alone, to
-- know a size field follows -- and the rest are reserved.  'getTagOfDataCon'
-- checks a program stays inside the first two.
ranTagBase :: Num a => a
ranTagBase = 150

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

-- | Symbols whose printed form is not their name.
--
-- @Passes.Codegen.initSymTable@ installs these into the RTS symbol table with
-- dedicated setters rather than @gib_add_symbol@, so a compiled program prints
-- the text below.  Every other backend has to agree, or the same program
-- prints different things depending on how it was run.
specialSymbolText :: String -> Maybe String
specialSymbolText s =
  case s of
    "NEWLINE" -> Just "\n"
    "SPACE" -> Just " "
    "COMMA" -> Just ","
    "LEFTPAREN" -> Just "("
    "RIGHTPAREN" -> Just ")"
    _ -> Nothing

-- | The text a symbol prints as: its special form if it has one, else itself.
symbolText :: String -> String
symbolText s = maybe s id (specialSymbolText s)
