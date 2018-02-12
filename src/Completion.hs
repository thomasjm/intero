{-# LANGUAGE LambdaCase #-}

-- | A GHC code completion module.

module Completion
  ( declarationByLine
  , declarationCompletions
  , declarationHoles
  , DeclarationCompletion(..)
  , Substitution(..)
  , Hole (..)
  ) where

import Bag
import Data.Generics
import Data.List
import Data.Maybe
import GHC
import SrcLoc

--------------------------------------------------------------------------------
-- Types

-- | All the context we need to generate completions for a declaration
-- in a module.
data Declaration = Declaration
  { declarationBind :: !(HsBindLR RdrName RdrName)
    -- ^ The actual declaration, which we use to find holes and
    -- substitute them with candidate replacements.
  , declarationSource :: !String
    -- ^ A sample source, which we use merely for debugging.
  , declarationRealSrcSpan :: !RealSrcSpan
    -- ^ A source span which we can provide to the client IDE.
  , declarationParsedModule :: !ParsedModule
   -- ^ The declaration belongs to a parsed module which we'll use to
   -- try out alterations to the tree and see if they type-check.
  }

instance Show Declaration where
  showsPrec p (Declaration b s real _parsedModule) =
    showString "Declaration {declarationBind = " .
    gshows b .
    showString ", declarationSource = " .
    showsPrec (p + 1) s .
    showString ", declarationRealSrcSpan = " .
    showsPrec (p + 1) real . showString "}"

-- | The source code of the module.
newtype ModuleSource = ModuleSource String
  deriving (Show)

-- | An identifier for a declaration in the module.
newtype DeclarationId = DeclarationId String
  deriving (Show)

-- | Line number from the module.
newtype LineNumber = LineNumber Int
  deriving (Show)

-- | A hole written `_` or `_foo` in the user-inputed source, which we
-- can fill in with candidates.
data Hole = Hole
  { holeRealSrcSpan :: !RealSrcSpan
  , holeType :: !Type
  }

instance Show Hole where
  showsPrec p (Hole realSrcSpan ty) =
    showString "Hole {holeRealSrcSpan = " .
    showsPrec (p + 1) realSrcSpan .
    showString ", holeType = " . gshows ty . showString "}"

-- | Completion for a declaration.
data DeclarationCompletion = DeclarationCompletion
  { declarationCompletionSubstitutions :: [Substitution]
  } deriving (Show)

-- | Substition of a source span in the source code with a new string.
data Substitution = Substitution
  { substitutionRealSrcSpan :: !RealSrcSpan
  , substitutionReplacement :: !String
  , substitutionType :: Type
  }

instance Show Substitution where
  showsPrec p (Substitution realSrcSpan replacement ty) =
    showString "Substitution {substitutionRealSrcSpan = " .
    gshows realSrcSpan .
    showString ", substitutionReplacement = " .
    showsPrec (p + 1) replacement .
    showString ", substitutionType = " . gshows ty . showString "}"

--------------------------------------------------------------------------------
-- Top-level API

-- | Find a declaration by line number. If the line is within a
-- declaration in the module, return that declaration.
declarationByLine ::
     ModuleSource
  -> ParsedModule
  -> LineNumber
  -> Maybe Declaration
declarationByLine (ModuleSource src) parsedModule (LineNumber line) = do
  located <- find ((`realSpans` (line, 1)) . getLoc) (bagToList binds)
  realSrcSpan <- getRealSrcSpan (getLoc located)
  let start = srcLocLine (realSrcSpanStart realSrcSpan)
  let end = srcLocLine (realSrcSpanEnd realSrcSpan)
  pure
    (Declaration
     { declarationSource =
         intercalate "\n" (take (end - (start - 1)) (drop (start - 1) (lines src)))
     , declarationBind = unLoc located
     , declarationRealSrcSpan = realSrcSpan
     , declarationParsedModule = parsedModule
     })
  where binds = parsedModuleToBag parsedModule

-- | Get completions for a declaration.
declarationCompletions :: GhcMonad m => Declaration -> m [DeclarationCompletion]
declarationCompletions = undefined

-- | Get all the holes in the given declaration.
declarationHoles :: Declaration -> [Hole]
declarationHoles = undefined

--------------------------------------------------------------------------------
-- Helpers

-- | Convert parsed source groups into one bag of binds.
parsedModuleToBag :: ParsedModule -> Bag (LHsBindLR RdrName RdrName)
parsedModuleToBag =
  listToBag . mapMaybe valD . hsmodDecls . unLoc . pm_parsed_source
  where
    valD =
      \case
        L l (ValD hsBind) -> pure (L l hsBind)
        _ -> Nothing

-- | Does X span over the point Y?
realSpans :: SrcSpan -> (Int, Int) -> Bool
realSpans x y =
  fromMaybe
    False
    (do _ <- getRealSrcSpan x
        pure (spans x y))

-- | Try to get a real span.
getRealSrcSpan :: SrcSpan  -> Maybe RealSrcSpan
getRealSrcSpan =
  \case
    RealSrcSpan r -> pure r
    _ -> Nothing
