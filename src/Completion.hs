{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}

-- | A GHC code completion module.

module Completion
  ( getCompletableModule
  , declarationByLine
  , declarationCompletions
  , declarationHoles
  , fillHole
  , Declaration(..)
  , DeclarationCompletion(..)
  , Substitution(..)
  , Hole(..)
  , ModuleSource(..)
  , LineNumber(..)
  ) where

import           Bag
import           Control.Monad
import           Control.Monad.IO.Class
import           Data.Function
import           Data.Generics
import           Data.List
import qualified Data.Map.Strict as M
import           Data.Maybe
import           Debug.Trace
import           DynFlags
import           FastString
import           GHC
import           HscTypes
import           Name
import           Outputable
import           RdrName
import           SrcLoc
import           TcRnDriver

--------------------------------------------------------------------------------
-- Types

-- | A module which can be completed. Cannot contain type errors,
-- including deferred ones.
data CompletableModule =
  CompletableModule TypecheckedModule

-- | All the context we need to generate completions for a declaration
-- in a module.
data Declaration = Declaration
  { declarationBind :: !(HsBindLR Name Name)
    -- ^ The actual declaration, which we use to find holes and
    -- substitute them with candidate replacements.
  , declarationSource :: !String
    -- ^ A sample source, which we use merely for debugging.
  , declarationRealSrcSpan :: !RealSrcSpan
    -- ^ A source span which we can provide to the client IDE.
  , declarationParsedModule :: !ParsedModule
   -- ^ The declaration belongs to a parsed module which we'll use to
   -- try out alterations to the tree and see if they type-check.
  , declarationRenamedModule :: !RenamedSource
     -- ^ The renamed module contains 'UnboundedVar', which marks a hole.
  , declarationModuleInfo :: !ModuleInfo
  }

instance Show Declaration where
  showsPrec p (Declaration b s real _parsedModule _renamedSource _) =
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
  , holeName :: !OccName
  }

instance Show Hole where
  showsPrec p (Hole realSrcSpan name) =
    showString "Hole {holeRealSrcSpan = " .
    showsPrec (p + 1) realSrcSpan .
    showString ", holeName = " . gshows name . showString "}"

-- | Completion for a declaration.
data DeclarationCompletion = DeclarationCompletion
  { declarationCompletionSubstitutions :: [Substitution]
  } deriving (Show)

-- | Substition of a source span in the source code with a new string.
data Substitution = Substitution
  { substitutionHole :: !Hole
  , substitutionReplacement :: !RdrName
  }

instance Show Substitution where
  showsPrec p (Substitution hole name) =
    showString "Substitution {substitutionHole = " .
    showsPrec (p + 1) hole .
    showString ", substitutionReplacement = " . gshows name . showString "}"

--------------------------------------------------------------------------------
-- Top-level API

-- | Get a module which can be completed. Cannot contain type errors,
-- including deferred ones.
getCompletableModule :: GhcMonad m => ModSummary -> m CompletableModule
getCompletableModule ms =
  fmap CompletableModule (parseModule ms >>= typecheckModuleNoDeferring)

-- | Find a declaration by line number. If the line is within a
-- declaration in the module, return that declaration.
declarationByLine ::
     ModuleSource
  -> CompletableModule
  -> LineNumber
  -> Maybe Declaration
declarationByLine (ModuleSource src) (CompletableModule typecheckedModule) (LineNumber line) = do
  renamedModule <- tm_renamed_source typecheckedModule
  let binds = renamedSourceToBag renamedModule
  located <- find ((`realSpans` (line, 1)) . getLoc) (bagToList binds)
  realSrcSpan <- getRealSrcSpan (getLoc located)
  let start = srcLocLine (realSrcSpanStart realSrcSpan)
  let end = srcLocLine (realSrcSpanEnd realSrcSpan)
  pure
    (Declaration
     { declarationSource =
         intercalate
           "\n"
           (take (end - (start - 1)) (drop (start - 1) (lines src)))
     , declarationBind = unLoc located
     , declarationRealSrcSpan = realSrcSpan
     , declarationRenamedModule = renamedModule
     , declarationParsedModule = tm_parsed_module typecheckedModule
     , declarationModuleInfo = tm_checked_module_info typecheckedModule
     })

-- | Get all the holes in the given declaration.
declarationHoles :: Declaration -> [Hole]
declarationHoles =
  mapMaybe
    (\h -> do
       (name, src) <- getHoleName h
       pure (Hole {holeRealSrcSpan = src, holeName = name})) .
  listify (isJust . getHoleName) . declarationBind
  where
    getHoleName :: LHsExpr Name -> Maybe (OccName, RealSrcSpan)
    getHoleName =
      \case
        L someSpan (HsUnboundVar (TrueExprHole name)) -> do
          rs <- getRealSrcSpan someSpan
          pure (name, rs)
        _ -> Nothing

-- | Get completions for a declaration.
declarationCompletions :: GhcMonad m => Declaration -> m [DeclarationCompletion]
declarationCompletions declaration = do
  rdrnames <- getRdrNamesInScope
  let names =
        filter
          (not . (`elem` ["undefined"]) . occNameString . rdrNameOcc)
          (nubBy
             (on (==) (occNameString . rdrNameOcc))
             (rdrnames ++
              map
                nameRdrName
                (fromMaybe
                   []
                   (modInfoTopLevelScope (declarationModuleInfo declaration)))))
  hscEnv <- getSession
  df <- getSessionDynFlags
  typedNames <-
    liftIO
      (mapM
         (\rdrName -> do
            (_, ty) <- tcRnExpr hscEnv TM_Inst (rdrNameToLHsExpr rdrName)
            when
              False
              (trace
                 (occNameString (rdrNameOcc rdrName) ++ " :: " ++ showPpr df ty)
                 (pure ()))
            pure (fmap (rdrName, ) ty))
         names)
  collectCompletions
    (catMaybes typedNames)
    (declarationParsedModule declaration)
    (declarationHoles declaration)

-- | Collect sets of compatible completions of holes for the
-- declaration.
collectCompletions ::
     GhcMonad f
  => [(RdrName, Type)]
  -> ParsedModule
  -> [Hole]
  -> f [DeclarationCompletion]
collectCompletions rdrNames parsedModule0 holes0 =
  fmap (map DeclarationCompletion) (go parsedModule0 holes0)
  where
    go :: GhcMonad f => ParsedModule -> [Hole] -> f [[Substitution]]
    go _ [] = pure []
    go parsedModule (hole:holes) = do
      rdrNamesAndParsedModules <- getWellTypedFills parsedModule hole rdrNames
      trace
        (show
           ( "hole"
           , hole
           , "rdrnames"
           , map (occNameString . rdrNameOcc . fst) rdrNamesAndParsedModules))
        (pure ())
      fmap
        concat
        (mapM
           (\(rdrName, parsedModule') -> do
              sets <- go parsedModule' holes
              pure
                (if null sets
                   then [[Substitution hole rdrName]]
                   else map ((Substitution hole rdrName) :) sets))
           rdrNamesAndParsedModules)

--------------------------------------------------------------------------------
-- Testing out completions

data StringEquality =
  StringEquality DynFlags Type
instance Show StringEquality where
  show (StringEquality df x) = showPpr df x
instance Eq StringEquality where
  StringEquality df t1 == StringEquality df' t2 =
    showPpr df t1 == showPpr df' t2
instance Ord StringEquality where
  compare (StringEquality df t1) (StringEquality df' t2) =
    compare (showPpr df t1) (showPpr df' t2)

-- | Get a set of well-typed fills for the given hole.
--
-- Candidates with the same type are cached, to avoid recompiling the
-- module more than neccessary.
getWellTypedFills ::
     GhcMonad m
  => ParsedModule
  -> Hole
  -> [(RdrName, Type)]
  -> m [(RdrName, ParsedModule)]
getWellTypedFills pm hole names = do
  df <- getSessionDynFlags
  fmap
    snd
    (foldM
       (\(!cache, candidates) (rdrname, typ) -> do
          mparsedModule <-
            (case M.lookup (StringEquality df typ) cache of
               Just mparsedModule ->
                 -- trace ("Type cached: " ++ showPpr df typ)
                 (pure mparsedModule)
               Nothing ->
                 -- trace
                 --   ("No cache for: " ++ showPpr df typ)
                   (tryWellTypedFill pm hole (rdrNameToHsExpr rdrname)))
          pure
            ( M.insert (StringEquality df typ) mparsedModule cache
            , case mparsedModule of
                Nothing -> candidates
                Just parsedModule -> (rdrname, parsedModule) : candidates))
       (mempty, [])
       names)

-- | Try to fill a hole with the given expression; if it type-checks,
-- we return the newly updated parse tree. Otherwise, we return Nothing.
tryWellTypedFill ::
     GhcMonad m
  => ParsedModule
  -> Hole
  -> HsExpr RdrName
  -> m (Maybe ParsedModule)
tryWellTypedFill pm hole expr =
  handleSourceError
    (const (pure Nothing))
    (fmap
       (Just . tm_parsed_module)
       (typecheckModuleNoDeferring (fillHole pm hole expr)))

--------------------------------------------------------------------------------
-- Filling holes in the AST

-- | Fill the given hole in the module with the given expression.
fillHole :: ParsedModule -> Hole -> HsExpr RdrName -> ParsedModule
fillHole pm hole expr =
  pm {pm_parsed_source = everywhere (mkT replace) (pm_parsed_source pm)}
  where
    replace :: LHsExpr RdrName -> LHsExpr RdrName
    replace =
      (\case
         L someSpan _
           | Just realSrcSpan <- getRealSrcSpan someSpan
           , realSrcSpan == holeRealSrcSpan hole -> L someSpan expr
         e -> e)

--------------------------------------------------------------------------------
-- Helpers

rdrNameToLHsExpr :: id -> GenLocated SrcSpan (HsExpr id)
rdrNameToLHsExpr rdrname =
  L (UnhelpfulSpan (mkFastString "Generated by rdrNameToLHsExpr"))
    (HsVar
       (L (UnhelpfulSpan (mkFastString "Generated by getWellTypedFills"))
          rdrname))

rdrNameToHsExpr :: id -> HsExpr id
rdrNameToHsExpr rdrname =
  HsVar
    (L (UnhelpfulSpan (mkFastString "Generated by rdrNameToHsExpr")) rdrname)

-- | Type-check the module without deferring type errors, and without
-- logging messages.
typecheckModuleNoDeferring :: GhcMonad m => ParsedModule -> m TypecheckedModule
typecheckModuleNoDeferring parsed = do
  typecheckModule
    parsed
    { GHC.pm_mod_summary =
        (GHC.pm_mod_summary parsed)
        { HscTypes.ms_hspp_opts =
            unSetGeneralFlag'
              Opt_DeferTypeErrors
              (HscTypes.ms_hspp_opts (GHC.pm_mod_summary parsed))
              {log_action = nullLogAction}
        }
    }
  where
    nullLogAction _df _reason _sev _span _style _msgdoc = pure ()

-- | Convert parsed source groups into one bag of binds.
_parsedModuleToBag :: ParsedModule -> Bag (LHsBindLR RdrName RdrName)
_parsedModuleToBag =
  listToBag . mapMaybe valD . hsmodDecls . unLoc . pm_parsed_source
  where
    valD =
      \case
        L l (ValD hsBind) -> pure (L l hsBind)
        _ -> Nothing

-- | Convert renamed source groups into one bag of binds.
renamedSourceToBag :: RenamedSource -> Bag (LHsBindLR Name Name)
renamedSourceToBag (hsGroup, _, _, _) = unHsValBindsLR (hs_valds hsGroup)
  where
    unHsValBindsLR =
      \case
        ValBindsIn binds _ -> binds
        ValBindsOut pairs _ -> unionManyBags (map snd pairs)

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
