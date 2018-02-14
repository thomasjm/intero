{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}
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
import           DynFlags
import           FastString
import           GHC
import           HscTypes
import           Name
import           Outputable
import           RdrName
import           SrcLoc
import           TcRnDriver
import           TyCoRep
import           TyCon

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
  , declarationTypecheckedModule :: !TypecheckedSource
    -- ^ Used to get type of holes.
  }

instance Show Declaration where
  showsPrec p (Declaration b s real _parsedModule _renamedSource _ _) =
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
  , holeType :: !Type
  , holeDf :: !DynFlags
  }

instance Show Hole where
  showsPrec p (Hole realSrcSpan name ty df) =
    showString "Hole {holeRealSrcSpan = " .
    showsPrec (p + 1) realSrcSpan .
    showString ", holeName = " . gshows name . showString ", holeType = " .
    showString (showPpr df ty) . showString "}"

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
     , declarationTypecheckedModule = tm_typechecked_source typecheckedModule
     , declarationModuleInfo = tm_checked_module_info typecheckedModule
     })

-- | Get all the holes in the given declaration.
declarationHoles :: DynFlags -> Declaration -> [Hole]
declarationHoles df declaration = go declaration
  where
    go =
      mapMaybe
        (\h -> do
           (name, src) <- getHoleName h
           case listToMaybe
                  (listify
                     (isJust . typeAt src)
                     (declarationTypecheckedModule declaration)) >>=
                typeAt src of
             Nothing -> Nothing
             Just typ ->
               pure
                 (Hole {holeRealSrcSpan = src, holeName = name, holeType = typ, holeDf = df})) .
      listify (isJust . getHoleName) . declarationBind
    typeAt :: RealSrcSpan -> LHsExpr Id -> Maybe Type
    typeAt rs expr =
      if getLoc expr == RealSrcSpan rs
        then case expr of
               L _ (HsVar (L _ i)) -> pure (idType i)
               _ -> Nothing
        else Nothing
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
            {-(trace
               (occNameString (rdrNameOcc rdrName) ++ " :: " ++ showPpr df ty)
               (pure ()))-}
            pure (fmap (rdrName, ) ty))
         names)
  collectCompletions
    (catMaybes typedNames)
    (declarationParsedModule declaration)
    (declarationHoles df declaration)

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
      {-trace
        (show
           ( "hole"
           , hole
           , "rdrnames"
           , map (occNameString . rdrNameOcc . fst) rdrNamesAndParsedModules))
        (pure ())-}
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

data StringEquality = StringEquality
  { _stringEqualityDf :: DynFlags
  , _stringEqualityType :: Type
  }
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
               Just mparsedModule
                 -- trace ("Type cached: " ++ showPpr df typ)
                -> (pure mparsedModule)
               Nothing
                 -- trace
                 --   ("No cache for: " ++ showPpr df typ)
                ->
                 (do if unifiable typ (holeType hole)
                       then do
                         {-liftIO
                           (putStrLn
                              ("tryWellTypedFill: " ++
                               showPpr df rdrname ++
                               " :: " ++
                               showPpr df typ ++
                               " unifiable with " ++ showPpr df (holeType hole)))-}
                         tryWellTypedFill pm hole (rdrNameToHsExpr rdrname)
                       else pure Nothing))
          pure
            ( M.insert (StringEquality df typ) mparsedModule cache
            , case mparsedModule of
                Nothing -> candidates
                Just parsedModule -> (rdrname, parsedModule) : candidates))
       (mempty, [])
       names)
                            -- trace
                            --   ("Skipping " ++
                            --    showPpr df rdrname ++
                            --    " :: " ++
                            --    showPpr df typ ++
                            --    " which contradicts hole type " ++
                            --    showPpr df (holeType hole) ++
                            --    ", unifiable:\n" ++
                            --    show (T df typ) ++
                            --    "\n" ++ show (T df (holeType hole)))

data T = T DynFlags Type
instance Show T where
  showsPrec p (T df ty0) =
    case ty0 of
      TyVarTy v ->
        showString "(TyVarTy " . showString (showPpr df v) . showString ")"
      AppTy t1 t2 ->
        showString "(AppTy " .
        showsPrec (p + 1) (T df t1) .
        showString " " . showsPrec (p + 1) (T df t2) . showString ")"
      TyConApp tyCon tys ->
        showString "(TyConApp " .
        showString (showPpr df tyCon) .
        showString " " . showsPrec (p + 1) (map (T df) tys) . showString ")"
      ForAllTy _tyvar ty ->
        showString "(ForAllTy _ " . showsPrec (p + 1) (T df ty) . showString ")"
      FunTy x y ->
        showString "(FunTy " .
        showsPrec p (T df x) .
        showString " " . showsPrec p (T df y) . showString ")"
      LitTy litTy ->
        showString "(LitTy " . showString (showPpr df litTy) . showString ")"
      CastTy ty _k ->
        showString "(CastTy " . showsPrec (p + 1) (T df ty) . showString " _)"
      CoercionTy _ -> showString "(Coercion _)"

-- | Are the two types at least unifiable? Should not produce false
-- negatives, but should produce false positives.
unifiable :: Type -> Type -> Bool
unifiable t1 t2 =
  case (t1, t2) of
    (CoercionTy {}, _) -> True -- Not sure, default to false positives.
    (_, CoercionTy {}) -> True -- Not sure, default to false positives.
    -- Skip type-classes.
    (FunTy (TyConApp (tyConFlavour -> "class") _) x, y) -> unifiable x y
    (x, FunTy (TyConApp ((tyConFlavour -> "class")) _) y) -> unifiable x y
    --
    (ForAllTy _ x, y) -> unifiable x y
    (x, ForAllTy _ y) -> unifiable x y
    (CastTy x _, y) -> unifiable x y
    (x, CastTy y _) -> unifiable x y
    (TyVarTy _, _) -> True
    (_, TyVarTy _) -> True
    (FunTy x y, FunTy x' y') -> unifiable x x' && unifiable y y'
    (AppTy x y, AppTy x' y') -> unifiable x x' && unifiable y y'
    (TyConApp con1 xs, TyConApp con2 ys) ->
      con1 == con2 && all (uncurry unifiable) (zip xs ys)
    (LitTy l1, LitTy l2) -> l1 == l2
    -- Type application
    (app@AppTy {}, TyConApp _ ys) ->
      let (f, xs) = fargs app
      in case f of
           TyVarTy {} -> all (uncurry unifiable) (zip xs ys)
           _ -> False
    (TyConApp {}, AppTy {}) -> unifiable t2 t1 -- Flip args for re-use.
    -- Incompatible types:
    (AppTy {}, FunTy {}) -> False
    (FunTy {}, AppTy {}) -> False
    (AppTy {}, LitTy {}) -> False
    (LitTy {}, AppTy {}) -> False
    (LitTy {}, FunTy {}) -> False
    (FunTy {}, LitTy {}) -> False
    (TyConApp {}, FunTy {}) -> False
    (FunTy {}, TyConApp {}) -> False
    (LitTy {}, TyConApp {}) -> False
    (TyConApp {}, LitTy {}) -> False

-- | Flatten an application f x y into (f,[x,y]).
fargs :: Type -> (Type, [(Type)])
fargs e = go e []
  where
    go (AppTy f x) args = go f (x : args)
    go f args = (f, args)

-- | Try to fill a hole with the given expression; if it type-checks,
-- we return the newly updated parse tree. Otherwise, we return Nothing.
tryWellTypedFill ::
     GhcMonad m
  => ParsedModule
  -> Hole
  -> HsExpr RdrName
  -> m (Maybe ParsedModule)
tryWellTypedFill pm hole expr =
  do handleSourceError
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
