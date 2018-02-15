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
  , timed
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
import           Data.Generics
import           Data.List
import qualified Data.Map.Strict as M
import           Data.Maybe
import           Data.Time
import           DynFlags
import           FastString
import           GHC
import           HscTypes
import           Name
import           Outputable
import           RdrName
import           SrcLoc
import           TcRnDriver
import           Text.Printf
import           TyCoRep
import           TyCon
import           Unify

--------------------------------------------------------------------------------
-- Types

timed :: MonadIO m => String -> m a -> m a
timed label m = do
  liftIO (putStrLn ("Starting " ++ label ++ " ... "))
  start <- liftIO getCurrentTime
  !v <- m
  end <- liftIO getCurrentTime
  liftIO (putStrLn (label ++ " took " ++ formatDiff (diffUTCTime end start)))
  pure v

formatDiff :: NominalDiffTime -> String
formatDiff d =
  printf "%.0fms" (realToFrac (d*1000) :: Double)

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
  timed
    "getCompletableModule"
    (fmap CompletableModule (parseModule ms >>= typecheckModuleNoDeferring))

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
declarationCompletions declaration =
  timed
    "declarationCompletions"
    (do names <-
          timed
            "declarationCompletions/combine names"
            (do let names =
                      map
                        nameRdrName
                        (filter
                           isValName
                           (fromMaybe
                              []
                              (modInfoTopLevelScope
                                 (declarationModuleInfo declaration))))
                liftIO (putStrLn ("Names: " ++ show (length names)))
                pure names)
        hscEnv <- getSession
        df <- getSessionDynFlags
        typedNames <-
          timed
            "declarationCompletions/typedNames"
            (liftIO
               (foldM
                  (\(!names') rdrName -> do
                     (_, ty) <-
                       tcRnExpr hscEnv TM_Inst (rdrNameToLHsExpr rdrName)
                     pure (maybe names' (: names') (fmap (rdrName, ) ty)))
                  []
                  names))
        timed
          "declarationCompletions/collectCompletions"
          (collectCompletions
             typedNames
             (declarationParsedModule declaration)
             (declarationHoles df declaration)))

-- showRdrName :: DynFlags -> GHC.RdrName -> String
-- showRdrName df n =
--   case n of
--     Unqual o -> "Unqual " ++ showPpr df o
--     Qual m o -> "Qual " ++ showPpr df m ++ " " ++ showPpr df o
--     Orig m o -> "Orig " ++ showPpr df m ++ " " ++ showPpr df o
--     Exact name -> "Exact " ++ showPpr df name

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
      rdrNamesAndParsedModules <-
        timed
          ("collectCompletions/getWellTypedFills for " ++ show hole)
          (getWellTypedFills parsedModule hole rdrNames)
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
  let hty = normalize (holeType hole)
  fmap
    snd
    (foldM
       (\(!cache, !candidates) (!rdrname, !typ) ->
          (do mparsedModule <-
                case M.lookup (StringEquality df typ) cache of
                  Just mparsedModule -> pure mparsedModule
                  Nothing ->
                    tryWellTypedFill pm hole (rdrNameToHsExpr rdrname) typ
              let !cache' = M.insert (StringEquality df typ) mparsedModule cache
                  !candidates' =
                    case mparsedModule of
                      Nothing -> candidates
                      Just parsedModule -> (rdrname, parsedModule) : candidates
              pure (cache', candidates')))
       (mempty, [])
       (filter (unifies hty . normalize . snd) names))

-- | The purpose of this function is to eliminate types that should
-- not be tested with a full module type-check. This checker is
-- stricter than GHC's own unifier, much stricter than Hoogle; it
-- produces false negatives. But it should not produce false positives
-- ideally.
unifies :: Type -> Type -> Bool
unifies t1 t2 = theirs t1 t2 && ours t1 t2
  where
    theirs x y = isJust (tcUnifyTyKi x y)
    -- Let them deal with lits:
    ours x@LitTy {} y@LitTy {} = theirs x y
    -- We assume a type variable unifies with anything, leave it to
    -- them:
    ours x@TyVarTy {} y = theirs x y
    ours x y@TyVarTy {} = theirs x y
    -- We ignore forall's:
    ours (ForAllTy _ x) y = ours x y
    ours x (ForAllTy _ y) = ours x y
    -- We ignore casts:
    ours (CastTy x _) y = ours x y
    ours x (CastTy y _) = ours x y
    -- We assume they know what to do with a coercion:
    ours x y@CoercionTy {} = theirs x y
    ours x@CoercionTy {} y = theirs x y
    -- We only let functions unify with functions, and apps unify with apps:
    ours (FunTy x y) (FunTy x' y') = ours x x' && ours y y'
    ours (AppTy f x) (AppTy f' x') = ours f f' && ours x x'
    -- We let them deal with this:
    ours x@TyConApp {} y@TyConApp {} = theirs x y
    -- These three should unify, so we let them deal with it:
    ours x@AppTy {} y@TyConApp {} = theirs x y
    ours y@TyConApp {} x@AppTy {} = theirs x y
    -- The rest SHOULD NOT be allowed to unify, because it's too
    -- general to produce DWIM results:
    ours FunTy {} _ = False
    ours _ FunTy {} = False
    ours AppTy {} _ = False
    ours _ AppTy {} = False
    ours TyConApp {} _ = False
    ours _ TyConApp {} = False

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

normalize :: Type -> Type
normalize =
  \case
    FunTy (TyConApp (tyConFlavour -> "class") _) x -> normalize x
    ForAllTy _ x -> normalize x
    CastTy x _ -> normalize x
    FunTy x y -> FunTy (normalize x) (normalize y)
    AppTy x y -> AppTy (normalize x) (normalize y)
    TyConApp tycon xs -> TyConApp tycon (map normalize xs)
    t@TyVarTy {} -> t
    t@LitTy {} -> t
    t@CoercionTy {} -> t

-- | Try to fill a hole with the given expression; if it type-checks,
-- we return the newly updated parse tree. Otherwise, we return Nothing.
tryWellTypedFill ::
     GhcMonad m
  => ParsedModule
  -> Hole
  -> HsExpr RdrName
  -> Type
  -> m (Maybe ParsedModule)
tryWellTypedFill pm hole expr typ =
  do df <- getSessionDynFlags
     timed
       ("tryWellTypedFill: " ++ showPpr df expr ++ " :: " ++ showPpr df typ)
       (handleSourceError
          (const (pure Nothing))
          (fmap
             (Just . tm_parsed_module)
             (typecheckModuleNoDeferring (fillHole pm hole expr))))

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
