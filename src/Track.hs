{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Track dependencies on a predicate.

module Track
  ( trackGraph
  , trackThrows
  , track
  ) where

import           Bag
import           Control.Monad.IO.Class
import           Data.Data
import           Data.Generics
import qualified Data.Graph as Graph
import           Data.List
import           Data.Maybe
import           Debug.Trace
import qualified FastString as GHC
import qualified GHC
import qualified Id as GHC
import qualified Module as GHC
import qualified Name as GHC

-- | Some binding declared top-level in a module.
data Binding = Binding
  { bindingFlagged :: Bool        -- ^ This binding was flagged by a predicate.
  , bindingId      :: BindingId   -- ^ A unique ID for this binding.
  , bindingSrcSpan :: GHC.SrcSpan -- ^ Location for the binding.
  , bindingRefs    :: [BindingId] -- ^ Bindings that I reference.
  } deriving (Show)

-- | ID for a binding declared in some package, in some module, with
-- some name.
data BindingId = BindingId
  { bindingIdPackage :: String
  , bindingIdModule :: String
  , bindingIdName :: String
  } deriving (Show)

prettyBindingId :: BindingId -> String
prettyBindingId (BindingId pkg md name) = pkg ++ ":" ++ md ++ "." ++ name

-- | Track through the module grpah.
trackThrows :: GHC.GhcMonad m => m ()
trackThrows = trackGraph existing (const (const False))
  where
    existing =
      [ Binding
          { bindingFlagged = True
          , bindingId =
              (BindingId
                 { bindingIdPackage = "base"
                 , bindingIdModule = "GHC.Err"
                 , bindingIdName = "undefined"
                 })
          , bindingSrcSpan = GHC.UnhelpfulSpan (GHC.mkFastString "")
          , bindingRefs = []
          }
      , Binding
          { bindingFlagged = True
          , bindingId =
              (BindingId
                 { bindingIdPackage = "base"
                 , bindingIdModule = "GHC.List"
                 , bindingIdName = "head"
                 })
          , bindingSrcSpan = GHC.UnhelpfulSpan (GHC.mkFastString "")
          , bindingRefs = []
          }
      ,  Binding
           { bindingFlagged = True
           , bindingId =
               (BindingId
                  { bindingIdPackage = "base"
                  , bindingIdModule = "GHC.IO.Unsafe"
                  , bindingIdName = "unsafeDupablePerformIO"
                  })
           , bindingSrcSpan = GHC.UnhelpfulSpan (GHC.mkFastString "")
           , bindingRefs = []
           }
      ]

-- | Track through the module grpah.
trackGraph :: GHC.GhcMonad m => [Binding] -> (GHC.Module -> GHC.HsExpr GHC.Id -> Bool) -> m ()
trackGraph existingBindings shouldFlag = do
  mgraph <- GHC.getModuleGraph
  liftIO
    (putStrLn
       ("Tracking module graph for " ++ show (length mgraph) ++ " module(s) ..."))
  newBindings <- fmap concat (mapM (track shouldFlag) mgraph)
  let (graph, vertexToNode, _lookupVertexByKey) =
        Graph.graphFromEdges
          (map
             (\binding -> (binding, bindingId binding, bindingRefs binding))
             (newBindings ++ existingBindings))
      flaggedVertices :: [(Graph.Vertex, Binding)]
      flaggedVertices =
        filter
          (bindingFlagged . snd)
          (map
             (\v ->
                (let (b, _, _) = vertexToNode v
                  in (v, b)))
             (Graph.topSort graph))
  liftIO
    (mapM_
       (\(v, judas) -> do
          putStrLn ("Flagged binding: " ++ prettyBindingId (bindingId judas))
          let revDeps = map vertexToNode (filter (/= v) (Graph.reachable (Graph.transposeG graph) v))
          if not (null revDeps)
            then do
              putStrLn "Which is used by these directly or indirectly:"
              mapM_
                (\(_, bid, _) ->
                   putStrLn ("  " ++ prettyBindingId bid))
                revDeps
            else pure ())
       flaggedVertices)

-- | Type-check the module and track through it.
track ::
     GHC.GhcMonad m
  => (GHC.Module -> GHC.HsExpr GHC.Id -> Bool)
  -> GHC.ModSummary
  -> m [Binding]
track shouldFlag modSummary = do
  df <- GHC.getSessionDynFlags
  parsedModule <- GHC.parseModule modSummary
  typecheckedModule <- GHC.typecheckModule parsedModule
  let typecheckedSource = GHC.tm_typechecked_source typecheckedModule
  pure (getBindings df typecheckedSource)
  where
    getBindings df bag = concatMap (getBinding df) (bagToList bag)
    getBinding ::
         GHC.DynFlags -> GHC.Located (GHC.HsBindLR GHC.Id GHC.Id) -> [Binding]
    getBinding df located =
      case GHC.unLoc located of
        GHC.VarBind {GHC.var_id = id', GHC.var_rhs = rhs} ->
          [ Binding
              { bindingFlagged = not (null (listify (shouldFlag module') rhs))
              , bindingId = idToBindingId (GHC.ms_mod modSummary) id'
              , bindingSrcSpan = GHC.getLoc located
              , bindingRefs =
                  map
                    (idToBindingId (GHC.ms_mod modSummary) . GHC.unLoc)
                    (referencedIds id' rhs)
              }
          ]
        GHC.FunBind {GHC.fun_id = (GHC.unLoc -> id'), GHC.fun_matches = rhs} ->
          [ Binding
              { bindingFlagged = not (null (listify (shouldFlag module') rhs))
              , bindingId = idToBindingId module' id'
              , bindingSrcSpan = GHC.getLoc located
              , bindingRefs =
                  map
                    (idToBindingId module' . GHC.unLoc)
                    (referencedIds id' rhs)
              }
          ]
        GHC.AbsBinds {GHC.abs_binds = binds} -> getBindings df binds
        GHC.AbsBindsSig {GHC.abs_sig_bind = bind} -> getBinding df bind
    module' = (GHC.ms_mod modSummary)

-- | Get all the referenced variable IDs listed in an AST.
referencedIds :: Data ast => GHC.Id -> ast -> [GHC.Located GHC.Id]
referencedIds ignore =
  nub .
  mapMaybe
    (\case
       GHC.HsVar i -> Just i
       _ -> Nothing) .
  listify
    (\case
       GHC.HsVar i -> GHC.unLoc i /= ignore
       _ -> False)

idToBindingId :: GHC.Module -> GHC.Id -> BindingId
idToBindingId module0 gid =
  BindingId
    { bindingIdPackage = packageNameVersion
    , bindingIdModule = moduleNameString
    , bindingIdName = nameString
    }
  where
    name = GHC.idName gid
    occName = GHC.nameOccName name
    module' = GHC.nameModule_maybe name
    nameString = GHC.occNameString occName
    unitId = GHC.moduleUnitId (fromMaybe module0 module')
    moduleName = GHC.moduleName (fromMaybe module0 module')
    packageNameVersion = GHC.unitIdString unitId
    moduleNameString = GHC.moduleNameString moduleName
