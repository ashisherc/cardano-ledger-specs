{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Shelley.Spec.Ledger.STS.Ppup
  ( PPUP,
    PPUPEnv (..),
    PredicateFailure (..),
  )
where

import Byron.Spec.Ledger.Core (dom, (⊆), (⨃))
import Cardano.Binary
  ( FromCBOR (..),
    ToCBOR (..),
    decodeListLen,
    decodeWord,
    encodeListLen,
    matchSize,
  )
import Cardano.Prelude (NoUnexpectedThunks (..))
import Control.Monad.Trans.Reader (asks)
import Control.State.Transition
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import Data.Typeable (Typeable)
import Data.Word (Word8)
import GHC.Generics (Generic)
import Shelley.Spec.Ledger.BaseTypes
import Shelley.Spec.Ledger.Crypto (Crypto)
import Shelley.Spec.Ledger.Keys
import Shelley.Spec.Ledger.PParams
import Shelley.Spec.Ledger.Slot

data PPUP crypto

data PPUPEnv crypto
  = PPUPEnv SlotNo PParams (GenDelegs crypto)

instance STS (PPUP crypto) where
  type State (PPUP crypto) = ProposedPPUpdates crypto
  type Signal (PPUP crypto) = Maybe (Update crypto)
  type Environment (PPUP crypto) = PPUPEnv crypto
  type BaseM (PPUP crypto) = ShelleyBase
  data PredicateFailure (PPUP crypto)
    = NonGenesisUpdatePPUP
        !(Set (KeyHash 'Genesis crypto)) -- KeyHashes which are voting
        !(Set (KeyHash 'Genesis crypto)) -- KeyHashes which should be voting
    | PPUpdateTooLatePPUP
        !SlotNo -- current slot
        !SlotNo -- bound on when votes are allowed this epoch
    | PPUpdateWrongEpoch
        !EpochNo -- current epoch
        !EpochNo -- intended epoch of update
    | PVCannotFollowPPUP
        !ProtVer -- the first bad protocol version
    deriving (Show, Eq, Generic)

  initialRules = []

  transitionRules = [ppupTransitionNonEmpty]

instance NoUnexpectedThunks (PredicateFailure (PPUP crypto))

instance
  (Typeable crypto, Crypto crypto) =>
  ToCBOR (PredicateFailure (PPUP crypto))
  where
  toCBOR = \case
    (NonGenesisUpdatePPUP a b) ->
      encodeListLen 3
        <> toCBOR (0 :: Word8)
        <> toCBOR a
        <> toCBOR b
    PPUpdateTooLatePPUP s t -> encodeListLen 3 <> toCBOR (1 :: Word8) <> toCBOR s <> toCBOR t
    PPUpdateWrongEpoch ce e -> encodeListLen 3 <> toCBOR (2 :: Word8) <> toCBOR ce <> toCBOR e
    PVCannotFollowPPUP p -> encodeListLen 2 <> toCBOR (3 :: Word8) <> toCBOR p

instance
  (Crypto crypto) =>
  FromCBOR (PredicateFailure (PPUP crypto))
  where
  fromCBOR = do
    n <- decodeListLen
    decodeWord >>= \case
      0 -> do
        matchSize "NonGenesisUpdatePPUP" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ NonGenesisUpdatePPUP a b
      1 -> do
        matchSize "PPUpdateTooLatePPUP" 3 n
        s <- fromCBOR
        t <- fromCBOR
        pure $ PPUpdateTooLatePPUP s t
      2 -> do
        matchSize "PPUpdateWrongEpoch" 3 n
        a <- fromCBOR
        b <- fromCBOR
        pure $ PPUpdateWrongEpoch a b
      3 -> do
        matchSize "PVCannotFollowPPUP" 2 n
        p <- fromCBOR
        pure $ PVCannotFollowPPUP p
      k -> invalidKey k

pvCanFollow :: ProtVer -> StrictMaybe ProtVer -> Bool
pvCanFollow _ SNothing = True
pvCanFollow (ProtVer m n) (SJust (ProtVer m' n')) =
  (m + 1, 0) == (m', n') || (m, n + 1) == (m', n')

ppupTransitionNonEmpty :: TransitionRule (PPUP crypto)
ppupTransitionNonEmpty = do
  TRC (PPUPEnv slot pp (GenDelegs _genDelegs), ProposedPPUpdates pupS, up) <-
    judgmentContext

  case up of
    Nothing -> pure (ProposedPPUpdates pupS)
    Just (Update (ProposedPPUpdates pup) te) -> do
      (dom pup ⊆ dom _genDelegs) ?! NonGenesisUpdatePPUP (dom pup) (dom _genDelegs)

      let goodPV = pvCanFollow (_protocolVersion pp) . _protocolVersion
      let badPVs = Map.filter (not . goodPV) pup
      case Map.toList (Map.map _protocolVersion badPVs) of
        ((_, SJust pv) : _) -> failBecause $ PVCannotFollowPPUP pv
        _ -> pure ()

      sp <- liftSTS $ asks stabilityWindow
      firstSlotNextEpoch <- liftSTS $ do
        ei <- asks epochInfo
        EpochNo e <- epochInfoEpoch ei slot
        epochInfoFirst ei (EpochNo $ e + 1)
      let tooLate = firstSlotNextEpoch *- (Duration (2 * sp))
      slot < tooLate ?! PPUpdateTooLatePPUP slot tooLate

      currentEpoch <- liftSTS $ do
        ei <- asks epochInfo
        epochInfoEpoch ei slot
      currentEpoch == te ?! PPUpdateWrongEpoch currentEpoch te

      pure $ ProposedPPUpdates (pupS ⨃ Map.toList pup)
