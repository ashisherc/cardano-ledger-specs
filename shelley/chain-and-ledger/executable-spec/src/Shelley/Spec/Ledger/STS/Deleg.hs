{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Shelley.Spec.Ledger.STS.Deleg
  ( DELEG,
    DelegEnv (..),
    PredicateFailure (..),
  )
where

import Byron.Spec.Ledger.Core (dom, range, singleton, (∈), (∉), (∪), (⋪), (⋫), (⨃))
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
  ( (?!),
    STS (..),
    TRC (..),
    TransitionRule,
    failBecause,
    judgmentContext,
    liftSTS,
  )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Typeable (Typeable)
import Data.Word (Word8)
import GHC.Generics (Generic)
import Shelley.Spec.Ledger.BaseTypes
  ( Globals (..),
    ShelleyBase,
    invalidKey,
  )
import Shelley.Spec.Ledger.Coin (Coin (..))
import Shelley.Spec.Ledger.Credential (Credential)
import Shelley.Spec.Ledger.Crypto (Crypto)
import Shelley.Spec.Ledger.Keys
  ( GenDelegs (..),
    Hash,
    KeyHash,
    KeyRole (..),
    VerKeyVRF,
  )
import Shelley.Spec.Ledger.LedgerState
  ( AccountState (..),
    DState,
    FutureGenDeleg (..),
    InstantaneousRewards (..),
    _delegations,
    _fGenDelegs,
    _genDelegs,
    _irwd,
    _ptrs,
    _rewards,
    _stkCreds,
    emptyDState,
  )
import Shelley.Spec.Ledger.Slot
  ( (*-),
    (+*),
    Duration (..),
    EpochNo (..),
    SlotNo,
    epochInfoEpoch,
    epochInfoFirst,
  )
import Shelley.Spec.Ledger.TxData
  ( DCert (..),
    DelegCert (..),
    Delegation (..),
    GenesisDelegCert (..),
    MIRCert (..),
    MIRPot (..),
    Ptr,
    RewardAcnt (..),
  )

data DELEG crypto

data DelegEnv = DelegEnv
  { slotNo :: SlotNo,
    ptr_ :: Ptr,
    acnt_ :: AccountState
  }
  deriving (Show, Eq)

instance STS (DELEG crypto) where
  type State (DELEG crypto) = DState crypto
  type Signal (DELEG crypto) = DCert crypto
  type Environment (DELEG crypto) = DelegEnv
  type BaseM (DELEG crypto) = ShelleyBase
  data PredicateFailure (DELEG crypto)
    = StakeKeyAlreadyRegisteredDELEG
        !(Credential 'Staking crypto) -- Credential which is already registered
    | StakeKeyNotRegisteredDELEG
        !(Credential 'Staking crypto) -- Credential which is not registered
    | StakeKeyNonZeroAccountBalanceDELEG
        !(Maybe Coin) -- The remaining reward account balance, if it exists
    | StakeDelegationImpossibleDELEG
        !(Credential 'Staking crypto) -- Credential that is not registered
    | WrongCertificateTypeDELEG -- The DCertPool constructor should not be used by this transition
    | GenesisKeyNotInpMappingDELEG
        !(KeyHash 'Genesis crypto) -- Unknown Genesis KeyHash
    | DuplicateGenesisDelegateDELEG
        !(KeyHash 'GenesisDelegate crypto) -- Keyhash which is already delegated to
    | InsufficientForInstantaneousRewardsDELEG
        !MIRPot -- which pot the rewards are to be drawn from, treasury or reserves
        !Coin -- amount of rewards to be given out
        !Coin -- size of the pot from which the lovelace is drawn
    | MIRCertificateTooLateinEpochDELEG
        !SlotNo -- current slot
        !SlotNo -- MIR must be submitted before this slot
    | DuplicateGenesisVRFDELEG
        !(Hash crypto (VerKeyVRF crypto)) --VRF KeyHash which is already delegated to
    deriving (Show, Eq, Generic)

  initialRules = [pure emptyDState]
  transitionRules = [delegationTransition]

instance NoUnexpectedThunks (PredicateFailure (DELEG crypto))

instance
  (Typeable crypto, Crypto crypto) =>
  ToCBOR (PredicateFailure (DELEG crypto))
  where
  toCBOR = \case
    StakeKeyAlreadyRegisteredDELEG cred ->
      encodeListLen 2 <> toCBOR (0 :: Word8) <> toCBOR cred
    StakeKeyNotRegisteredDELEG cred ->
      encodeListLen 2 <> toCBOR (1 :: Word8) <> toCBOR cred
    StakeKeyNonZeroAccountBalanceDELEG rewardBalance ->
      encodeListLen 2 <> toCBOR (2 :: Word8) <> toCBOR rewardBalance
    StakeDelegationImpossibleDELEG cred ->
      encodeListLen 2 <> toCBOR (3 :: Word8) <> toCBOR cred
    WrongCertificateTypeDELEG ->
      encodeListLen 1 <> toCBOR (4 :: Word8)
    GenesisKeyNotInpMappingDELEG gkh ->
      encodeListLen 2 <> toCBOR (5 :: Word8) <> toCBOR gkh
    DuplicateGenesisDelegateDELEG kh ->
      encodeListLen 2 <> toCBOR (6 :: Word8) <> toCBOR kh
    InsufficientForInstantaneousRewardsDELEG pot needed potAmount ->
      encodeListLen 4 <> toCBOR (7 :: Word8)
        <> toCBOR pot
        <> toCBOR needed
        <> toCBOR potAmount
    MIRCertificateTooLateinEpochDELEG sNow sTooLate ->
      encodeListLen 3 <> toCBOR (8 :: Word8) <> toCBOR sNow <> toCBOR sTooLate
    DuplicateGenesisVRFDELEG vrf ->
      encodeListLen 2 <> toCBOR (9 :: Word8) <> toCBOR vrf

instance
  (Crypto crypto) =>
  FromCBOR (PredicateFailure (DELEG crypto))
  where
  fromCBOR = do
    n <- decodeListLen
    decodeWord >>= \case
      0 -> do
        matchSize "StakeKeyAlreadyRegisteredDELEG" 2 n
        kh <- fromCBOR
        pure $ StakeKeyAlreadyRegisteredDELEG kh
      1 -> do
        matchSize "StakeKeyNotRegisteredDELEG" 2 n
        kh <- fromCBOR
        pure $ StakeKeyNotRegisteredDELEG kh
      2 -> do
        matchSize "StakeKeyNonZeroAccountBalanceDELEG" 2 n
        b <- fromCBOR
        pure $ StakeKeyNonZeroAccountBalanceDELEG b
      3 -> do
        matchSize "StakeDelegationImpossibleDELEG" 2 n
        kh <- fromCBOR
        pure $ StakeDelegationImpossibleDELEG kh
      4 -> do
        matchSize "WrongCertificateTypeDELEG" 1 n
        pure WrongCertificateTypeDELEG
      5 -> do
        matchSize "GenesisKeyNotInpMappingDELEG" 2 n
        gkh <- fromCBOR
        pure $ GenesisKeyNotInpMappingDELEG gkh
      6 -> do
        matchSize "DuplicateGenesisDelegateDELEG" 2 n
        kh <- fromCBOR
        pure $ DuplicateGenesisDelegateDELEG kh
      7 -> do
        matchSize "InsufficientForInstantaneousRewardsDELEG" 4 n
        pot <- fromCBOR
        needed <- fromCBOR
        potAmount <- fromCBOR
        pure $ InsufficientForInstantaneousRewardsDELEG pot needed potAmount
      8 -> do
        matchSize "MIRCertificateTooLateinEpochDELEG" 3 n
        sNow <- fromCBOR
        sTooLate <- fromCBOR
        pure $ MIRCertificateTooLateinEpochDELEG sNow sTooLate
      9 -> do
        matchSize "DuplicateGenesisVRFDELEG" 2 n
        vrf <- fromCBOR
        pure $ DuplicateGenesisVRFDELEG vrf
      k -> invalidKey k

delegationTransition ::
  TransitionRule (DELEG crypto)
delegationTransition = do
  TRC (DelegEnv slot ptr acnt, ds, c) <- judgmentContext
  network <- liftSTS $ asks networkId
  case c of
    DCertDeleg (RegKey hk) -> do
      -- note that pattern match is used instead of regCred, as in the spec
      hk ∉ dom (_stkCreds ds) ?! StakeKeyAlreadyRegisteredDELEG hk

      pure $
        ds
          { _stkCreds = _stkCreds ds ∪ singleton hk slot,
            _rewards = _rewards ds ∪ Map.singleton (RewardAcnt network hk) (Coin 0), -- ∪ is override left
            _ptrs = _ptrs ds ∪ Map.singleton ptr hk
          }
    DCertDeleg (DeRegKey hk) -> do
      -- note that pattern match is used instead of cwitness, as in the spec
      hk ∈ dom (_stkCreds ds) ?! StakeKeyNotRegisteredDELEG hk

      let rewardCoin = Map.lookup (RewardAcnt network hk) (_rewards ds)
      rewardCoin == Just 0 ?! StakeKeyNonZeroAccountBalanceDELEG rewardCoin

      pure $
        ds
          { _stkCreds = Set.singleton hk ⋪ _stkCreds ds,
            _rewards = Set.singleton (RewardAcnt network hk) ⋪ _rewards ds,
            _delegations = Set.singleton hk ⋪ _delegations ds,
            _ptrs = _ptrs ds ⋫ Set.singleton hk
          }
    DCertDeleg (Delegate (Delegation hk dpool)) -> do
      -- note that pattern match is used instead of cwitness and dpool, as in the spec
      hk ∈ dom (_stkCreds ds) ?! StakeDelegationImpossibleDELEG hk

      pure $
        ds
          { _delegations = _delegations ds ⨃ [(hk, dpool)]
          }
    DCertGenesis (GenesisDelegCert gkh vkh vrf) -> do
      sp <- liftSTS $ asks stabilityWindow
      -- note that pattern match is used instead of genesisDeleg, as in the spec
      let s' = slot +* Duration sp
          (GenDelegs genDelegs) = _genDelegs ds

      gkh ∈ dom genDelegs ?! GenesisKeyNotInpMappingDELEG gkh

      let currentOtherDelegations =
            range $
              Map.filterWithKey (\k _ -> k /= gkh) genDelegs
          futureOtherDelegations =
            range $
              Map.filterWithKey (\(FutureGenDeleg _ k) _ -> k /= gkh) (_fGenDelegs ds)
          currentOtherColdKeyHashes = Set.map fst currentOtherDelegations
          futureOtherColdKeyHashes = Set.map fst futureOtherDelegations
          currentOtherVrfKeyHashes = Set.map snd currentOtherDelegations
          futureOtherVrfKeyHashes = Set.map snd futureOtherDelegations

      vkh ∉ (currentOtherColdKeyHashes `Set.union` futureOtherColdKeyHashes)
        ?! DuplicateGenesisDelegateDELEG vkh
      vrf ∉ (currentOtherVrfKeyHashes `Set.union` futureOtherVrfKeyHashes)
        ?! DuplicateGenesisVRFDELEG vrf

      pure $
        ds
          { _fGenDelegs = _fGenDelegs ds ⨃ [(FutureGenDeleg s' gkh, (vkh, vrf))]
          }
    DCertMir (MIRCert targetPot credCoinMap) -> do
      sp <- liftSTS $ asks stabilityWindow
      firstSlot <- liftSTS $ do
        ei <- asks epochInfo
        EpochNo currEpoch <- epochInfoEpoch ei slot
        epochInfoFirst ei $ EpochNo (currEpoch + 1)
      let tooLate = firstSlot *- Duration sp
      slot < tooLate
        ?! MIRCertificateTooLateinEpochDELEG slot tooLate

      let (potAmount, instantaneousRewards) =
            case targetPot of
              ReservesMIR -> (_reserves acnt, iRReserves $ _irwd ds)
              TreasuryMIR -> (_treasury acnt, iRTreasury $ _irwd ds)
      let combinedMap = Map.union credCoinMap instantaneousRewards
          requiredForRewards = sum combinedMap
      requiredForRewards <= potAmount
        ?! InsufficientForInstantaneousRewardsDELEG targetPot requiredForRewards potAmount

      case targetPot of
        ReservesMIR -> pure $ ds {_irwd = (_irwd ds) {iRReserves = combinedMap}}
        TreasuryMIR -> pure $ ds {_irwd = (_irwd ds) {iRTreasury = combinedMap}}
    DCertPool _ -> do
      failBecause WrongCertificateTypeDELEG -- this always fails
      pure ds
