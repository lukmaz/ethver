module ConstantsEthver where

import AbsEthver

-------------
-- NUMBERS --
-------------

nMaxRuns = 2 -- ???

nMaxCommitments = 2

nUndefModuleNumber = 42
nWrongExp = 43
nInitContractState = 1
nInitCommState = 1

nMinP0State = -1
nMinP1State = -1
nInitP0State = 0
nInitP1State = 0

-- transaction states
nTNone = 0
nTBroadcast = 1
nTExecuted = 2
nTInvalidated = 3

nTStates = 4
-------------
-- STRINGS --
-------------

-- Constants

sMaxUserBalance = "USER_BALANCE_MAX"
sMaxContractBalance = "CONTRACT_BALANCE_MAX"
sNumContractStates = "NUM_CONTRACT_STATES"
sNumCommStates = "NUM_COMMUNICATION_STATES"
sNumP0States = "NUM_PLAYER0_STATES"
sNumP1States = "NUM_PLAYER1_STATES"

-- TODO: wymagać, żeby było w .etv:
sInitContractBalance = "CONTRACT_BALANCE_INIT"
sInitUser0Balance = "USER0_BALANCE_INIT"
sInitUser1Balance = "USER1_BALANCE_INIT"
sMaxValue = "MAX_VALUE"
sMaxTime = "MAX_TIME"
sMaxSignatures = "MAX_SIGNATURES"
sTimeDelta = "TIME_DELTA"

sContrState = "contrstate"
sCommState = "commstate"
sBCState = "bcstate"
sP0State = "state0"
sP1State = "state1"
sStatePrefix = "state"
sStatusSuffix = "_status"
-- TODO: to remove
sSigSuffix = "_sig"
sAttrSuffix = "_attr"
sKeySuffix = "_key"
-- TODO: To remove
sRunsSuffix = "_runs"
sEmptyState = "empty_state"
sEmptySender = "empty_sender"
sTimeElapsed = "time_elapsed"
sTimelockStep = "timelock_step"
sNextState = "next_state"
sCommitmentValSuffix = "_val"
sCommitmentNonceSuffix = "_nonce"
sGlobalCommitments = "global_commitments"
sGlobalSignatures = "global_signatures"
sRandomCommitment = "random_commitment"
sOpenCommitment = "open_commitment"

sEmptyModule = "emptyModule"

sBCModule = "blockchain"
sContrModule = "contract"
sCommModule = "communication"
sP0Module = "player0"
sP1Module = "player1"


sContractBalance = "contract_balance"
sBalancePrefix = "balance"
sP0Balance = "balance0"
sP1Balance = "balance1"
sLocalSuffix = "_local"
sStateSuffix = "_state"
sValueSuffix = "_value"
sBroadcastPrefix = "broadcast_"
sCommunicatePrefix = "communicate_"

sCriticalSection = "critical_section"
sCriticalSection0 = "critical_section0"
sCriticalSection1 = "critical_section1"

sAdversaryFlag = "ADVERSARY"
sContrSender = "contr_sender"
sCommSender = "comm_sender"
sValue = "value"

sNull = "null"

sContractStart = "contract_start"
sNow = "now"

-- transaction states
sTNone = "T_NONE"
sTBroadcast = "T_BROADCAST"
sTExecuted = "T_EXECUTED"
sTInvalidated = "T_INVALIDATED"

sSendTransaction = "sendTransaction"
sSendCommunication = "sendCommunication"
sCall = "call"
sRandom = "random"

sReturnValueSuffix = "_returnValue"

-- IDENTS

iContrState = Ident sContrState
iCommState = Ident sCommState
iMaxUserBalance = Ident sMaxUserBalance
iMaxContractBalance = Ident sMaxContractBalance
iNextState = Ident sNextState
iMaxValue = Ident sMaxValue

iContractBalance = Ident sContractBalance

iCriticalSection = Ident sCriticalSection
iCriticalSection0 = Ident sCriticalSection0
iCriticalSection1 = Ident sCriticalSection1

iContrSender = Ident sContrSender
iCommSender = Ident sCommSender
iValue = Ident sValue

iTNone = Ident sTNone
iTBroadcast = Ident sTBroadcast
iTExecuted = Ident sTExecuted
iTInvalidated = Ident sTInvalidated

iAdversaryFlag = Ident sAdversaryFlag

iSendTransaction = Ident sSendTransaction
iSendCommunication = Ident sSendCommunication
iCall = Ident sCall
iRandom = Ident sRandom

iTimeElapsed = Ident sTimeElapsed
