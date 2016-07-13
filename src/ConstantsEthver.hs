module ConstantsEthver where

import AbsEthver

-------------
-- NUMBERS --
-------------

nUndefModuleNumber = 42
nWrongExp = 43
nInitContractState = 1

-- TODO: wczytywać
nInitUserBalance = 2

nMinP0State = -1
nMinP1State = -1
nInitP0State = 0
nInitP1State = 0
nInitContrState = 1

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
sNumP0States = "NUM_PLAYER0_STATES"
sNumP1States = "NUM_PLAYER1_STATES"

sContrState = "contrstate"
sCommState = "commstate"
sBCState = "bcstate"
sP0State = "state0"
sP1State = "state1"
sStatePrefix = "state"
sEmptyState = "emptyState"

sNextState = "next_state"

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
sLocalSufix = "_local"
sStateSufix = "_state"
sValueSufix = "_value"
sBroadcastPrefix = "broadcast_"
sCommunicatePrefix = "communicate_"

sCriticalSection = "critical_section"
sCriticalSection0 = "critical_section0"
sCriticalSection1 = "critical_section1"

sAdversaryFlag = "ADVERSARY"
sSender = "sender"
sValue = "value"

-- transaction states
sTNone = "T_NONE"
sTBroadcast = "T_BROADCAST"
sTExecuted = "T_EXECUTED"
sTInvalidated = "T_INVALIDATED"

sSendTransaction = "sendTransaction"
sSendCommunication = "sendCommunication"
sCall = "call"
sRandom = "random"
sRandomLazy = "random_lazy"

sReturnValueSufix = "_returnValue"


-- IDENTS

iContrState = Ident sContrState
iMaxUserBalance = Ident sMaxUserBalance
iMaxContractBalance = Ident sMaxContractBalance
iNextState = Ident sNextState

iContractBalance = Ident sContractBalance

iCriticalSection = Ident sCriticalSection
iCriticalSection0 = Ident sCriticalSection0
iCriticalSection1 = Ident sCriticalSection1

iSender = Ident sSender
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
iRandomLazy = Ident sRandomLazy
