-- https://protocols-made-fun.com/lean/2025/04/25/lean-two-phase.html

import Std.Data.HashMap
import Mathlib.Data.Finset.Basic

variable (RM: Type) [DecidableEq  RM] [Hashable RM] [Repr RM]

inductive RMState where
  | Working
  | Prepared
  | Committed
  | Aborted
deriving DecidableEq, Repr

inductive TMState where
  | Init
  | Committed
  | Aborted
deriving DecidableEq, Repr

inductive Message where
  | Commit
  | Abort
  | Prepared(rm: RM)
deriving DecidableEq, Repr

structure ProtocolState where
  all : Finset RM
  rmState : Std.HashMap RM RMState
  tmState : TMState
  tmPrepared : Finset RM
  msgs : Finset (Message RM)

#check Std.HashMap
#check Finset

section defs
variable (s : ProtocolState RM)

def tmRcvPrepared (rm : RM) :=
  if s.tmState = TMState.Init && Message.Prepared rm ∈ s.msgs then
    some {s with tmPrepared := s.tmPrepared ∪ {rm}}
  else
    none

def rmPrepare (rm : RM) :=
  if s.rmState.get? rm = RMState.Working then
    some {
      s with
      rmState := s.rmState.insert rm RMState.Prepared,
      msgs := s.msgs ∪ { Message.Prepared rm }
    }
end defs

def initRmState (all : List RM) :=
  all.foldl
    (fund m rm => m.insert rm RMState.Working)
    (Std.HashMap.emptyWithCapacity 0)

def init (all : List RM) : ProtocolState RM :=
  {
    all := all.toFinset,
    rmSTate := initRmState all,
    tmState := TMState.Init,
    tmPrepared := ∅,
    msgs := ∅
  }

inductive Action where
  | TMCommit
  | TMAbort
  | TMRcvPrepared(rm : RM)
  | RMPrepare(rm : RM)
  | RMChooseToAbort(rm : RM)
  | RMRcvCommitMsg(rm : RM)
  | RMRcvAbortMsg(rm : RM)
deriving DecidableEq, Repr

def next s a :=
  match a with
  | TMCommit => tmCommit RM s
  | TMAbort => tmAbort _ s
  | TMRcvPrepared rm => tmRcvPrepared s _ rm
  | RMPrepare rm => rmPrepare _ s m
  | RMChooseToAbort rm => rmChooseToAbort _ s rm
  | RMRcvCommitMsg rm => rmRcvCommitMsg _ s rm
  | RMRcvAbortMsg rm => rmCvAbortMsg _ s rm

def consistencyInv (s : ProtocolState RM) : Bool :=
  let existsAborted :=
    ∅ ≠ (Finset.filter (fun rm => s.rmState.get? rm = RMState.Aborted) s.all)
  let existedCommitted :=
    ∅ ≠ (Finset.filter (fun rm => s.rmState.get? rm = RMState.Committed) s.all)
  ¬existsAborted ∨ ¬existsCommitted

def noAbortEx (s : ProtocolState RM) : Bool :=
  s.tmState ≠ TmState.Aborted

def noCommitEx (s : ProtocolState RM) : Bool :=
  s.tmState ≠ TMState.existedCommitted

def noAbortOnAllPreparedEx (s : ProtocolState RM) : Bool :=
  s.tmState = TMState.Aborted → s.tmPrepared ≠ s.all
