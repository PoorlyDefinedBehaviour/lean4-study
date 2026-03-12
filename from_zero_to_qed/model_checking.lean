structure Config where
  threshold : Nat
  timeout : Nat
deriving DecidableEq, Repr

inductive State where
  | closed (failures : Nat) : State
  | opened (openedAt : Nat) : State
  | halfOpen : State
deriving DecidableEq, Repr

inductive Event where
  | success :Event
  | failure (time : Nat) : Event
  | tick (time : Nat) : Event
  | probeSuccess (time : Nat) : Event
  | probeFailure (time : Nat) : Event
deriving DecidableEq

def step (cfg : Config) (s : State) (e : Event) : State :=
  match s, e with
  | .closed _, .success => .closed 0
  | .closed failures, .failure time =>
    if failures + 1 ≥ cfg.threshold then .opened time
    else .closed (failures + 1)
  | .opened openedAt, .tick time =>
    if time - openedAt ≥ cfg.timeout then .halfOpen
    else .opened openedAt
  | .halfOpen, .probeSuccess _ => .closed 0
  | .halfOpen, .probeFailure time => .opened time
  | s, _ => s

def Invariant (cfg : Config) : State → Prop
  | .closed failures => failures < cfg.threshold
  | .opened _ => True
  | .halfOpen => True


theorem initial_invariant (cfg : Config) (h : cfg.threshold > 0) :
    Invariant cfg initial := h

theorem step_preserves_invariant (cfg : Config) (s : State) (e : Event) (hinv : Invariant cfg s) (hpos : cfg.threshold > 0) :
  Invariant cfg (step cfg s e) := by
  cases s with
  | closed failures =>
    cases e with
    | success => simp [step, Invariant, hpos]
    | failure time =>
      simp only [step]
      split
      · simp [Invariant]
      · simp [Invariant]
        omega
    | tick _ =>
      simp [step, Invariant]
      exact hinv
    | probeSuccess _ =>
      simp [step, Invariant]
      exact hinv
    | probeFailure _ =>
      simp [step, Invariant]
      exact hinv
  | opened openedAt =>
    cases e with
    | tick time =>
      simp only [step]
      split <;> simp [Invariant]
    | _ => simp [step, Invariant]
  | halfOpen =>
    cases e with
    | probeSuccess _ => simp [step, Invariant, hpos]
    | probeFailure _ => simp [step, Invariant]
    | _ => simp [step, Invariant]

theorem success_resets (cfg : Config) (f : Nat) :
    step cfg (.closed f) .success = .closed 0 := rfl

theorem threshold_trips (cfg : Config) (f t : Nat) (h : f + 1 >= cfg.threshold) :
    step cfg (.closed f) (.failure t) = .opened t := by simp [step, h]

theorem below_threshold_increments (cfg : Config) (f t : Nat) (h : f + 1 < cfg.threshold) :
    step cfg (.closed f) (.failure t) = .closed (f + 1) := by
  simp [step]; omega

theorem timeout_transitions (cfg : Config) (o t : Nat) (h : t - o >= cfg.timeout) :
    step cfg (.opened o) (.tick t) = .halfOpen := by simp [step, h]

theorem probe_success_closes (cfg : Config) (t : Nat) :
    step cfg .halfOpen (.probeSuccess t) = .closed 0 := rfl

theorem probe_failure_reopens (cfg : Config) (t : Nat) :
    step cfg .halfOpen (.probeFailure t) = .opened t := rfl
