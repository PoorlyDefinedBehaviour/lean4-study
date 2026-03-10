def greet : IO Unit := do
  IO.println "What is your name?"
  let stdin ← IO.getStdin
  let name ← stdin.getLine
  IO.println s!"Hello, {name.trim}!"

def printNumbers : IO Unit := do
  for i in [1,2,3,4,5] do
    IO.println s!"Number: {i}"

def getCurrentTime : IO Unit := do
  let now ← IO.monoMsNow
  IO.println s!"Milliseconds since start: {now}"

#eval greet
#eval printNumbers
#eval getCurrentTime

def pureComputation : IO Nat := do
  let x := 10
  let y := 20
  return x + y

def combineIO : IO String := do
  let a ← pure "Hello"
  let b ← pure "World"
  return s!"{a}, {b}"

#eval pureComputation
#eval combineIO

def writeToFile (path : String) (content : String) : IO Unit := do
  IO.FS.writeFile path content

def readFromFile (path : String) : IO String := do
  IO.FS.readFile path

def appendToFile (path : String) (content : String) : IO Unit := do
  let handle ← IO.FS.Handle.mk path .append
  handle.putStrLn content

def copyFile (src dst : String) : IO Unit := do
  let content ← IO.FS.readFile src
  IO.FS.writeFile dst content

#eval readFromFile "from_zero_to_qed/io_and_concurrency.lean"

def processLines (path : String) : IO (List String) := do
  let content ← IO.FS.readFile path
  return content.splitOn "\n"

def countLines (path : String) : IO Nat := do
  let lines ← processLines path
  return lines.length

def filterLines' (path : String) (pred : String → Bool) : IO (List String) := do
  let lines ← processLines path
  return lines.filter pred

#eval countLines "from_zero_to_qed/io_and_concurrency.lean"

def safeDivideIO (x y : Nat) : IO Nat := do
  if y == 0 then
    throw <| IO.userError "Division by zero"
  return x / y

def trySafeDivide : IO Unit := do
  try
    let result ← safeDivideIO 10 0
    IO.println s!"Result: {result}"
  catch e =>
    IO.println s!"Error: {e}"

def foo : IO Unit := do
  let x ← safeDivideIO 10 0
  IO.println s!"x: {x}"

#eval foo

def counterExample : IO Nat := do
  let counter ← IO.mkRef 0
  for _ in List.range 10 do
    counter.modify (· + 1)
  counter.get

#eval counterExample

def accumulate (values : List Nat) : IO Nat := do
  let sum ← IO.mkRef 0
  for v in values do
    sum.modify (· + v)
  sum.get

#eval accumulate [1,2,3,4,5]

abbrev AppM := ExceptT String IO

def validatePositive (n : Int) : AppM Int := do
  if n ≤ 0 then throw "Must be positive"
  return n

def validateRange (n : Int) (lo hi : Int) : AppM Int := do
  if n < lo ∨ n > hi then throw s!"Must be between {lo} and {hi}"
  return n

def processNumber : AppM Int := do
  let n ← validatePositive 42
  let m ← validateRange n 50 100
  return m * 2

def runApp : IO Unit := do
  match ← processNumber.run with
  | .ok result => IO.println s!"Success: {result}"
  | .error msg => IO.println s!"Failed: {msg}"

#eval runApp

structure Config where
  verbose : Bool
  maxRetries : Nat
  timeout : Nat
deriving Repr

abbrev ConfigM := ReaderT Config IO

def getVerbose : ConfigM Bool := do
  let cfg ← read
  return cfg.verbose

def logIfVerbose (msg : String) : ConfigM Unit := do
  if ← getVerbose then
    IO.println s!"[LOG] {msg}"

def runWithConfig : IO Unit := do
  let config : Config := {verbose := true, maxRetries := 3, timeout := 5000}
  (logIfVerbose "Starting process").run config

def runCommand (cmd : String) (args : List String) : IO String := do
  let output ← IO.Process.output {
    cmd := cmd,
    args := args.toArray
  }
  return output.stdout

def shellExample : IO Unit := do
  let result ← runCommand "echo" ["Hello", "World"]
  IO.println result

#eval shellExample

def getEnvVar (name : String) : IO (Option String) := do
  IO.getEnv name

def printPath : IO Unit := do
  match ← getEnvVar "PATH" with
  | some path => IO.println s!"PATH: {path}"
  | none => IO.println "Path no set"

def getCwd' : IO System.FilePath := do
  IO.currentDir

#eval printPath
#eval getCwd'
