def main: IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be adressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"

def twice (action : IO Unit) : IO Unit := do
  action
  action

#eval twice (IO.println "shy")

def nTimes (action : IO Unit) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    action
    nTimes action n

#eval nTimes (IO.println "Hello") 3

def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def from5 : List (IO Unit) := countdown 5

#eval from5.length

def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions

def main2 : IO Unit := runActions from5

#eval main2
