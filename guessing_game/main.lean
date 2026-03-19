def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let secretNumber ← IO.rand 0 10
  repeat
    let line ← stdin.getLine
    match line.trimAscii.toNat? with
    | none => stdout.putStrLn "A number is required"
    | some v =>
      if v == secretNumber then
        stdout.putStrLn "You win"
        return
      else
        stdout.putStrLn "Wrong number, try again"
