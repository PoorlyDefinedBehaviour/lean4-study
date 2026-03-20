def accessControl : IO Unit := do
  IO.println "What is the password?"
  let password ← (← IO.getStdin).getLine
  if password.trimAscii.copy ≠ "secret" then
    throw (.userError "Incorrect password")
  else
    return

def repeatAccessControl : IO Unit := do
  repeat
    try
      accessControl
      break
    catch
      | .userError "Incorrect password"  => continue
      | other => throw other

def main : IO Unit := do
  repeatAccessControl
  IO.println "Access granted!"

def main2 : IO Unit := do
  IO.print "This is the "
  IO.print "Lean"
  IO.println " language reference."
  IO.println "Thank you for reading it!"
  IO.eprint "Please report any "
  IO.eprint "errors"
  IO.eprintln " so they can be corrected."

def main3 : IO Unit := do
  let balance ← IO.mkRef (100 : Int)

  let mut orders := #[]
  IO.println "Sending out orders..."
  for _ in [0:100] do
    let o ← IO.asTask (prio := .dedicated) do
      let cost ← IO.rand 1 100
      IO.sleep (← IO.rand 10 100).toUInt32
      if cost < (← balance.get) then
        IO.sleep (← IO.rand 10 100).toUInt32
        balance.set ((← balance.get) - cost)
    orders := orders.push o

  for o in orders do
    match o.get with
    | .ok () => pure ()
    | .error e => throw e

  if (← balance.get) < 0 then
    IO.eprintln "Final balance is negative!"
  else
    IO.println "Final balance is zero or positive."

def main4 : IO Unit := do
  let balance ← IO.mkRef (100 : Int)

  let mut orders := #[]
  for _ in [0:100] do
    let o ← IO.asTask (prio := .dedicated) do
      let cost ← IO.rand 1 100
      IO.sleep (← IO.rand 10 100).toUInt32
      balance.modify λb ↦ if cost < b then b - cost else b
    orders := orders.push o

  for o in orders do
    match o.get with
    | .ok () => pure ()
    | .error e => throw e

  if (← balance.get) < 0 then
    IO.eprintln "Negative balance"
  else
    IO.println "Balance is fine"

open IO.FS (Handle)
def main5 : IO Unit := do
  IO.println s!"Starting contents: '{(← IO.FS.readFile "data").trimAscii}'"

  let h ← Handle.mk "data" .read
  let h' ← Handle.mk "data" .readWrite
  h'.rewind

  let mut count := 0
  let mut buf : ByteArray ← h.read 1
  while ok : buf.size = 1 do
    if Char.ofUInt8 buf[0] == 'A' then
      count := count + 1
      h'.write (ByteArray.empty.push '!'.toUInt8)
    else
      h'.write buf
    buf ← h.read 1

  h'.flush

  IO.println s!"Count: {count}"
  IO.println s!"Contents: '{(← IO.FS.readFile "data").trimAscii}'"

def countdown : Nat → IO Unit
  | 0 => IO.println "Blastoff!"
  | n + 1 => do
    IO.println s!"{n + 1}"
    countdown n

def runCountdown : IO String := do
  let (output, ()) ← IO.FS.withIsolatedStreams (countdown 10)
  return output

#eval runCountdown

def main6 : IO Unit := do
  let src2 ← IO.Process.run {cmd := "cat", args := #["io.lean"]}
  IO.println src2

def main7 : IO Unit := do
  IO.FS.withFile "numbers.txt" .write λh ↦
    for i in [0:10000] do
      h.putStrLn (toString i)

  let palindromes ← IO.Process.run {
    cmd := "grep",
    args := #[r#"^\([0-9]\)\([0-9]\)\2\1$"#, "numbers.txt"]
  }

  let count := palindromes.trimAscii.split "\n" |>.count

  IO.println s!"There are {count} four-digit palindromes."

def main8 : IO UInt32 := do
  let src1 ← IO.Process.output {cmd := "cat",  args := #["Nonexistent.lean"]}
  IO.println s!"Exit code from failed process: {src1.exitCode}"

  let src2 ← IO.Process.output {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  if src2.exitCode == 0 then
    IO.println src2.stdout
    return 0
  else
    IO.eprintln "Concatenation failed"
    return 1

def main9 : IO Unit := do
  let grep ← IO.Process.spawn {
      cmd := "grep",
      args := #[r#"^\([0-9]\)\([0-9]\)\2\1$"#],
      stdin := .piped,
      stdout := .piped,
      stderr := .null
  }

  for i in [0:10000] do
    grep.stdin.putStrLn (toString i)

  IO.sleep 100
  let count := (← grep.stdout.readToEnd).trimAscii.split "\n" |>.count

  IO.println s!"There are {count} four-digit palindromes."

def main10 : IO Unit := do
