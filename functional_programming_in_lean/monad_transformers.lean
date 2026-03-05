structure Config where
  useAscii : Bool := false
  currentPrefix : String := ""

def ConfigIO (α : Type) : Type :=
  Config → IO α

instance : Monad ConfigIO where
  pure x := fun _ => pure x
  bind result next :=
    fun cfg => do
    let v ← result cfg
    next v cfg

def ConfigIO.run (action : ConfigIO α) (cfg : Config) : IO α :=
  action cfg

def currentConfig : ConfigIO Config :=
  fun cfg => pure cfg

def locally (change : Config → Config) (action : ConfigIO α) : ConfigIO α :=
  fun cfg => action (change cfg)

def runIO (action : IO α) : ConfigIO α :=
  fun _ => action

def Config.preFile (cfg : Config) :=
  if cfg.useAscii then "|  " else "├──"

def Config.preDir (cfg : Config) :=
  if cfg.useAscii then "|  " else "│  "

def Config.fileName (cfg : Config) (file : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {file}"

def Config.dirName (cfg : Config) (dir : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {dir}"

def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}

def usage : String :=
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"

def configFromArgs : List String → Option Config
  | [] => some {} -- both fields default
  | ["--ascii"] => some {useAscii := true}
  | _ => none

inductive Entry where
  | file : String → Entry
  | dir : String → Entry

def toEntry (path : System.FilePath) : IO (Option Entry) := do
  match path.components.getLast? with
  | none => pure (some (.dir ""))
  | some "." | some ".." => pure none
  | some name =>
    pure (some (if (<- path.isDir) then .dir name else .file name))

def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _ => pure ()
  | x :: xs, action =>
    action x *> doList xs action

def dirLT (e1 e2 : IO.FS.DirEntry) : Bool :=
  e1.fileName < e2.fileName

def showFileName (file : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).fileName file))

def showDirName (dir : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).dirName dir))

partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← runIO (toEntry path) with
    | none => pure ()
    | some (.file name) => showFileName name
    | some (.dir name) =>
      showDirName name
      let contents ← runIO path.readDir
      locally (·.inDirectory)
        (doList (contents.qsort dirLT).toList fun d =>
          dirTree d.path)


def main (args : List String) : IO UInt32 := do
    match configFromArgs args with
    | some config =>
      (dirTree (← IO.currentDir)).run config
      pure 0
    | none =>
      IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
      IO.eprintln usage
      pure 1
#eval s!"{[1,2,3]}"

#eval forM [1, 2, 3] fun x => IO.println x

def two : Nat := Id.run do
  let mut x := 0
  x := x + 1
  x := x + 1
  return x

def two : Nat :=
  let block : StateT Nat Id Nat := do
    modify (· + 1)
    modify (· + 1)
    return (← get)
  let (result, _finalState) := block 0
  resutl
