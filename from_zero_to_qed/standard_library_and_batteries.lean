import Std.Data.HashMap
import Std.Data.HashSet
import Std.Data.TreeMap
import Std.Internal.Parsec

def hashMapDemo : IO Unit := do
  let mut scores : Std.HashMap String Nat := {}
  scores := scores.insert "alice" 85
  scores := scores.insert "bob" 87
  scores := scores.insert "carol" 92

  let aliceScore := scores.get? "alice"
  IO.println s!"alice: {aliceScore}"

  IO.println s!"contains bob {scores.contains "bob"}"

  let daveScore := scores.getD "dave" 0
  IO.println s!"dave (default 0): {daveScore}"

  IO.println "All scores:"
  for (name, score) in scores do
    IO.println s!"  {name}: {score}"

#eval hashMapDemo

def hashsetDemo : IO Unit := do
  let mut seen : Std.HashSet String := {}
  seen := seen.insert "apple"
  seen := seen.insert "banana"
  seen := seen.insert "cherry"

  IO.println s!"contains apple: {seen.contains "apple"}"

  let more : Std.HashSet String := Std.HashSet.ofList ["banana", "date", "elderberry"]
  let combined := seen ∪ more
  IO.println s!"union size: {combined.size}"

#eval hashsetDemo

def treemapDemo : IO Unit := do
  let mut prices : Std.TreeMap String Nat := {}
  prices := prices.insert "banana" 120
  prices := prices.insert "apple" 100
  prices := prices.insert "cherry" 300

  IO.println "Prices (sorted by name)"
  for (fruit, price) in prices do
    IO.println s!"  {fruit}: {price}"

  IO.println s!"size: {prices.size}"
  IO.println s!"contains apple: {prices.contains "apple"}"

#eval treemapDemo

def timeDemo : IO Unit := do
  let now ← IO.monoNanosNow
  IO.println s!"Monotonic nanoseconds: {now}"

  let oneSecond := 1000000000
  let elapsed := now % oneSecond
  IO.println s!"Nanoseconds into current second: {elapsed}"

  let heartbeats ← IO.getNumHeartbeats
  IO.println s!"Heartbeats {heartbeats}"

#eval timeDemo

open Std.Internal.Parsec String in
def parseDemo : IO Unit := do
  let parseNat : Parser Nat := digits

  let parseWord : Parser String := many1Chars asciiLetter

  let parseNumList : Parser (List Nat) := do
    let first ← parseNat
    let rest ← many (skipChar ',' *> parseNat)
    pure (first :: rest.toList)

  IO.println (parseNat.run "12345")
  IO.println (parseWord.run "hello123")
  IO.println (parseNumList.run "1,23,456")

#eval parseDemo

def countWords (text : String) : Std.HashMap String Nat :=
  let words := text.toLower.splitOn " "
    |>.map (λw ↦ w.toList.filter Char.isAlpha |> String.ofList)
    |>.filter (λv ↦ ¬v.isEmpty)

  words.foldl (λ map word ↦ map.insert word ((map.get? word).getD 0 + 1)) {}

def wordFreqDemo : IO Unit := do
  let text := "The quick brown fox jumps over the lazy dog The dog barks"
  let freq := countWords text

  IO.println "Word frequencies:"
  let sorted := freq.toList.toArray
    |>.qsort (λ a b ↦ a.2 > b.2)

  for (word, count) in sorted do
    IO.println s!"    {word}: {count}"

#eval wordFreqDemo
