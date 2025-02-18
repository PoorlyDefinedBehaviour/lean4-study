def hello := "Hello"

#check hello

def lean : String := "lean"

#eval String.append (String.append hello " ") lean

def add1 (n : Nat) : Nat := n + 1

#eval add1 1

def maximum (a : Nat) (b : Nat) : Nat :=
  if a > b then
    a
  else
    b

#eval maximum 3 5

#check add1

#check (add1)

def joinStringsWith (a : String) (b : String) (c : String) : String :=
  String.append b (String.append a c)

#eval joinStringsWith ", " "one" "and another"

def volume (height : Nat) (width : Nat) (depth : Nat) : Nat :=
  width * height * depth

def Str : Type := String

def aStr : Str := "this is a string"

def NaturalNumber : Type := Nat

def thirtyEight : NaturalNumber := (38 : Nat)

abbrev N : Type := Nat

def thirtyNine : N := 39
