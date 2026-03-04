def hello := "Hello"

def lean : String := "Lean"

#eval String.append hello (String.append " " lean)

def add1 (n: Nat) : Nat := n + 1

#eval add1 7

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else
    n

def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)

#check add1
#check (add1)
#check maximum
#check (maximum)
#check maximum 3


def joinStringsWith (a b c : String) : String :=
  String.append b (String.append a c)

#eval joinStringsWith ", " "one" "and another"

#check (joinStringsWith)

def volume (height width depth : Nat) : Nat :=
  width * height * depth

#check (volume)

def Str : Type := String

def aStr : Str := "This is a string"

#check aStr

def NaturalNumber : Type := Nat

def thirtyEight : NaturalNumber := (38 : Nat)

abbrev N : Type := Nat
def thirtyNine : N := 39
