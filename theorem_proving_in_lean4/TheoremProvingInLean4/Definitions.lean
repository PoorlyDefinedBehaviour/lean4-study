def double (x : Nat) : Nat := x + x

#eval double 2 -- 4

def double2: Nat → Nat :=
  fun x => x + x

#eval double2 2 -- 4

def double3 :=
  fun (x : Nat) => x + x

#eval double3 2 -- 4

def pi := 3.141592654

def add (x y : Nat) := x + y

#eval add 3 2 -- 5

def add2 (x : Nat) (y : Nat) := x + y

#eval add2 3 2 -- 5

def greater (x  y : Nat) :=
  if x > y then
    x
  else
    y

#eval greater 5 3 -- 5

def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2 -- 8

def compose (a b y : Type) (g : b → y) (f : a → b) (x : a) : y :=
  g (f x)

def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3 -- 18

def twice_double (x : Nat) : Nat :=
  let y := x + x
  y * y

#eval twice_double 2 -- 16
