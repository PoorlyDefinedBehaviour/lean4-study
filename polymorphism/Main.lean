structure PPoint (a : Type) where
  x : a
  y : a
deriving Repr

def natOrigin : PPoint Nat :=
  {x := 0, y := 0}

def replaceX (a: Type) (point: PPoint a) (newX: a): PPoint a :=
  {point with x := newX}

inductive Sign where
  | pos
  | neg

def posOrNegative (s: Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

def primesUnder10 : List Nat := [2, 3, 5, 7]

inductive MyList (a: Type) where
  | nil : MyList a
  | cons : a -> MyList a -> MyList a

def length1 (a : Type) (xs : List a): Nat :=
  match xs with
  | List.nil => 0
  | List.cons _ xs' => 1 + (length1 a xs')

def length2 (a : Type) (xs : List a): Nat :=
  match xs with
  | [] => 0
  | _ :: xs' => 1 + (length2 a xs')

def length3 {a: Type} (xs: List a): Nat :=
  match xs with
  | [] => 0
  | _ :: xs' => 1 + (length3 xs')

inductive MyOption (a: Type) where
  | none: MyOption a
  | some (val: a): MyOption a

def MyList.head? {a : Type} (xs : MyList a): MyOption a :=
  match xs with
  | MyList.nil => MyOption.none
  | MyList.cons x _ => MyOption.some x

#eval (MyList.cons 1 MyList.nil).head?

structure MyProd (a: Type) (b: Type) : Type where
  fst: a
  snd : b

def fiives: String × Int := ("5", 5)
