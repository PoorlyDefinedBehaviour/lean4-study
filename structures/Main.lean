#check 1.2

#check 0

#check (0 : Float)

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point :=  {x := 0.0, y := 0.0}

#eval origin

#eval origin.x

#eval origin.y

def addPoints (p1: Point) (p2: Point): Point :=
  {x := p1.x + p2.x, y := p1.y + p2.y}

def distance (p1: Point) (p2: Point): Float :=
    Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

def zeroX (p: Point): Point :=
  { p with x := 0}

#check Point.mk 1.0 2.0
