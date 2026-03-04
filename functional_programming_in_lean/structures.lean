#check 1.2

#check -454.2123215

#check 0.0

#check 0

#check (0 : Float)

structure Point where
  x : Float
  y : Float

def origin : Point := {x := 0.0, y := 0.0}

#eval origin

#eval origin.x
#eval origin.y

def addPoints (a b : Point) : Point :=
  {x := a.x + b.x, y := a.y + b.y}

#eval addPoints {x := 1.5, y:= 32} {x := -8, y := 0.2}

def distance (p1 p2 : Point) := Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

structure Point3D where
  x : Float
  y : Float
  z : Float

def origin3D : Point3D := {x := 0.0, y := 0.0, z := 0.0}

#check ({x := 0.0, y := 0.0} : Point)
#check { x := 0.0, y := 0.0 : Point}

def zeroX (p : Point) : Point :=
  {x := 0, y := p.y}

def zeroX2 (p : Point) : Point :=
  {p with x := 0}

def fourAndThree : Point :=
  {x := 4.3, y := 3.4}

#check Point.mk 1.5 2.9
#check (Point.mk)

structure Point2 where
  point ::
  x : Float
  y : Float

#eval Point2.point 1.2 2.1
#check (Point.x)


structure RectangularPrism where
  height : Float
  width : Float
  depth : Float

def volume (p : RectangularPrism) : Float :=
  p.height * p.width * p.depth

structure Segment where
  a : Point
  b : Point

def length (s : Segment) : Float :=
  Float.sqrt (((s.b.x - s.a.x) ^ 2.0) + ((s.b.y - s.a.y) ^ 2.0))
