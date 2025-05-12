/- Evaluation is the process of finding the value of an expression.
  In Lean, programs are first and foremost expressions. -/

#eval String.append "Hello, " "Lean!"

#eval String.append "it is " (if 1 > 2 then "yes" else "no")

#eval if 3 == 4 then "equal" else "not equal"


/- Every program in Lean must have a type. In particular,
  every expression must have a type before it can be evaluated. -/

#eval (1 - 2 : Nat)  -- 0

#eval (1 - 2 : Int)  -- -1


/- Definition of variables -/

def hello := "Hello"
def lean : String := "Lean"
#eval String.append hello (String.append " " lean)

/- Definition of functions -/

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n

#eval maximum 14 15

/- Function Signatures (used in the def) V.S Functions Types (type used for functions)-/
#check maximum      -- maximum (n k : Nat) : Nat (function sigature)
#check (maximum)    -- maximum : Nat → Nat → Nat (function type)

/- A function that returns a function -/

#check maximum 14  -- maximum 14 : Nat → Nat

------------------------------------------------------------------------
/- exercise -/

def joinStringsWith (x1: String) (x2: String) (x3: String): String :=
  String.append x2 (String.append x1 x3)

#eval joinStringsWith ", " "one" "and another"
#check joinStringsWith ": "
-------------------------------------------------------------------------

/- Types are expressions, and in an expression, a defined name can
  be replaced with its definition. -/

def Str : Type := String

def aStr : Str := "This is a string."

#check aStr  -- aStr : Str

-------------------------------------------------------------------------

/- Structure -/

structure Point where
  x : Float
  y : Float
deriving Repr

/- Constructor of the structure type with the curly-brace syntax -/

def origin : Point := { x := 0.0, y := 0.0 }

#eval origin  -- { x := 0.000000, y := 0.000000 }
#eval origin.x  -- accessor, dot notation


def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

#eval addPoints { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }

/- Updating Structures - Lean does not have mutable state
  a updated Point is allocated with the x field pointing
  to the new value, and all other fields pointing to the
  original values from the input -/

def zeroX (p : Point) : Point :=
  { x := 0, y := p.y }

/- Lean provides a convenient syntax for replacing some
  fields in a structure while leaving the others alone.
  This is done by using the with keyword in a structure
  initialization. -/

def oneX (p : Point) : Point :=
  { p with x := 1.0 }

/- Structure updates do not modify the original structure. -/

#eval oneX origin  -- { x := 1.000000, y := 0.000000 }
#eval origin  -- { x := 0.000000, y := 0.000000 }

/- Constructor of structure types -/

-- Structure.mk - the generic constructor function
#check Point.mk -- Point.mk (x y : Float) : Point
#check (Point.mk) -- Point.mk : Float → Float → Point
-- curly-brace constructor
#check ({x:= 2.0, y:= 3.0}: Point)  -- { x := 2.0, y := 3.0 } : Point


/- Accessor function is defined for each field of a structure. -/

#check (Point.x) -- Point.x : Point → Float
#eval Point.x origin -- 0.000000
#eval origin.x -- 0.000000


/- Function applied to fields of structure types -/

#eval String.append "one string " "and another"
#eval "one string ".append "and another"

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

#eval Point.modifyBoth Float.floor {x:= 1.23, y:=2.12}
#eval ({x:= 1.23, y:=2.12}: Point).modifyBoth Float.floor
-- { x := 1.000000, y := 2.000000 }

-------------------------------------------------------------------------
/- Exercises -/

structure RectangularPrism where
  x: Float
  y: Float
  z: Float
deriving Repr

def volume (r: RectangularPrism): Float :=
  r.x * r.y * r.z

#eval volume ({x:= 2.0, y:= 3.0, z:= 4.0}: RectangularPrism) -- 24.000000
-------------------------------------------------------------------------

/- Datatypes -/

/-
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
-/

#eval Nat.succ (Nat.succ 2) -- 4, constructor function


/- Pattern Matching -/

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

#eval pred 4

/- Recursive Functions -/

-- recall 'Nat' is inductive, thus apply its constructors

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')

#eval plus 3 2

/- Polymorphism - (generic) datatypes and definitions that take
  types as arguments. These type arguments allow the same
  datatype or definition to be used with any type that
  results from replacing the arguments' names with some other types.
 -/

/- Types are ordinary expressions in Lean, so passing arguments to
  polymorphic types (like PPoint) doesn't require any special syntax. -/

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

/- Definitions involved with polymorphic types may also take types
  as arguments, so that later arguments refer back to the fist argument's name -/

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#check (replaceX) -- replaceX : (α : Type) → PPoint α → α → PPoint α
#check replaceX Nat -- replaceX Nat : PPoint Nat → Nat → PPoint Nat

/- Type arguments can be inductive types -/

inductive Sign where
  | pos
  | neg

/-  Types can be computed as first class objects -/
def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)


#check posOrNegThree  -- function signature
/-
posOrNegThree (s : Sign) :
  match s with
  | Sign.pos => Nat
  | Sign.neg => Int
-/


#check (posOrNegThree) -- function type

/-
posOrNegThree : (s : Sign) →
  match s with
  | Sign.pos => Nat
  | Sign.neg => Int
-/

#eval posOrNegThree Sign.pos  -- 3


/-
  structure Prod (α : Type) (β : Type) : Type where
  fst : α
  snd : β
-/

/- The constructor for this structure type is the usual curly-brace one -/

def fives : String × Int := { fst := "five", snd := 5 }
#check fives  -- fives : String × Int


/-
  inductive Sum (α : Type) (β : Type) : Type where
  | inl : α → Sum α β
  | inr : β → Sum α β
-/

def DogOrCat: Type := Sum String String
#check DogOrCat

/- There are two constructors for this type -/
#check Sum.inl  -- Sum.inl.{u, v} {α : Type u} {β : Type v} (val : α) : α ⊕ β
def Pets: List DogOrCat :=
[Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex"]

/- For the type of String ⊕ String, we used wrapper type: DogOrCat. -/

/- Pattern matching can even used to distinguish the constructors -/
def howManyDogs (pets : List DogOrCat) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

#eval howManyDogs Pets  -- 3

-------------------------------------------------------------------------
/- exercise -/

def lastEntry? {α: Type} (xs: List α): Option α :=
  match xs with
  | [] => none
  | head :: [] => some head
  | _ :: tail => lastEntry? tail

#eval lastEntry? [1,2,3]
#eval lastEntry? (["a", "b"]: List String)
-------------------------------------------------------------------------
/- exercise -/

def findFirst? {α: Type} (xs: List α) (predicate: α -> Bool): Option α :=
  match xs with
  | [] => none
  | head :: tail =>
    if (predicate head) then some head
    else findFirst? tail predicate

def p (b: Bool): Bool := b
def q (n: Int) : Bool := n > 0
#eval findFirst? [false, false] p  -- none
#eval findFirst? [-1, -2, 3, 2, 0] q  -- some 3
-------------------------------------------------------------------------
/- exercise -/

def Prod.swap {α β: Type} (pair : α × β) : β × α :=
  match pair with
  | (y, x) => (x, y)
-------------------------------------------------------------------------
/- exercise -/

inductive CatOrDog: Type where
  | addCat: String → CatOrDog
  | addDog: String → CatOrDog

def LstOfPets: List CatOrDog :=
[CatOrDog.addCat "Tiger", CatOrDog.addDog "Spot", CatOrDog.addDog "Rex"]

def howManyCats (pets: List CatOrDog): Nat :=
  match pets with
  | [] => 0
  | CatOrDog.addCat _ :: morePets => howManyCats morePets + 1
  | CatOrDog.addDog _ :: morePets => howManyCats morePets


#eval howManyCats LstOfPets  -- 1
-------------------------------------------------------------------------
/- exercise -/

/- Pattern-Matching Definitions -/

def zip {α β: Type}: List α → List β → List (α × β)
  | [], _ => []
  | x :: [], y :: _ => (x, y) :: []
  | _, [] => []
  | x :: _, y :: [] => (x, y) :: []
  | x :: xs, y :: ys => (x, y) :: zip xs ys

#eval zip ([1, 2, 3, 4]: List Nat) ([1, 2, 3]: List Int)
-------------------------------------------------------------------------
/- exercise -/

def take {α: Type}: Nat → List α → List α
  | 0, _ => []
  | n + 1, y :: ys => y :: take n ys
  | _, [] => []

#eval take 3 ["bolete", "oyster"]

-------------------------------------------------------------------------
/- exercise -/

def distr (α β γ: Type): α × (β ⊕ γ) → (α × β) ⊕ (α × γ)
  | ⟨x, Sum.inl y⟩ => Sum.inl ⟨x, y⟩
  | ⟨x, Sum.inr y⟩ => Sum.inr ⟨x, y⟩

#eval distr String Nat Nat {fst:= "string", snd:= Sum.inl 1}

-------------------------------------------------------------------------

/- exercise -/

def bsum {α: Type}: Bool × α → α ⊕ α
  | ⟨true, x⟩ => Sum.inl x
  | ⟨false, x⟩ => Sum.inr x

#eval bsum ⟨true, (1: Nat)⟩
