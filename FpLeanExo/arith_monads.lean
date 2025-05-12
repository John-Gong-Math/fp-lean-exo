-----------------------------------------------------------------------------------------------------------
/- Arithmetic in Monads -/

inductive Arith where
  | plus
  | minus
  | times
  | div

def applyDivOption (x y: Int) : Option Int :=
  if y == 0 then none
  else pure (x / y)

def applyDivExcept (x : Int) (y : Int) : Except String Int :=
  if y == 0 then
    Except.error s!"Tried to divide {x} by zero"
  else pure (x / y)

-- The Monad m represents Option m or Except String m
def applyArith [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → Int → m Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => applyDiv x y

#eval applyArith applyDivOption Arith.div 1 0  -- none
#eval applyArith applyDivExcept Arith.div 2 0  -- Except.error "Tried to divide 2 by zero"

inductive Expr (α : Type) where   -- α can be replaced by Arith, or Prim later
  | const : Int → Expr α
  | prim : α → Expr α → Expr α → Expr α

open Expr   -- in is the command for openning the namespace in one shot
open Arith

-- 14 / (45 - 5 * 9)
def fourteenDivided : Expr Arith :=
  prim div (const 14) (prim minus (const 45) (prim times (const 5) (const 9)))
-- (10 + 4) / 0
def fourtenDivided: Expr Arith :=
  prim div (prim plus (const 10) (const 5)) (const 0)

-- evaluate the type Expr Arith
def evaluateArith [Monad m] (applyDiv : Int → Int → m Int): Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateArith applyDiv e1 >>= fun v1 =>
    evaluateArith applyDiv e2 >>= fun v2 =>
    applyArith applyDiv p v1 v2

#eval evaluateArith applyDivOption fourtenDivided  -- none
#eval evaluateArith applyDivExcept fourteenDivided -- Except.error "Tried to divide 14 by zero"

-- extend the arithmetics to more primitives, α can be replaced by e.g CanFail
inductive Prim (α : Type) where
  | plus
  | minus
  | times
  | special : α → Prim α

inductive CanFail where
  | div

-- (10 + 4) / 0
def fourtenCanFail: Expr (Prim CanFail) :=
  prim (Prim.special CanFail.div) (prim Prim.plus (const 10) (const 5)) (const 0)

def canFailOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)

def canFailExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m] (applySpecial : α → Int → Int → m Int) : Prim α → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.special α, x, y => applySpecial α x y

def evaluatePrim [Monad m] (applySpecial : α → Int → Int → m Int): Expr (Prim α) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluatePrim applySpecial e1 >>= fun v1 =>
    evaluatePrim applySpecial e2 >>= fun v2 =>
    applyPrim applySpecial p v1 v2

#eval evaluatePrim canFailExcept fourtenCanFail -- Except.error "Tried to divide 15 by zero"

-------------------------------------------------------------------------------------------------------------------
/- Non Deterministic in Monad -/

inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)

def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys  -- identity for union operation
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ => Many.none
  | Many.more x xs, f =>  -- apply to each element and do the union
    (f x).union (bind (xs ()) f)

def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, Many.none => []
  | n + 1, Many.more x xs => x :: ((xs ()).take n)  -- put into the front of the list

def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll

def Many.toList : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: ((xs ()).toList)

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

def Many.divMany : Many Int -> Many Int -> Many Int
  | xs, ys =>
    xs >>= fun x =>
    ys >>= fun y =>
    if y == 0 then Many.none
    else Many.one (x / y)

def ex1: Many Nat := Many.more 0 (fun () => Many.more 1 fun () => Many.none)
#eval Many.toList ex1  -- [0, 1]
#eval Many.toList (Many.union Many.none ex1)  -- [0, 1]
def ex2: Many (List Nat) := Many.more [0, 1] (fun () => Many.more [2] fun () => Many.none)
#eval Many.toList ex2  -- [[0, 1], [2]]

def ex3: Many Nat := Many.more 2 (fun () => Many.more 3 fun () => Many.none)

-- {2, 3} ÷ {0, 1} = {2, 3}
#eval (Many.divMany ex3 ex1).toList  -- [2, 3]

def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] =>
    if goal == 0 then
      pure []
    else
      Many.none   -- propagate the union identity across the computation
  | x :: xs =>
    if x > goal then
      addsTo goal xs
    else
      (addsTo goal xs).union
        (addsTo (goal - x) xs >>= fun answer =>
         pure (x :: answer))

#eval Many.toList (addsTo 3 [3, 1, 1, 2])  -- [[1, 2], [1, 2], [3]]
#eval [1, 2]::[[3, 4], [5, 6, 7]]  -- [[1, 2], [3, 4], [5, 6, 7]]
#eval []::[[1, 2], [3]] -- [[], [1, 2], [3]]

def Many.fromList : List α → Many α
  | [] => Many.none
  | x :: xs => Many.more x (fun () => fromList xs)

inductive NeedsSearch
  | div
  | choose

def applySearch : NeedsSearch → Int → Int → Many Int
  | NeedsSearch.choose, x, y =>
    Many.fromList [x, y]
  | NeedsSearch.div, x, y =>
    if y == 0 then
      Many.none
    else Many.one (x / y)

-- then Prim NeedsSearch is a type, also for Expr (Prim NeedsSearch)

-- {3, 6}
def ex4 : Expr (Prim NeedsSearch) :=
  prim (Prim.special NeedsSearch.choose) (const 3) (const 6)

-- 3 ÷ 0
def ex5: Expr (Prim NeedsSearch) :=
  prim (Prim.special NeedsSearch.div) (const 3) (const 0)

-- {3, 6} ÷ {3, 0}
def ex6: Expr (Prim NeedsSearch) :=
  prim (Prim.special NeedsSearch.div) (ex4) (prim (Prim.special NeedsSearch.choose) (const 3) (const 0))

-- applyPrim parameterized by applySearch with the Monad of Many Int, is used to evaluate the Expr

#eval (evaluatePrim (applySearch) ex4).toList  -- [3, 6]
#eval (evaluatePrim (applySearch) ex5).toList  -- []
#eval (evaluatePrim (applySearch) ex6).toList -- [1, 2]
---------------------------------------------------------------------------------------------------------------

/- Environment Monad -/
def Reader (ρ : Type) (α : Type) : Type := ρ → α

def Reader.pure (x : α) : Reader ρ α := fun _ => x

def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result env) env

instance : Monad (Reader ρ) where
  pure x := Reader.pure x
  bind x f := Reader.bind x f

-- the instance of constant function
def read : Reader ρ ρ := fun env => env

abbrev Env : Type := List (String × (Int → Int → Int))

-- the functor can be viewed as Reader Env _
def applyReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= fun env =>
  match env.lookup op with
  | none => pure 0
  | some f => pure (f x y)

-- function max 6 9 in String of "max"
def ex7: Expr (Prim String) :=
  prim (Prim.special "max") (const 6) (const 9)

-- List of String with function
def exampleEnv : Env := [("max", max), ("mod", (· % ·))]

#eval evaluatePrim applyReader ex7 exampleEnv  -- 9
