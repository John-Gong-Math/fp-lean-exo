/- Positive Numbers and Their Instances -/

inductive Pos: Type where
  | one: Pos
  | succ: Pos -> Pos

def Pos.toNat: Pos -> Nat
  | one => 1
  | succ n => (toNat n) + 1

instance: ToString Pos where
  toString x := toString (Pos.toNat x)

#eval Pos.succ Pos.one  -- 2 (thanks to the instance of ToString)

def Pos.add: Pos -> Pos -> Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (add n k)


instance: Add Pos where
  add := Pos.add

def Pos.two: Pos := Pos.one + Pos.one

#eval Pos.two  -- 2 (thanks to the instance of Add)

def Pos.mul: Pos -> Pos -> Pos
  | Pos.one, k => k
  | Pos.succ n, k => (mul n k) + k

instance: Mul Pos where
  mul := Pos.mul

#eval Pos.two * Pos.two  -- 4 as expected

instance: OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne: Nat -> Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

#check (2: Pos)  -- Pos (thanks to the instance of OfNat)

----------------------------------------------------------------------------------------------------------
namespace Struc

structure Pos: Type where
  succ::  -- renmame the constructor
  pred: Nat

def two: Pos := Pos.succ 1

#check two  -- Pos

instance: ToString Pos where
  toString x := toString (x.pred + 1)

#eval two  -- 2 (thanks to the instance of ToString)

def Pos.add: Pos -> Pos -> Pos
  | x, y => Pos.succ (x.pred + y.pred + 1)

instance: Add Pos where
  add := Pos.add

#eval two + two -- 4

-- #eval (2 + 2: Pos) failed as Pos not instance of OfNat

instance: OfNat Pos (n + 1) where
  ofNat := Pos.succ n

#eval (2 + 2: Pos)  -- 4

end Struc
--------------------------------------------------------------------------------------------
inductive Even: Type where
  | zero: Even
  | succ: Even -> Even

-- def Even.toNat: Even -> Nat
--   | zero => 0
--   | succ k => (toNat k) + 2

-- instance: ToString Even where
--   toString x := toString (Even.toNat x)

-- #eval Even.succ Even.zero  -- 2

instance : OfNat Even 0 where
  ofNat := Even.zero

instance [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := Even.succ (inferInstance: OfNat Even n).ofNat
-------------------------------------------------------------------------------------------

structure PPoint (α: Type) where
  x: α
  y: α
deriving Repr

instance [Mul α] : HMul α (PPoint α) (PPoint α) where
  hMul n p := {x := n * p.x, y := n * p.y}

#eval 2.0 * {x := 2.5, y := 3.7 : PPoint Float}  -- { x := 5.000000, y := 7.400000 }

--------------------------------------------------------------------------------------------
instance : GetElem (List α) Pos α (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat]
