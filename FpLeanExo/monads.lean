
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)

-------------------------------------------------------------------------------
/-
  Monad: α ---> WithLog logged α
-/

namespace WithLog

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
deriving Repr

def andThen (first : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := first
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}

def save_val (x : β) : WithLog α β := {log := [], val := x}

def save_log (data : α) : WithLog α Unit :=
  {log := [data], val := ()}

instance : Monad (WithLog logged) where
  pure := save_val
  bind first next := andThen first next

def isEven (i : Int) : Bool :=
  i % 2 == 0

def sumAndFindEvens : List Int → WithLog Int Int
  | [] => pure 0
  | i :: is =>
    (if isEven i then save_log i else pure ()) >>= fun () =>
    (sumAndFindEvens is) >>= fun sum =>
    pure (i + sum)

#eval sumAndFindEvens [1, 2, 3, 4] -- { log := [2, 4], val := 10 }

def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i then save_log i else pure ()) >>= fun () =>
  pure i

#eval mapM saveIfEven [1, 2, 3, 4, 5]
-- { log := [2, 4], val := [1, 2, 3, 4, 5] }

end WithLog
-------------------------------------------------------------------------------
/-
  Monad: α --> ( σ → (σ × α) )
-/

namespace State

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α) -- σ stands for a state stream while α is for a specific value

def write_value (x : α) : State σ α :=
  fun s => (s, x)

def read_state : State σ σ :=
  fun s => (s, s)

def reset_state (s : σ) : State σ Unit :=
  fun _ => (s, ())

def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', x) := first s
    next x s'

-- operations upon the state stream of next based on the current value x

instance : Monad (State σ) where
  pure x := write_value x
  bind first next := andThen first next

/-
 increment: α -> State Int α
 given n, return (n + howmuch, n)
-/
def increment (howMuch : Int) : State Int Int :=
  read_state >>= fun i =>
  reset_state (i + howMuch) >>= fun () =>
  pure i

#eval increment 1 0  -- (1, 0)
#eval increment 2 1  -- (3, 1)
#eval increment 3 3  -- (6, 3)
#eval increment 4 6  -- (10, 6)
#eval increment 5 10 -- (15, 10)


#eval mapM increment [1, 2, 3, 4, 5] 0

/-
(15, [0, 1, 3, 6, 10])
-/
---------------------------------------------------------------------------

inductive BinaryTree (α: Type) where
  | empty: BinaryTree α
  | node:  BinaryTree α -> α -> BinaryTree α -> BinaryTree α
deriving Repr

def myTree : BinaryTree Int :=
  BinaryTree.node
    (BinaryTree.node
      (BinaryTree.node
        (BinaryTree.empty)
        (7)
        (BinaryTree.empty))
      (7)
      (BinaryTree.node
        (BinaryTree.empty)
        (8)
        (BinaryTree.empty)))
    (5)
    (BinaryTree.node BinaryTree.empty 15 BinaryTree.empty)
  /-

          5
        /  \
       7   15
      /\
     7  8

  -/

-- Inorder tranversal

-- Monad: State Int BinaryTree

def inorder (t : BinaryTree α) : Int × BinaryTree (Int × α) :=
  let rec helper : BinaryTree α → State Int (BinaryTree (Int × α))
    | BinaryTree.empty => write_value BinaryTree.empty
    | BinaryTree.node left x right =>
      helper left>>= (fun numberedLeft =>
      read_state>>= (fun n =>
      reset_state (n + 1)>>= (fun () =>
      helper right>>= (fun numberedRight =>
      write_value (BinaryTree.node numberedLeft (n, x) numberedRight)))))
  (helper t 0)

#eval inorder myTree
/-
(5,
 State.BinaryTree.node
   (State.BinaryTree.node
     (State.BinaryTree.node (State.BinaryTree.empty) (0, 7) (State.BinaryTree.empty))
     (1, 7)
     (State.BinaryTree.node (State.BinaryTree.empty) (2, 8) (State.BinaryTree.empty)))
   (3, 5)
   (State.BinaryTree.node (State.BinaryTree.empty) (4, 15) (State.BinaryTree.empty)))

-/

/-
      (3,5)
     /     \
  (1,7)   (4,15)
  /   \
(0,7) (2,8)

-/

-- Preorder tranversal
def preorder (t : BinaryTree α) : Int × BinaryTree (Int × α) :=
  let rec helper : BinaryTree α → State Int (BinaryTree (Int × α))
    | BinaryTree.empty => write_value BinaryTree.empty
    | BinaryTree.node left x right =>
      read_state >>= (fun n =>
      (reset_state (n + 1)) >>= (fun () =>
      helper left >>= (fun numberedLeft =>
      helper right >>= (fun numberedRight =>
      write_value (BinaryTree.node numberedLeft (n, x) numberedRight)))))
  (helper t 0)

#eval preorder myTree

/-
(5,
 State.BinaryTree.node
   (State.BinaryTree.node
     (State.BinaryTree.node (State.BinaryTree.empty) (2, 7) (State.BinaryTree.empty))
     (1, 7)
     (State.BinaryTree.node (State.BinaryTree.empty) (3, 8) (State.BinaryTree.empty)))
   (0, 5)
   (State.BinaryTree.node (State.BinaryTree.empty) (4, 15) (State.BinaryTree.empty)))

      (0,5)
     /     \
  (1,7)   (4,15)
  /   \
(2,7) (3,8)

-/

def BinaryTree.mapM [Monad m] (f : α → m β) : BinaryTree α → m (BinaryTree β)
  | empty => pure empty
  | node left x right =>
    f x >>= fun val =>
    mapM f left >>= fun f_left =>
    mapM f right >>= fun f_right =>
    pure (node f_left val f_right)

#eval BinaryTree.mapM increment myTree 0

/-
(42,
 State.BinaryTree.node
   (State.BinaryTree.node
     (State.BinaryTree.node (State.BinaryTree.empty) 12 (State.BinaryTree.empty))
     5
     (State.BinaryTree.node (State.BinaryTree.empty) 19 (State.BinaryTree.empty)))
   0
   (State.BinaryTree.node (State.BinaryTree.empty) 27 (State.BinaryTree.empty)))

     0
    / \
   5   27
  / \
 12  19

-/
end State
--------------------------------------------------------------------------------
