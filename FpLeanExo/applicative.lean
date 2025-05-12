import FpLeanExo.arith_monads

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving Repr

instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }
---------------------------------------------------------------------
inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
deriving Repr

instance : Functor (Validate ε) where
  map f x :=
    match x with
    | .ok y => .ok (f y)
    | .errors errs => .errors errs

instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x
------------------------------------------------------------
def Field := String
def Reason := String
abbrev NonEmptyString := { s : String // s ≠ "" }

def reportError (f : Field) (msg : Reason) : Validate (Field × Reason) α :=
  .errors { head := (f, msg), tail := [] }

def checkName (name : String) : Validate (Field × Reason) NonEmptyString :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩

def checkYearIsNat (year : String) : Validate (Field × Reason) Nat :=
  match year.trim.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some n => pure n

def checkBirthYear (thisYear inputYear : Nat) : Validate (Field × Reason) { y : Nat // y > 1900 ∧ y ≤ thisYear } :=
  if h : inputYear > 1900 then
    if h' : inputYear ≤ thisYear then
      pure ⟨inputYear, by simp [*]⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"

structure RawInput where
  name : String
  birthYear : String

structure CheckedInput (thisYear : Nat) : Type where
  name : NonEmptyString
  birthYear : { y : Nat // y > 1900 ∧ y ≤ thisYear }
deriving Repr

def checkInput (thisYear : Nat) (input : RawInput) : Validate (Field × Reason) (CheckedInput thisYear) :=
  pure CheckedInput.mk <*>
    checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen fun birthYearAsNat =>
      checkBirthYear thisYear birthYearAsNat

#eval checkInput 2023 {name := "", birthYear := "2045"}
-- Validate.errors { head := ("name", "Required"), tail := [("birth year", "Must be no later than 2023")] }

#eval checkInput 2023 {name := "David", birthYear := "syzygy"}
-- Validate.errors { head := ("birth year", "Must be digits"), tail := [] }

---------------------------------------------------------

inductive LegacyCheckedInput where
  | humanBefore1970:
    (birthYear: { y : Nat // y > 999 ∧ y ≤ 1970 }) -> String -> LegacyCheckedInput
  | humanAfter1970:
    (birthYear: {y: Nat // y > 1970}) -> String -> LegacyCheckedInput
  | company: NonEmptyString -> LegacyCheckedInput  -- the birth year is "FIRM" by default
deriving Repr

def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε) : Validate ε {t : α // p t} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors { head := err, tail := [] }

def checkHumanBefore1970 (input : RawInput) : Validate (Field × Reason) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun x => x > 999 ∧ x ≤ 1970) (("birth year", "less than or equal to 1970"): Field × Reason) <*>
      pure input.name

def checkHumanAfter1970 (input : RawInput) : Validate (Field × Reason) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970) (("birth year", "greater than 1970"): Field × Reason) <*>
      pure input.name

def checkThat (condition : Bool) (field : Field) (msg : Reason) : Validate (Field × String) Unit :=
  if condition then pure () else reportError field msg

def checkCompany (input : RawInput) : Validate (Field × Reason) LegacyCheckedInput :=
  pure (fun () name => .company name) <*>
    checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" <*>
    checkName input.name

def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)

instance : OrElse (Validate ε α) where
  orElse := Validate.orElse

def checkLegacyInput (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkCompany input <|> checkHumanBefore1970 input <|> checkHumanAfter1970 input

#eval checkLegacyInput ⟨"Johnny", "1963"⟩
-- Validate.ok (LegacyCheckedInput.humanBefore1970 ⟨1963, by simp⟩ "Johnny")

#eval checkLegacyInput ⟨"Ontario", "FIRM"⟩
-- Validate.ok (LegacyCheckedInput.company "Ontario")

#eval checkLegacyInput ⟨"", "1970"⟩
-- Validate.errors { head := ("name", "Required"), tail := [("birth year", "greater than 1970")] }

#eval checkLegacyInput ⟨"Ontario", "1970"⟩
-- Validate.errors { head := ("birth year", "greater than 1970"), tail := []

------------------------------------------------------------

def Many.orElse : Many α → (Unit → Many α) → Many α
  | .none, ys => ys ()
  | .more x xs, ys => .more x (fun () => orElse (xs ()) ys)

instance : Alternative Many where
  failure := .none
  orElse := Many.orElse

def Many.countdown : Nat → Many Nat
  | 0 => .none
  | n + 1 => .more n (fun () => countdown n)

#eval (Many.countdown 21).toList
-- [20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

def evenDivisors (n : Nat) : Many Nat := do
  let k ← Many.countdown (n + 1)
  guard (k % 2 = 0)
  guard (n % k = 0)
  pure k

#eval (evenDivisors 20).toList
-- [20, 10, 4, 2]
