-- def onePlusOneIsTwo: 1 + 1 = 2 := rfl

abbrev OneOneTwo : Prop := 1 + 1 = 2

theorem onePlusOneIsTwo : OneOneTwo := rfl

#check Prop

theorem one_one_two: 1 + 1 = 2 := by simp

theorem bad_one_one_two: OneOneTwo := by simp

theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by simp

def test1: 5 < 18 := by simp
def test2: 1 + 1 = 2 ∧ 1 + 2 = 3 := by simp
