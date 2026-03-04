def woorlandCritters : List String := ["hedgehog", "deeer", "snail"]

def hedgehog := woorlandCritters[0]
def deer := woorlandCritters[1]
def snail := woorlandCritters[2]
def oops := woorlandCritters[3]

def onePlusOneIsTwo : 1 + 1 = 2 := rfl

def onePlusOneIsFifteen : 1 + 1 = 15 := rfl

def OnePlusOneIsTwoProp : Prop := 1 + 1 = 2
theorem onePlusOneIsTwo2 : OnePlusOneIsTwoProp := rfl

theorem onePlusOneIsTwo3 : 1 + 1 = 2 := by
  decide

theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  decide

theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _ => Or.inl a

theorem onePlusOneOrLessThan : 1 + 1 = 2 ∨ 3 < 5 := by decide

theorem notTwoEqualFive : ¬(1 + 1 = 5) := by decide

theorem trueIsTrue : True := by decide

theorem trueOrFalse : True ∨ False := by decide

theorem falseImpliesTrue : False → True := by decide

def third (xs : List α) : α := xs[2]

def third2 (xs : List α) (ok : xs.length > 2) : α := xs[2]


#eval third2 woorlandCritters (by decide)

def thirdOption (xs : List α) : Option α := xs[2]?

#eval thirdOption woorlandCritters

#eval thirdOption ["only", "two"]

#eval woorlandCritters[1]!
