import Game.Metadata

World "CatWorld"
Level 2

Title "Another easy lemma"

Introduction "First we start out with some easy lemmas to get us warmed up.

If $$f : X ⟶ Y$$ and $$g : X ⟶ Y$$ are morphisms such that $$f = g$$, then $$f ≫ h = g ≫ h$$.
"

open CategoryTheory
universe v u  -- The order in this declaration matters: v often needs to be explicitly specified while u often can be omitted
variable (C : Type u) [Category.{v} C]

Statement {X Y Z : C} {f g : Y ⟶ Z} (w : f = g) (h : X ⟶  Y) : h ≫ f = h ≫ g := by
  Hint "You can easily solve this using `{w}`."
  rw [w]

Conclusion "Easy right?"

/- Use these commands to add items to the game's inventory. -/

-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

