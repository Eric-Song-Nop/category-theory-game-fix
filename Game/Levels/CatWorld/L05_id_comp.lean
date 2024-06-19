import Game.Metadata

World "CatWorld"
Level 5

Title "Only `𝟙` left"

Introduction "
Only `𝟙` compose with `g` gets `g`.
"
open CategoryTheory
universe v u  -- The order in this declaration matters: v often needs to be explicitly specified while u often can be omitted
variable (C : Type u) [Category.{v} C]

Statement (X: C) {f : X ⟶ X} (w : ∀ {Y : C} (g : X ⟶ Y), f ≫ g = g) : f = 𝟙 X := by
  Hint "Consider the lemma `eq_of_comp_left_eq` or `eq_of_comp_right_eq` that we have proved in the previous level."
  apply eq_of_comp_left_eq
  Hint "Introduce more variables from the statement"
  intro Y g
  rw [Category.id_comp]
  exact w g

Conclusion "We call this `id_of_comp_left_id`"

/- Use these commands to add items to the game's inventory. -/

/--
use the `specialize` tactic to give a specify case for proof!
-/
TacticDoc specialize
/--
Apply the exactly same condition or theorem to finish the proof.
-/
TacticDoc exact
/--
Apply the condition or theorem to goal.
-/
TacticDoc apply
/--
Introduces one or more hypotheses, optionally naming and/or pattern-matching them.
  For each hypothesis to be introduced, the remaining main goal's target type must
  be a `let` or function type.
-/
TacticDoc intro
NewTactic intro apply

-- NewLemma Nat.add_comm Nat.add_assoc
/--
[[mathlib_doc]]
A morphism `f` is equal to identity morphism compose with `f`.
This is the left identity law of category theory, reverse of `comp_id`.
`f = 𝟙 X ≫ f`
-/
DefinitionDoc Category.id_comp as "Category.id_comp"

/--
[[mathlib_doc]]
Given two morphisms composing with the same morphism are equal, we can conclude that they are equal.
-/
TheoremDoc CategoryTheory.eq_of_comp_left_eq as "eq_of_comp_left_eq" in "Comp"
NewTheorem CategoryTheory.eq_of_comp_left_eq
