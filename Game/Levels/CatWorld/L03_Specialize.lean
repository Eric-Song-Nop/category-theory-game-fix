import Game.Metadata

World "CatWorld"
Level 3

Title "The `specialize` tactic"

Introduction " Given two morphisms composing with the same morphism are equal, we can conclude that they are equal.

If $$f : X ⟶ Y$$ and $$g : X ⟶ Y$$ are morphisms such that $$f ∘ h = g ∘ h$$, then $$f = g$$.
"

open CategoryTheory
universe v u  -- The order in this declaration matters: v often needs to be explicitly specified while u often can be omitted
variable (C : Type u) [Category.{v} C]

Statement (X Y : C) {f g : X ⟶ Y} (w : ∀ {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) : f = g := by
  Hint "Consider the special case when `h` is the identity morphism, you can write an identity morphism on Category `{Y}` as `𝟙 Y`."
  specialize w (𝟙 Y)
  Hint "Try to simplify the `f` compose `id` part"
  rw [Category.comp_id] at w
  rw [Category.comp_id] at w
  exact w

Conclusion "Easy right?"

/- Use these commands to add items to the game's inventory. -/


/--
use the `specialize` tactic to give a specify case for proof!
-/
TacticDoc specialize
/--
Apply the exactly same condition or theorem to finish the proof.
-/
TacticDoc exact
NewTactic specialize exact
-- NewLemma Nat.add_comm Nat.add_assoc
/--
A morphism `f` is equal to `f` composed with the identity morphism.
`f = f ≫ 𝟙 X`
-/
DefinitionDoc Category.comp_id as "Category.comp_id"
NewDefinition Category.comp_id


