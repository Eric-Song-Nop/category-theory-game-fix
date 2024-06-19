import Game.Metadata

World "CatWorld"
Level 4

Title "left identity"

Introduction " Given two morphisms composing with the same morphism are equal, we can conclude that they are equal.

If $$f : Y ⟶ Z$$ and $$g : Y ⟶ Z$$ are morphisms such that $$h ≫ f = h ≫ g$$, then $$f = g$$.

This lemma is similar to the previous one, but the morphisms are in the reversed order.
We will make use of the identity axiom: $𝟙 ≫ X = f$ to prove this.
"

open CategoryTheory
universe v u  -- The order in this declaration matters: v often needs to be explicitly specified while u often can be omitted
variable (C : Type u) [Category.{v} C]

/--
Given two morphisms composed with the same morphism are equal, we can conclude that they are equal.
-/
TheoremDoc eq_of_comp_right_eq as "eq_of_comp_right_eq" in "Comp"

Statement eq_of_comp_right_eq (X Y : C) {f g : Y ⟶ Z} (w : ∀ {X : C} (h : X ⟶ Y), h ≫ f = h ≫ g) : f = g := by
  Hint "Consider the special case when `h` is the identity morphism, you can write an identity morphism on Category `{Y}` as `𝟙 Y`."
  specialize w (𝟙 Y)
  Hint "Try to simplify the `id` compose `f` part"
  rw [Category.id_comp] at w
  rw [Category.id_comp] at w
  exact w

Conclusion "We call this equal of left equal lemma."

/- Use these commands to add items to the game's inventory. -/

/--
use the `specialize` tactic to give a specify case for proof!
-/
TacticDoc specialize
/--
Apply the exactly same condition or theorem to finish the proof.
-/
TacticDoc exact
-- NewLemma Nat.add_comm Nat.add_assoc
/--
A morphism `f` is equal to identity morphism compose with `f`.
This is the left identity law of category theory, reverse of `comp_id`.
`f = 𝟙 X ≫ f`
-/
DefinitionDoc Category.id_comp as "Category.id_comp"
NewDefinition Category.id_comp
