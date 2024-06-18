import Game.Levels.CatWorld.L01_HelloWorld

World "CatWorld"
Title "Cat World"

Introduction "
Let's learn some category theory!

## Definition of category

A category `C` consists of
  * a collection of objects `X, Y, Z, ...`
  * a collection of morphisms `f, g, h, ...`
so that:
  * each morphism has specified domain and codomain objects;
    `f : X ⟶ Y` signifies that `f` is a morphism with
    domain `X` and codomain `Y`
  * each object has a designated identity morphism `𝟙 X : X ⟶ X`
  * for any pair of morphisms `f, g` with the codomain of `f` equal
    to the domain of `g`,the exists a specified composite morphism
    `f ≫ g` whose domain is that of `f` and codomain that of `g`,
    i.e. `f : X ⟶ Y, g : Y ⟶ Z` then `f ≫ g : X ⟶ Z`
This data is subject to the following axioms:
  * For any `f : X ⟶ Y`,
  -/
  /- Axiom :
    f ≫ 𝟙 Y = f-/
  /- Axiom:
    𝟙 X ≫ f = f-/

  /-* For any composable triple of morphisms `f, g, h`, we have associativity
  `f ≫ (g ≫ h) = (f ≫ g) ≫ h`-/
  /- Axiom:
    f ≫ (g ≫ h) = (f ≫ g) ≫ h-/
"
