import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Local sites
A site (C,J) is called local if it has a terminal object whose only covering sieve is trivial -
this makes it possible to define codiscrete sheaves on it, giving its sheaf topos the structure
of a local topos. This makes them an important stepping stone to cohesive sites.

See https://ncatlab.org/nlab/show/local+site.
-/

universe u v w

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A local site is a site that has a terminal object with only a single covering sieve. -/
class LocalSite extends HasTerminal C where
  /-- The only covering sieve of the terminal object is the trivial sieve. -/
  eq_top_of_mem : ∀ S ∈ J (⊤_ C), S = ⊤

/-- On a local site, every covering sieve contains every morphism from the terminal object. -/
lemma LocalSite.from_terminal_mem_of_mem [LocalSite J] {X : C} (f : ⊤_ C ⟶ X) {S : Sieve X}
    (hS : S ∈ J X) : S.arrows f :=
  (S.pullback_eq_top_iff_mem f).2 <| LocalSite.eq_top_of_mem _ <| J.pullback_stable f hS

/-- Every category with a terminal object becomes a local site with the trivial topology. -/
instance {C : Type u} [Category.{v} C] [HasTerminal C] : LocalSite (trivial C) where
  eq_top_of_mem _ := trivial_covering.1

/-- The functor that sends any set `A` to the functor `Cᵒᵖ → Type _` that sends any `X : C`
to the set of all functions `A → (⊤_ C ⟶ X)`. This can be defined on any site with a terminal
object, but has values in sheaves in the case of local sites. -/
noncomputable def Presheaf.codisc {C : Type u} [Category.{v} C] [HasTerminal C] :
    Type w ⥤ (Cᵒᵖ ⥤ Type max v w) :=
  uliftFunctor ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj
    (coyoneda.obj (op (⊤_ C)) ⋙ uliftFunctor).op
  --curry.obj <| uliftFunctor.prod (coyoneda.obj (op (⊤_ C)) ⋙ uliftFunctor).op ⋙ (uncurry.obj <| yoneda)

noncomputable example [HasTerminal C] : Type max v w ⥤ (Cᵒᵖ ⥤ Type max v w) :=
  Presheaf.codisc.{u,v,max v w} (C := C)

/-- The right adjoint to the global sections functor that exists over any local site.
Takes a type `X` to the sheaf that sends each `Y : C` to the type of functions `Y → X`. -/
noncomputable def Sheaf.codisc (J : GrothendieckTopology C) [LocalSite J] :
    Type w ⥤ Sheaf J (Type (max v w)) where
  obj X := {
    val := Presheaf.codisc.obj X
    cond := (isSheaf_iff_isSheaf_of_type J _).2 fun Y S hS f hf ↦ by
      refine ⟨fun g ↦ f g.down (LocalSite.from_terminal_mem_of_mem J g.down hS) ⟨𝟙 _⟩, ?_, ?_⟩
      · intro Z g hg
        exact funext fun (x : ULift (_ ⟶ _)) ↦
          (congrFun (f.comp_of_compatible S hf hg x.down) _).trans (congrArg (f g hg) <| by simp)
      · intro g hg
        exact funext fun h : ULift (⊤_ C ⟶ Y) ↦ Eq.trans (by simp [Presheaf.codisc]) <|
          congrFun (hg h.down ((LocalSite.from_terminal_mem_of_mem J h.down hS))) _
  }
  map {X Y} (f : X → Y) := ⟨Presheaf.codisc.map f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end CategoryTheory
