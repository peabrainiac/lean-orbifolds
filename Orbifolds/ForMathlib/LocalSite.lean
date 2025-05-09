import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Adjunction.Triple

/-!
# Local sites
A site (C,J) is called local if it has a terminal object whose only covering sieve is trivial -
this makes it possible to define coconstant sheaves on it, giving its sheaf topos the structure
of a local topos. This makes them an important stepping stone to cohesive sites.

See https://ncatlab.org/nlab/show/local+site.

## Main definitions / results
* `J.IsLocalSite`: typeclass stating that (C,J) is a local site.
* `coconstantSheaf`: the coconstant sheaf functor `Type w ⥤ Sheaf J (Type max v w)` defined on any
  local site.
* `ΓCoconstantSheafAdj`: the adjunction between the global sections functor `Γ` and
  `coconstantSheaf`.
* `fullyFaithfulCoconstantSheaf`: `coconstantSheaf` is fully faithful.
* `fullyFaithfulConstantSheaf`: on local sites, the constant sheaf functor is fully faithful.
All together this shows that for local sites `Sheaf J (Type max u v w)` forms a local topos, but
since we don't yet have local topoi this can't be stated yet.

TODO: generalise universe levels from `max u v` to `max u v w` again once that is possible.
-/

universe u v w

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A local site is a site that has a terminal object with only a single covering sieve. -/
class GrothendieckTopology.IsLocalSite extends HasTerminal C where
  /-- The only covering sieve of the terminal object is the trivial sieve. -/
  eq_top_of_mem : ∀ S ∈ J (⊤_ C), S = ⊤

/-- On a local site, every covering sieve contains every morphism from the terminal object. -/
lemma LocalSite.from_terminal_mem_of_mem [J.IsLocalSite] {X : C} (f : ⊤_ C ⟶ X) {S : Sieve X}
    (hS : S ∈ J X) : S.arrows f :=
  (S.mem_iff_pullback_eq_top f).2 <| IsLocalSite.eq_top_of_mem _ <| J.pullback_stable f hS

/-- Every category with a terminal object becomes a local site with the trivial topology. -/
instance {C : Type u} [Category.{v} C] [HasTerminal C] : (trivial C).IsLocalSite where
  eq_top_of_mem _ := trivial_covering.1

/-- The functor that sends any set `A` to the functor `Cᵒᵖ → Type _` that sends any `X : C`
to the set of all functions `A → (⊤_ C ⟶ X)`. This can be defined on any site with a terminal
object, but has values in sheaves in the case of local sites. -/
noncomputable def Presheaf.coconst {C : Type u} [Category.{v} C] [HasTerminal C] :
    Type w ⥤ (Cᵒᵖ ⥤ Type max v w) :=
  uliftFunctor ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj
    (coyoneda.obj (op (⊤_ C)) ⋙ uliftFunctor).op

/-- On local sites, `Presheaf.coconst` actually takes values in sheaves. -/
lemma Presheaf.coconst_isSheaf [J.IsLocalSite] (X : Type w) : IsSheaf J (coconst.obj X) := by
  refine (isSheaf_iff_isSheaf_of_type J _).2 fun Y S hS f hf ↦ ?_
  refine ⟨fun g ↦ f g.down (LocalSite.from_terminal_mem_of_mem J g.down hS) ⟨𝟙 _⟩, ?_, ?_⟩
  · intro Z g hg
    exact funext fun (x : ULift (_ ⟶ _)) ↦
      (congrFun (f.comp_of_compatible S hf hg x.down) _).trans (congrArg (f g hg) <| by simp)
  · intro g hg
    exact funext fun h : ULift (⊤_ C ⟶ Y) ↦ Eq.trans (by simp [Presheaf.coconst]) <|
      congrFun (hg h.down ((LocalSite.from_terminal_mem_of_mem J h.down hS))) _

/-- The right adjoint to the global sections functor that exists over any local site.
Takes a type `X` to the sheaf that sends each `Y : C` to the type of functions `Y → X`. -/
noncomputable def coconstantSheaf [J.IsLocalSite] :
    Type w ⥤ Sheaf J (Type (max v w)) where
  obj X := ⟨Presheaf.coconst.obj X, Presheaf.coconst_isSheaf J X⟩
  map f := ⟨Presheaf.coconst.map f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

-- this is currently needed to obtain the instance `HasSheafify J (Type max u v)`.
attribute [local instance] CategoryTheory.Types.instConcreteCategory
attribute [local instance] CategoryTheory.Types.instFunLike

/-- On local sites, the global sections functor `Γ` is left-adjoint to the coconstant functor. -/
@[simps!]
noncomputable def ΓCoconstantSheafAdj [J.IsLocalSite] : Γ J (Type max u v) ⊣ coconstantSheaf J := by
  refine Adjunction.ofNatIsoLeft ?_ (ΓNatIsoSheafSections J _ terminalIsTerminal).symm
  exact {
    unit := {
      app X := ⟨{
        app Y (x : X.val.obj Y) y := ⟨X.val.map (op y.down) x⟩
        naturality Y Z f := by
          ext (x : X.val.obj Y); dsimp [coconstantSheaf, Presheaf.coconst]; ext z
          exact (FunctorToTypes.map_comp_apply X.val _ _ x).symm
      }⟩
      naturality X Y f := by
        ext Z (x : X.val.obj Z); dsimp [coconstantSheaf, Presheaf.coconst]; ext z
        exact (NatTrans.naturality_apply f.val _ x).symm
    }
    counit := { app X := fun f : ULift (_ ⟶ _) → _ ↦ (f default).down }
    left_triangle_components X := by
      ext (x : X.val.obj _)
      dsimp; convert congrFun (X.val.map_id _) x; exact Subsingleton.elim _ _
    right_triangle_components X := by
      ext Y (f : _ → _); dsimp [coconstantSheaf, Presheaf.coconst]; ext y
      dsimp; congr; convert Category.id_comp _; exact Subsingleton.elim _ _
  }

instance [J.IsLocalSite] : (Γ J (Type max u v)).IsLeftAdjoint :=
  ⟨coconstantSheaf J, ⟨ΓCoconstantSheafAdj J⟩⟩

instance [J.IsLocalSite] : (coconstantSheaf.{u,v,max u v} J).IsRightAdjoint :=
  ⟨Γ J _, ⟨ΓCoconstantSheafAdj J⟩⟩

/-- The global sections of the coconstant sheaf on a type are naturally isomorphic to that type.-/
noncomputable def coconstantSheafΓNatIsoId [J.IsLocalSite] :
    coconstantSheaf J ⋙ Γ J _ ≅ 𝟭 (Type max u v) := by
  refine (isoWhiskerLeft _ (ΓNatIsoSheafSections J _ terminalIsTerminal)).trans ?_
  exact (NatIso.ofComponents (fun X ↦ {
    hom x := fun _ ↦ ⟨x⟩
    inv f := (f (default : ULift (⊤_ C ⟶ ⊤_ C))).down
    inv_hom_id := by
      dsimp [coconstantSheaf, Presheaf.coconst]; ext; dsimp
      congr; exact Subsingleton.elim _ _
  })).symm

/-- `coconstantSheaf` is fully faithful. -/
noncomputable def fullyFaithfulCoconstantSheaf [J.IsLocalSite] :
    (coconstantSheaf.{u,v,max u v} J).FullyFaithful :=
  (ΓCoconstantSheafAdj J).fullyFaithfulROfCompIsoId (coconstantSheafΓNatIsoId J)

instance [J.IsLocalSite] : (coconstantSheaf.{u,v,max u v} J).Full :=
  (fullyFaithfulCoconstantSheaf J).full

instance [J.IsLocalSite] : (coconstantSheaf.{u,v,max u v} J).Faithful :=
  (fullyFaithfulCoconstantSheaf J).faithful

/-- On local sites, the constant sheaf functor is fully faithful. -/
noncomputable def fullyFaithfulConstantSheaf [HasWeakSheafify J (Type max u v)] [J.IsLocalSite] :
    (constantSheaf J (Type max u v)).FullyFaithful :=
  ((constantSheafΓAdj J _).fullyFaithfulEquiv (ΓCoconstantSheafAdj J)).symm <|
    fullyFaithfulCoconstantSheaf J

instance [HasWeakSheafify J (Type max u v)] [J.IsLocalSite] :
    (constantSheaf J (Type max u v)).Full :=
  (fullyFaithfulConstantSheaf J).full

instance [HasWeakSheafify J (Type max u v)] [J.IsLocalSite] :
    (constantSheaf J (Type max u v)).Faithful :=
  (fullyFaithfulConstantSheaf J).faithful

end CategoryTheory
