import Mathlib.CategoryTheory.Sites.DenseSubSite.Basic
import Mathlib.CategoryTheory.ChosenFiniteProducts

universe u v w u₂ v₂ w₂

open CategoryTheory Limits Sheaf Opposite

namespace CategoryTheory

/-- An explicit choice of terminal object in `C`.
  TODO: integrate this into `Mathlib.CategoryTheory.ChosenFiniteProducts`. -/
class ChosenTerminal (C : Type u) [Category.{v} C] where
  /-- A choice of a terminal object. -/
  terminal : LimitCone (Functor.empty.{0} C)

instance (C : Type u) [Category.{v} C] [ChosenTerminal C] : HasTerminal C where
  has_limit _ := @hasLimitOfIso _ _ _ _ _ _ ⟨⟨ChosenTerminal.terminal⟩⟩
    (Functor.uniqueFromEmpty _).symm

/-- The chosen terminal object in a category endowed with such a choice. -/
def Limits.chosenTerminal (C : Type u) [Category.{v} C] [ChosenTerminal C] : C :=
  ChosenTerminal.terminal.cone.pt

/-- The chosen terminal object is indeed terminal. -/
def Limits.chosenTerminalIsTerminal {C : Type u} [Category.{v} C] [ChosenTerminal C] :
    IsTerminal (chosenTerminal C) :=
  (ChosenTerminal.terminal (C := C)).isLimit.ofIsoLimit <| Cones.ext (Iso.refl _) default

def ChosenTerminal.ofIsTerminal {C : Type u } [Category.{v} C] (X : C) (h : IsTerminal X) :
    ChosenTerminal C where
  terminal := ⟨_, h⟩

noncomputable instance : ChosenTerminal (Type u) :=
  ChosenTerminal.ofIsTerminal PUnit Types.isTerminalPunit

/-- The chosen terminal sheaf is the constant functor on the chosen terminal object. -/
instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (A : Type u₂)
    [Category.{v₂} A] [ChosenTerminal A] : ChosenTerminal (Sheaf J A) :=
  .ofIsTerminal {
    val := (Functor.const _).obj (chosenTerminal A)
    cond := fun _ _ _ _ _ _ ↦ ⟨chosenTerminalIsTerminal.from _,
      fun _ _ _ ↦ chosenTerminalIsTerminal.hom_ext _ _,
      fun _ _ ↦ chosenTerminalIsTerminal.hom_ext _ _⟩
  } <| IsTerminal.ofUniqueHom (fun X ↦ ⟨{
    app X := chosenTerminalIsTerminal.from _
  }⟩) fun _ _ ↦ by ext; exact chosenTerminalIsTerminal.hom_ext _ _

attribute [local instance] ConcreteCategory.hasCoeToSort
attribute [local instance] ConcreteCategory.instFunLike

/-- A terminal sheaf is also terminal as a presheaf. -/
noncomputable def Limits.IsTerminal.isTerminalSheafVal {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {A : Type u₂} [Category.{v₂} A] [HasLimits A]
    {X : Sheaf J A} (hX : IsTerminal X) : IsTerminal X.val :=
  hX.isTerminalObj (sheafToPresheaf J A)

/-- Evaluating a terminal functor yields terminal objects. -/
noncomputable def Limits.IsTerminal.isTerminalObj_functor {C : Type u} [Category.{v} C] {D : Type u₂}
    [Category.{v₂} D] [HasLimits D] {F : C ⥤ D} (hF : IsTerminal F) (X : C) :
    IsTerminal (F.obj X) :=
  hF.isTerminalObj ((evaluation C D).obj X)

/-- Sections of a terminal sheaf are terminal objects. -/
noncomputable def Limits.IsTerminal.isTerminalSheafValObj {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {A : Type u₂} [Category.{v₂} A] [HasLimits A]
    {X : Sheaf J A} (hX : IsTerminal X) (Y : Cᵒᵖ) : IsTerminal (X.val.obj Y) :=
  hX.isTerminalSheafVal.isTerminalObj_functor Y

/-- For sheaves valued in a concrete category whose terminal object is a point,
  sections of the terminal sheaf are unique. -/
noncomputable instance Sheaf.instUniqueTerminalValObjForget {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {A : Type u₂} [Category.{v₂} A] [HasLimits A]
    [ConcreteCategory.{w} A] [PreservesLimit (Functor.empty _) (forget A)] (Y : Cᵒᵖ) :
    Unique ((⊤_ Sheaf J A).val.obj Y) :=
  Concrete.uniqueOfTerminalOfPreserves _ <| terminalIsTerminal.isTerminalSheafValObj Y

/-- Sections of the terminal sheaf are unique. -/
noncomputable instance Sheaf.instUniqueTerminalValObj {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}  (Y : Cᵒᵖ) :
    Unique ((⊤_ Sheaf J (Type w)).val.obj Y) :=
  Types.isTerminalEquivUnique _ <| terminalIsTerminal.isTerminalSheafValObj Y

variable {C : Type u} [Category.{v} C]

/-- A presieve `S` on `X` in a concrete category is jointly surjective if every `x : X` is in
  the image of some `f` in `S`. -/
def Presieve.IsJointlySurjective [ConcreteCategory.{w} C] {X : C} (S : Presieve X) : Prop :=
  ∀ x : X, ∃ (Y : C), ∃ f ∈ @S Y, ∃ y, f y = x

lemma Presieve.isJointlySurjective_iff_iUnion_range_eq_univ [ConcreteCategory.{w} C]
    {X : C} {S : Presieve X} : IsJointlySurjective S ↔
    ⋃ (Y : C) (f ∈ @S Y), Set.range f = Set.univ := by
  simp [IsJointlySurjective, Set.iUnion_eq_univ_iff]

/-- A site is concrete if it is a concrete category in such a way that points correspond to
  morphisms from a terminal object, and all sieves are jointly surjective. -/
class ConcreteSite (J : GrothendieckTopology C)
    extends ChosenTerminal C, ConcreteCategory.{v} C where
  /-- The forgetful functor is given by morphisms from the terminal object. Since a forgetful
    functor might already exists, this is encoded here as a natural isomorphism. -/
  forget_natIso_coyoneda : (CategoryTheory.forget C) ≅ coyoneda.obj (.op (⊤_ C))
  /-- Said isomorphism takes `x : X` to a morphism with underlying map `fun _ ↦ x`. -/
  forget_natIso_coyoneda_apply {X : C} {x : X} :
    (DFunLike.coe (F := ⊤_ C ⟶ X) <| forget_natIso_coyoneda.hom.app X x) = fun _ ↦ x
  /-- All covering sieves are jointly surjective. -/
  sieves_isJointlySurjective {X : C} {S : Sieve X} :
    S ∈ J.sieves X → S.arrows.IsJointlySurjective

/-- The terminal object of a concrete site has exactly one point. -/
noncomputable instance ConcreteSite.instUniqueTerminal (J : GrothendieckTopology C) [ConcreteSite J] :
    Unique (⊤_ C) :=
  (forget_natIso_coyoneda.app (⊤_ C)).toEquiv.unique (β := ⊤_ C ⟶ ⊤_ C)

/-- The global sections functor on sheaves of types. Points of a sheaf `X` correspond to
  morphisms from the terminal sheaf into `X`; this corresponds to sections on the terminal
  of `C` when `C` has a terminal object, but is a bit more general. -/
noncomputable def Sheaf.Γ {J : GrothendieckTopology C} : Sheaf J (Type w) ⥤ Type (max u w) :=
  coyoneda.obj (.op (⊤_ _))

/-- The sections functor on sheaves over a concrete site as evaluation over the terminal
  object. -/
noncomputable def Sheaf.Γ' {J : GrothendieckTopology C} [ConcreteSite J] :
    Sheaf J (Type w) ⥤ Type _ where
  obj X := X.val.obj (op (⊤_ C))
  map f := f.val.app (op (⊤_ C))

noncomputable def Sheaf.Γ_natIso_Γ' {J : GrothendieckTopology C} [ConcreteSite J] :
    (Γ : Sheaf J (Type max u w) ⥤ _) ≅ Γ' where
  hom := {
    app X f := f.val.app (op (⊤_ C)) default
  }
  inv := {
    app X := fun x ↦ ⟨{
      app Y := fun y ↦ X.val.map (op (terminalIsTerminal.from _)) x
      naturality := fun _ _ _ ↦ by
        ext _
        convert FunctorToTypes.map_comp_apply X.val _ _ _
        refine congrFun (congrArg X.val.map ((op_inj_iff _ _).2 ?_)) x
        exact terminalIsTerminal.hom_ext _ _
    }⟩
    naturality X Y f := by
      ext x; apply Sheaf.hom_ext; ext y
      exact congrFun (f.val.naturality _).symm x
  }
  hom_inv_id := by
    ext X f; apply Sheaf.hom_ext; ext Y (y : (⊤_ Sheaf J _).val.obj Y)
    have h := @f.val.naturality (op (⊤_ _)) Y (op (terminalIsTerminal.from _))
    replace h := congrFun h.symm <| default
    dsimp at h; convert h; exact Subsingleton.elim _ _
  inv_hom_id := by
    ext X x; dsimp; rw [terminalIsTerminal.from_self]
    exact congrFun (X.val.map_id _) x

/-- The right adjoint to the global sections functor that exists over any concrete site.
  Takes a type `X` to the sheaf that sends each `Y : C` to the type of functions `Y → X`. -/
noncomputable def Sheaf.codisc (J : GrothendieckTopology C) [ConcreteSite J] :
    Type w ⥤ Sheaf J (Type (max v w)) where
  obj X := {
    val := {
      obj := fun Y ↦ Y.unop → X
      map := fun f g ↦ Function.comp g f.unop
    }
    cond := (isSheaf_iff_isSheaf_of_type J _).2 fun Y S hS f hf ↦ by
      choose Z g hg z hgz using ConcreteSite.sieves_isJointlySurjective hS
      refine ⟨fun y ↦ f (g y) (hg y) (z y), ?_, ?_⟩
      · intro Z' g' hg'; dsimp; ext z'
        dsimp
        have h := hf (ConcreteSite.forget_natIso_coyoneda.hom.app (Z (g' z')) (z (g' z')))
          ((ConcreteSite.forget_natIso_coyoneda).hom.app Z' z') (hg (g' z')) hg' ?_
        · dsimp at h; simp_rw [ConcreteSite.forget_natIso_coyoneda_apply] at h
          exact congrFun h (default)
        · exact (NatTrans.naturality_apply (ConcreteSite.forget_natIso_coyoneda).hom
            (g (g' z')) (z (g' z'))).symm.trans <| Eq.trans (congrArg _ (hgz (g' z'))) <|
            NatTrans.naturality_apply (ConcreteSite.forget_natIso_coyoneda).hom g' z'
      · intro f' hf'; ext y
        nth_rewrite 1 [← hgz y]
        exact congrFun (hf' (g y) (hg y)) (z y)
  }
  map {X Y} (f : X → Y) := ⟨{
    app := fun Z g ↦ f ∘ g
    naturality := fun _ _ _ ↦ rfl
  }⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/- The global sections functor on concrete sites is left-adjoint to the codiscrete functor. -/
noncomputable def Sheaf.ΓCodiscAdjunction (J : GrothendieckTopology C) [ConcreteSite J] :
    Γ.{u,v,max u v w} ⊣ codisc J :=
  Adjunction.ofNatIsoLeft (Adjunction.mkOfUnitCounit {
    unit := {
      app := fun X ↦ ⟨{
        app Y (x : X.val.obj Y) y :=
          X.val.map (op (ConcreteSite.forget_natIso_coyoneda.hom.app (unop Y) y)) x
        naturality Y Z f := by
          ext (x : X.val.obj Y); dsimp [codisc, Γ']; ext z
          have h := NatTrans.naturality_apply
            (ConcreteSite.forget_natIso_coyoneda (J := J)).hom f.unop z
          refine ((congrFun (congrArg X.val.map (congrArg Opposite.op h)) x).trans ?_).symm
          exact congrFun (X.val.map_comp _ _) x
      }⟩
      naturality X Y f := by
        ext Z (x : X.val.obj Z); dsimp [codisc, Γ']; ext z
        exact Eq.symm <| NatTrans.naturality_apply f.val
          (op (ConcreteSite.forget_natIso_coyoneda.hom.app (unop Z) z)) x
    }
    counit := { app := fun X x ↦ by exact x default }
    left_triangle := by
      ext X (x : X.val.obj _)
      dsimp [Γ']
      convert congrFun (X.val.map_id _) x
      exact congrArg op <| ((uniqueToTerminal (⊤_ C)).instSubsingleton).allEq _ _
    right_triangle := by
      ext X Y (f : _ → _); dsimp [codisc, Γ']; ext y
      exact congrArg f (congrFun ConcreteSite.forget_natIso_coyoneda_apply _)
  }) (Γ_natIso_Γ'.{u,v,max u v w} (J := J)).symm

variable (J : GrothendieckTopology C) [ConcreteSite J]

instance : (Γ.{u,v,max u v w} (J := J)).IsLeftAdjoint :=
  ⟨codisc J, ⟨ΓCodiscAdjunction J⟩⟩

instance : (Γ'.{u,v,max u v w} (J := J)).IsLeftAdjoint :=
  ⟨codisc J, ⟨Adjunction.ofNatIsoLeft (ΓCodiscAdjunction J) (Γ_natIso_Γ'.{u,v,max u v w})⟩⟩

instance : (codisc.{u,v,max u v w} J).IsRightAdjoint :=
  ⟨Γ, ⟨ΓCodiscAdjunction J⟩⟩

def Presheaf.IsConcrete (P :  Cᵒᵖ ⥤ Type w) : Prop :=
  ∀ X : C, Function.Injective fun p : P.obj (.op X) ↦ fun f : (⊤_ C ⟶ X) ↦ P.map (.op f) p

/-- The category of concrete sheaves. -/
structure ConcreteSheaf extends Sheaf J (Type w) where
  concrete : Presheaf.IsConcrete J val

/-- Morphisms of concrete sheaves are simply morphisms of sheaves. -/
instance : Category (ConcreteSheaf J) :=
  InducedCategory.category ConcreteSheaf.toSheaf

/-- The forgetful functor from concrete sheaves to sheaves. -/
def concreteSheafToSheaf : ConcreteSheaf J ⥤ Sheaf J (Type w) :=
  inducedFunctor _

def fullyFaithfulConcreteSheafToSheaf : (concreteSheafToSheaf J).FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : (concreteSheafToSheaf J).Full :=
  (fullyFaithfulInducedFunctor _).full

instance : (concreteSheafToSheaf J).Faithful :=
  (fullyFaithfulInducedFunctor _).faithful

end CategoryTheory
