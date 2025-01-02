import Mathlib.CategoryTheory.Monad.Limits
import Orbifolds.Diffeology.Sites
import Orbifolds.Diffeology.DiffSp

/-!
# Smooth Spaces
Smooth spaces are sheaves on the site `CartSp`; see https://ncatlab.org/nlab/show/smooth+set.

Main definitions / results:
* `SmoothSp`: the category of smooth spaces, as the category of sheaves on `CartSp`
* `DiffSp.toSmoothSp`: the embedding of diffeological spaces into smooth sets
* `SmoothSp.Γ`: the global sections functor taking a smooth space to the set of its points
* `SmoothSp.concr`: the concretisation functor from smooth spaces to diffeological spaces
* `DiffSp.reflectorAdjunction`: the adjunction between `SmoothSp.concr` and `DiffSp.toSmoothSp`
  turning `DiffSp` into a reflective subcategory of `SmoothSp`

## TODO
* discrete and codiscrete smooth spaces, corresponding adjunctions
* connected components functor `Π_0`, corresponding adjunction
* smooth spaces `Ω k` of differential forms
* De-Rham cohomology for smooth spaces?
-/

universe u

open CategoryTheory Sheaf

/-- The category of sheaves on `CartSp`, also known as *smooth spaces*. -/
def SmoothSp := Sheaf CartSp.openCoverTopology (Type u)

/-- Morphisms of smooth spaces are simply morphisms of sheaves. -/
instance : Category.{u,u+1} SmoothSp.{u} := by unfold SmoothSp; infer_instance

/-- The embedding of diffeological spaces into smooth spaces. -/
def DiffSp.toSmoothSp : DiffSp.{u} ⥤ SmoothSp.{u} where
  obj X := ⟨{
    obj := fun n => DSmoothMap n.unop X
    map := fun f g => g.comp f.unop
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl
  }, by
    rw [CartSp.openCoverTopology, isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_coverage]
    refine fun {n} s hs f hf => ?_
    have hs' : ∀ x : n, _ := fun x => Set.mem_iUnion.1 <| hs.2.symm ▸ Set.mem_univ x
    let k := fun x => (hs' x).choose
    have hk : ∀ x, ∃ f' : k x ⟶ n, _ := fun x => Set.mem_iUnion₂.1 (hs' x).choose_spec
    let f' := fun x => (hk x).choose
    have hf' : ∀ x, s (f' x) ∧ x ∈ Set.range (f' x).1 :=
      fun x => exists_prop.1 (hk x).choose_spec
    let f'' := fun x => f (f' x) (hf' x).1 (hf' x).2.choose
    have hf'' : ∀ l (g : l ⟶ n) (hg : s g), f'' ∘ g = f g hg := fun l g hg => by
      ext x
      dsimp [f'']
      have h := @hf _ _ 0 (DSmoothMap.const (hf' (g x)).2.choose)
        (DSmoothMap.const x) _ _ (hf' (g x)).1 hg
        (by ext; exact (hf' (g x)).2.choose_spec)
      exact DFunLike.congr_fun h 0
    refine ⟨⟨f'', ?_⟩, ?_, ?_⟩
    · refine dsmooth_iff_locally_dsmooth.2 fun x : n =>
        ⟨_, (hs.1 _ _ (hf' x).1).2.isOpen_range, (hf' x).2, ?_⟩
      rw [(DDiffeomorph.ofInduction (hs.1 _ _ (hf' x).1).1).subduction.dsmooth_iff]
      convert (f (f' x) (hf' x).1).2; exact hf'' (k x) (f' x) (hf' x).1
    · intro l g hg; ext x; exact congr_fun (hf'' l g hg) _
    · intro f''' hf'''; ext (x : n)
      rw [← (hf' x).2.choose_spec]
      exact (DFunLike.congr_fun (hf''' (f' x) (hf' x).1) _).trans
        (congr_fun (hf'' _ (f' x) (hf' x).1) _).symm⟩
  map f := ⟨{
    app := fun _ g => f.comp g
    naturality := fun _ _ _ => rfl
  }⟩
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- `DiffSp.toSmoothSp` is fully faithful. -/
def DiffSp.toSmoothSp.fullyFaithful : DiffSp.toSmoothSp.{u}.FullyFaithful where
  preimage f := ⟨fun x ↦
      (by exact f.val.app (.op 0) ⟨fun _ ↦ x, dsmooth_const⟩ : DSmoothMap (Eucl 0) _) 0, by
    intro n p hp; convert (f.val.app (.op n) ⟨p, hp.dsmooth⟩).dsmooth.isPlot using 1; ext x
    exact DFunLike.congr_fun (F := DSmoothMap _ _)
      (congrFun (f.val.naturality ⟨fun _ ↦ x, dsmooth_const⟩) ⟨p, hp.dsmooth⟩) 0⟩
  map_preimage f := by
    apply Sheaf.Hom.ext; ext n p; refine DSmoothMap.ext fun x ↦ ?_
    exact DFunLike.congr_fun (F := DSmoothMap _ _)
      (congrFun (f.val.naturality ⟨fun _ : Eucl 0 ↦ x, dsmooth_const⟩) p) 0

instance : DiffSp.toSmoothSp.{u}.Full := DiffSp.toSmoothSp.fullyFaithful.full

instance : DiffSp.toSmoothSp.{u}.Faithful := DiffSp.toSmoothSp.fullyFaithful.faithful

/-- The global sections functor taking a smooth space to its type of points. Note that this
  is by no means faithful; `SmoothSp` is not a concrete category. -/
def SmoothSp.Γ : SmoothSp.{u} ⥤ Type u where
  obj X := X.val.obj (.op 0)
  map f := f.val.app (.op 0)
  map_id := fun _ ↦ by rfl
  map_comp := fun _ _ ↦ by rfl

/-- The diffeology on the points of a smooth space given by the concretisation functor. -/
instance SmoothSp.instDiffeologicalSpaceΓ (X : SmoothSp) : DiffeologicalSpace (Γ.obj X) :=
  .generateFrom {⟨n,p⟩ | ∃ (p' : X.val.obj (.op n)),
    p = fun x : Eucl n ↦ X.val.map (Opposite.op ⟨fun _ : Eucl 0 ↦ x, dsmooth_const⟩) p'}

/-- The reflector of `DiffSp` inside of `SmoothSp`, sending a smooth space to its concretisation. -/
def SmoothSp.concr : SmoothSp.{u} ⥤ DiffSp.{u} where
  obj X := ⟨Γ.obj X, X.instDiffeologicalSpaceΓ⟩
  map f := ⟨Γ.map f, by
    rw [dsmooth_generateFrom_iff]; intro n p ⟨p', hp⟩
    refine DiffeologicalSpace.isPlot_generatedFrom_of_mem ⟨f.val.app _ p', ?_⟩
    rw [hp]; ext x; exact congrFun (f.val.naturality ⟨fun _ : Eucl 0 ↦ x, dsmooth_const⟩) p'⟩
  map_id := fun _ ↦ by rfl
  map_comp := fun _ _ ↦ by rfl

/-- The adjunction between the concretisation functor `SmoothSp ⥤ DiffSp` and the
  embedding `DiffSp ⥤ SmoothSp`. -/
def DiffSp.reflectorAdjunction : SmoothSp.concr.{u} ⊣ DiffSp.toSmoothSp.{u} :=
  Adjunction.mkOfUnitCounit {
    unit := {
      app := fun X ↦ ⟨{
        app := fun _ p ↦ ⟨fun x ↦ X.val.map ⟨fun _ ↦ x, dsmooth_const⟩ p,
          IsPlot.dsmooth (DiffeologicalSpace.isPlot_generatedFrom_of_mem ⟨p, rfl⟩)⟩
        naturality := fun ⟨n⟩ ⟨m⟩ f ↦ by
          ext p; refine DSmoothMap.ext fun x ↦ ?_
          change X.val.map (Opposite.op ⟨fun _ ↦ x, dsmooth_const⟩) (X.val.map f p) =
            X.val.map (Opposite.op ⟨fun _ ↦ f.unop x, dsmooth_const⟩) p
          exact congrFun (X.val.map_comp f _).symm p
      }⟩
      naturality := fun {X Y} f ↦ by
        apply Sheaf.Hom.ext; ext n p; refine DSmoothMap.ext fun x ↦ ?_
        dsimp at p ⊢
        change Y.val.map (Opposite.op ⟨fun _ ↦ x, dsmooth_const⟩) (f.val.app n p) =
          f.val.app (.op 0) (X.val.map _ _)
        exact congrFun (f.val.naturality _).symm p
    }
    counit := {
      app := fun X ↦ ⟨fun p : DSmoothMap _ _ ↦ p 0,
        dsmooth_generateFrom_iff.2 fun _ p ⟨p', hp⟩ ↦ by rw [hp]; exact p'.dsmooth.isPlot⟩
      naturality := fun _ _ _ ↦ rfl
    }
    left_triangle := by
      ext X x; change X.val.obj (.op 0) at x
      change X.val.map _ x = x
      rw [← show DSmoothMap.id (X := Eucl 0) = ⟨fun x ↦ 0, dsmooth_const⟩ by
        ext1 x; exact (Unique.eq_default x).trans (Unique.default_eq 0)]
      exact congrFun (X.val.map_id (.op 0) : _ = id) x
    right_triangle := rfl
  }

/-- `SmoothSp.concr` is a left-adjoint. In particular, this means that it preserves colimits. -/
instance : Functor.IsLeftAdjoint SmoothSp.concr :=
  ⟨DiffSp.toSmoothSp, ⟨DiffSp.reflectorAdjunction⟩⟩

/-- Diffeological spaces form a reflective subcategory of the category of smooth spaces. -/
instance DiffSp.toSmoothSp.reflective : Reflective toSmoothSp where
  L := SmoothSp.concr
  adj := DiffSp.reflectorAdjunction

noncomputable instance DiffSp.toSmoothSp.createsLimits : CreatesLimits toSmoothSp :=
  monadicCreatesLimits _
