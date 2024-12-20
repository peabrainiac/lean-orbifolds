import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Convex.Normed

/-!
# Delta-generated topological spaces

This file defines delta-generated spaces, as topological spaces whose topology is coinduced by all
maps from euclidean spaces into them. Categorical properties are shown in `DeltaGenerated.lean`.

See https://ncatlab.org/nlab/show/Delta-generated+topological+space.

Adapted from `Mathlib.Topology.Compactness.CompactlyGeneratedSpace`.

TODO:
* Delta-generated spaces are compactly generated.
* Delta-generated spaces are equivalently generated by the simplices Δⁿ.
* Delta-generated spaces are equivalently generated by the unit interval I.
* Disjoint unions of delta-generated spaces are delta-generated.
* Quotients of delta-generated spaces are delta-generated.
-/

universe u v

open TopologicalSpace Topology

/-- The topology coinduced by all maps from ℝⁿ into a space. -/
def TopologicalSpace.deltaGenerated (X : Type u) [TopologicalSpace X] : TopologicalSpace X :=
  ⨆ f : (n : ℕ) × C(((Fin n) → ℝ),X), coinduced f.2 inferInstance

/-- The topology coinduced by a map out of a sigma type is the surpremum of the topologies
  coinduced by its components.
  Probably should go into mathlib; `induced_to_pi` is already there. -/
lemma coinduced_sigma {ι Y : Type u} {X : ι → Type v} [tX : (i : ι) → TopologicalSpace (X i)]
    (f : (i : ι) → X i → Y) : coinduced (fun x : (i : ι) × X i => f x.1 x.2) inferInstance =
    ⨆ i : ι, coinduced (f i) inferInstance := by
  rw [instTopologicalSpaceSigma,coinduced_iSup]; rfl

/-- The delta-generated topology is also coinduced by a single map out of a sigma type. -/
lemma deltaGenerated_eq_coinduced {X : Type u} [t : TopologicalSpace X] :
    deltaGenerated X = coinduced
    (fun x : (f : (n : ℕ) × C(((Fin n) → ℝ),X)) × ((Fin f.1) → ℝ) => x.1.2 x.2)
    inferInstance := by
  rw [deltaGenerated,←coinduced_sigma]

/-- The delta-generated topology is at least as fine as the original one. -/
lemma deltaGenerated_le {X : Type u} [t : TopologicalSpace X] : deltaGenerated X ≤ t :=
  iSup_le_iff.mpr fun f => f.2.continuous.coinduced_le

lemma isOpen_deltaGenerated_iff {X : Type u} [t : TopologicalSpace X] {u : Set X} :
    IsOpen[deltaGenerated X] u ↔ ∀ (n : ℕ) (p : C(((Fin n) → ℝ),X)), IsOpen (p ⁻¹' u) := by
  simp_rw [deltaGenerated,isOpen_iSup_iff,isOpen_coinduced,Sigma.forall]

/-- A map from ℝⁿ to X is continuous iff it is continuous regarding the
  delta-generated topology on X. -/
lemma continuous_to_deltaGenerated' {X : Type u} [t : TopologicalSpace X] {n : ℕ}
    {f : ((Fin n) → ℝ) → X} : Continuous[_,deltaGenerated X] f ↔ Continuous f := by
  simp_rw [continuous_iff_coinduced_le]
  refine' ⟨fun h => h.trans deltaGenerated_le,fun h => _⟩
  simp_rw [deltaGenerated]
  exact le_iSup_of_le (i := ⟨n,f,continuous_iff_coinduced_le.mpr h⟩) le_rfl

lemma deltaGenerated_deltaGenerated_eq {X : Type u} [t : TopologicalSpace X] :
    @deltaGenerated X (deltaGenerated X) = deltaGenerated X := by
  ext u; simp_rw [isOpen_deltaGenerated_iff]; refine' forall_congr' fun n => _
  -- somewhat awkward because `ContinuousMap` doesn't play well with multiple topologies.
  refine' ⟨fun h p => h <| @ContinuousMap.mk (Fin n → ℝ) X _ (deltaGenerated X) p <|
      continuous_to_deltaGenerated'.mpr p.2,
    fun h p => h ⟨p,continuous_to_deltaGenerated'.mp <|
      @ContinuousMap.continuous_toFun _ _ _ (deltaGenerated X) p⟩⟩

/-- A space is delta-generated if its topology is equal to the delta-generated topology, i.e.
  coinduced by all continuous maps ℝⁿ → X. Since the delta-generated topology is always finer
  than the original one, it suffices to show that it is also coarser. -/
class DeltaGeneratedSpace (X : Type u) [t : TopologicalSpace X] : Prop where
  le_deltaGenerated : t ≤ deltaGenerated X

variable {X : Type u} [t : TopologicalSpace X]

lemma eq_deltaGenerated [DeltaGeneratedSpace X] : t = deltaGenerated X :=
  eq_of_le_of_le DeltaGeneratedSpace.le_deltaGenerated deltaGenerated_le

/-- A subset of a delta-generated space is open iff its preimage is open for every
  continuous map from ℝⁿ to X. -/
lemma DeltaGeneratedSpace.isOpen_iff [DeltaGeneratedSpace X] {u : Set X} : IsOpen u ↔
    ∀ (n : ℕ) (p : ContinuousMap ((Fin n) → ℝ) X), IsOpen (p ⁻¹' u) := by
  nth_rewrite 1 [eq_deltaGenerated (X := X)]; exact isOpen_deltaGenerated_iff

/-- A map out of a delta-generated space is continuous iff it preserves continuity of maps
  from ℝⁿ into X. -/
lemma DeltaGeneratedSpace.continuous_iff {X Y : Type u} [tX : TopologicalSpace X]
    [tY : TopologicalSpace Y] [DeltaGeneratedSpace X] {f : X → Y} :
    Continuous f ↔ ∀ (n : ℕ) (p : C(((Fin n) → ℝ),X)), Continuous (f ∘ p) := by
  simp_rw [continuous_iff_coinduced_le]
  nth_rewrite 1 [eq_deltaGenerated (X := X),deltaGenerated]
  simp [coinduced_compose]
  constructor
  · intro h n p; apply h ⟨n,p⟩
  · rintro h ⟨n,p⟩; apply h n p

/-- A map out of a delta-generated space is continuous iff it is continuous with respect
  to the delta-generification of the topology on the codomain. -/
lemma continuous_to_deltaGenerated {X Y : Type u} [tX : TopologicalSpace X]
    [tY : TopologicalSpace Y] [DeltaGeneratedSpace X] {g : X → Y} :
    Continuous[_,deltaGenerated Y] g ↔ Continuous g := by
  simp_rw [DeltaGeneratedSpace.continuous_iff,continuous_to_deltaGenerated']

namespace DeltaGeneratedSpace

/-- Type synonym to be equipped with the delta-generated topology. -/
def of (X : Type u) [TopologicalSpace X] : Type u := X

instance : TopologicalSpace (of X) := deltaGenerated X

instance : DeltaGeneratedSpace (of X) :=
  ⟨le_of_eq deltaGenerated_deltaGenerated_eq.symm⟩

/-- The natural map from the delta-generification of `X` to `X`. -/
def counit : (of X) → X := id

/-- The delta-generification counit is continuous. -/
lemma continuous_counit : Continuous (counit : _ → X) := by
  rw [continuous_iff_coinduced_le]; exact deltaGenerated_le

end DeltaGeneratedSpace

/--
Some lemmas about locally path-connected spaces that really should move into mathlib.
-/

lemma isOpen_pathComponentIn {X : Type u} [TopologicalSpace X] [LocPathConnectedSpace X] {x : X}
    {F : Set X} (hF : IsOpen F) : IsOpen (pathComponentIn x F) := by
  refine' isOpen_iff_mem_nhds.mpr fun y hy => _
  let ⟨s,hs⟩ := (path_connected_basis y).mem_iff.mp (hF.mem_nhds (pathComponentIn_subset hy))
  exact Filter.mem_of_superset hs.1.1 <| pathComponentIn_congr hy ▸
    hs.1.2.subset_pathComponentIn (mem_of_mem_nhds hs.1.1) hs.2

lemma isOpen_pathComponent {X : Type u} [TopologicalSpace X] [LocPathConnectedSpace X] {x : X} :
    IsOpen (pathComponent x) :=
  pathComponentIn_univ x ▸ isOpen_pathComponentIn isOpen_univ

lemma isClosed_pathComponent {X : Type u} [TopologicalSpace X] [LocPathConnectedSpace X] {x : X} :
    IsClosed (pathComponent x) := by
  refine' isClosed_iff_nhds.mpr fun y h => _
  let ⟨z,hz⟩ := h _ (isOpen_pathComponent.mem_nhds <| mem_pathComponent_self y)
  exact hz.2.trans hz.1.symm

lemma isClopen_pathComponent {X : Type u} [TopologicalSpace X] [LocPathConnectedSpace X] {x : X} :
    IsClopen (pathComponent x) :=
  ⟨isClosed_pathComponent,isOpen_pathComponent⟩

/-- Locally path-connected spaces are locally connected. -/
instance {X : Type u} [TopologicalSpace X] [LocPathConnectedSpace X] :
    LocallyConnectedSpace X := by
  refine' ⟨forall_imp (fun x h => ⟨fun s => _⟩) path_connected_basis⟩
  refine' (h.mem_iff' s).trans ⟨fun ⟨s,hs⟩ => _,fun ⟨u,hu⟩ => ⟨u,⟨hu.1.1.mem_nhds hu.1.2.1,
    hu.1.1.isConnected_iff_isPathConnected.mp hu.1.2.2⟩,hu.2⟩⟩
  let ⟨u,hu⟩ := mem_nhds_iff.mp hs.1.1
  exact ⟨pathComponentIn x u,⟨isOpen_pathComponentIn hu.2.1,⟨mem_pathComponentIn_self hu.2.2,
    (isPathConnected_pathComponentIn hu.2.2).isConnected⟩⟩,
    pathComponentIn_subset.trans <| hu.1.trans hs.2⟩

/-- A space is locally path-connected iff all path components of open subsets are open. -/
lemma isLocPathConnected_iff {X : Type u} [TopologicalSpace X] :
    LocPathConnectedSpace X ↔ ∀ x : X, ∀ u : Set X, IsOpen u → IsOpen (pathComponentIn x u) :=
  ⟨fun _ _ _ hu => isOpen_pathComponentIn hu,fun h => ⟨fun x => ⟨fun s => by
    refine' ⟨fun hs => _,fun ⟨_,ht⟩ => Filter.mem_of_superset ht.1.1 ht.2⟩
    let ⟨u,hu⟩ := mem_nhds_iff.mp hs
    exact ⟨pathComponentIn x u,⟨(h x u hu.2.1).mem_nhds (mem_pathComponentIn_self hu.2.2),
      isPathConnected_pathComponentIn hu.2.2⟩,pathComponentIn_subset.trans hu.1⟩⟩⟩⟩

/-- A space is locally path-connected iff all path components of open subsets are neighbourhoods. -/
lemma isLocPathConnected_iff' {X : Type u} [TopologicalSpace X] :
    LocPathConnectedSpace X ↔ ∀ x : X, ∀ u : Set X, IsOpen u → x ∈ u →
      pathComponentIn x u ∈ nhds x := by
  simp_rw [isLocPathConnected_iff,forall_comm (β := Set X),←imp_forall_iff]
  refine' forall_congr' fun u => imp_congr_right fun _ => _
  exact ⟨fun h x hxu => (h x).mem_nhds (mem_pathComponentIn_self hxu),
    fun h x => isOpen_iff_mem_nhds.mpr fun y hy =>
      pathComponentIn_congr hy ▸ h y <| pathComponentIn_subset hy⟩

/-- Any topology coinduced by a locally path-connected topology is locally path-connected. -/
lemma LocPathConnectedSpace.coinduced {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [LocPathConnectedSpace X] (f : X → Y) : @LocPathConnectedSpace Y (coinduced f ‹_›) := by
  let _ := TopologicalSpace.coinduced f ‹_›; have hf : Continuous f := continuous_coinduced_rng
  refine' isLocPathConnected_iff.mpr fun y u hu =>
    isOpen_coinduced.mpr <| isOpen_iff_mem_nhds.mpr fun x hx => _
  have hx' := Set.preimage_mono pathComponentIn_subset hx
  refine' mem_nhds_iff.mpr ⟨pathComponentIn x (f ⁻¹' u),_,
    isOpen_pathComponentIn <| hu.preimage hf,mem_pathComponentIn_self hx'⟩
  rw [←Set.image_subset_iff,←pathComponentIn_congr hx]
  exact ((isPathConnected_pathComponentIn hx').image hf).subset_pathComponentIn
    ⟨x,mem_pathComponentIn_self hx',rfl⟩ <|
    (Set.image_mono pathComponentIn_subset).trans <| u.image_preimage_subset f

/-- Quotients of locally path-connected spaces are locally path-connected. -/
lemma Topology.IsQuotientMap.locPathConnectedSpace {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [LocPathConnectedSpace X] {f : X → Y} (h : IsQuotientMap f) :
    LocPathConnectedSpace Y :=
  h.2 ▸ LocPathConnectedSpace.coinduced f

/-- Quotients of locally path-connected spaces are locally path-connected. -/
instance Quot.locPathConnectedSpace {X : Type u} [TopologicalSpace X] {r : X → X → Prop}
    [LocPathConnectedSpace X] : LocPathConnectedSpace (Quot r) :=
  isQuotientMap_quot_mk.locPathConnectedSpace

/-- Quotients of locally path-connected spaces are locally path-connected. -/
instance Quotient.locPathConnectedSpace {X : Type u} [TopologicalSpace X] {s : Setoid X}
    [LocPathConnectedSpace X] : LocPathConnectedSpace (Quotient s) :=
  isQuotientMap_quotient_mk'.locPathConnectedSpace

/-- Disjoint unions of locally path-connected spaces are locally path-connected. -/
instance Sigma.locPathConnectedSpace {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] [(i : ι) → LocPathConnectedSpace (X i)] :
    LocPathConnectedSpace ((i : ι) × X i) := by
  rw [isLocPathConnected_iff']; intro x u hu hxu; rw [mem_nhds_iff]
  refine' ⟨(Sigma.mk x.1) '' (pathComponentIn x.2 ((Sigma.mk x.1) ⁻¹' u)),_,_,_⟩
  · apply IsPathConnected.subset_pathComponentIn
    · exact (isPathConnected_pathComponentIn (by exact hxu)).image continuous_sigmaMk
    · exact ⟨x.2,mem_pathComponentIn_self hxu,rfl⟩
    · exact (Set.image_mono pathComponentIn_subset).trans (u.image_preimage_subset _)
  · exact isOpenMap_sigmaMk _ <| isOpen_pathComponentIn <| hu.preimage continuous_sigmaMk
  · exact ⟨x.2,mem_pathComponentIn_self hxu,rfl⟩

/-- Delta-generated spaces are locally connected. -/
instance [DeltaGeneratedSpace X] : LocPathConnectedSpace X := by
  rw [eq_deltaGenerated (X := X),deltaGenerated_eq_coinduced]
  exact LocPathConnectedSpace.coinduced _
