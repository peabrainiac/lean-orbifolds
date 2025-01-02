import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.DenseSubSite.Basic
import Orbifolds.Diffeology.DDiffeomorph

/-!
# CartSp and EuclOp

This file defines the sites `CartSp` and `EuclOp` of cartesian spaces resp. open subsets of
cartesian spaces and smooth maps, both with the good open cover coverage. These
sites are of relevance because concrete sheaves on them correspond to diffeological spaces,
although sheaves on them are studied not in this file but in `Orbifolds.Diffeology.SmoothSp`.

See https://ncatlab.org/nlab/show/CartSp.

Note that with the current implementation, this could not be used to *define*
diffeological spaces - it already uses diffeology in the definition of
`CartSp.openCoverCoverage`. The reason is that smooth embeddings are apparently not yet
implemented in mathlib, so diffeological inductions are used instead.

Main definitions / results:
* `CartSp`: the category of euclidean spaces and smooth maps between them
* `CartSp.openCoverCoverage`: the coverage given by jointly surjective open inductions
* `EuclOp`: the category of open subsets of euclidean spaces and smooth maps between them
* `EuclOp.openCoverCoverage`: the coverage given by jointly surjective open inductions
* `CartSp.toEuclOp`: the fully faithful embedding of `CartSp` into `EuclOp`

## TODO
* `CartSp.toEuclOp` makes `CartSp` a dense sub-site of `EuclOp`
* Generalise `CartSp` to take a smoothness parameter in `ℕ∞`
* Generalise `EuclOp` to take a smoothness parameter in `WithTop ℕ∞`
* General results about concrete sites
-/

universe u

open CategoryTheory Sheaf TopologicalSpace

def CartSp := ℕ

instance : CoeSort CartSp Type where
  coe n := EuclideanSpace ℝ (Fin n)

instance (n : ℕ) : OfNat CartSp n where
  ofNat := n

instance : SmallCategory CartSp where
  Hom := fun n m => DSmoothMap n m
  id := fun n => DSmoothMap.id
  comp := fun f g => g.comp f

instance : ConcreteCategory CartSp where
  forget := { obj := fun n => n, map := fun f => f.1 }
  forget_faithful := { map_injective := fun {_ _} => DSmoothMap.coe_injective }

instance CartSp.instFunLike (n m : CartSp) : FunLike (n ⟶ m) n m where
  coe := Subtype.val
  coe_injective' := Subtype.coe_injective

@[simp]
theorem CartSp.id_app (n : CartSp) (x : n) : (𝟙 n : n ⟶ n) x = x := rfl

@[simp]
theorem CartSp.comp_app {n m k : CartSp} (f : n ⟶ m) (g : m ⟶ k) (x : n) :
    (f ≫ g : n → k) x = g (f x) := rfl

/-- The open cover coverage on `CartSp`, consisting of all coverings by open smooth embeddings.
  Since mathlib apparently doesn't have smooth embeddings yet, diffeological inductions are
  used instead. -/
def CartSp.openCoverCoverage : Coverage CartSp where
  covering n := {s | (∀ (m : _) (f : m ⟶ n), s f → Induction f.1 ∧ IsOpenMap f.1) ∧
    ⋃ (m : CartSp) (f ∈ s (Y := m)), Set.range f.1 = Set.univ}
  pullback n m g s hs := by
    use fun k => {f | (∃ (k : _) (f' : k ⟶ n), s f' ∧ Set.range (g.1 ∘ f.1) ⊆ Set.range f'.1)
      ∧ Induction f.1 ∧ IsOpenMap f.1}
    refine ⟨⟨fun k f hf => hf.2, ?_⟩, ?_⟩
    · refine Set.iUnion_eq_univ_iff.2 fun x => ?_
      let ⟨k,hk⟩ := Set.iUnion_eq_univ_iff.1 hs.2 (g x)
      let ⟨f,hf,hgx⟩ := Set.mem_iUnion₂.1 hk
      refine ⟨m, Set.mem_iUnion₂.2 ?_⟩
      let ⟨ε, hε, hxε⟩ := Metric.isOpen_iff.1
        ((hs.1 k f hf).2.isOpen_range.preimage g.2.continuous) x hgx
      let e := (DDiffeomorph.univBall x hε)
      use ⟨_, dsmooth_subtype_val.comp e.dsmooth⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · refine ⟨k, f, hf, _root_.subset_trans ?_ (Set.image_subset_iff.2 hxε)⟩
        simp_rw [Set.range_comp]; apply Set.image_mono; simp
      · refine ⟨induction_subtype_val.comp e.induction, ?_⟩
        have := (Metric.isOpen_ball  (x := x) (ε := ε)).dTopCompatible
        exact (Metric.isOpen_ball).isOpenMap_subtype_val.comp e.toHomeomorph'.isOpenMap
      · change x ∈ Set.range (Subtype.val ∘ e.toEquiv)
        rw [e.toEquiv.surjective.range_comp]; simp [hε]
    · intro k f ⟨⟨k',f',hf'⟩,_⟩; use k'
      let f'' := (DDiffeomorph.ofInduction (hs.1 k' f' hf'.1).1)
      use ⟨_,(f''.dsmooth_invFun.comp <|
        (f ≫ g).2.subtype_mk (fun x => hf'.2 (Set.mem_range_self x)))⟩
      refine ⟨f', hf'.1, ?_⟩; ext x; change f'.1 (f''.invFun _) = _
      simp_rw [show f'.1 = Subtype.val ∘ f'' by rfl]
      dsimp; rw [DDiffeomorph.apply_symm_apply,comp_apply]; rfl

/-- The open cover grothendieck topology on `CartSp`. -/
def CartSp.openCoverTopology : GrothendieckTopology CartSp :=
  openCoverCoverage.toGrothendieck

def EuclOp := (n : ℕ) × Opens (EuclideanSpace ℝ (Fin n))

instance : CoeSort EuclOp Type where
  coe u := u.2

instance : SmallCategory EuclOp where
  Hom := fun u v => DSmoothMap u v
  id := fun n => DSmoothMap.id
  comp := fun f g => g.comp f

instance : ConcreteCategory EuclOp where
  forget := { obj := fun u => u, map := fun f => f.1 }
  forget_faithful := { map_injective := fun {_ _} => DSmoothMap.coe_injective }

instance EuclOp.instFunLike (u v : EuclOp) : FunLike (u ⟶ v) u v where
  coe := Subtype.val
  coe_injective' := Subtype.coe_injective

@[simp]
theorem EuclOp.id_app (u : EuclOp) (x : u) : (𝟙 u : u ⟶ u) x = x := rfl

@[simp]
theorem EuclOp.comp_app {u v w : EuclOp} (f : u ⟶ v) (g : v ⟶ w) (x : u) :
    (f ≫ g : u → w) x = g (f x) := rfl

/-- The open cover coverage on `EuclOp`, consisting of all coverings by open smooth embeddings.
  Since mathlib apparently doesn't have smooth embeddings yet, diffeological inductions are
  used instead. -/
def EuclOp.openCoverCoverage : Coverage EuclOp where
  covering u := {s | (∀ (v : _) (f : v ⟶ u), s f → Induction f.1 ∧ IsOpenMap f.1) ∧
    ⋃ (v : EuclOp) (f ∈ s (Y := v)), Set.range f.1 = Set.univ}
  pullback u v g s hs := by
    use fun k => {f | (∃ (k : _) (f' : k ⟶ u), s f' ∧ Set.range (g.1 ∘ f.1) ⊆ Set.range f'.1)
      ∧ Induction f.1 ∧ IsOpenMap f.1}
    refine ⟨⟨fun k f hf => hf.2, ?_⟩, ?_⟩
    · refine Set.iUnion_eq_univ_iff.2 fun x => ?_
      let ⟨w,hw⟩ := Set.iUnion_eq_univ_iff.1 hs.2 (g x)
      let ⟨f,hf,hgx⟩ := Set.mem_iUnion₂.1 hw
      have h := v.2.2.isOpenMap_subtype_val _ ((hs.1 _ _ hf).2.isOpen_range.preimage g.2.continuous')
      use ⟨_, _, h⟩
      refine Set.mem_iUnion₂.2 ⟨⟨_, dsmooth_inclusion (Subtype.coe_image_subset _ _)⟩, ?_⟩
      refine ⟨⟨⟨w, f, hf, ?_⟩, ?_, ?_⟩, ?_⟩
      · simp only [Opens.carrier_eq_coe, SetLike.coe_sort_coe]
        rw [Set.range_comp, Set.range_inclusion]
        convert Set.image_preimage_subset _ _; ext x
        rw [Set.mem_setOf_eq, Subtype.val_injective.mem_set_image]
      · exact induction_inclusion <| Subtype.coe_image_subset _ _
      · exact h.isOpenMap_inclusion <| Subtype.coe_image_subset _ _
      · dsimp; rw [Set.range_inclusion]; exact ⟨_, hgx, rfl⟩
    · intro k f ⟨⟨k',f',hf'⟩,_⟩; use k'
      let f'' := (DDiffeomorph.ofInduction (hs.1 k' f' hf'.1).1)
      use ⟨_,(f''.dsmooth_invFun.comp <|
        (f ≫ g).2.subtype_mk (fun x => hf'.2 (Set.mem_range_self x)))⟩
      refine ⟨f', hf'.1, ?_⟩; ext x; change f'.1 (f''.invFun _) = _
      simp_rw [show f'.1 = Subtype.val ∘ f'' by rfl]
      dsimp; rw [DDiffeomorph.apply_symm_apply,comp_apply]; rfl

/-- The open cover grothendieck topology on `EuclOp`. -/
def EuclOp.openCoverTopology : GrothendieckTopology EuclOp :=
  openCoverCoverage.toGrothendieck

/-- The embedding of `CartSp` into `EuclOp`. -/
noncomputable def CartSp.toEuclOp : CartSp ⥤ EuclOp where
  obj n := ⟨n, ⊤⟩
  map f := ⟨_, f.2.restrict (Set.mapsTo_univ f Set.univ)⟩

/-- Open subsets of cartesian spaces can be covered with cartesian spaces. -/
instance : CartSp.toEuclOp.IsCoverDense EuclOp.openCoverTopology := by
  constructor; intro u
  refine EuclOp.openCoverCoverage.mem_toGrothendieck_sieves_of_superset (R := ?_) ?_ ?_
  · exact fun {v} f ↦ v.2.1 = Set.univ ∧ Induction f.1 ∧ IsOpenMap f.1
  · intro v f hf
    refine ⟨⟨v.1, ⟨_, dsmooth_id.restrict (Set.mapsTo_univ _ _)⟩, ?_, ?_⟩⟩
    · let e : CartSp.toEuclOp.obj v.1 ⟶ v :=
        ⟨_, dsmooth_id.restrict (by convert Set.mapsTo_univ _ _; exact hf.1)⟩
      exact e ≫ f
    · ext x; rfl
  · refine ⟨fun v f hf ↦ hf.2, Set.iUnion_eq_univ_iff.2 fun x => ?_⟩
    use ⟨u.1, ⊤⟩; apply Set.mem_iUnion₂.2
    let ⟨ε, hε, hxε⟩ := Metric.isOpen_iff.1 u.2.2 x.1 x.2
    let e := (DDiffeomorph.Set.univ _).trans (DDiffeomorph.univBall x.1 hε)
    use ⟨_, (dsmooth_inclusion hxε).comp e.dsmooth⟩
    refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
    · exact (induction_inclusion hxε).comp e.induction
    · have := (@isOpen_univ (EuclideanSpace ℝ (Fin u.1)) _).dTopCompatible
      have h : IsOpen (Metric.ball x.1 ε) := Metric.isOpen_ball
      have := h.dTopCompatible
      exact (h.isOpenMap_inclusion hxε).comp e.toHomeomorph'.isOpenMap
    · rw [Set.range_comp, e.surjective.range_eq, Set.image_univ]
      use ⟨x.1, Metric.mem_ball_self hε⟩; rfl

instance CartSp.toEuclOp_fullyFaithful : CartSp.toEuclOp.FullyFaithful where
  preimage {n m} f := by
    exact ⟨_, (dsmooth_subtype_val.comp f.2).comp (dsmooth_id.subtype_mk (Set.mem_univ))⟩

instance : CartSp.toEuclOp.Full := CartSp.toEuclOp_fullyFaithful.full

instance : CartSp.toEuclOp.Faithful := CartSp.toEuclOp_fullyFaithful.faithful

instance : CartSp.toEuclOp.IsDenseSubsite
    CartSp.openCoverTopology EuclOp.openCoverTopology where
  functorPushforward_mem_iff {n} s := by
    unfold EuclOp.openCoverTopology CartSp.openCoverTopology
      EuclOp.openCoverCoverage CartSp.openCoverCoverage
    --rw [Coverage.toGrothendieck_eq_sInf]
    sorry
