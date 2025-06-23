/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Embedded submanifolds

We define a new typeclass `SliceModel` to denote a model with corners which "embeds" into another
one: i.e., there is an embedding of the underlying topological spaces, a continuous linear
equivalence inclusion between the normed spaces, which are compatible with the maps given by the
models with corners.

A future PR will use this condition to define smooth (immersed and embedded) submanifolds: for `M`
to be a submanifold of `N`, to begin with their models with corners should be slice models.

## Main definitions and results

* `SliceModel F I I`: TODO!

* each model with corners is a slice model w.r.t. itself
* being slice models is transitive
* each model with corners `I` embeds into the products `I.prod J` and `J.prod I`

* Euclidean `n`-half-space with its standard model with corners embeds into Euclidean `n`-space
* the standard model with corners on the Euclidean `n`-quadrant embeds into its cousin on
  Euclidean `n`-half-space (hence into its cousin on Euclidean `n`-space)
* if `n ≤ m`, the standard model with corners on Euclidean `n`-space embeds into its cousin on
  Euclidean `m`-space

## Implementation notes

We model the continuous inclusion similarly to the definition of smooth immersions:
instead of an injective continuous linear map `E → E'`, we ask for a linear isomorphism
`E × F ≃L[𝕜] → E'`, where the closed complement `F` is part of the definition's data.
(Closed-ness of `F` is automatic in finite dimensions, but is required in general.)

-/

open scoped Manifold ContDiff
open Topology Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E'' E''' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E''']
    [NormedSpace 𝕜 E''']
  {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H H' H'' H''' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace H''] [TopologicalSpace H''']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {I'' : ModelWithCorners 𝕜 E'' H''}
  {J : ModelWithCorners 𝕜 E''' H'''}
  {M M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] {n : WithTop ℕ∞}

variable (I I' F) in
/--
Informally speaking, two models with corners `I` and `I'` form a **slice model** if "`I` embeds
into `I'`". More precisely, there are an embedding `H → H'` and a continuous linear map `E →L[𝕜] E'`
so the diagram
```
  H  -I  → E'
  |        |
  |        |
  H' -I' → E'
```
commutes. Formally, we prescribe a continuous linear equivalence `E × F ≃L[𝕜] E`, for some normed
space `F`, which induces the map `E → E'` in the obvious way.
-/
class SliceModel where
  /-- The continuous linear equivalence `E × F ≃L[𝕜] E'` underlying this slice model -/
  equiv: (E × F) ≃L[𝕜] E'
  /-- The embedding `H → H'` underlying this slice model -/
  map: H → H'
  hmap : Topology.IsEmbedding map
  compatible : I' ∘ map = equiv ∘ ((·, 0) : E → E × F) ∘ I

namespace SliceModel

/-- A choice of inverse of `map`: its value outside of `range map` is unspecified. -/
noncomputable def inverse [Nonempty H] (h : SliceModel F I I') : H' → H :=
  (Function.extend h.map id (fun _ ↦ (Classical.arbitrary H)))

lemma inverse_left_inv [Nonempty H] (h : SliceModel F I I') (x : H) :
    h.inverse (h.map x) = x :=
  Injective.extend_apply h.hmap.injective ..

lemma inverse_right_inv [Nonempty H] (h : SliceModel F I I') (z : H') (hz : z ∈ range h.map) :
    h.map (h.inverse z) = z := by
  choose x hx using hz
  rw [← hx, h.inverse_left_inv]

end SliceModel

namespace ContinuousLinearEquiv -- PRed in #26082

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Unique G]

variable (R M₁ M₂ M₃ : Type*) [Semiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M₁] [Module R M₂] [Module R M₃]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]

/-- The product of topological modules is associative up to continuous linear isomorphism.
This is `LinearEquiv.prodAssoc` prodAssoc as a continuous linear equivalence. -/
def prodAssoc : ((M₁ × M₂) × M₃) ≃L[R] M₁ × M₂ × M₃ where
  toLinearEquiv := LinearEquiv.prodAssoc R M₁ M₂ M₃
  continuous_toFun := (continuous_fst.comp continuous_fst).prodMk
    ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  continuous_invFun := (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd)

@[simp]
lemma prodAssoc_toLinearEquiv :
  (prodAssoc 𝕜 E E' E'').toLinearEquiv = LinearEquiv.prodAssoc 𝕜 E E' E'' := rfl

-- not simp as the combination of existing lemmas. TODO: should this one still be added?
lemma prodAssoc_toEquiv :
  (prodAssoc 𝕜 E E' E'').toEquiv = Equiv.prodAssoc E E' E'' := rfl

-- TODO: move up to Equiv.prodAssoc or so, then this one is implied...
@[simp]
lemma prodAssoc_apply (p₁ : E) (p₂ : E') (p₃ : E'') :
  (prodAssoc 𝕜 E E' E'') ((p₁, p₂), p₃) = (p₁, (p₂, p₃)) := rfl

@[simp]
lemma prodAssoc_symm_apply (p₁ : E) (p₂ : E') (p₃ : E'') :
  (prodAssoc 𝕜 E E' E'').symm (p₁, (p₂, p₃)) = ((p₁, p₂), p₃) := rfl

end ContinuousLinearEquiv

section instances

/-- Every model with corners is a slice model over itself. -/
instance : SliceModel (⊥ : Subspace 𝕜 E) I I where
  equiv := ContinuousLinearEquiv.prodUnique 𝕜 E _
  map := id
  hmap := Topology.IsEmbedding.id
  compatible := by ext x; dsimp

/-- If `I` is a slice model of `I'`, then `J.prod I` is a slice model of `J.prod I'`. -/
instance [h : SliceModel F I I'] : SliceModel F (J.prod I) (J.prod I') where
  -- Up to the obvious maps, we just apply h.equiv.
  equiv := (ContinuousLinearEquiv.prodAssoc 𝕜 E''' E F).trans <|
    (ContinuousLinearEquiv.refl 𝕜 E''').prodCongr h.equiv
  map := Prod.map id h.map
  hmap := IsEmbedding.id.prodMap h.hmap
  compatible := by
    dsimp
    ext ⟨x, y⟩ <;> simp
    -- XXX: is there a better tactic for this?
    change (I' ∘ SliceModel.map F I I') y = ((SliceModel.equiv I I') ∘ ((·, 0) : E → E × F) ∘ I) y
    rw [h.compatible]

/-- If `I` is a slice model of `I'`, then `I.prod J` is a slice model of `I'.prod J`. -/
instance [h : SliceModel F I I'] : SliceModel F (I.prod J) (I'.prod J) where
  equiv := by
    letI pre := (ContinuousLinearEquiv.prodComm 𝕜 E E''').prodCongr (.refl 𝕜 F)
    letI post := ContinuousLinearEquiv.prodComm 𝕜 E' E'''
    letI main : ((E''' × E) × F) ≃L[𝕜] E''' × E' :=
      (ContinuousLinearEquiv.prodAssoc 𝕜 E''' E F).trans <|
      (ContinuousLinearEquiv.refl 𝕜 E''').prodCongr h.equiv
    apply pre.trans (main.trans post.symm)
  map := Prod.map h.map id
  hmap := h.hmap.prodMap IsEmbedding.id
  compatible := by
    ext ⟨x, y⟩ <;> simp
    -- XXX: is there a better tactic for this?
    change (I' ∘ SliceModel.map F I I') x = ((SliceModel.equiv I I') ∘ ((·, 0) : E → E × F) ∘ I) x
    rw [h.compatible]

/-- If `E' ≃ E × F`, then the trivial models with corners of `E` and `E'` form a slice model. -/
def SliceModel.modelWithCornersSelf (h : (E × F) ≃L[𝕜] E') : SliceModel F (𝓘(𝕜, E)) (𝓘(𝕜, E')) where
  equiv := h
  map := h ∘ (·, (0 : F))
  hmap := by
    apply h.toHomeomorph.isEmbedding.comp
    rw [← IsEmbedding.of_comp_iff (ContinuousLinearEquiv.prodComm 𝕜 E F).toHomeomorph.isEmbedding]
    exact isEmbedding_prodMkRight (0 : F)
  compatible := by simp

-- TODO: make an instance/ figure out why Lean complains about synthesisation order!
/-- If `I` is a slice model w.r.t. `I'` and `I'` is a slice model w.r.t. `I''`,
then `I` is a slice model w.r.t. `I''`. -/
def instTrans (h : SliceModel F I I') (h' : SliceModel F' I' I'') : SliceModel (F × F') I I'' where
  equiv := (ContinuousLinearEquiv.prodAssoc 𝕜 E F F').symm.trans
    ((h.equiv.prodCongr (ContinuousLinearEquiv.refl 𝕜 F')).trans h'.equiv)
  map := h'.map ∘ h.map
  hmap := h'.hmap.comp h.hmap
  compatible := by -- paste the commutative diagrams for `h` and `h'` together
    ext x
    simp only [comp_apply, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.refl_apply, ContinuousLinearEquiv.prodAssoc_symm_apply]
    -- can this be condensed? feels unnecessarily painful
    -- (grind errors with `unknown constant h.compatible`)
    calc
      _ = (I'' ∘ SliceModel.map F' I' I'') (SliceModel.map F I I' x) := by
        simp [Function.comp_apply]
      _ = (SliceModel.equiv I' I'' ∘ (fun x ↦ (x, (0 : F'))) ∘ ↑I') (SliceModel.map F I I' x) := by
        rw [h'.compatible]
      _ = (SliceModel.equiv I' I'' ∘ (fun x ↦ (x, (0 : F')))) ((I' ∘ SliceModel.map F I I') x) := by
        simp [Function.comp_apply]
      _ = _ := by
        rw [h.compatible]
        congr

/-- *Any* model with corners on `E` which is an embedding is a slice model with the trivial model
on `E`. (The embedding condition excludes strange cases of submanifolds with boundary.)
For boundaryless models, that is always true. -/
def SliceModel.ofEmbedding {I : ModelWithCorners 𝕜 E H} (hI : IsEmbedding I) :
    SliceModel (⊥ : Subspace 𝕜 E) I 𝓘(𝕜, E) where
  equiv := ContinuousLinearEquiv.prodUnique 𝕜 E _
  map := I
  hmap := hI
  compatible := by ext; simp

-- TODO: prove that I is an embedding if I is boundaryless, then add the corresponding definition

-- TODO: think about the boundary case, and which particular version of submanifolds
-- this definition enforces...

-- FIXME: should these instances move to `Manifold/Instances/Real.lean` instead?
section RealInstances

open scoped Manifold

/-- Euclidean half-space is a slice model w.r.t. Euclidean space. -/
-- NB. Golfing this using the previous instance is not as obvious because of instance mismatches.
noncomputable instance {n : ℕ} [NeZero n] :
    SliceModel (⊥ : Subspace ℝ ((Fin n → ℝ))) (𝓡∂ n) (𝓡 n) where
  equiv := ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin n)) _
  map := Subtype.val
  hmap := Topology.IsEmbedding.subtypeVal
  compatible := by
    ext x'
    simp only [modelWithCornersSelf_coe, comp_apply, id_eq, ContinuousLinearEquiv.prodUnique_apply]
    rfl

/-- The standard model on `ℝ^n` is a slice model for the standard model for `ℝ^m`, for `n ≤ m`. -/
noncomputable instance {n m : ℕ} :
    SliceModel ((EuclideanSpace ℝ (Fin m))) (𝓡 n) (𝓡 (n + m)) where
  equiv := EuclideanSpace.finAddEquivProd.symm
  map x := EuclideanSpace.finAddEquivProd.symm (x, 0)
  hmap :=
    (EuclideanSpace.finAddEquivProd.symm).toHomeomorph.isEmbedding.comp (isEmbedding_prodMkLeft 0)
  compatible := by ext; simp

noncomputable instance {n : ℕ} [NeZero n] :
    SliceModel (⊥ : Subspace ℝ ((Fin n → ℝ))) (modelWithCornersEuclideanQuadrant n) (𝓡∂ n) where
  equiv := ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin n)) _
  map := fun ⟨x, hx⟩ ↦ ⟨x, hx 0⟩
  hmap := by
    have h : IsEmbedding (Subtype.val : (EuclideanHalfSpace n) → (EuclideanSpace ℝ (Fin n))) :=
      IsEmbedding.subtypeVal
    have : IsEmbedding (Subtype.val : (EuclideanQuadrant n) → (EuclideanSpace ℝ (Fin n))) :=
      IsEmbedding.subtypeVal
    rw [← IsEmbedding.of_comp_iff h]
    convert this
  compatible := by
    ext x
    simp only [comp_apply, ContinuousLinearEquiv.prodUnique_apply]
    rfl

end RealInstances

end instances

open IsManifold

-- XXX: should h and f be part of the underlying data? well, I may want a SliceModel class to be
-- inferred first, right? at least, otherwise they should be explicit...
variable (M M' n) in
/--
`IsImmersedSubmanifold M N h f` means `M` is an immersed `C^n` submanifold of `N`, w.r.t. the map
`f : M → N` and a `SliceModel` `h` from `I` to `I'`.
We will endow `M` with a topology and manifold structure so `f` is a `C^k` immersion.
TODO: may need to revise this to ensure no diamonds occur; revisit once a basic version of this
compiles
-/
class IsImmersedSubmanifold [TopologicalSpace M] {f : M → M'} [h : SliceModel F I I'] where
    hf : Continuous f
    sliceChartAt : M' → PartialHomeomorph M' H'
    sliceChartAt_mem_maximalAtlas : ∀ y, y ∈ range f → (sliceChartAt y) ∈ maximalAtlas I' n M'
    hf' : ∀ y, y ∈ range f → InjOn f (f ⁻¹' (sliceChartAt y).source)
    -- Is this too strong? At least it's not obviously nonsense (and it should be satisfied)
    -- if this is coming from an immersion, right?
    hfoo : ∀ y, y ∈ range f → (sliceChartAt y).target ⊆ range h.map
    -- TODO: formalise enough so I can state this!
    -- hcharts : ∀ x, pullback (sliceChartAt f x) ∈ maximalAtlas I n M

variable {f : M → M'} [h : SliceModel F I I']

-- If `f` is injective, we can simplify the construction slightly.
def IsImmersedSubmanifold.mk_of_injective [TopologicalSpace M]
  (sliceChartAt : M' → PartialHomeomorph M' H')
  (sliceChartAt_mem_maximalAtlas : ∀ y, y ∈ range f → (sliceChartAt y) ∈ maximalAtlas I' n M')
  (hfoo : ∀ y, y ∈ range f → (sliceChartAt y).target ⊆ range h.map)
  (hf : Continuous f) (hf' : Injective f) : IsImmersedSubmanifold M M' (h := h) (f := f) n where
  sliceChartAt := sliceChartAt
  sliceChartAt_mem_maximalAtlas := sliceChartAt_mem_maximalAtlas
  hf := hf
  hf' _y _hy := hf'.injOn
  hfoo := hfoo

#exit

-- TODO: prove that:
-- IsImmersedSubmanifold M N n h f implies IsImmersion f n I I'
-- IsImmersion f n I I' implies IsImmersedSubmanifold (f '' M) N n h f

namespace PartialHomeomorph

variable [TopologicalSpace M] [IsManifold I' n M']

variable [Nonempty H] {φ : PartialHomeomorph M' H'} {f : M → M'}

def _root_.PartialEquiv.pullback_sliceModel (φ : PartialEquiv M' H') (f : M → M')
    (h : SliceModel F I I') : PartialEquiv M H where
  toFun := sorry
  invFun := sorry
  source := sorry
  target := sorry
  map_source' := sorry
  map_target' := sorry
  left_inv' := sorry
  right_inv' := sorry

variable (φ f) in
def pullback_sliceModel (h : SliceModel F I I') : PartialHomeomorph M H where
  toPartialEquiv := φ.toPartialEquiv.pullback_sliceModel f h
  open_source := sorry
  open_target := sorry
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry


end PartialHomeomorph
