/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.Misc
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Elaborators

/-!
# Covariant derivatives

TODO: add a more complete doc-string

-/

open Bundle Filter Topology Set

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section general_lemmas -- those lemmas should move

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] -- [IsManifold I 0 M]

section
variable {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']


def map_of_loc_one_jet (e u : E) (e' u' : E') : E → E' := sorry

lemma map_of_loc_one_jet_spec (e u : E) (e' u' : E') :
    map_of_loc_one_jet e u e' u' e = e' ∧
    DifferentiableAt 𝕜 (map_of_loc_one_jet e u e' u') e ∧
    fderiv 𝕜 (map_of_loc_one_jet e u e' u') e u = u' := by
  sorry

def map_of_one_jet {x : M} (u : TangentSpace I x) {x' : M'} (u' : TangentSpace I' x') :
    M → M' :=
  letI ψ := extChartAt I' x'
  letI φ := extChartAt I x
  ψ.symm ∘
  (map_of_loc_one_jet (φ x) (mfderiv I 𝓘(𝕜, E) φ x u) (ψ x') (mfderiv I' 𝓘(𝕜, E') ψ x' u')) ∘
  φ

-- TODO: version assuming `x` and `x'` are in the interior, or maybe `x` is enough.

/-- For any `(x, u) ∈ TM` and `(x', u') ∈ TM'`, `map_of_one_jet u u'` sends `x` to `x'` and
its derivative sends `u` to `u'`. We need to assume the target manifold `M'` has no boundary
since we cannot hope the result is `x` and `x'` are boundary points and `u` is inward
while `u'` is outward.
-/
lemma map_of_one_jet_spec [IsManifold I 1 M] [IsManifold I' 1 M']
      [BoundarylessManifold I' M'] {x : M} (u : TangentSpace I x) {x' : M'}
      (u' : TangentSpace I' x') :
    map_of_one_jet u u' x = x' ∧
    MDiffAt (map_of_one_jet u u') x ∧
    mfderiv I I' (map_of_one_jet u u') x u = u' := by
  let ψ := extChartAt I' x'
  let φ := extChartAt I x
  let g := map_of_loc_one_jet (φ x) (mfderiv I 𝓘(𝕜, E) φ x u) (ψ x') (mfderiv I' 𝓘(𝕜, E') ψ x' u')
  let Ψ : M' → E' := ψ -- FIXME: this is working around a limitation of MDiffAt elaborator
  have hψ : MDiffAt Ψ x' := mdifferentiableAt_extChartAt (ChartedSpace.mem_chart_source x')
  let Φ : M → E := φ -- FIXME: this is working around a limitation of MDiffAt elaborator
  have hφ : MDiffAt Φ x := mdifferentiableAt_extChartAt (ChartedSpace.mem_chart_source x)
  rcases  map_of_loc_one_jet_spec (𝕜 := 𝕜)
    (φ x) (mfderiv I 𝓘(𝕜, E) φ x u) (ψ x') (mfderiv I' 𝓘(𝕜, E') ψ x' u') with
    ⟨h : g (φ x) = ψ x', h', h''⟩
  have hg : MDiffAt g (φ x) := mdifferentiableAt_iff_differentiableAt.mpr h'
  have hgφ : MDiffAt (g ∘ φ) x := h'.comp_mdifferentiableAt hφ
  let Ψi : E' → M' := ψ.symm -- FIXME: this is working around a limitation of MDiffAt elaborator
  have hψi : MDiffAt Ψi (g (φ x)) := by
    rw [h]
    have := mdifferentiableWithinAt_extChartAt_symm (I := I') (mem_extChartAt_target x')
    exact this.mdifferentiableAt (range_mem_nhds_isInteriorPoint <|
      BoundarylessManifold.isInteriorPoint' x')
  unfold map_of_one_jet
  refold_let g φ ψ at *
  refine ⟨by simp [h, ψ], hψi.comp x hgφ, ?_⟩
  rw [mfderiv_comp x hψi hgφ, mfderiv_comp x hg hφ, mfderiv_eq_fderiv]
  change (mfderiv 𝓘(𝕜, E') I' Ψi (g (φ x))) (fderiv 𝕜 g (φ x) <| mfderiv I 𝓘(𝕜, E) φ x u) = u'
  rw [h] at hψi
  rw [h'', h, ← mfderiv_comp_apply x' hψi hψ]
  have : Ψi ∘ ψ =ᶠ[𝓝 x'] id := by
    have : ∀ᶠ z in 𝓝 x', z ∈ ψ.source := extChartAt_source_mem_nhds x'
    filter_upwards [this] with z hz
    exact ψ.left_inv hz
  simp [this.mfderiv_eq]
  rfl
end

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  -- `V` vector bundle

lemma mfderiv_const_smul (s : M → F) {x : M} (a : 𝕜) (v : TangentSpace I x) :
    mfderiv I 𝓘(𝕜, F) (a • s) x v = a • mfderiv I 𝓘(𝕜, F) s x v := by
  by_cases hs : MDifferentiableAt% s x
  · have hs' := hs.const_smul a
    suffices
      (fderivWithin 𝕜 ((a • s) ∘ (chartAt H x).symm ∘ I.symm) (range I) (I ((chartAt H x) x))) v =
       a • (fderivWithin 𝕜 (s ∘ (chartAt H x).symm ∘ I.symm) (range I)
       (I ((chartAt H x) x))) v by simpa [mfderiv, hs, hs']
    change fderivWithin 𝕜 (a • (s ∘ ↑(chartAt H x).symm ∘ ↑I.symm)) _ _ _ = _
    rw [fderivWithin_const_smul_field _ I.uniqueDiffWithinAt_image ]
    rfl
  · by_cases ha : a = 0
    · have : a • s = 0 := by ext; simp [ha]
      rw [this, ha]
      change (mfderiv I 𝓘(𝕜, F) (fun _ ↦ 0) x) v = _
      simp
    have hs' : ¬ MDifferentiableAt I 𝓘(𝕜, F) (a • s) x :=
      fun h ↦ hs (by simpa [ha] using h.const_smul a⁻¹)
    rw [mfderiv_zero_of_not_mdifferentiableAt hs, mfderiv_zero_of_not_mdifferentiableAt hs']
    simp
    rfl

lemma mfderiv_smul {f : M → F} {s : M → 𝕜} {x : M} (hf : MDiffAt f x)
    (hs : MDiffAt s x) (v : TangentSpace I x) :
    letI dsxv : 𝕜 := mfderiv I 𝓘(𝕜, 𝕜) s x v
    letI dfxv : F := mfderiv I 𝓘(𝕜, F) f x v
    mfderiv I 𝓘(𝕜, F) (s • f) x v = (s x) • dfxv + dsxv • f x := by
  sorry

end general_lemmas

section extend
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  -- `V` vector bundle

-- TODO: either change `localFrame` to make sure it is everywhere smooth
-- or introduce a cut-off here. First option is probaly better.
-- TODO: comment why we chose the second option in the end, and adapt the definition accordingly
-- new definition: smooth a bump function, then smul with localExtensionOn
/-- Extend a vector `v ∈ V x` to a section of the bundle `V`, whose value at `x` is `v`.
The details of the extension are mostly unspecified: for covariant derivatives, the value of
`s` at points other than `x` will not matter (except for shorter proofs).
Thus, we choose `s` to be somewhat nice: our chosen construction is linear in `v`.
-/
noncomputable def extend [FiniteDimensional ℝ F] [T2Space M] {x : M} (v : V x) :
    (x' : M) → V x' :=
  letI b := Basis.ofVectorSpace ℝ F
  letI t := trivializationAt F V x
  -- Choose a smooth bump function ψ near `x`, supported within t.baseSet
  -- and return ψ • V₀ instead.
  letI ht := t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  let ψ := Classical.choose <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  ψ.toFun • localExtensionOn b t x v

variable {I F}

-- NB. These two lemmas don't hold for *any* choice of extension of `v`, but they hold for
-- *well-chosen* extensions (such as ours).
-- so, one may argue this is mathematically wrong, but it encodes the "choice some extension
-- with this and that property" nicely
-- a different proof would be to argue only the value at a point matters for cov
@[simp]
lemma extend_add [FiniteDimensional ℝ F] [T2Space M] {x : M} (v v' : V x) :
    extend I F (v + v') = extend I F v + extend I F v' := by
  simp [extend, localExtensionOn_add]

@[simp]
lemma extend_smul [FiniteDimensional ℝ F] [T2Space M] {a : ℝ} {x : M} (v : V x) :
  extend I F (a • v) = a • extend I F v := by simp [extend, localExtensionOn_smul]; module

@[simp] lemma extend_apply_self [FiniteDimensional ℝ F] [T2Space M] {x : M} (v : V x) :
    extend I F v x = v := by
  simpa [extend] using
    localExtensionOn_apply_self _ _ (FiberBundle.mem_baseSet_trivializationAt' x) v

variable (I F)

lemma contMDiff_extend [IsManifold I ∞ M] [FiniteDimensional ℝ F] [T2Space M]
    [ContMDiffVectorBundle ∞ F V I] {x : M} (σ₀ : V x) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% extend I F σ₀) := by
  letI t := trivializationAt F V x
  letI ht := t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  have hx : x ∈ t.baseSet := by exact FiberBundle.mem_baseSet_trivializationAt' x
  let ψ := Classical.choose <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  let hψ :=
    Classical.choose_spec <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  apply ψ.contMDiff.contMDiffOn.smul_section_of_tsupport t.open_baseSet hψ.1
  apply contMDiffOn_localExtensionOn _ hx

lemma mdifferentiable_extend [IsManifold I ∞ M] [FiniteDimensional ℝ F] [T2Space M]
    [ContMDiffVectorBundle ∞ F V I] {x : M} (σ₀ : V x) :
    MDiff (T% extend I F σ₀) :=
  contMDiff_extend I F σ₀ |>.mdifferentiable (by simp)

theorem contDiff_extend
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    (x : E) (y : E') : ContDiff ℝ ∞ (extend 𝓘(ℝ, E) E' y (x := x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x'
  rw [← contMDiffAt_iff_contDiffAt]
  simpa [contMDiffAt_section] using contMDiff_extend (V := Trivial E E') _ _ y x'

end extend

section any_field
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] -- [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] -- [IsManifold I 0 M]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  -- [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] --[VectorBundle 𝕜 F V]
  -- `V` vector bundle

structure IsCovariantDerivativeOn
    (f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x))
    (s : Set M := Set.univ) : Prop where
  -- All the same axioms as CovariantDerivative, but restricted to the set s.
  addX (f) (X X' : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hx : x ∈ s := by trivial) : f (X + X') σ x = f X σ x + f X' σ x
  smulX (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (g : M → 𝕜) {x : M}
    (hx : x ∈ s := by trivial) : f (g • X) σ x = g x • f X σ x
  addσ (X : Π x : M, TangentSpace I x) {σ σ' : Π x : M, V x} {x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hx : x ∈ s := by trivial) :
    f X (σ + σ') x = f X σ x + f X σ' x
  leibniz (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x} {g : M → 𝕜} {x}
    (hσ : MDiffAt (T% σ) x) (hg : MDiffAt g x) (hx : x ∈ s := by trivial):
    f X (g • σ) x = (g • f X σ) x + (bar _ <| mfderiv I 𝓘(𝕜) g x (X x)) • σ x
  smul_const_σ (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (a : 𝕜) {x}
    (hx : x ∈ s := by trivial) : f X (a • σ) x = a • f X σ x

/--
A covariant derivative ∇ is called of class `C^k` iff,
whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇ X σ` is a `C^k` section.
This is a class so typeclass inference can deduce this automatically.
-/
class ContMDiffCovariantDerivativeOn [IsManifold I 1 M] (k : ℕ∞)
    (cov : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x))
    (u : Set M)  where
  contMDiff : ∀ {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x},
    CMDiff[u] (k + 1) (T% σ) → CMDiff[u] k (T% X) →
    CMDiff[u] k (T% (cov X σ))

variable {F}

namespace IsCovariantDerivativeOn

section changing_set
/-! Changing set

In this changing we change `s` in `IsCovariantDerivativeOn F f s`.

-/
lemma mono
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)} {s t : Set M}
    (hf : IsCovariantDerivativeOn F f t) (hst : s ⊆ t) : IsCovariantDerivativeOn F f s where
  addX X X' σ _ hx := hf.addX X X' σ (hst hx)
  smulX X σ f _ hx := hf.smulX X σ f (hst hx)
  addσ X _ _ _ hσ hσ' hx := hf.addσ X hσ hσ' (hst hx)
  leibniz X _ _ _ hσ hf' hx := hf.leibniz X hσ hf' (hst hx)
  smul_const_σ X σ a _ hx := hf.smul_const_σ X σ a (hst hx)

lemma iUnion {ι : Type*}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)} {s : ι → Set M}
    (hf : ∀ i, IsCovariantDerivativeOn F f (s i)) : IsCovariantDerivativeOn F f (⋃ i, s i) where
  addX X X' σ x hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).addX ..
  smulX X σ f x hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).smulX ..
  addσ X σ σ' x hσ hσ' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).addσ _ hσ hσ'
  leibniz X σ f x hσ hf' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).leibniz _ hσ hf'
  smul_const_σ X σ a x hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hf i).smul_const_σ ..

end changing_set

/- Congruence properties -/
section

lemma congr {f g : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)} {s : Set M}
    (hf : IsCovariantDerivativeOn F f s)
    -- Is this too strong? Will see!
    (hfg : ∀ {X : Π x : M, TangentSpace I x},
      ∀ {σ : Π x : M, V x}, ∀ {x}, x ∈ s → f X σ x = g X σ x) :
    IsCovariantDerivativeOn F g s := sorry

end

section computational_properties

lemma smul_const_X
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {s : Set M} (h : IsCovariantDerivativeOn F f s) {x} (a : 𝕜)
    (X : Π x, TangentSpace I x) (σ : Π x, V x) (hx : x ∈ s := by trivial) :
    f (a • X) σ x = a • f X σ x :=
  h.smulX ..

variable {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)} {s : Set M}

@[simp]
lemma zeroX (hf : IsCovariantDerivativeOn F f s)
    {x : M} (hx : x ∈ s := by trivial)
    (σ : Π x : M, V x) : f 0 σ x = 0 := by
  simpa using IsCovariantDerivativeOn.addX f hf 0 0 σ hx

@[simp]
lemma zeroσ [VectorBundle 𝕜 F V] (hf : IsCovariantDerivativeOn F f s)
    (X : Π x : M, TangentSpace I x)
    {x} (hx : x ∈ s := by trivial) : f X 0 x = 0 := by
  simpa using (hf.addσ X (mdifferentiableAt_zeroSection ..)
    (mdifferentiableAt_zeroSection ..) : f X (0+0) x = _)

lemma sum_X (hf : IsCovariantDerivativeOn F f s)
    {ι : Type*} {u : Finset ι} {X : ι → Π x : M, TangentSpace I x} {σ : Π x : M, V x}
    {x} (hx : x ∈ s) :
    f (∑ i ∈ u, X i) σ x = ∑ i ∈ u, f (X i) σ x := by
  classical
  have := hf.zeroX hx σ
  induction u using Finset.induction_on with
  | empty => simp [hf.zeroX hx]
  | insert a u ha h =>
    simp [Finset.sum_insert ha, ← h, hf.addX]

end computational_properties

section operations

variable {s : Set M}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}

/-- A convex combination of covariant derivatives is a covariant derivative. -/
@[simps]
def convexCombination
    {f' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hf : IsCovariantDerivativeOn F f s) (hf' : IsCovariantDerivativeOn F f' s) (g : M → 𝕜) :
    IsCovariantDerivativeOn F (fun X σ ↦ (g • (f X σ)) + (1 - g) • (f' X σ)) s where
  addX X X' σ _ hx := by simp [hf.addX, hf'.addX]; module
  smulX X σ φ _ hx := by simp [hf.smulX, hf'.smulX]; module
  addσ X σ σ' x hx hσ hσ' := by
      simp [hf.addσ X hx hσ hσ', hf'.addσ X hx hσ hσ']
      module
  smul_const_σ X {σ a} x hx := by
      simp [hf.smul_const_σ, hf'.smul_const_σ]
      module
  leibniz X σ φ x hσ hφ hx := by
      simp [hf.leibniz X hσ hφ, hf'.leibniz X hσ hφ]
      module

/-- A convex combination of two `C^k` connections is a `C^k` connection. -/
lemma _root_.ContMDiffCovariantDerivativeOn.convexCombination
    [IsManifold I 1 M] [VectorBundle 𝕜 F V]
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {u: Set M} {f : M → 𝕜} {n : ℕ∞} (hf : CMDiff[u] n f)
    (Hcov : ContMDiffCovariantDerivativeOn (F := F) n cov u)
    (Hcov' : ContMDiffCovariantDerivativeOn (F := F) n cov' u) :
    ContMDiffCovariantDerivativeOn F n (fun X σ ↦ (f • (cov X σ)) + (1 - f) • (cov' X σ)) u where
  contMDiff hX hσ := by
    apply ContMDiffOn.add_section
    · exact hf.smul_section <| Hcov.contMDiff hX hσ
    · exact (contMDiffOn_const.sub hf).smul_section <| Hcov'.contMDiff hX hσ

/-- A finite convex combination of covariant derivatives is a covariant derivative:
auxiliary case, where every weight functions is never one. -/
def convexCombination'_aux {ι : Type*} {s : Finset ι} (hs : Finset.Nonempty s)
    {u : Set M} {cov : ι → (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (h : ∀ i, IsCovariantDerivativeOn F (cov i) u) {f : ι → M → 𝕜} (hf : Set.EqOn (∑ i ∈ s, f i) 1 u)
    (hf₂ : ∀ i ∈ s, ∀ x ∈ u, f i x ≠ 0) (hf₃ : ∀ i ∈ s, ∀ x ∈ u, f i x ≠ 1) :
    IsCovariantDerivativeOn F (fun X σ x ↦ ∑ i ∈ s, (f i x) • (cov i) X σ x) u := by
  classical
  induction hs using Finset.Nonempty.cons_induction generalizing f with
  | singleton a =>
    simp at hf ⊢
    sorry -- use congruence now! simp_all
  | cons i₀ s hi₀ hs h' =>
    simp only [Finset.cons_eq_insert]
    let g : ι → M → 𝕜 := fun i x ↦ f i x / (1 - f i₀ x)
    have hg : Set.EqOn (∑ i ∈ s, g i) 1 u := by
      intro x hx
      simp [g]
      calc ∑ i ∈ s, f i x / (1 - f i₀ x)
        _ = ∑ i ∈ s, (1 - f i₀ x)⁻¹ • f i x := by simp_rw [smul_eq_mul, inv_mul_eq_div]
        _ = (1 - f i₀ x)⁻¹ • ∑ i ∈ s, f i x := by rw [Finset.smul_sum]
        _ = (1 - f i₀ x)⁻¹ • (∑ i ∈ Finset.cons i₀ s hi₀, f i x - f i₀ x):= by
          congr
          rw [eq_sub_iff_add_eq, Finset.sum_cons, add_comm]
        _ = (1 - f i₀ x)⁻¹ • (1 - f i₀ x):= by
          congr
          sorry -- simp [hf]
        _ = 1 := by
          simp
          refine (inv_mul_eq_one₀ ?_).mpr rfl
          rw [sub_ne_zero]; symm
          apply hf₃ i₀ (Finset.mem_cons_self i₀ s)
          exact hx
    have hg₂ : ∀ i ∈ s, ∀ x ∈ u, g i x ≠ 0 := by
      intro i hi x hx
      simp only [ne_eq, div_eq_zero_iff, not_or, g]
      refine ⟨hf₂ i (Finset.mem_cons_of_mem hi) x hx, ?_⟩
      rw [sub_eq_zero]
      exact (hf₃ i₀ (Finset.mem_cons_self i₀ s) x hx).symm
    have hg₃ : ∀ i ∈ s, ∀ x ∈ u, g i x ≠ 1 := by
      intro i hi x hx
      simp [g]
      -- wan the f i to never be 1/2... that's fishy!
      -- simp only [ne_eq, div_eq_zero_iff, not_or, g]
      -- refine ⟨hf₂ i (Finset.mem_cons_of_mem hi) x hx, ?_⟩
      -- rw [sub_eq_zero]
      -- exact (hf₃ i₀ (Finset.mem_cons_self i₀ s) x hx).symm
      sorry

    -- TODO: rejigger my set-up to provide this
    -- at x, some function is non-zero, and then the same holds in a neighbourhood
    -- (by continuity, which I'll also assume)
    -- so, need to shrink the open set and patch together, awful, but can be done
    have bettersetup : ∀ x, f i₀ x ≠ 1 := sorry -- XXX use assumption instead
    have side_computation (X σ x) : ∑ i ∈ insert i₀ s, f i x • cov i X σ x
        = f i₀ x • cov i₀ X σ x + (1 - f i₀ x) • ∑ i ∈ s, g i x • cov i X σ x := calc
        _ = f i₀ x • cov i₀ X σ x + ∑ i ∈ s, f i x • cov i X σ x := by
          simp [Finset.sum_insert hi₀]
        _ = f i₀ x • cov i₀ X σ x + (1 - f i₀ x) • ∑ i ∈ s, g i x • cov i X σ x := by
          congr
          rw [Finset.smul_sum]
          congr; ext i
          simp only [g]
          -- this should be obvious now!
          rw [← smul_assoc, smul_eq_mul, mul_div_cancel₀ (a := f i x) (b := 1 - f i₀ x)]
          rw [sub_ne_zero]; exact (bettersetup x).symm
    have : IsCovariantDerivativeOn F (fun X σ x ↦
        f i₀ x • cov i₀ X σ x + (1 - f i₀ x) • ∑ i ∈ s, g i x • cov i X σ x) u := by
      apply (h i₀).convexCombination --(h' hg hg') _
      apply h' ?_ _ hg₃
      apply hg
      · intro i hi x hx
        apply hg₂ _ hi _ hx
    exact this.congr fun X σ {x} hx ↦ (side_computation ..).symm

#exit

/-- A finite convex combination of covariant derivatives is a covariant derivative. -/
def convexCombination' {ι : Type*} {s : Finset ι} (hs : Finset.Nonempty s)
    {u : Set M} {cov : ι → (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (h : ∀ i, IsCovariantDerivativeOn F (cov i) u) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) :
    IsCovariantDerivativeOn F (fun X σ x ↦ ∑ i ∈ s, (f i x) • (cov i) X σ x) u := by
  classical
  induction hs using Finset.Nonempty.cons_induction generalizing f with
  | singleton a => simp_all
  | cons i₀ s hi₀ hs h' =>
    simp only [Finset.cons_eq_insert]
    let g : ι → M → 𝕜 := fun i x ↦ f i x / (1 - f i₀ x)
    have hg : ∑ i ∈ s, g i = 1 := by
      ext x
      simp [g]
      calc ∑ i ∈ s, f i x / (1 - f i₀ x)
        _ = ∑ i ∈ s, (1 - f i₀ x)⁻¹ • f i x := by simp_rw [smul_eq_mul, inv_mul_eq_div]
        _ = (1 - f i₀ x)⁻¹ • ∑ i ∈ s, f i x := by rw [Finset.smul_sum]
        _ = (1 - f i₀ x)⁻¹ • (∑ i ∈ Finset.cons i₀ s hi₀, f i x - f i₀ x):= by
          congr
          rw [eq_sub_iff_add_eq, Finset.sum_cons, add_comm]
        _ = (1 - f i₀ x)⁻¹ • (1 - f i₀ x):= by
          congr
          sorry -- exact hf except applied
        _ = 1 := sorry

    -- TODO: rejigger my set-up to provide this
    -- at x, some function is non-zero, and then the same holds in a neighbourhood
    -- (by continuity, which I'll also assume)
    -- so, need to shrink the open set and patch together, awful, but can be done
    have bettersetup : ∀ x, f i₀ x ≠ 1 := sorry
    have side_computation (X σ x) : ∑ i ∈ insert i₀ s, f i x • cov i X σ x
        = f i₀ x • cov i₀ X σ x + (1 - f i₀ x) • ∑ i ∈ s, g i x • cov i X σ x := calc
        _ = f i₀ x • cov i₀ X σ x + ∑ i ∈ s, f i x • cov i X σ x := by
          simp [Finset.sum_insert hi₀]
        _ = f i₀ x • cov i₀ X σ x + (1 - f i₀ x) • ∑ i ∈ s, g i x • cov i X σ x := by
          congr
          rw [Finset.smul_sum]
          congr; ext i
          simp only [g]
          -- this should be obvious now!
          rw [← smul_assoc, smul_eq_mul, mul_div_cancel₀ (a := f i x) (b := 1 - f i₀ x)]
          rw [sub_ne_zero]; exact (bettersetup x).symm
    have : IsCovariantDerivativeOn F (fun X σ x ↦
        f i₀ x • cov i₀ X σ x + (1 - f i₀ x) • ∑ i ∈ s, g i x • cov i X σ x) u :=
      (h i₀).convexCombination (h' hg) _
    exact this.congr fun X σ {x} hx ↦ (side_computation ..).symm

/-- A convex combination of finitely many `C^k` connections on `u` is a `C^k` connection on `u`. -/
lemma _root_.ContMDiffCovariantDerivativeOn.convexCombination' {n : ℕ∞}
    [IsManifold I 1 M] [VectorBundle 𝕜 F V] {ι : Type*} {s : Finset ι} {u : Set M}
    {cov : ι → (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hcov : ∀ i ∈ s, ContMDiffCovariantDerivativeOn F n (cov i) u)
    {f : ι → M → 𝕜} (hf : ∀ i ∈ s, CMDiff[u] n (f i)) :
    ContMDiffCovariantDerivativeOn F n (fun X σ x ↦ ∑ i ∈ s, (f i x) • (cov i) X σ x) u where
  contMDiff hσ hX :=
    ContMDiffOn.sum_section (fun i hi ↦ (hf i hi).smul_section <| (hcov i hi).contMDiff hσ hX)

variable {s : Set M}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}

lemma add_one_form [∀ (x : M), IsTopologicalAddGroup (V x)]
    [∀ (x : M), ContinuousSMul 𝕜 (V x)] (hf : IsCovariantDerivativeOn F f s)
    (A : Π x : M, TangentSpace I x →L[𝕜] V x →L[𝕜] V x) :
    IsCovariantDerivativeOn F (fun X σ x ↦ f X σ x + A x (X x) (σ x)) s where
  addX X X' σ x hx := by
    simp [hf.addX]
    abel
  smulX X σ g x hx := by
    simp [hf.smulX]
  addσ X σ σ' x hσ hσ' hx := by
    simp [hf.addσ X hσ hσ']
    abel
  smul_const_σ X {σ a} x hx := by
    simp [hf.smul_const_σ]
  leibniz X σ g x hσ hg hx := by
    simp [hf.leibniz X hσ hg]
    module

end operations

section trivial_bundle

variable (I M F) in
@[simps]
noncomputable def trivial :
    IsCovariantDerivativeOn F (V := Trivial M F)
      (fun X s x ↦ mfderiv I 𝓘(𝕜, F) s x (X x)) univ where
  addX X X' σ x _ := by simp
  smulX X σ c' x _ := by simp
  addσ X σ σ' x hσ hσ' hx := by
    rw [mdifferentiableAt_section] at hσ hσ'
    -- TODO: specialize mdifferentiableAt_section to trivial bundles?
    change MDifferentiableAt I 𝓘(𝕜, F) σ x at hσ
    change MDifferentiableAt I 𝓘(𝕜, F) σ' x at hσ'
    rw [mfderiv_add hσ hσ']
    rfl
  smul_const_σ X σ a x hx := by
    rw [mfderiv_const_smul]
  leibniz X σ f x hσ hf hx := by
    rw [mdifferentiableAt_section] at hσ
    exact mfderiv_smul hσ hf (X x)

lemma of_endomorphism (A : (x : M) → TangentSpace I x →L[𝕜] F →L[𝕜] F) :
    IsCovariantDerivativeOn F
      (fun (X : Π x : M, TangentSpace I x) (s : M → F) x ↦
        letI d : F := mfderiv I 𝓘(𝕜, F) s x (X x)
        d + A x (X x) (s x)) univ :=
  trivial I M F |>.add_one_form A

end trivial_bundle

end IsCovariantDerivativeOn

/-! Bundled global covariant derivatives -/

variable (I F V) in
@[ext]
structure CovariantDerivative where
  toFun : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)
  isCovariantDerivativeOn : IsCovariantDerivativeOn F toFun Set.univ

namespace CovariantDerivative

attribute [coe] toFun

/-- Coercion of a `CovariantDerivative` to function -/
instance : CoeFun (CovariantDerivative I F V)
    fun _ ↦ (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x) :=
  ⟨fun e ↦ e.toFun⟩

instance (cov : CovariantDerivative I F V) {s : Set M} :
    IsCovariantDerivativeOn F cov s := by
  apply cov.isCovariantDerivativeOn.mono (fun ⦃a⦄ a ↦ trivial)

/-- If `f : Vec(M) × Γ(E) → Vec(M)` is a covariant derivative on each set in an open cover,
it is a covariant derivative. -/
def of_isCovariantDerivativeOn_of_open_cover {ι : Type*} {s : ι → Set M}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hf : ∀ i, IsCovariantDerivativeOn F f (s i)) (hs : ⋃ i, s i = Set.univ) :
    CovariantDerivative I F V :=
  ⟨f, hs ▸ IsCovariantDerivativeOn.iUnion hf⟩

@[simp]
lemma of_isCovariantDerivativeOn_of_open_cover_coe {ι : Type*} {s : ι → Set M}
    {f : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    (hf : ∀ i, IsCovariantDerivativeOn F f (s i)) (hs : ⋃ i, s i = Set.univ) :
    of_isCovariantDerivativeOn_of_open_cover hf hs = f := rfl


/--
A covariant derivative ∇ is called of class `C^k` iff,
whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇ X σ` is a `C^k` section.
This is a class so typeclass inference can deduce this automatically.
-/
class ContMDiffCovariantDerivative [IsManifold I 1 M]
    (cov : CovariantDerivative I F V) (k : ℕ∞) where
  contMDiff : ContMDiffCovariantDerivativeOn F k cov.toFun Set.univ

@[simp]
lemma contMDiffCovariantDerivativeOn_univ_iff [IsManifold I 1 M]
    {cov : CovariantDerivative I F V} {k : ℕ∞} :
    ContMDiffCovariantDerivativeOn F k cov.toFun Set.univ ↔ ContMDiffCovariantDerivative cov k :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.contMDiff⟩

-- future: if g is a C^k metric on a manifold M, the corresponding Levi-Civita connection
-- is of class C^k (up to off-by-one errors)

section computational_properties

@[simp]
lemma zeroX (cov : CovariantDerivative I F V) (σ : Π x : M, V x) : cov 0 σ = 0 := by
  ext x
  apply cov.isCovariantDerivativeOn.zeroX

@[simp]
lemma zeroσ [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V)
    (X : Π x : M, TangentSpace I x) : cov X 0 = 0 := by
  ext x
  apply cov.isCovariantDerivativeOn.zeroσ

lemma sum_X (cov : CovariantDerivative I F V)
    {ι : Type*} {s : Finset ι} {X : ι → Π x : M, TangentSpace I x} {σ : Π x : M, V x} :
    cov (∑ i ∈ s, X i) σ = ∑ i ∈ s, cov (X i) σ := by
  ext x
  simpa using cov.isCovariantDerivativeOn.sum_X

end computational_properties

section operations

/-- A convex combination of covariant derivatives is a covariant derivative. -/
@[simps]
def convexCombination (cov cov' : CovariantDerivative I F V) (g : M → 𝕜) :
    CovariantDerivative I F V where
  toFun := fun X σ ↦ (g • (cov X σ)) + (1 - g) • (cov' X σ)
  isCovariantDerivativeOn :=
    cov.isCovariantDerivativeOn.convexCombination cov'.isCovariantDerivativeOn _

/-- A finite convex combination of covariant derivatives is a covariant derivative. -/
def convexCombination' {ι : Type*} {s : Finset ι} (hs : Finset.Nonempty s)
    (cov : ι → CovariantDerivative I F V) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) :
    CovariantDerivative I F V where
  toFun X t x := ∑ i ∈ s, (f i x) • (cov i) X t x
  isCovariantDerivativeOn := IsCovariantDerivativeOn.convexCombination' hs
    (fun i ↦ (cov i).isCovariantDerivativeOn) hf

/-- A convex combination of two `C^k` connections is a `C^k` connection. -/
lemma ContMDiffCovariantDerivative.convexCombination [IsManifold I 1 M] [VectorBundle 𝕜 F V]
  (cov cov' : CovariantDerivative I F V)
    {f : M → 𝕜} {n : ℕ∞} (hf : ContMDiff I 𝓘(𝕜) n f)
    (hcov : ContMDiffCovariantDerivative cov n) (hcov' : ContMDiffCovariantDerivative cov' n) :
    ContMDiffCovariantDerivative (convexCombination cov cov' f) n where
  contMDiff :=
    ContMDiffCovariantDerivativeOn.convexCombination hf.contMDiffOn hcov.contMDiff hcov'.contMDiff

/-- A convex combination of finitely many `C^k` connections is a `C^k` connection. -/
lemma ContMDiffCovariantDerivative.convexCombination' [IsManifold I 1 M] [VectorBundle 𝕜 F V]
    {ι : Type*} {s : Finset ι} (hs : Finset.Nonempty s)
    (cov : ι → CovariantDerivative I F V) {f : ι → M → 𝕜} (hf : ∑ i ∈ s, f i = 1) {n : ℕ∞}
    (hf' : ∀ i ∈ s, ContMDiff I 𝓘(𝕜) n (f i))
    (hcov : ∀ i ∈ s, ContMDiffCovariantDerivative (cov i) n) :
    ContMDiffCovariantDerivative (convexCombination' hs cov hf) n where
  contMDiff :=
    ContMDiffCovariantDerivativeOn.convexCombination'
      (fun i hi ↦ (hcov i hi).contMDiff) (fun i hi ↦ (hf' i hi).contMDiffOn)

-- Future: prove a version with a locally finite sum, and deduce that C^k connections always
-- exist (using a partition of unity argument)

end operations

section trivial_bundle

variable (I M F) in
@[simps]
noncomputable def trivial : CovariantDerivative I F (Trivial M F) where
  toFun X s x := mfderiv I 𝓘(𝕜, F) s x (X x)
  isCovariantDerivativeOn := -- TODO use previous work
  { addX X X' σ x _ := by simp
    smulX X σ c' x _ := by simp
    addσ X σ σ' x hσ hσ' hx := by
      rw [mdifferentiableAt_section] at hσ hσ'
      -- TODO: specialize mdifferentiableAt_section to trivial bundles?
      change MDifferentiableAt I 𝓘(𝕜, F) σ x at hσ
      change MDifferentiableAt I 𝓘(𝕜, F) σ' x at hσ'
      rw [mfderiv_add hσ hσ']
      rfl
    smul_const_σ X σ a x hx := by
      rw [mfderiv_const_smul]
    leibniz X σ f x hσ hf hx := by
      rw [mdifferentiableAt_section] at hσ
      exact mfderiv_smul hσ hf (X x) }
end trivial_bundle

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']


-- TODO: does it make sense to speak of analytic connections? if so, change the definition of
-- regularity and use ∞ from `open scoped ContDiff` instead.

/-- The trivial connection on the trivial bundle is smooth -/
lemma trivial_isSmooth : ContMDiffCovariantDerivative (𝕜 := 𝕜) (trivial 𝓘(𝕜, E) E E') (⊤ : ℕ∞) where
  contMDiff := by -- {X σ} hX hσ
    sorry /-
    -- except for local trivialisations, contDiff_infty_iff_fderiv covers this well
    simp only [trivial]
    -- use a local trivialisation
    intro x
    specialize hX x
    -- TODO: use contMDiffOn instead, to get something like
    -- have hX' : ContMDiffOn 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (∞ + 1)
    --  (T% σ) (trivializationAt x).baseSet := hX.contMDiffOn
    -- then want a version contMDiffOn_totalSpace
    rw [contMDiffAt_totalSpace] at hX ⊢
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_apply]
    refine ⟨contMDiff_id _, ?_⟩
    obtain ⟨h₁, h₂⟩ := hX
    -- ... hopefully telling me
    -- have h₂scifi : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E') ∞
    --   (fun x ↦ σ x) (trivializationAt _).baseSet_ := sorry
    simp at h₂
    -- now use ContMDiffOn.congr and contDiff_infty_iff_fderiv,
    -- or perhaps a contMDiffOn version of this lemma?
    sorry -/

noncomputable def of_endomorphism (A : E → E →L[𝕜] E' →L[𝕜] E') :
    CovariantDerivative 𝓘(𝕜, E) E' (Trivial E E') where
  toFun X σ := fun x ↦ fderiv 𝕜 σ x (X x) + A x (X x) (σ x)
  isCovariantDerivativeOn := by
    convert IsCovariantDerivativeOn.of_endomorphism (I := 𝓘(𝕜, E)) A
    ext f x v
    rw [mfderiv_eq_fderiv]
end CovariantDerivative
end any_field

section real

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]
  -- `V` vector bundle

namespace IsCovariantDerivativeOn

/-- `cov X σ x` only depends on `X` via `X x` -/
lemma congr_X_at [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [VectorBundle ℝ F V]
    {cov : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {u : Set M} (hcov : IsCovariantDerivativeOn F cov u)
    (X X' : Π x : M, TangentSpace I x) {σ : Π x : M, V x} {x : M} (hx : x ∈ u) (hXX' : X x = X' x) :
    cov X σ x = cov X' σ x := by
  apply tensoriality_criterion' (E := E) (I := I) E (TangentSpace I) F V hXX'
  · intro f X
    rw [hcov.smulX]
  · intro X X'
    rw [hcov.addX]

-- TODO: prove that `cov X σ x` depends on σ only via σ(X) and the 1-jet of σ at x

/-- The difference of two covariant derivatives, as a function `Γ(TM) × Γ(E) → Γ(E)`.
Future lemmas will upgrade this to a map `TM ⊕ E → E`. -/
def differenceAux (cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)) :
    (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x) :=
  fun X σ ↦ cov X σ - cov' X σ

omit [(x : M) → Module ℝ (V x)] [(x : M) → TopologicalSpace (V x)] in
@[simp]
lemma differenceAux_apply
    (cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x))
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    differenceAux cov cov' X σ = cov X σ - cov' X σ := rfl

lemma differenceAux_smul_eq
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {u : Set M} (hcov : IsCovariantDerivativeOn F cov u)
    (hcov' : IsCovariantDerivativeOn F cov' u)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → ℝ)
    {x : M} (hx : x ∈ u := by trivial)
    (hσ : MDiffAt (T% σ) x)
    (hf : MDiffAt f x) :
    differenceAux cov cov' X ((f : M → ℝ) • σ) x = f x • differenceAux cov cov' X σ x:=
  calc _
    _ = cov X ((f : M → ℝ) • σ) x - cov' X ((f : M → ℝ) • σ) x := rfl
    _ = (f x • cov X σ x +  (bar _ <| mfderiv I 𝓘(ℝ) f x (X x)) • σ x)
        - (f x • cov' X σ x +  (bar _ <| mfderiv I 𝓘(ℝ) f x (X x)) • σ x) := by
      simp [hcov.leibniz X hσ hf, hcov'.leibniz X hσ hf]
    _ = f x • cov X σ x - f x • cov' X σ x := by simp
    _ = f x • (cov X σ x - cov' X σ x) := by simp [smul_sub]
    _ = _ := rfl

lemma differenceAux_smul_eq'
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {u : Set M} (hcov : IsCovariantDerivativeOn F cov u)
    (hcov' : IsCovariantDerivativeOn F cov' u)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (f : M → ℝ)
    {x : M} (hx : x ∈ u := by trivial) :
    differenceAux cov cov' (f • X) σ x = f x • differenceAux cov cov' X σ x := by
  simp [differenceAux, hcov.smulX, hcov'.smulX, smul_sub]

/-- The value of `differenceAux cov cov' X σ` at `x₀` depends only on `X x₀` and `σ x₀`. -/
lemma differenceAux_tensorial
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {u : Set M} (hcov : IsCovariantDerivativeOn F cov u)
    (hcov' : IsCovariantDerivativeOn F cov' u)
    [T2Space M] [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {X X' : Π x : M, TangentSpace I x} {σ σ' : Π x : M, V x} {x₀ : M}
    (hσ : MDiffAt (T% σ) x₀)
    (hσ' : MDiffAt (T% σ') x₀)
    (hXX' : X x₀ = X' x₀) (hσσ' : σ x₀ = σ' x₀) (hx : x₀ ∈ u := by trivial) :
    differenceAux cov cov' X σ x₀ = differenceAux cov cov' X' σ' x₀ := by
  trans differenceAux cov cov' X' σ x₀
  · let φ : (Π x : M, TangentSpace I x) → (Π x, V x) := fun X ↦ differenceAux cov cov' X σ
    change φ X x₀ = φ X' x₀
    apply tensoriality_criterion' (E := E) (I := I) E (TangentSpace I) F V hXX'
    · intro f X
      apply hcov.differenceAux_smul_eq' hcov'
    · intro X X'
      unfold φ differenceAux
      simp only [Pi.sub_apply, hcov.addX, hcov'.addX]
      abel
  · let φ : (Π x : M, V x) → (Π x, V x) := fun σ ↦ differenceAux cov cov' X' σ
    change φ σ x₀ = φ σ' x₀
    apply tensoriality_criterion (E := E) (I := I) F V F V hσ hσ' hσσ'
    · intro f σ x hf
      exact hcov.differenceAux_smul_eq hcov' X' σ f hx hf x
    · intro σ σ' hσ hσ'
      unfold φ differenceAux
      simp
      rw [hcov.addσ, hcov'.addσ] <;> try assumption
      abel

lemma isBilinearMap_differenceAux
    [FiniteDimensional ℝ F] [T2Space M] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] {s : Set M} {cov cov'} {x : M}
    (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : IsCovariantDerivativeOn F cov' s) (hx : x ∈ s := by trivial) :
    IsBilinearMap ℝ (fun (X₀ : TangentSpace I x) (σ₀ : V x) ↦
      differenceAux cov cov' (extend I E X₀) (extend I F σ₀) x) where
  add_left u v w := by
    simp only [differenceAux, extend_add, Pi.sub_apply, hcov.addX, hcov'.addX]
    abel
  add_right u v w := by
    have hv := mdifferentiable_extend I F v x
    have hw := mdifferentiable_extend I F w x
    simp only [differenceAux, extend_add, Pi.sub_apply]
    rw [hcov.addσ _ hv hw, hcov'.addσ _ hv hw]
    abel
  smul_left a u v := by
    unfold differenceAux
    simp only [extend_smul, Pi.sub_apply, hcov.smul_const_X, hcov'.smul_const_X]
    module
  smul_right a u v := by
    unfold differenceAux
    simp only [extend_smul, Pi.sub_apply, hcov.smul_const_σ, hcov'.smul_const_σ]
    module

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

/-- The difference of two covariant derivatives, as a tensorial map -/
noncomputable def difference [∀ x, FiniteDimensional ℝ (V x)] [∀ x, T2Space (V x)]
    [FiniteDimensional ℝ F] [T2Space M] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {s : Set M}
    (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : IsCovariantDerivativeOn F cov' s)
    (x : M) : TangentSpace I x →L[ℝ] V x →L[ℝ] V x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := by assumption
  open Classical in
  if hx : x ∈ s then (isBilinearMap_differenceAux (F := F) hcov hcov').toContinuousLinearMap
  else 0

lemma difference_def [∀ x, FiniteDimensional ℝ (V x)] [∀ x, T2Space (V x)]
    [FiniteDimensional ℝ F] [T2Space M] [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {s : Set M} {x : M}
    (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : IsCovariantDerivativeOn F cov' s)
    (hx : x ∈ s := by trivial) (X₀ : TangentSpace I x) (σ₀ : V x) :
    difference hcov hcov' x X₀ σ₀ =
      cov (extend I E X₀) (extend I F σ₀) x - cov' (extend I E X₀) (extend I F σ₀) x := by
  simp only [difference, hx, reduceDIte]
  rfl

@[simp]
lemma difference_apply [∀ x, FiniteDimensional ℝ (V x)] [∀ x, T2Space (V x)]
    [FiniteDimensional ℝ F] [T2Space M] [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, V x) → (Π x : M, V x)}
    {s : Set M} {x : M}
    (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : IsCovariantDerivativeOn F cov' s)
    (hx : x ∈ s := by trivial) (X : Π x, TangentSpace I x) {σ : Π x, V x}
    (hσ : MDiffAt (T% σ) x) :
    difference hcov hcov' x (X x) (σ x) =
      cov X σ x - cov' X σ x := by
  simp only [difference, hx, reduceDIte]
  exact hcov.differenceAux_tensorial hcov' (mdifferentiable_extend ..) hσ (extend_apply_self _)
    (extend_apply_self _) hx

-- The classification of real connections over a trivial bundle
section classification

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [IsManifold I ∞ M]

/-- Classification of covariant derivatives over a trivial vector bundle: every connection
is of the form `D + A`, where `D` is the trivial covariant derivative, and `A` a zeroth-order term
-/
lemma exists_one_form {cov : (Π x : M, TangentSpace I x) → (M → F) → (M → F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s) :
    ∃ (A : (x : M) → TangentSpace I x →L[ℝ] F →L[ℝ] F),
    ∀ X : (x : M) → TangentSpace I x, ∀ σ : M → F, ∀ x ∈ s,
    MDiffAt (T% σ) x →
    letI d : F := mfderiv I 𝓘(ℝ, F) σ x (X x)
    cov X σ x = d + A x (X x) (σ x) := by
  use fun x ↦ hcov.difference (trivial I M F |>.mono <| subset_univ s) x
  intro X σ x hx hσ
  rw [difference_apply]
  · module
  · assumption

noncomputable def one_form {cov : (Π x : M, TangentSpace I x) → (M → F) → (M → F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s) :
    Π x : M, TangentSpace I x →L[ℝ] F →L[ℝ] F :=
  hcov.exists_one_form.choose

lemma eq_one_form {cov : (Π x : M, TangentSpace I x) → (M → F) → (M → F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    {X : (x : M) → TangentSpace I x} {σ : M → F}
    {x : M} (hσ : MDiffAt (T% σ) x) (hx : x ∈ s := by trivial) :
    letI d : F := mfderiv I 𝓘(ℝ, F) σ x (X x)
    cov X σ x = d + hcov.one_form x (X x) (σ x) :=
  hcov.exists_one_form.choose_spec X σ x hx hσ

lemma _root_.CovariantDerivative.exists_one_form
    (cov : CovariantDerivative I F (Bundle.Trivial M F)) :
    ∃ (A : (x : M) → TangentSpace I x →L[ℝ] F →L[ℝ] F),
    ∀ X : (x : M) → TangentSpace I x, ∀ σ : M → F, ∀ x,
    MDiffAt (T% σ) x →
    letI d : F := mfderiv I 𝓘(ℝ, F) σ x (X x)
    cov X σ x = d + A x (X x) (σ x) := by
  simpa using cov.isCovariantDerivativeOn.exists_one_form

end classification

section projection_trivial_bundle

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space M] [IsManifold I ∞ M]

local notation "TM" => TangentSpace I

instance (f : F) : CoeOut (TangentSpace 𝓘(ℝ, F) f) F :=
  ⟨fun x ↦ x⟩

variable {cov : (Π x : M, TangentSpace I x) → (M → F) → (M → F)} {s : Set M}

noncomputable
def projection (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) : (TM x) × F →L[ℝ] F :=
  .snd ℝ (TM x) F + (evalL ℝ F F f ∘L hcov.one_form x ∘L .fst ℝ (TM x) F)

@[simp]
lemma projection_apply (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) (v : TM x) (w : F) :
  hcov.projection x f (v, w) = w + hcov.one_form x v f := rfl

lemma cov_eq_proj (hcov : IsCovariantDerivativeOn F cov s) (X : Π x : M, TM x) (σ : M → F)
    {x : M} (hσ : MDiffAt (T% σ) x) (hx : x ∈ s := by trivial) :
    cov X σ x = hcov.projection x (σ x) (X x, mfderiv I 𝓘(ℝ, F) σ x (X x)) := by
  simpa using hcov.eq_one_form hσ

noncomputable def horiz (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) :
    Submodule ℝ (TM x × F) :=
  LinearMap.ker (hcov.projection x f)

lemma horiz_vert_direct_sum (hcov : IsCovariantDerivativeOn F cov s) (x : M) (f : F) :
    IsCompl (hcov.horiz x f) (.prod ⊥ ⊤) := by
  refine IsCompl.of_eq ?_ ?_
  · refine (Submodule.eq_bot_iff _).mpr ?_
    rintro ⟨u, w⟩ ⟨huw, hu, hw⟩
    simp_all [horiz]
  · apply Submodule.sup_eq_top_iff _ _ |>.2
    intro u
    use u - (0, hcov.projection x f u), ?_, (0, hcov.projection x f u), ?_, ?_
    all_goals simp [horiz]

lemma mem_horiz_iff_exists (hcov : IsCovariantDerivativeOn F cov s) {x : M} {f : F}
    {u : TM x} {v : F} (hx : x ∈ s := by trivial) : (u, v) ∈ hcov.horiz x f ↔
    ∃ σ : M → F, MDiffAt (T% σ) x ∧
                 σ x = f ∧
                 mfderiv I 𝓘(ℝ, F) σ x u = v ∧
                 cov (extend I E u) σ x = 0 := by
  constructor
  · intro huv
    simp [horiz] at huv
    let w : TangentSpace 𝓘(ℝ, F) f := v
    rcases map_of_one_jet_spec u w with ⟨h, h', h''⟩
    use map_of_one_jet u w, ?_, h, h''
    · rw [hcov.eq_one_form]
      · simp [w, h'', h, huv]
      · rwa [mdifferentiableAt_section]
    · rwa [mdifferentiableAt_section]
  · rintro ⟨σ, σ_diff, rfl, rfl, covσ⟩
    simp [horiz, ← covσ]
    rw [hcov.eq_one_form σ_diff, extend_apply_self]

end projection_trivial_bundle

end IsCovariantDerivativeOn

section from_trivialization

variable (e : Trivialization F (π F V)) [MemTrivializationAtlas e]

noncomputable
def Trivialization.covDeriv (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x)
    (x : M) : V x := e.symm x (mfderiv I 𝓘(ℝ, F) (fun x' ↦ (e (σ x')).2) x (X x))

lemma Trivialization.covDeriv_isCovariantDerivativeOn :
    IsCovariantDerivativeOn (I := I) F e.covDeriv e.baseSet where
  addX X X' σ x hx := by sorry
  smulX X σ c' x hx := by sorry
  addσ X σ σ' x hσ hσ' hx := by sorry
  smul_const_σ X σ a x hx := by sorry
  leibniz X σ f x hσ hf hx := by sorry

end from_trivialization


section horiz
namespace CovariantDerivative

def proj (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    TangentSpace (I.prod 𝓘(ℝ, F)) v →L[ℝ] V v.proj := by
  sorry

noncomputable def horiz (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    Submodule ℝ (TangentSpace (I.prod 𝓘(ℝ, F)) v) :=
  LinearMap.ker (cov.proj v)

noncomputable def _root_.Bundle.vert (v : TotalSpace F V) :
    Submodule ℝ (TangentSpace (I.prod 𝓘(ℝ, F)) v) :=
  LinearMap.ker (mfderiv (I.prod 𝓘(ℝ, F)) I Bundle.TotalSpace.proj v)

lemma horiz_vert_direct_sum (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    IsCompl (cov.horiz v) (vert v) := by
  sorry

variable [IsManifold I 1 M]
variable {cov : CovariantDerivative I F V}

lemma proj_mderiv {X : Π x : M, TangentSpace I x} {σ : Π x : M, V x} (x : M)
    (hX : MDiffAt (T% X) x)
    (hσ : MDiffAt (T% σ) x) :
    cov X σ x = cov.proj (σ x)
      (mfderiv I (I.prod 𝓘(ℝ, F)) (T% σ) x (X x)) := by
  sorry

end CovariantDerivative
end horiz

section torsion
namespace CovariantDerivative

variable [h : IsManifold I ∞ M]

-- The torsion tensor of a covariant derivative on the tangent bundle `TM`.
variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

variable (cov) in
noncomputable def torsion :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) :=
  fun X Y ↦ cov X Y - cov Y X - VectorField.mlieBracket I X Y

variable {X X' Y : Π x : M, TangentSpace I x}

variable (X) in
lemma torsion_self : torsion cov X X = 0 := by
  simp [torsion]

variable (X Y) in
lemma torsion_antisymm : torsion cov X Y = - torsion cov Y X := by
  simp only [torsion]
  rw [VectorField.mlieBracket_swap]
  module

variable (X) in
@[simp]
lemma torsion_zero : torsion cov 0 X = 0 := by
  ext x
  simp [torsion]

variable (X) in
@[simp]
lemma torsion_zero' : torsion cov X 0 = 0 := by rw [torsion_antisymm, torsion_zero]; simp

set_option linter.style.commandStart false -- new delaborators confuse the pretty-printer

variable (Y) in
lemma torsion_add_left_apply [CompleteSpace E] {x : M}
    (hX : MDiffAt (T% X) x)
    (hX' : MDiffAt (T% X') x) :
    torsion cov (X + X') Y x = torsion cov X Y x + torsion cov X' Y x := by
  simp [torsion, cov.isCovariantDerivativeOn.addX X X' (x := x)]
  rw [cov.isCovariantDerivativeOn.addσ Y hX hX', VectorField.mlieBracket_add_left hX hX']
  module

variable (Y) in
lemma torsion_add_left [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) :
    torsion cov (X + X') Y = torsion cov X Y + torsion cov X' Y := by
  ext x
  exact cov.torsion_add_left_apply _ (hX x) (hX' x)

lemma torsion_add_right_apply [CompleteSpace E] {x : M}
    (hX : MDiffAt (T% X) x)
    (hX' : MDiffAt (T% X') x) :
    torsion cov Y (X + X') x = torsion cov Y X x + torsion cov Y X' x := by
  rw [torsion_antisymm, Pi.neg_apply,
    cov.torsion_add_left_apply _ hX hX', torsion_antisymm Y, torsion_antisymm Y]
  simp; abel

lemma torsion_add_right [CompleteSpace E]
    (hX : MDiff (T% X)) (hX' : MDiff (T% X')) :
    torsion cov Y (X + X') = torsion cov Y X + torsion cov Y X' := by
  rw [torsion_antisymm, torsion_add_left _ hX hX', torsion_antisymm X, torsion_antisymm X']; module

variable (Y) in
lemma torsion_smul_left_apply [CompleteSpace E] {f : M → ℝ} {x : M} (hf : MDiffAt f x)
    (hX : MDiffAt (T% X) x) :
    torsion cov (f • X) Y x = f x • torsion cov X Y x := by
  simp only [torsion, cov.isCovariantDerivativeOn.smulX X Y f, Pi.sub_apply]
  rw [cov.isCovariantDerivativeOn.leibniz Y hX hf, VectorField.mlieBracket_smul_left hf hX]
  simp [bar, smul_sub]
  abel

variable (Y) in
lemma torsion_smul_left [CompleteSpace E] {f : M → ℝ} (hf : MDiff f) (hX : MDiff (T% X)) :
    torsion cov (f • X) Y = f • torsion cov X Y := by
  ext x
  exact cov.torsion_smul_left_apply _ (hf x) (hX x)

variable (X) in
lemma torsion_smul_right_apply [CompleteSpace E] {f : M → ℝ} {x : M} (hf : MDiffAt f x)
    (hX : MDiffAt (T% Y) x) :
    torsion cov X (f • Y) x = f x • torsion cov X Y x := by
  rw [torsion_antisymm, Pi.neg_apply, torsion_smul_left_apply X hf hX, torsion_antisymm X]
  simp

variable (X) in
lemma torsion_smul_right [CompleteSpace E] {f : M → ℝ} (hf : MDiff f) (hY : MDiff (T% Y)) :
    torsion cov X (f • Y) = f • torsion cov X Y := by
  ext x
  apply cov.torsion_smul_right_apply _ (hf x) (hY x)

/-- The torsion of a covariant derivative is tensorial:
the value of `torsion cov X Y` at `x₀` depends only on `X x₀` and `Y x₀`. -/
def torsion_tensorial [T2Space M] [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
    {X X' Y Y' : Π x : M, TangentSpace I x} {x₀ : M}
    (hX : MDiffAt (T% X) x₀) (hX' : MDiffAt (T% X') x₀)
    (hY : MDiffAt (T% Y) x₀) (hY' : MDiffAt (T% Y') x₀)
    (hXX' : X x₀ = X' x₀) (hYY' : Y x₀ = Y' x₀) :
    (torsion cov X Y) x₀ = (torsion cov X' Y') x₀ := by
  apply tensoriality_criterion₂ I E (TangentSpace I) E (TangentSpace I) hX hX' hY hY' hXX' hYY'
  · intro f σ τ hf hσ
    exact cov.torsion_smul_left_apply _ hf hσ
  · intro σ σ' τ hσ hσ'
    exact cov.torsion_add_left_apply _ hσ hσ'
  · intros f σ σ' hf hσ'
    exact cov.torsion_smul_right_apply _ hf hσ'
  · intro σ τ τ' hτ hτ'
    exact cov.torsion_add_right_apply hτ hτ'

set_option linter.style.commandStart true

variable (cov) in
/-- A covariant derivation is called **torsion-free** iff its torsion tensor vanishes. -/
def IsTorsionFree : Prop := torsion cov = 0

lemma isTorsionFree_def : IsTorsionFree cov ↔ torsion cov = 0 := by simp [IsTorsionFree]

-- This should be obvious, I'm doing something wrong.
lemma isTorsionFree_iff : IsTorsionFree cov ↔
    ∀ X Y, cov X Y - cov Y X = VectorField.mlieBracket I X Y := by
  simp [IsTorsionFree]
  constructor
  · intro h X Y
    have : torsion cov X Y = 0 := by simp [h]
    -- XXX: abel, ring, module and grind all fail here
    exact eq_of_sub_eq_zero this
  · intro h
    ext X Y x
    specialize h X Y
    apply congr_fun
    simp_all [torsion]

-- lemma the trivial connection on a normed space is torsion-free
-- lemma trivial.isTorsionFree : IsTorsionFree (TangentBundle 𝓘(ℝ, E) E) := sorry

-- lemma: tangent bundle of E is trivial -> there exists a single trivialisation with baseSet univ
-- make a new abbrev Bundle.Trivial.globalFrame --- which is localFrame for the std basis of F,
--    w.r.t. to this trivialisation
-- add lemmas: globalFrame is contMDiff globally

-- proof of above lemma: write sections s and t in the global frame above
-- by linearity (proven above), suffices to consider s = s^i and t = s^j (two sections in the frame)
-- compute: their Lie bracket is zero
-- compute: the other two terms cancel, done

end CovariantDerivative
end torsion

end real


/- the following lemmas are subsubmed by tensoriality_criterion
  XXX should they be extracted as separate lemmas (stated twice)?
omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
/-- If `X` and `X'` agree in a neighbourhood of `p`, then `∇_X σ` and `∇_X' σ` agree at `p`. -/
lemma congr_X_of_eventuallyEq (cov : CovariantDerivative I F V) [T2Space M]
    {X X' : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {x : M} {s : Set M} (hs : s ∈ nhds x)
    (hσσ' : ∀ x ∈ s, X x = X' x) :
    cov X σ x = cov X' σ x := by
  -- Choose a smooth bump function ψ with support around `x` contained in `s`
  obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hs).mem_iff.1 hs
  -- Observe that `ψ • X = ψ • X'` as dependent functions.
  have (x : M) : ((ψ : M → ℝ) • X) x = ((ψ : M → ℝ) • X') x := by
    by_cases h : x ∈ s
    · simp [hσσ' x h]
    · simp [notMem_support.mp fun a ↦ h (hψ a)]
  -- Then, it's a chain of (dependent) equalities.
  calc cov X σ x
    _ = cov ((ψ : M → ℝ) • X) σ x := by simp [cov.smulX]
    _ = cov ((ψ : M → ℝ) • X') σ x := by rw [funext this]
    _ = cov X' σ x := by simp [cov.smulX]

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
lemma congr_X_at_aux (cov : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x} {x : M}
    (hX : X x = 0) : cov X σ x = 0 := by
  -- Consider the local frame {Xⁱ} on TangentSpace I x induced by chartAt H x.
  -- To do so, choose a basis of TangentSpace I x = E.
  let n : ℕ := Module.finrank ℝ E
  let b : Basis (Fin n) ℝ E := Module.finBasis ℝ E
  let e := trivializationAt E (TangentSpace I) x
  let Xi (i : Fin n) := b.localFrame e i
  -- Write X in coordinates: X = ∑ i, a i • Xi i near `x`.
  let a := fun i ↦ b.localFrame_repr e i X
  have : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have aux : ∀ᶠ (x' : M) in 𝓝 x, X x' = ∑ i, a i x' • Xi i x' := b.localFrame_repr_spec this X
  have (i : Fin n) : a i x = 0 := b.localFrame_repr_apply_zero_at hX i
  calc cov X σ x
    _ = cov (∑ i, a i • Xi i) σ x := cov.congr_X_of_eventuallyEq aux (by simp)
    _ = ∑ i, cov (a i • Xi i) σ x := by rw [cov.sum_X]; simp
    _ = ∑ i, a i x • cov (Xi i) σ x := by
      congr; ext i; simp [cov.smulX (Xi i) σ (a i)]
    _ = 0 := by simp [this] -/

/- TODO: are these lemmas still useful after the general tensoriality lemma?
are they worth extracting separately?
omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
lemma congr_σ_smoothBumpFunction (cov : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x}
    (hσ : MDiffAt (T% σ) x)
    (f : SmoothBumpFunction I x) :
    cov X ((f : M → ℝ) • σ) x = cov X σ x := by
  rw [cov.leibniz _ _ _ _ hσ]
  swap; · apply f.contMDiff.mdifferentiable (by norm_num)
  calc _
    _ = cov X σ x + 0 := ?_
    _ = cov X σ x := by rw [add_zero]
  simp [f.eq_one, f.eventuallyEq_one.mfderiv_eq]
  rw [show mfderiv I 𝓘(ℝ, ℝ) 1 x = 0 by apply mfderiv_const]
  left
  rfl

omit [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul ℝ (V x)]
  [VectorBundle ℝ F V] in
lemma congr_σ_of_eventuallyEq
    (cov : CovariantDerivative I F V) [T2Space M] [IsManifold I ∞ M]
    (X : Π x : M, TangentSpace I x) {σ σ' : Π x : M, V x} {x : M} {s : Set M} (hs : s ∈ nhds x)
    (hσ : MDiffAt (T% σ) x)
    (hσσ' : ∀ x ∈ s, σ x = σ' x) :
    cov X σ x = cov X σ' x := by
  -- Choose a smooth bump function ψ with support around `x` contained in `s`
  obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hs).mem_iff.1 hs
  -- Observe that `ψ • σ = ψ • σ'` as dependent functions.
  have (x : M) : ((ψ : M → ℝ) • σ) x = ((ψ : M → ℝ) • σ') x := by
    by_cases h : x ∈ s
    · simp [hσσ' x h]
    · simp [notMem_support.mp fun a ↦ h (hψ a)]
  -- Then, it's a chain of (dependent) equalities.
  calc cov X σ x
    _ = cov X ((ψ : M → ℝ) • σ) x := by rw [cov.congr_σ_smoothBumpFunction _ hσ]
    _ = cov X ((ψ : M → ℝ) • σ') x := sorry -- use simp [funext hσ] and (by simp [this])
    _ = cov X σ' x := by
      simp [cov.congr_σ_smoothBumpFunction, mdifferentiableAt_dependent_congr hs hσ hσσ']
-/

-- variable (E E') in
-- /-- The trivial connection on a trivial bundle, given by the directional derivative -/
-- @[simps]
-- noncomputable def trivial : CovariantDerivative 𝓘(𝕜, E) E'
--   (Bundle.Trivial E E') where
--   toFun X s := fun x ↦ fderiv 𝕜 s x (X x)
--   isCovariantDerivativeOn :=
--   { addX X X' σ x _ := by simp
--     smulX X σ c' x _ := by simp
--     addσ X σ σ' x hσ hσ' hx := by
--       rw [Bundle.Trivial.mdifferentiableAt_iff] at hσ hσ'
--       rw [fderiv_add hσ hσ']
--       rfl
--     smul_const_σ X σ a x hx := by simp [fderiv_const_smul_of_field a]
--     leibniz X σ f x hσ hf hx := by
--       have : fderiv 𝕜 (f • σ) x = f x • fderiv 𝕜 σ x + (fderiv 𝕜 f x).smulRight (σ x) :=
--         fderiv_smul (by simp_all) (by simp_all)
--       simp [this, bar]
--       rfl }
