/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.IsImmersionEmbedding

/-! # Smooth submersions

to be written

**Please do not work** on this file without prior discussion with Michael Rothgang.
This will be the topic of Samantha Naranjo's master's thesis, and it's nice to coordinate.

-/

open scoped Manifold Topology ContDiff

open Function Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞}

-- XXX: should the next three definitions be a class instead?
-- Are these slice charts canonical enough that we want the typeclass system to kick in?

variable (I I') in
/-- The local property of being a submersion at `x` -/
def SubmersionAtProp (equiv : E ≃L[𝕜] (E' × F)) :
    ((M → M') → PartialHomeomorph M H → PartialHomeomorph M' H' → Prop) :=
  fun f domChart codChart ↦
    EqOn ((codChart.extend I') ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace H' M'] in
/-- Being a submersion at `x` is a "nice" local property. -/
lemma SubmersionAtPropIsNice (f : M → M') (x) (equiv : E ≃L[𝕜] (E' × F)) :
    LocalSourceTargetPropertyAt f x (SubmersionAtProp I I' equiv) where
  mono_source f φ ψ s hf := by
    have {a b c : Set E} : a ∩ (b ∩ c) ⊆ b := by intro; aesop
    exact hf.mono (by simpa using this)
  congr f g φ ψ s hs hfg hf := by
    apply EqOn.trans ?_ (hf.mono (by simp))
    intro x hx
    set Φ := (φ.restr s).extend I
    have aux : Φ.source ⊆ s := by
      simpa only [Φ, PartialHomeomorph.extend_source, PartialHomeomorph.restr_source,
        interior_eq_iff_isOpen.mpr hs] using inter_subset_right
    have : (f ∘ Φ.symm) x = (g ∘ Φ.symm) x := hfg <| aux (PartialEquiv.map_target _ hx)
    rw [Function.comp_apply, ← this]
    simp [Φ]

variable (F I I' n) in
/-- `f : M → N` is a `C^k` submersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u, v) ↦ u`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlasses used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.
-/
def IsSubmersionAt (f : M → M') (x : M) : Prop :=
  ∃(equiv : E ≃L[𝕜] (E' × F)),
  LiftSourceTargetPropertyAt I I' n f x (SubmersionAtProp I I' equiv)

namespace IsSubmersionAt

-- TODO: add all the standard lemmas

end IsSubmersionAt

variable (F I I' n) in
/-- `f : M → N` is a `C^k` submersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `(u, v) ↦ u`.

In other words, `f` is a submersion at each `x ∈ M`.
-/
def IsSubmersion (f : M → M') : Prop := ∀ x, IsSubmersionAt F I I' n f x

namespace IsSubmersion

variable {f g : M → M'}

/-- If `f` is a submersion, it is a submersion at each point. -/
lemma isSubmersionAt (h : IsSubmersion F I I' n f) (x : M) : IsSubmersionAt F I I' n f x := h x

/-- If `f = g` and `f` is a submersion, so is `g`. -/
theorem congr (h : IsSubmersion F I I' n f) (heq : f = g) : IsSubmersion F I I' n g :=
  heq ▸ h

-- TODO: add more API in the future!

end IsSubmersion
