import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

open Bundle

section
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [RiemannianBundle V] [IsContMDiffRiemannianBundle I 1 F V]
  [ContMDiffVectorBundle 1 F V I]
  (cov : CovariantDerivative I F V)

/-- info: cov.IsMetricCompatible : Prop -/
#guard_msgs in
#check  cov.IsMetricCompatible
end

section
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

set_option pp.mvars.anonymous false in
/--
error: Application type mismatch: The argument
  cov
has type
  @CovariantDerivative ℝ DenselyNormedField.toNontriviallyNormedField E inst✝⁸ inst✝⁷ H inst✝⁵ I M
    PseudoEMetricSpace.toUniformSpace.toTopologicalSpace inst✝³ E inst✝⁸ inst✝⁷ (TangentSpace I)
    instTopologicalSpaceTangentBundle (instAddCommGroupTangentSpace I) (instModuleTangentSpace I)
    (instTopologicalSpaceTangentSpace I) ⋯ ⋯ TangentSpace.fiberBundle
but is expected to have type
  @CovariantDerivative ℝ DenselyNormedField.toNontriviallyNormedField ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun x ↦ NormedAddCommGroup.toAddCommGroup) (fun x ↦ InnerProductSpace.toNormedSpace.toModule)
    (fun x ↦ PseudoMetricSpace.toUniformSpace.toTopologicalSpace) ⋯ ⋯ ?_
in the application
  @CovariantDerivative.IsMetricCompatible ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ cov
-/
#guard_msgs in
#check cov.IsMetricCompatible --(M := M) (V := TangentSpace I)

end
