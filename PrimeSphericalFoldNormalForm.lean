import PrimeSphericalFoldSmooth

namespace PrimeSphericalFold
noncomputable section
open scoped ContDiff Topology Manifold
open Set ChartedSpace

def cylinderObservation (p : Cylinder) : ℝ × ℝ :=
  circleObservation (cylinderToPhase p)

theorem cylinder_global_fold_equation (p : Cylinder) :
    cylinderObservation p = standardFold (globalDiffeomorph p).1 :=
  global_fold_equation (cylinderToPhase p)

def translationDiffeomorph (a : ℝ × ℝ) : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) where
  toEquiv := Equiv.subRight a
  contMDiff_toFun := (contDiff_id.sub contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff

def shiftedPlaneOpen (a : ℝ × ℝ) : TopologicalSpace.Opens (ℝ × ℝ) :=
  ⟨{q | q + a ≠ (0, 0)},
    isClosed_singleton.isOpen_compl.preimage (continuous_id.add continuous_const)⟩

def shiftedPlaneDiffeomorph (a : ℝ × ℝ) :
    SmoothPlane ≃ₘ⟮𝓘(ℝ, ℝ × ℝ), 𝓘(ℝ, ℝ × ℝ)⟯ shiftedPlaneOpen a where
  toEquiv := {
    toFun := fun q => ⟨q.1 - a, by
      change (q.1 - a) + a ≠ (0, 0)
      rw [sub_add_cancel]
      exact q.2⟩
    invFun := fun q => ⟨q.1 + a, q.2⟩
    left_inv := fun q => Subtype.ext (sub_add_cancel q.1 a)
    right_inv := fun q => Subtype.ext (add_sub_cancel_right q.1 a) }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (shiftedPlaneOpen a) _).mp
    exact contMDiff_subtype_val.sub contMDiff_const
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff puncturedOpen _).mp
    exact contMDiff_subtype_val.add contMDiff_const

/-- Smooth centered source and target coordinates with the actual square normal form.
The source chart covers the whole cylinder and has an open planar image. -/
def HasWhitneyFoldAt (f : Cylinder → ℝ × ℝ) (p : Cylinder) : Prop :=
  ∃ U : TopologicalSpace.Opens (ℝ × ℝ),
    ∃ source : Cylinder ≃ₘ⟮cylinderModel, 𝓘(ℝ, ℝ × ℝ)⟯ U,
      ∃ target : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
        (source p).1 = 0 ∧ target (f p) = 0 ∧
          ∀ q, target (f q) = standardFold (source q).1

theorem cylinder_whitney_fold (p : Cylinder) (hs : (p.2 : ℂ).im = 0) :
    HasWhitneyFoldAt cylinderObservation p := by
  let a : ℝ × ℝ := ((globalDiffeomorph p).1.1, 0)
  let source := globalDiffeomorph.trans (shiftedPlaneDiffeomorph a)
  refine ⟨shiftedPlaneOpen a, source, translationDiffeomorph a, ?_, ?_, ?_⟩
  · change (globalDiffeomorph p).1 - a = 0
    apply Prod.ext
    · simp [a]
    · change Real.sqrt p.1.1 * (p.2 : ℂ).im - 0 = 0
      rw [hs]; ring
  · change cylinderObservation p - a = 0
    rw [cylinder_global_fold_equation]
    apply Prod.ext
    · simp [a, standardFold]
    · change (Real.sqrt p.1.1 * (p.2 : ℂ).im) ^ 2 - 0 = 0
      rw [hs]; ring
  · intro q
    change cylinderObservation q - a = standardFold ((globalDiffeomorph q).1 - a)
    rw [cylinder_global_fold_equation]
    apply Prod.ext <;> simp [standardFold, a]

theorem cylinder_observation_smooth :
    ContMDiff cylinderModel 𝓘(ℝ, ℝ × ℝ) ∞ cylinderObservation := by
  apply (contMDiff_prod_module_iff _).mpr
  exact ⟨cylinder_radius_smooth.mul cylinder_c_smooth,
    cylinder_radius_smooth.mul (cylinder_s_smooth.pow 2)⟩

def positiveDiagonal (t : PositiveRadius) : ℝ × ℝ × ℝ := diagonalCurve t.1

theorem diagonalCurve_smooth : ContDiff ℝ ∞ diagonalCurve := by
  unfold diagonalCurve G
  fun_prop

theorem positiveDiagonal_smooth :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞ positiveDiagonal :=
  diagonalCurve_smooth.contMDiff.comp contMDiff_subtype_val

def radiusFunction (v : ℝ × ℝ × ℝ) : ℝ := Real.sqrt (normSq3 v)

theorem radiusFunction_continuous : Continuous radiusFunction := by
  unfold radiusFunction normSq3
  fun_prop

theorem positiveDiagonal_radius (t : PositiveRadius) : radiusFunction (positiveDiagonal t) = t.1 := by
  change Real.sqrt (normSq3 (G t.1 t.1)) = t.1
  rw [radius_squared, Real.sqrt_sq (le_of_lt t.2)]

theorem positiveDiagonal_embedding : Topology.IsEmbedding positiveDiagonal := by
  apply Topology.IsEmbedding.of_comp positiveDiagonal_smooth.continuous radiusFunction_continuous
  have h : radiusFunction ∘ positiveDiagonal = (Subtype.val : PositiveRadius → ℝ) :=
    funext positiveDiagonal_radius
  rw [h]
  exact Topology.IsEmbedding.subtypeVal

/-- A smooth embedded positive curve with nonzero actual velocity at every point. -/
theorem positiveDiagonal_smoothEmbedding :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞ positiveDiagonal ∧
      Topology.IsEmbedding positiveDiagonal ∧
        ∀ t : PositiveRadius, deriv diagonalCurve t.1 ≠ 0 :=
  ⟨positiveDiagonal_smooth, positiveDiagonal_embedding,
    fun t => diagonalCurve_immersion t.1 t.2⟩

end
end PrimeSphericalFold
