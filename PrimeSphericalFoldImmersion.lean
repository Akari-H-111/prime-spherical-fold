import PrimeSphericalFoldSmooth
import PrimeSphericalFoldGeometry
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

namespace PrimeSphericalFold
noncomputable section
open scoped ContDiff Topology Manifold
open Set ChartedSpace

def coordinateReciprocal (q : ℝ × ℝ) : ℝ :=
  (Real.sqrt (inverseRadius q.1 q.2))⁻¹

theorem coordinateReciprocal_smoothAt (q : PuncturedPlane) :
    ContDiffAt ℝ ∞ coordinateReciprocal q.1 := by
  exact ((inverseRadius_contDiffAt q).sqrt (ne_of_gt (inverseRadius_pos q))).inv
    (ne_of_gt (Real.sqrt_pos.2 (inverseRadius_pos q)))

def coordinateSurface (q : ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (q.2 * q.1 * coordinateReciprocal q, q.2 ^ 2, q.1)

def coordinateSurfaceDerivative (q : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ) :=
  (rowCLM (q.2 * coordinateReciprocal q) (q.1 * coordinateReciprocal q) +
      (q.2 * q.1) • fderiv ℝ coordinateReciprocal q).prod
    ((rowCLM 0 (2 * q.2)).prod (rowCLM 1 0))

theorem coordinateSurface_hasFDerivAt (q : PuncturedPlane) :
    HasFDerivAt coordinateSurface (coordinateSurfaceDerivative q.1) q.1 := by
  have hx := hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := q.1)
  have hy := hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := q.1)
  have hi := (coordinateReciprocal_smoothAt q).differentiableAt (by simp)
  have h := ((hy.mul hx).mul hi.hasFDerivAt).prodMk ((hy.pow 2).prodMk hx)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · simp [coordinateSurfaceDerivative, rowCLM_apply]
    ring
  · apply Prod.ext
    · simp [coordinateSurfaceDerivative, rowCLM_apply]
    · simp [coordinateSurfaceDerivative, rowCLM_apply]

theorem coordinateSurface_smoothAt (q : PuncturedPlane) :
    ContDiffAt ℝ ∞ coordinateSurface q.1 := by
  exact (((contDiffAt_snd.mul contDiffAt_fst).mul
    (coordinateReciprocal_smoothAt q)).prodMk
      ((contDiffAt_snd.pow 2).prodMk contDiffAt_fst))

theorem coordinateSurface_derivative_injective (q : PuncturedPlane) :
    Function.Injective (fderiv ℝ coordinateSurface q.1) := by
  rw [(coordinateSurface_hasFDerivAt q).fderiv]
  suffices hk : ∀ v, coordinateSurfaceDerivative q.1 v = 0 → v = 0 by
    intro v w h
    exact sub_eq_zero.mp (hk (v - w) (by rw [map_sub, h, sub_self]))
  intro v h
  have hz := congrArg (fun z : ℝ × ℝ × ℝ => z.2.2) h
  have hy := congrArg (fun z : ℝ × ℝ × ℝ => z.2.1) h
  have hx := congrArg (fun z : ℝ × ℝ × ℝ => z.1) h
  simp only [coordinateSurfaceDerivative, ContinuousLinearMap.prod_apply,
    add_apply, smul_apply,
    rowCLM_apply, smul_eq_mul, Prod.fst_zero, Prod.snd_zero] at hz hy hx
  have hv1 : v.1 = 0 := by simpa using hz
  have hv2 : v.2 = 0 := by
    by_cases he : q.1.2 = 0
    · have hxi : q.1.1 ≠ 0 := by
        intro hxi
        exact q.2 (Prod.ext hxi he)
      have hi : coordinateReciprocal q.1 ≠ 0 :=
        inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (inverseRadius_pos q)))
      simp only [he, zero_mul, zero_add, add_zero] at hx
      exact (mul_eq_zero.mp hx).resolve_left (mul_ne_zero hxi hi)
    · have hcoef : 2 * q.1.2 ≠ 0 := mul_ne_zero (by norm_num) he
      have : (2 * q.1.2) * v.2 = 0 := by simpa using hy
      exact (mul_eq_zero.mp this).resolve_left hcoef
  exact Prod.ext hv1 hv2

def cylinderSurface (p : Cylinder) : ℝ × ℝ × ℝ := phaseSurface (cylinderToPhase p)

theorem cylinderSurface_smooth :
    ContMDiff cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) ∞ cylinderSurface := by
  apply (contMDiff_prod_module_iff _).mpr
  refine ⟨(cylinder_radius_smooth.mul cylinder_s_smooth).mul cylinder_c_smooth, ?_⟩
  apply (contMDiff_prod_module_iff _).mpr
  exact ⟨cylinder_radius_smooth.mul (cylinder_s_smooth.pow 2),
    cylinder_radius_smooth.mul cylinder_c_smooth⟩

theorem coordinateSurface_fromPlane (q : PuncturedPlane) :
    coordinateSurface q.1 = phaseSurface (fromPlane q) := by
  have hr := inverseRadius_pos q
  have hsq := Real.sq_sqrt (le_of_lt hr)
  have hrne := ne_of_gt hr
  have hsne := ne_of_gt (Real.sqrt_pos.2 hr)
  apply Prod.ext
  · dsimp [coordinateSurface, coordinateReciprocal, phaseSurface, fromPlane]
    field_simp
  · apply Prod.ext
    · dsimp [coordinateSurface, phaseSurface, fromPlane]
      rw [div_pow, hsq]
      field_simp
    · dsimp [coordinateSurface, phaseSurface, fromPlane]
      field_simp

theorem cylinderSurface_coordinate_formula (p : Cylinder) :
    cylinderSurface p = coordinateSurface (globalDiffeomorph p).1 := by
  rw [coordinateSurface_fromPlane (globalDiffeomorph p)]
  exact congrArg phaseSurface (globalCoordinateEquiv.symm_apply_apply (cylinderToPhase p)).symm

theorem plane_coe_mfderiv (q : SmoothPlane) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (Subtype.val : SmoothPlane → ℝ × ℝ) q =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := mfderiv_extChartAt_self

def cylinderCoordinate (p : Cylinder) : ℝ × ℝ := (globalDiffeomorph p).1

theorem cylinderCoordinate_smooth :
    ContMDiff cylinderModel 𝓘(ℝ, ℝ × ℝ) ∞ cylinderCoordinate :=
  contMDiff_subtype_val.comp globalDiffeomorph.contMDiff

set_option backward.isDefEq.respectTransparency false in
theorem cylinderCoordinate_mfderiv (p : Cylinder) :
    mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ) cylinderCoordinate p =
      mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ) globalDiffeomorph p := by
  change mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ) (Subtype.val ∘ globalDiffeomorph) p = _
  rw [mfderiv_comp p ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
    (globalDiffeomorph.contMDiff.mdifferentiableAt (by simp)), plane_coe_mfderiv]
  apply ContinuousLinearMap.ext
  intro v
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem cylinderCoordinate_derivative_bijective (p : Cylinder) :
    Function.Bijective (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ) cylinderCoordinate p) := by
  let he := globalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) p
  rw [cylinderCoordinate_mfderiv]
  exact he.bijective

theorem cylinderSurface_mfderiv_formula (p : Cylinder) :
    mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) cylinderSurface p =
      (coordinateSurfaceDerivative (cylinderCoordinate p)).comp
        (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ) cylinderCoordinate p) := by
  have heq : cylinderSurface = coordinateSurface ∘ cylinderCoordinate :=
    funext cylinderSurface_coordinate_formula
  rw [heq, mfderiv_comp p
    ((coordinateSurface_smoothAt (globalDiffeomorph p)).contMDiffAt.mdifferentiableAt (by simp))
    (cylinderCoordinate_smooth.mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
  apply ContinuousLinearMap.ext
  intro v
  change fderiv ℝ coordinateSurface (cylinderCoordinate p)
      (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ) cylinderCoordinate p v) =
    coordinateSurfaceDerivative (cylinderCoordinate p)
      (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ) cylinderCoordinate p v)
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ) =>
    L (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ) cylinderCoordinate p v))
      (coordinateSurface_hasFDerivAt (globalDiffeomorph p)).fderiv

/-- Immersion on the intrinsic standard cylinder, using the actual manifold derivative. -/
theorem cylinderSurface_immersion (p : Cylinder) :
    Function.Injective (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) cylinderSurface p) := by
  have heq : cylinderSurface = coordinateSurface ∘ cylinderCoordinate :=
    funext cylinderSurface_coordinate_formula
  rw [heq, mfderiv_comp p
    ((coordinateSurface_smoothAt (globalDiffeomorph p)).contMDiffAt.mdifferentiableAt (by simp))
    (cylinderCoordinate_smooth.mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
  exact (coordinateSurface_derivative_injective (globalDiffeomorph p)).comp
    (cylinderCoordinate_derivative_bijective p).injective

def coordinateTangent (p : Cylinder) (v : ℝ × ℝ) : TangentSpace cylinderModel p :=
  (globalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) p).symm v

set_option backward.isDefEq.respectTransparency false in
theorem coordinateTangent_roundtrip (p : Cylinder) (v : ℝ × ℝ) :
    mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ) cylinderCoordinate p (coordinateTangent p v) = v := by
  rw [cylinderCoordinate_mfderiv]
  exact (globalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) p).apply_symm_apply v

theorem cylinderSurface_coordinateTangent (p : Cylinder) (v : ℝ × ℝ) :
    mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) cylinderSurface p (coordinateTangent p v) =
      coordinateSurfaceDerivative (cylinderCoordinate p) v := by
  rw [cylinderSurface_mfderiv_formula]
  change coordinateSurfaceDerivative (cylinderCoordinate p)
    (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ) cylinderCoordinate p (coordinateTangent p v)) = _
  rw [coordinateTangent_roundtrip]

theorem double_phase_derivative_first (p : Cylinder) (hc : (p.2 : ℂ).re = 0) :
    mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) cylinderSurface p
      (coordinateTangent p (1, 0)) = ((p.2 : ℂ).im, 0, 1) := by
  rw [cylinderSurface_coordinateTangent]
  have hr : inverseRadius (cylinderCoordinate p).1 (cylinderCoordinate p).2 = p.1.1 :=
    radius_toPlane (cylinderToPhase p)
  have hx : (cylinderCoordinate p).1 = 0 := by
    change p.1.1 * (p.2 : ℂ).re = 0
    rw [hc, mul_zero]
  have hy : (cylinderCoordinate p).2 = Real.sqrt p.1.1 * (p.2 : ℂ).im := rfl
  have hi : coordinateReciprocal (cylinderCoordinate p) = (Real.sqrt p.1.1)⁻¹ := by
    unfold coordinateReciprocal
    rw [hr]
  have hsqrt : Real.sqrt p.1.1 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 p.1.2)
  simp [coordinateSurfaceDerivative, rowCLM_apply, hx, hy, hi]
  field_simp [hsqrt]
  rfl

theorem double_phase_derivative_second (p : Cylinder) (hc : (p.2 : ℂ).re = 0) :
    mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) cylinderSurface p
      (coordinateTangent p (0, 1)) = (0, 2 * (Real.sqrt p.1.1 * (p.2 : ℂ).im), 0) := by
  rw [cylinderSurface_coordinateTangent]
  have hx : (cylinderCoordinate p).1 = 0 := by
    change p.1.1 * (p.2 : ℂ).re = 0
    rw [hc, mul_zero]
  simp [coordinateSurfaceDerivative, rowCLM_apply, hx]
  rfl

end
end PrimeSphericalFold
