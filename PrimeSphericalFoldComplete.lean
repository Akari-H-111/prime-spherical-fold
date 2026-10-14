import PrimeSphericalFoldImmersion
import PrimeSphericalFoldNormalForm

namespace PrimeSphericalFold
noncomputable section
open scoped ContDiff Topology Manifold
open Set ChartedSpace

def standardFoldDerivative (q : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (rowCLM 1 0).prod (rowCLM 0 (2 * q.2))

theorem standardFold_hasFDerivAt (q : ℝ × ℝ) :
    HasFDerivAt standardFold (standardFoldDerivative q) q := by
  have hx := hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := q)
  have hy := hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := q)
  apply (hx.prodMk (hy.pow 2)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [standardFoldDerivative, rowCLM_apply]

theorem standardFold_derivative_injective_iff (q : ℝ × ℝ) :
    Function.Injective (fderiv ℝ standardFold q) ↔ q.2 ≠ 0 := by
  rw [(standardFold_hasFDerivAt q).fderiv]
  constructor
  · intro hi hzero
    have hh : standardFoldDerivative q (0, 1) = standardFoldDerivative q (0, 0) := by
      simp [standardFoldDerivative, rowCLM_apply, hzero]
    have := congrArg Prod.snd (hi hh)
    norm_num at this
  · intro h v w heq
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    simp only [standardFoldDerivative, ContinuousLinearMap.prod_apply, rowCLM_apply,
      one_mul, zero_mul, add_zero, zero_add] at hx hy
    exact Prod.ext hx (mul_left_cancel₀ (mul_ne_zero (by norm_num) h) hy)

def IsCritical (p : Cylinder) : Prop :=
  ¬ Function.Injective (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ) cylinderObservation p)

theorem cylinder_critical_coordinate_iff (p : Cylinder) :
    IsCritical p ↔ (cylinderCoordinate p).2 = 0 := by
  have heq : cylinderObservation = standardFold ∘ cylinderCoordinate :=
    funext cylinder_global_fold_equation
  unfold IsCritical
  rw [heq, mfderiv_comp p
    ((standardFold_hasFDerivAt (cylinderCoordinate p)).differentiableAt.mdifferentiableAt)
    (cylinderCoordinate_smooth.mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
  have hiff := Function.Injective.of_comp_iff' (fderiv ℝ standardFold (cylinderCoordinate p))
    (cylinderCoordinate_derivative_bijective p)
  change (¬ Function.Injective ((fderiv ℝ standardFold (cylinderCoordinate p)) ∘
    (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ) cylinderCoordinate p))) ↔ _
  rw [hiff, standardFold_derivative_injective_iff, not_not]

theorem cylinder_critical_iff (p : Cylinder) :
    IsCritical p ↔ (p.2 : ℂ).im = 0 := by
  rw [cylinder_critical_coordinate_iff]
  change Real.sqrt p.1.1 * (p.2 : ℂ).im = 0 ↔ _
  exact mul_eq_zero.trans (or_iff_right (ne_of_gt (Real.sqrt_pos.2 p.1.2)))

theorem all_critical_points_are_whitney_folds (p : Cylinder) (hp : IsCritical p) :
    HasWhitneyFoldAt cylinderObservation p :=
  cylinder_whitney_fold p ((cylinder_critical_iff p).mp hp)

theorem critical_values_iff (v : ℝ × ℝ) :
    (∃ p, IsCritical p ∧ cylinderObservation p = v) ↔ v.2 = 0 ∧ v.1 ≠ 0 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hy := (cylinder_critical_coordinate_iff p).mp hp
    rw [cylinder_global_fold_equation]
    refine ⟨by simp [standardFold, cylinderCoordinate] at hy ⊢; exact hy, ?_⟩
    intro hx
    exact (globalDiffeomorph p).2 (Prod.ext hx hy)
  · rintro ⟨hy, hx⟩
    let q : SmoothPlane := ⟨v, by
      intro h
      exact hx (congrArg Prod.fst h)⟩
    refine ⟨globalDiffeomorph.symm q, ?_, ?_⟩
    · rw [cylinder_critical_coordinate_iff]
      change (globalDiffeomorph (globalDiffeomorph.symm q)).1.2 = 0
      rw [globalDiffeomorph.apply_symm_apply]
      exact hy
    · rw [cylinder_global_fold_equation, globalDiffeomorph.apply_symm_apply]
      apply Prod.ext
      · rfl
      · change v.2 ^ 2 = v.2
        rw [hy]
        norm_num

theorem cylinderSurface_fiber_iff (a b : Cylinder) :
    cylinderSurface a = cylinderSurface b ↔ a = b ∨
      (a.1.1 = b.1.1 ∧ (a.2 : ℂ).re = 0 ∧ (b.2 : ℂ).re = 0 ∧
        (((a.2 : ℂ).im = 1 ∧ (b.2 : ℂ).im = -1) ∨
         ((a.2 : ℂ).im = -1 ∧ (b.2 : ℂ).im = 1))) := by
  rw [cylinderSurface, cylinderSurface, phaseSurface_fiber_iff]
  constructor
  · rintro (h | h)
    · left
      exact cylinderPhaseEquiv.injective h
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

/-- Every nontrivial double fiber has three independent actual tangent-image vectors. -/
theorem all_double_fibers_transverse_determinant (a b : Cylinder)
    (hne : a ≠ b) (heq : cylinderSurface a = cylinderSurface b) :
    determinant3
      (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) cylinderSurface a (coordinateTangent a (1, 0)))
      (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) cylinderSurface a (coordinateTangent a (0, 1)))
      (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) cylinderSurface b (coordinateTangent b (1, 0))) ≠ 0 := by
  obtain ⟨hr, ha, hb, hs⟩ := ((cylinderSurface_fiber_iff a b).mp heq).resolve_left hne
  rw [double_phase_derivative_first a ha, double_phase_derivative_second a ha,
    double_phase_derivative_first b hb]
  have hdet : determinant3 ((a.2 : ℂ).im, 0, 1)
      (0, 2 * (Real.sqrt a.1.1 * (a.2 : ℂ).im), 0) ((b.2 : ℂ).im, 0, 1) =
        4 * Real.sqrt a.1.1 := by
    rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> simp [determinant3, ha, hb] <;> ring
  rw [hdet]
  exact ne_of_gt (mul_pos (by norm_num) (Real.sqrt_pos.2 a.1.2))

/-- Transversality as equality of the sum of the two actual tangent images with R³. -/
theorem all_double_fibers_tangent_span (a b : Cylinder)
    (hne : a ≠ b) (heq : cylinderSurface a = cylinderSurface b) :
    LinearMap.range (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) cylinderSurface a).toLinearMap ⊔
      LinearMap.range (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) cylinderSurface b).toLinearMap = ⊤ := by
  obtain ⟨hr, ha, hb, hs⟩ := ((cylinderSurface_fiber_iff a b).mp heq).resolve_left hne
  apply Submodule.eq_top_iff'.mpr
  rintro ⟨x, y, z⟩
  let s := (a.2 : ℂ).im
  let k := 2 * (Real.sqrt a.1.1 * s)
  have hsne : s ≠ 0 := by
    rcases hs with ⟨h, _⟩ | ⟨h, _⟩ <;> dsimp [s] <;> rw [h] <;> norm_num
  have hkn : k ≠ 0 := mul_ne_zero (by norm_num)
    (mul_ne_zero (ne_of_gt (Real.sqrt_pos.2 a.1.2)) hsne)
  have hbneg : (b.2 : ℂ).im = -s := by
    rcases hs with ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp [s, h, h']
  let α := (x / s + z) / 2
  let β := y / k
  let γ := (z - x / s) / 2
  let va : TangentSpace cylinderModel a :=
    α • coordinateTangent a (1, 0) + β • coordinateTangent a (0, 1)
  let vb : TangentSpace cylinderModel b := γ • coordinateTangent b (1, 0)
  let Da : TangentSpace cylinderModel a →L[ℝ] (ℝ × ℝ × ℝ) :=
    mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) cylinderSurface a
  let Db : TangentSpace cylinderModel b →L[ℝ] (ℝ × ℝ × ℝ) :=
    mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) cylinderSurface b
  have hDa1 : Da (coordinateTangent a (1, 0)) = ((a.2 : ℂ).im, 0, 1) :=
    double_phase_derivative_first a ha
  have hDa2 : Da (coordinateTangent a (0, 1)) = (0, k, 0) :=
    double_phase_derivative_second a ha
  have hDb1 : Db (coordinateTangent b (1, 0)) = ((b.2 : ℂ).im, 0, 1) :=
    double_phase_derivative_first b hb
  have hv :
      Da va + Db vb = (x, y, z) := by
    dsimp [va, vb]
    rw [map_add, map_smul, map_smul, map_smul,
      hDa1, hDa2, hDb1, hbneg]
    apply Prod.ext
    · change α * s + β * 0 + γ * (-s) = x
      dsimp [α, γ]
      field_simp
      ring
    · apply Prod.ext
      · change α * 0 + β * k + γ * 0 = y
        dsimp [β]
        simp [hkn]
      · change α * 1 + β * 0 + γ * 1 = z
        dsimp [α, γ]
        ring
  change (x, y, z) ∈ LinearMap.range Da.toLinearMap ⊔ LinearMap.range Db.toLinearMap
  rw [← hv]
  exact Submodule.add_mem_sup ⟨va, rfl⟩ ⟨vb, rfl⟩

def angleLift (r : PositiveRadius) (u : ℝ) : Cylinder := (r, Circle.exp u)

theorem cylinderSurface_angleLift (r : PositiveRadius) (u : ℝ) :
    cylinderSurface (angleLift r u) = G r.1 u := by
  simp [cylinderSurface, phaseSurface, cylinderToPhase, angleLift, G,
    Circle.coe_exp, Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem cylinderObservation_angleLift (r : PositiveRadius) (u : ℝ) :
    cylinderObservation (angleLift r u) = observation r.1 u := by
  simp [cylinderObservation, circleObservation, cylinderToPhase, angleLift, observation,
    Circle.coe_exp, Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem cylinderCoordinate_angleLift (r : PositiveRadius) (u : ℝ) :
    cylinderCoordinate (angleLift r u) = chart r.1 u := by
  change (r.1 * (Circle.exp u : ℂ).re, Real.sqrt r.1 * (Circle.exp u : ℂ).im) = chart r.1 u
  simp [chart, Circle.coe_exp, Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

def positivePole (r : PositiveRadius) : Cylinder :=
  phaseToCylinder ⟨r.1, 0, 1, r.2, by norm_num⟩

def negativePole (r : PositiveRadius) : Cylinder :=
  phaseToCylinder ⟨r.1, 0, -1, r.2, by norm_num⟩

theorem pole_images (r : PositiveRadius) :
    cylinderSurface (positivePole r) = (0, r.1, 0) ∧
      cylinderSurface (negativePole r) = (0, r.1, 0) := by
  simp [positivePole, negativePole, cylinderSurface, phaseSurface, cylinderToPhase, phaseToCylinder]

theorem poles_distinct (r : PositiveRadius) : positivePole r ≠ negativePole r := by
  intro h
  have hh := congrArg (fun p : Cylinder => (p.2 : ℂ).im) h
  norm_num [positivePole, negativePole, phaseToCylinder] at hh

/-- The double-line fiber has exactly these two distinct intrinsic circle phases. -/
theorem double_line_exact_fiber (r : PositiveRadius) (p : Cylinder) :
    cylinderSurface p = (0, r.1, 0) ↔ p = positivePole r ∨ p = negativePole r := by
  constructor
  · intro h
    have he : cylinderSurface p = cylinderSurface (positivePole r) :=
      h.trans (pole_images r).1.symm
    rcases (cylinderSurface_fiber_iff p (positivePole r)).mp he with h | ⟨hr, hc, _, hs⟩
    · exact Or.inl h
    · right
      have hp : (p.2 : ℂ).im = -1 := by
        rcases hs with ⟨_, hbad⟩ | ⟨hp, _⟩
        · norm_num [positivePole, phaseToCylinder] at hbad
        · exact hp
      apply cylinderPhaseEquiv.injective
      apply PhasePoint.ext'
      · exact hr
      · exact hc
      · exact hp
  · rintro (rfl | rfl)
    · exact (pole_images r).1
    · exact (pole_images r).2

theorem multiple_fibers_iff_positive_y_axis (v : ℝ × ℝ × ℝ) :
    (∃ a b : Cylinder, a ≠ b ∧ cylinderSurface a = v ∧ cylinderSurface b = v) ↔
      ∃ r : PositiveRadius, v = (0, r.1, 0) := by
  constructor
  · rintro ⟨a, b, hne, ha, hb⟩
    obtain ⟨_, hc, _, hs⟩ := ((cylinderSurface_fiber_iff a b).mp (ha.trans hb.symm)).resolve_left hne
    refine ⟨a.1, ?_⟩
    rw [← ha]
    rcases hs with ⟨h, _⟩ | ⟨h, _⟩ <;>
      simp [cylinderSurface, phaseSurface, cylinderToPhase, hc, h]
  · rintro ⟨r, rfl⟩
    exact ⟨positivePole r, negativePole r, poles_distinct r, (pole_images r).1, (pole_images r).2⟩

theorem positiveDiagonal_mfderiv_injective (t : PositiveRadius) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) positiveDiagonal t) := by
  have hi : Function.Injective (fderiv ℝ diagonalCurve t.1) := by
    intro v w h
    have hz : fderiv ℝ diagonalCurve t.1 (v - w) = 0 := by
      rw [map_sub, h, sub_self]
    rw [fderiv_eq_smul_deriv] at hz
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (diagonalCurve_immersion t.1 t.2))
  have hc : Function.Injective
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : PositiveRadius → ℝ) t) := by
    have h : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : PositiveRadius → ℝ) t =
        ContinuousLinearMap.id ℝ ℝ := mfderiv_extChartAt_self
    rw [h]
    exact Function.injective_id
  change Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ)
    (diagonalCurve ∘ Subtype.val) t)
  rw [mfderiv_comp t (diagonalCurve_hasDerivAt t.1).differentiableAt.mdifferentiableAt
    ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
  exact hi.comp hc

/-- A--E together, on the standard positive-radius cylinder and with actual derivatives. -/
theorem complete_geometry :
    (ContMDiff cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) ∞ cylinderSurface ∧
      ∀ p, Function.Injective (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) cylinderSurface p)) ∧
    (∀ v : ℝ × ℝ × ℝ,
      (∃ a b : Cylinder, a ≠ b ∧ cylinderSurface a = v ∧ cylinderSurface b = v) ↔
        ∃ r : PositiveRadius, v = (0, r.1, 0)) ∧
    (∀ r : PositiveRadius, ∀ p : Cylinder,
      cylinderSurface p = (0, r.1, 0) ↔ p = positivePole r ∨ p = negativePole r) ∧
    (∀ a b : Cylinder, a ≠ b → cylinderSurface a = cylinderSurface b →
      LinearMap.range (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) cylinderSurface a).toLinearMap ⊔
        LinearMap.range (mfderiv cylinderModel 𝓘(ℝ, ℝ × ℝ × ℝ) cylinderSurface b).toLinearMap = ⊤) ∧
    (∀ p : Cylinder, IsCritical p ↔ (p.2 : ℂ).im = 0) ∧
    (∀ p : Cylinder, IsCritical p → HasWhitneyFoldAt cylinderObservation p) ∧
    (ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞ positiveDiagonal ∧
      Topology.IsEmbedding positiveDiagonal ∧
        ∀ t : PositiveRadius, Function.Injective
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) positiveDiagonal t)) ∧
    (∃ H : Cylinder ≃ₘ⟮cylinderModel, 𝓘(ℝ, ℝ × ℝ)⟯ SmoothPlane,
      ∀ p, cylinderObservation p = standardFold (H p).1) :=
  ⟨⟨cylinderSurface_smooth, cylinderSurface_immersion⟩,
    multiple_fibers_iff_positive_y_axis, double_line_exact_fiber,
    all_double_fibers_tangent_span, cylinder_critical_iff,
    all_critical_points_are_whitney_folds,
    ⟨positiveDiagonal_smooth, positiveDiagonal_embedding, positiveDiagonal_mfderiv_injective⟩,
    ⟨globalDiffeomorph, cylinder_global_fold_equation⟩⟩

end
end PrimeSphericalFold
