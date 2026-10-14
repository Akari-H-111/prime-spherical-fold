import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Prime spherical fold: algebraic and differential groundwork

Independent companion for a smooth ruled cone and its observation map.
It does not import or modify any existing Stokes theorem. A connection to a
prime-indexed sampling construction is outside the formalized scope.
-/

namespace PrimeSphericalFold

noncomputable section

/-- The three-coordinate smooth parametrization. -/
def G (r u : ℝ) : ℝ × ℝ × ℝ :=
  (r * Real.sin u * Real.cos u, r * Real.sin u ^ 2, r * Real.cos u)

/-- Euclidean squared norm in the three coordinates. -/
def normSq3 (v : ℝ × ℝ × ℝ) : ℝ := v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2

/-- The observation of the z and y coordinates. -/
def observation (r u : ℝ) : ℝ × ℝ := (r * Real.cos u, r * Real.sin u ^ 2)

/-- The source coordinate map for the fold normal form. -/
def chart (r u : ℝ) : ℝ × ℝ :=
  (r * Real.cos u, Real.sqrt r * Real.sin u)

/-- The target Whitney normal form. -/
def standardFold (q : ℝ × ℝ) : ℝ × ℝ := (q.1, q.2 ^ 2)

/-- The squared radius is exactly r². -/
theorem radius_squared (r u : ℝ) : normSq3 (G r u) = r ^ 2 := by
  let s : ℝ := Real.sin u
  let c : ℝ := Real.cos u
  have hsc : s ^ 2 + c ^ 2 = 1 := by
    dsimp [s, c]
    nlinarith [Real.sin_sq_add_cos_sq u]
  change (r * s * c) ^ 2 + (r * s ^ 2) ^ 2 + (r * c) ^ 2 = r ^ 2
  calc
    (r * s * c) ^ 2 + (r * s ^ 2) ^ 2 + (r * c) ^ 2 =
        r ^ 2 * (s ^ 2 + c ^ 2) ^ 2 - r ^ 2 * c ^ 2 * (s ^ 2 + c ^ 2 - 1) := by ring
    _ = r ^ 2 := by rw [hsc]; ring

/-- The (positive-radius) diagonal curve is injective. -/
theorem diagonal_injective :
    Function.Injective (fun t : {t : ℝ // 0 < t} => G t.1 t.1) := by
  intro a b hab
  have heq := congrArg normSq3 hab
  rw [radius_squared, radius_squared] at heq
  have hzero : (a.1 - b.1) * (a.1 + b.1) = 0 := by nlinarith [heq]
  have hplus : a.1 + b.1 ≠ 0 := ne_of_gt (add_pos a.2 b.2)
  have hminus : a.1 - b.1 = 0 := (mul_eq_zero.mp hzero).resolve_right hplus
  apply Subtype.ext
  exact sub_eq_zero.mp hminus

/-- The selected plane projection is exactly a fold in source coordinates. -/
theorem observation_eq_standardFold (r u : ℝ) (hr : 0 < r) :
    observation r u = standardFold (chart r u) := by
  have hs : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt (le_of_lt hr)
  apply Prod.ext
  · rfl
  · simp only [observation, standardFold, chart, mul_pow, hs]

/-- Explicit Jacobian determinant of the z,y observation. -/
def observationJacobian (r u : ℝ) : ℝ :=
  Real.cos u * (2 * r * Real.sin u * Real.cos u) -
    (-r * Real.sin u) * Real.sin u ^ 2

theorem observationJacobian_factor (r u : ℝ) :
    observationJacobian r u = r * Real.sin u * (1 + Real.cos u ^ 2) := by
  have htrig := Real.sin_sq_add_cos_sq u
  unfold observationJacobian
  calc
    Real.cos u * (2 * r * Real.sin u * Real.cos u) -
      (-r * Real.sin u) * Real.sin u ^ 2 =
      r * Real.sin u * (Real.sin u ^ 2 + 2 * Real.cos u ^ 2) := by ring
    _ = r * Real.sin u * (1 + Real.cos u ^ 2) := by
      congr 1
      nlinarith [htrig]

theorem observationJacobian_zero_iff (r u : ℝ) (hr : 0 < r) :
    observationJacobian r u = 0 ↔ Real.sin u = 0 := by
  rw [observationJacobian_factor]
  have hp : 0 < 1 + Real.cos u ^ 2 := by positivity
  constructor
  · intro h
    have hz := (mul_eq_zero.mp h).resolve_right (ne_of_gt hp)
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hr)
  · intro h
    rw [h]
    ring

/-- Two different angle values have the same image on the double line. -/
theorem double_line (r : ℝ) :
    G r (Real.pi / 2) = G r (-(Real.pi / 2)) := by
  simp [G, Real.sin_neg, Real.cos_neg, Real.cos_pi_div_two]
end
end PrimeSphericalFold

/-!
# Algebraic global coordinates for the prime spherical fold

A circle phase is represented as a unit pair (c,s).  This avoids using a
real-valued angle for a global chart: the latter is periodic and noninjective.
The codomain is the punctured plane.
-/

namespace PrimeSphericalFold

noncomputable section

structure PhasePoint where
  radius : ℝ
  c : ℝ
  s : ℝ
  radius_pos : 0 < radius
  unit : c ^ 2 + s ^ 2 = 1

abbrev PuncturedPlane := {q : ℝ × ℝ // q ≠ (0, 0)}

def chartPair (p : PhasePoint) : ℝ × ℝ :=
  (p.radius * p.c, Real.sqrt p.radius * p.s)

private theorem chartPair_ne_zero (p : PhasePoint) : chartPair p ≠ (0, 0) := by
  intro hz
  have h1 : p.radius * p.c = 0 := congrArg Prod.fst hz
  have h2 : Real.sqrt p.radius * p.s = 0 := congrArg Prod.snd hz
  have hc0 : p.c = 0 := (mul_eq_zero.mp h1).resolve_left (ne_of_gt p.radius_pos)
  have hs0 : p.s = 0 :=
    (mul_eq_zero.mp h2).resolve_left (ne_of_gt (Real.sqrt_pos.2 p.radius_pos))
  have hu := p.unit
  rw [hc0, hs0] at hu
  norm_num at hu

def toPlane (p : PhasePoint) : PuncturedPlane := ⟨chartPair p, chartPair_ne_zero p⟩

def inverseRadius (x y : ℝ) : ℝ :=
  (y ^ 2 + Real.sqrt (y ^ 4 + 4 * x ^ 2)) / 2

private theorem inverseRadius_quadratic (x y : ℝ) :
    inverseRadius x y ^ 2 - y ^ 2 * inverseRadius x y - x ^ 2 = 0 := by
  have hsq : (Real.sqrt (y ^ 4 + 4 * x ^ 2)) ^ 2 = y ^ 4 + 4 * x ^ 2 :=
    Real.sq_sqrt (by positivity)
  dsimp [inverseRadius]
  nlinarith [hsq]

theorem inverseRadius_pos (q : PuncturedPlane) :
    0 < inverseRadius q.1.1 q.1.2 := by
  obtain ⟨⟨x, y⟩, hne⟩ := q
  change 0 < inverseRadius x y
  by_cases hy : y = 0
  · have hx : x ≠ 0 := by
      intro hx
      exact hne (by simp [hx, hy])
    have hdisc : 0 < y ^ 4 + 4 * x ^ 2 := by
      rw [hy]
      nlinarith [sq_pos_of_ne_zero hx]
    dsimp [inverseRadius]
    have hsqrt := Real.sqrt_pos.2 hdisc
    nlinarith [sq_nonneg y]
  · have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
    have hsqrt : 0 ≤ Real.sqrt (y ^ 4 + 4 * x ^ 2) := Real.sqrt_nonneg _
    dsimp [inverseRadius]
    linarith

/-- Explicit inverse formula; the positive root enforces the intended sheet. -/
def fromPlane (q : PuncturedPlane) : PhasePoint := by
  let x : ℝ := q.1.1
  let y : ℝ := q.1.2
  let r : ℝ := inverseRadius x y
  have hr : 0 < r := inverseRadius_pos q
  have hrne : r ≠ 0 := ne_of_gt hr
  have hsqrtr : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt (le_of_lt hr)
  have hsqrtne : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr)
  have hquad : r ^ 2 - y ^ 2 * r - x ^ 2 = 0 := inverseRadius_quadratic x y
  refine ⟨r, x / r, y / Real.sqrt r, hr, ?_⟩
  calc
    (x / r) ^ 2 + (y / Real.sqrt r) ^ 2 = x ^ 2 / r ^ 2 + y ^ 2 / r := by
      rw [div_pow, div_pow, hsqrtr]
    _ = (x ^ 2 + y ^ 2 * r) / r ^ 2 := by
      field_simp [hrne]
    _ = 1 := by
      have heq : x ^ 2 + y ^ 2 * r = r ^ 2 := by linarith
      rw [heq, div_self (pow_ne_zero 2 hrne)]

theorem radius_toPlane (p : PhasePoint) :
    inverseRadius (toPlane p).1.1 (toPlane p).1.2 = p.radius := by
  let x := p.radius * p.c
  let y := Real.sqrt p.radius * p.s
  have hrad := inverseRadius_pos (toPlane p)
  have hquad0 := inverseRadius_quadratic x y
  have hsqrtr := Real.sq_sqrt (le_of_lt p.radius_pos)
  have hquad1 : p.radius ^ 2 - y ^ 2 * p.radius - x ^ 2 = 0 := by
    calc
      p.radius ^ 2 - y ^ 2 * p.radius - x ^ 2 =
          p.radius ^ 2 * (1 - (p.c ^ 2 + p.s ^ 2)) := by
            dsimp [x, y]
            rw [mul_pow, hsqrtr]
            ring
      _ = 0 := by rw [p.unit]; ring
  have hsle : p.s ^ 2 ≤ 1 := by nlinarith [p.unit, sq_nonneg p.c]
  have hy_le : y ^ 2 ≤ p.radius := by
    dsimp [y]
    rw [mul_pow, hsqrtr]
    simpa only [mul_one] using (mul_le_mul_of_nonneg_left hsle (le_of_lt p.radius_pos))
  have hfactor :
      (inverseRadius x y - p.radius) * (inverseRadius x y + p.radius - y ^ 2) = 0 := by
    nlinarith [hquad0, hquad1]
  have hpos : 0 < inverseRadius x y + p.radius - y ^ 2 := by
    have hh : inverseRadius x y = inverseRadius (toPlane p).1.1 (toPlane p).1.2 := rfl
    rw [hh]
    linarith
  have : inverseRadius x y = p.radius := by
    have hh := (mul_eq_zero.mp hfactor).resolve_right (ne_of_gt hpos)
    linarith
  exact this

private theorem phasePoint_ext (a b : PhasePoint)
    (hr : a.radius = b.radius) (hc : a.c = b.c) (hs : a.s = b.s) : a = b := by
  cases a with
  | mk ar ac as ahr ahu =>
    cases b with
    | mk br bc bs bhr bhu =>
      cases hr
      cases hc
      cases hs
      rfl

private theorem from_to (p : PhasePoint) : fromPlane (toPlane p) = p := by
  have hr := radius_toPlane p
  cases p with
  | mk r c s hpos hunit =>
    have hr' : inverseRadius (r * c) (Real.sqrt r * s) = r := by
      simpa [toPlane, chartPair] using hr
    apply phasePoint_ext
    · exact hr'
    · change (r * c) / inverseRadius (r * c) (Real.sqrt r * s) = c
      rw [hr']
      field_simp [ne_of_gt hpos]
    · change (Real.sqrt r * s) /
          Real.sqrt (inverseRadius (r * c) (Real.sqrt r * s)) = s
      rw [hr']
      field_simp [ne_of_gt (Real.sqrt_pos.2 hpos)]

private theorem to_from (q : PuncturedPlane) : toPlane (fromPlane q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · change inverseRadius q.1.1 q.1.2 * (q.1.1 / inverseRadius q.1.1 q.1.2) = q.1.1
    field_simp [ne_of_gt (inverseRadius_pos q)]
  · change Real.sqrt (inverseRadius q.1.1 q.1.2) *
          (q.1.2 / Real.sqrt (inverseRadius q.1.1 q.1.2)) = q.1.2
    field_simp [ne_of_gt (Real.sqrt_pos.2 (inverseRadius_pos q))]

/-- Global one-to-one coordinates of the positive-radius circle cylinder. -/
def globalCoordinateEquiv : PhasePoint ≃ PuncturedPlane where
  toFun := toPlane
  invFun := fromPlane
  left_inv := from_to
  right_inv := to_from

/-- The original observation factors through the standard fold in global coordinates. -/
def circleObservation (p : PhasePoint) : ℝ × ℝ :=
  (p.radius * p.c, p.radius * p.s ^ 2)

theorem global_fold_equation (p : PhasePoint) :
    circleObservation p = standardFold (globalCoordinateEquiv p).1 := by
  apply Prod.ext
  · rfl
  · dsimp [circleObservation, standardFold, globalCoordinateEquiv, toPlane, chartPair]
    rw [mul_pow, Real.sq_sqrt (le_of_lt p.radius_pos)]

end
end PrimeSphericalFold

namespace PrimeSphericalFold
noncomputable section

/-- A row vector as a continuous linear map; kept local to avoid a Stokes dependency. -/
def rowCLM (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem rowCLM_apply (a b : ℝ) (v : ℝ × ℝ) :
    rowCLM a b v = a * v.1 + b * v.2 := by
  simp [rowCLM]

/-- The original two-variable map, uncurried. -/
def surface (p : ℝ × ℝ) : ℝ × ℝ × ℝ := G p.1 p.2

/-- The actual derivative candidate in Cartesian coordinates. -/
def surfaceDerivative (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ) :=
  (rowCLM (Real.sin p.2 * Real.cos p.2)
    (p.1 * (Real.cos p.2 ^ 2 - Real.sin p.2 ^ 2))).prod
  ((rowCLM (Real.sin p.2 ^ 2)
    (2 * p.1 * Real.sin p.2 * Real.cos p.2)).prod
   (rowCLM (Real.cos p.2) (-p.1 * Real.sin p.2)))

/-- The candidate differential is genuinely the Fréchet derivative of G. -/
theorem surface_hasFDerivAt (p : ℝ × ℝ) :
    HasFDerivAt surface (surfaceDerivative p) p := by
  have hr := (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p))
  have hu := (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p))
  have hs : HasFDerivAt (fun q : ℝ × ℝ => Real.sin q.2)
      (Real.cos p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (Real.hasDerivAt_sin p.2).comp_hasFDerivAt p hu
  have hc : HasFDerivAt (fun q : ℝ × ℝ => Real.cos q.2)
      (-Real.sin p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (Real.hasDerivAt_cos p.2).comp_hasFDerivAt p hu
  have hh := ((hr.mul hs).mul hc).prodMk ((hr.mul (hs.pow 2)).prodMk (hr.mul hc))
  apply (hh.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)).congr_fderiv
  apply ContinuousLinearMap.ext
  rintro ⟨v, w⟩
  apply Prod.ext
  · simp [surfaceDerivative, rowCLM_apply]
    ring
  · apply Prod.ext
    · simp [surfaceDerivative, rowCLM_apply]
      ring
    · simp [surfaceDerivative, rowCLM_apply]
      ring

/-- Positive-radius points have injective Fréchet derivative. -/
theorem surface_derivative_injective (p : ℝ × ℝ) (hr : 0 < p.1) :
    Function.Injective (surfaceDerivative p) := by
  intro v w heq
  suffices hzero : ∀ q : ℝ × ℝ, surfaceDerivative p q = 0 → q = 0 by
    have hh : surfaceDerivative p (v - w) = 0 := by
      rw [map_sub, sub_eq_zero.mpr heq]
    have h := hzero (v-w) hh
    exact sub_eq_zero.mp h
  intro q hq
  let s := Real.sin p.2
  let c := Real.cos p.2
  have hsc : s ^ 2 + c ^ 2 = 1 := by
    dsimp [s,c]
    nlinarith [Real.sin_sq_add_cos_sq p.2]
  have hx : (s * c) * q.1 + (p.1 * (c ^ 2 - s ^ 2)) * q.2 = 0 := by
    have hh := congrArg (fun x : ℝ × ℝ × ℝ => x.1) hq
    simpa [surfaceDerivative, rowCLM_apply, s, c] using hh
  have hy : s ^ 2 * q.1 + (2 * p.1 * s * c) * q.2 = 0 := by
    have hh := congrArg (fun x : ℝ × ℝ × ℝ => x.2.1) hq
    simpa [surfaceDerivative, rowCLM_apply, s, c] using hh
  have hz : c * q.1 + (-p.1 * s) * q.2 = 0 := by
    have hh := congrArg (fun x : ℝ × ℝ × ℝ => x.2.2) hq
    simpa [surfaceDerivative, rowCLM_apply, s, c] using hh
  have hradnorm : s ^ 2 * c ^ 2 + s ^ 4 + c ^ 2 = 1 := by
    calc
      s ^ 2 * c ^ 2 + s ^ 4 + c ^ 2 = s ^ 2 * (s ^ 2 + c ^ 2) + c ^ 2 := by ring
      _ = 1 := by rw [hsc]; nlinarith [hsc]
  have hq1 : q.1 = 0 := by
    have hcombined :
      (s * c) * ((s * c) * q.1 + (p.1 * (c ^ 2 - s ^ 2)) * q.2) +
        s ^ 2 * (s ^ 2 * q.1 + (2 * p.1 * s * c) * q.2) +
        c * (c * q.1 + (-p.1 * s) * q.2) = q.1 := by
      calc
        _ = (s ^ 2 * c ^ 2 + s ^ 4 + c ^ 2) * q.1 +
              p.1 * s * c * (s ^ 2 + c ^ 2 - 1) * q.2 := by ring
        _ = q.1 := by rw [hradnorm, hsc]; ring
    rw [hx, hy, hz] at hcombined
    simpa using hcombined.symm
  have hq2 : q.2 = 0 := by
    have hcombined :
      (c ^ 2 - s ^ 2) * ((s * c) * q.1 + (p.1 * (c ^ 2 - s ^ 2)) * q.2) +
        (2 * s * c) * (s ^ 2 * q.1 + (2 * p.1 * s * c) * q.2) -
        s * (c * q.1 + (-p.1 * s) * q.2) = p.1 * (1 + s ^ 2) * q.2 := by
      calc
        _ = p.1 * ((s ^ 2 + c ^ 2) ^ 2 + s ^ 2) * q.2 +
              s * c * (s ^ 2 + c ^ 2 - 1) * q.1 := by ring
        _ = p.1 * (1 + s ^ 2) * q.2 := by rw [hsc]; ring
    rw [hx, hy, hz] at hcombined
    have hh : p.1 * (1 + s ^ 2) * q.2 = 0 := by simpa using hcombined.symm
    have hp : p.1 * (1 + s ^ 2) ≠ 0 := ne_of_gt (mul_pos hr (by positivity))
    exact (mul_eq_zero.mp hh).resolve_left hp
  exact Prod.ext hq1 hq2

/-- Full immersion statement, using the actual Fréchet derivative. -/
theorem surface_isImmersion (p : ℝ × ℝ) (hr : 0 < p.1) :
    DifferentiableAt ℝ surface p ∧ Function.Injective (fderiv ℝ surface p) := by
  constructor
  · exact (surface_hasFDerivAt p).differentiableAt
  · rw [(surface_hasFDerivAt p).fderiv]
    exact surface_derivative_injective p hr

end
end PrimeSphericalFold

namespace PrimeSphericalFold
noncomputable section

def observationPlane (p : ℝ × ℝ) : ℝ × ℝ := observation p.1 p.2

def observationDerivative (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (rowCLM (Real.cos p.2) (-p.1 * Real.sin p.2)).prod
    (rowCLM (Real.sin p.2 ^ 2)
      (2 * p.1 * Real.sin p.2 * Real.cos p.2))

theorem observationPlane_hasFDerivAt (p : ℝ × ℝ) :
    HasFDerivAt observationPlane (observationDerivative p) p := by
  have hr := (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p))
  have hu := (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := p))
  have hs : HasFDerivAt (fun q : ℝ × ℝ => Real.sin q.2)
      (Real.cos p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (Real.hasDerivAt_sin p.2).comp_hasFDerivAt p hu
  have hc : HasFDerivAt (fun q : ℝ × ℝ => Real.cos q.2)
      (-Real.sin p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (Real.hasDerivAt_cos p.2).comp_hasFDerivAt p hu
  have hh := (hr.mul hc).prodMk (hr.mul (hs.pow 2))
  apply (hh.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)).congr_fderiv
  apply ContinuousLinearMap.ext
  rintro ⟨v, w⟩
  apply Prod.ext
  · simp [observationDerivative, rowCLM_apply]
    ring
  · simp [observationDerivative, rowCLM_apply]
    ring

def jacobianOf (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) : ℝ :=
  (L (1, 0)).1 * (L (0, 1)).2 - (L (0, 1)).1 * (L (1, 0)).2

theorem observation_plane_jacobian (p : ℝ × ℝ) :
    jacobianOf (fderiv ℝ observationPlane p) = observationJacobian p.1 p.2 := by
  rw [(observationPlane_hasFDerivAt p).fderiv]
  simp [jacobianOf, observationDerivative, rowCLM_apply, observationJacobian]

theorem critical_det_iff (p : ℝ × ℝ) (hr : 0 < p.1) :
    jacobianOf (fderiv ℝ observationPlane p) = 0 ↔ Real.sin p.2 = 0 := by
  rw [observation_plane_jacobian]
  exact observationJacobian_zero_iff p.1 p.2 hr

end
end PrimeSphericalFold

namespace PrimeSphericalFold
noncomputable section

def determinant3 (v w z : ℝ × ℝ × ℝ) : ℝ :=
  v.1 * (w.2.1 * z.2.2 - w.2.2 * z.2.1) -
    w.1 * (v.2.1 * z.2.2 - v.2.2 * z.2.1) +
    z.1 * (v.2.1 * w.2.2 - v.2.2 * w.2.1)

theorem double_line_transverse_actual (r : ℝ) (hr : 0 < r) :
    determinant3
      (surfaceDerivative (r, Real.pi / 2) (1, 0))
      (surfaceDerivative (r, Real.pi / 2) (0, 1))
      (surfaceDerivative (r, -(Real.pi / 2)) (0, 1)) ≠ 0 := by
  have hdet : determinant3
      (surfaceDerivative (r, Real.pi / 2) (1, 0))
      (surfaceDerivative (r, Real.pi / 2) (0, 1))
      (surfaceDerivative (r, -(Real.pi / 2)) (0, 1)) = 2 * r ^ 2 := by
    simp [determinant3, surfaceDerivative, rowCLM_apply,
      Real.sin_neg, Real.cos_neg, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  rw [hdet]
  exact ne_of_gt (mul_pos (by norm_num : (0:ℝ) < 2) (sq_pos_of_ne_zero (ne_of_gt hr)))

def diagonalCurve (t : ℝ) : ℝ × ℝ × ℝ := G t t

theorem diagonalCurve_hasDerivAt (t : ℝ) :
    HasDerivAt diagonalCurve (surfaceDerivative (t,t) (1,1)) t := by
  have hdiag : HasDerivAt (fun z : ℝ => (z,z)) (1,1) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_id t)
  change HasDerivAt (surface ∘ fun z : ℝ => (z,z)) (surfaceDerivative (t,t) (1,1)) t
  exact (surface_hasFDerivAt (t,t)).comp_hasDerivAt (f := fun z : ℝ => (z,z)) t hdiag

theorem diagonalCurve_immersion (t : ℝ) (ht : 0 < t) :
    deriv diagonalCurve t ≠ 0 := by
  have hinj := surface_derivative_injective (t,t) ht
  rw [(diagonalCurve_hasDerivAt t).deriv]
  intro hzero
  have heq : surfaceDerivative (t,t) (1,1) = surfaceDerivative (t,t) (0,0) := by
    exact hzero.trans (map_zero (surfaceDerivative (t,t))).symm
  have hpre := hinj heq
  have hbad : (1 : ℝ) = 0 := congrArg Prod.fst hpre
  norm_num at hbad

end
end PrimeSphericalFold
