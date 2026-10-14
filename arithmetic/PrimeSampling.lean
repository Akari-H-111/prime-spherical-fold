import PrimeSphericalFoldComplete
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.Prime.Basic
import Lean.Util.CollectAxioms

/-!
# Exact prime sampling and the arithmetic filling bridge

No prime-equidistribution or Matomaki theorem is added as an axiom. The
infinite-subsequence transfer below takes its Diophantine input explicitly.
-/

namespace PrimeSphericalFold.Arithmetic
noncomputable section
open scoped ContDiff Topology Manifold

abbrev PrimeIndex := {p : ℕ // p.Prime}

theorem one_div_pi_irrational : Irrational (1 / Real.pi) := by
  simpa only [one_div] using irrational_pi.inv

def primeObservation (p : PrimeIndex) : ℝ × ℝ := observation p.1 p.1

def recoverRadius (q : ℝ × ℝ) : ℝ :=
  (q.2 + Real.sqrt (q.2 ^ 2 + 4 * q.1 ^ 2)) / 2

theorem recoverRadius_observation (r u : ℝ) (hr : 0 < r) :
    recoverRadius (observation r u) = r := by
  let y := r * Real.sin u ^ 2
  let z := r * Real.cos u
  have hunit := Real.sin_sq_add_cos_sq u
  have hyle : y ≤ r := by
    have hs : Real.sin u ^ 2 ≤ 1 := by nlinarith [sq_nonneg (Real.cos u)]
    simpa [y] using mul_le_mul_of_nonneg_left hs hr.le
  have hquad : r ^ 2 - y * r - z ^ 2 = 0 := by
    calc
      _ = r ^ 2 * (1 - (Real.sin u ^ 2 + Real.cos u ^ 2)) := by dsimp [y, z]; ring
      _ = 0 := by rw [hunit]; ring
  have hdisc : y ^ 2 + 4 * z ^ 2 = (2 * r - y) ^ 2 := by nlinarith
  change (y + Real.sqrt (y ^ 2 + 4 * z ^ 2)) / 2 = r
  rw [hdisc, Real.sqrt_sq (by linarith : 0 ≤ 2 * r - y)]
  ring

theorem primeObservation_recovery (p : PrimeIndex) : recoverRadius (primeObservation p) = p.1 :=
  recoverRadius_observation p.1 p.1 (by exact_mod_cast p.2.pos)

theorem primeObservation_injective : Function.Injective primeObservation := by
  intro p q h
  have he := congrArg recoverRadius h
  rw [primeObservation_recovery, primeObservation_recovery] at he
  apply Subtype.ext
  exact_mod_cast he

theorem sin_natCast_ne_zero (n : ℕ) (hn : 0 < n) : Real.sin (n : ℝ) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
  have hk0 : k ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero, zero_mul] at hk
    have : (0 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hi := irrational_pi.intCast_mul hk0
  rw [hk] at hi
  exact hi.ne_rat (n : ℚ) (by simp)

theorem cos_natCast_ne_zero (n : ℕ) (hn : 0 < n) : Real.cos (n : ℝ) ≠ 0 := by
  intro h
  have hs := sin_natCast_ne_zero (2 * n) (Nat.mul_pos (by norm_num) hn)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Real.sin_two_mul, h, mul_zero] at hs
  exact hs rfl

def primeLift (p : PrimeIndex) : Cylinder :=
  angleLift ⟨p.1, by change 0 < (p.1 : ℝ); exact_mod_cast p.2.pos⟩ p.1

theorem prime_never_critical (p : PrimeIndex) : ¬IsCritical (primeLift p) := by
  rw [cylinder_critical_iff]
  change (Circle.exp (p.1 : ℝ) : ℂ).im ≠ 0
  have him (t : ℝ) : (Circle.exp t : ℂ).im = Real.sin t := by
    simp [Circle.coe_exp, Complex.exp_mul_I, Complex.sin_ofReal_re, Complex.cos_ofReal_im]
  rw [him]
  exact sin_natCast_ne_zero p.1 p.2.pos

theorem prime_has_no_surface_partner (p : PrimeIndex) (q : Cylinder)
    (hq : cylinderSurface (primeLift p) = cylinderSurface q) : primeLift p = q := by
  rcases (cylinderSurface_fiber_iff (primeLift p) q).mp hq with h | ⟨_, hc, _⟩
  · exact h
  · have hcos : (Circle.exp (p.1 : ℝ) : ℂ).re = 0 := hc
    have hre (t : ℝ) : (Circle.exp t : ℂ).re = Real.cos t := by
      simp [Circle.coe_exp, Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
    have : Real.cos (p.1 : ℝ) = 0 := by
      rw [hre] at hcos
      exact hcos
    exact (cos_natCast_ne_zero p.1 p.2.pos this).elim

def holonomy (t : ℝ) : ℂ := Complex.exp (Complex.I * (2 * t : ℝ)) - 1

/-- Finite filling branch; its HMR interpretation requires nonzero holonomy. -/
def finiteFillingCost (t : ℝ) : ℝ := ‖holonomy t‖⁻¹

def foldHeight (t : ℝ) : ℝ := Real.sin t ^ 2

theorem holonomy_norm (t : ℝ) : ‖holonomy t‖ = 2 * |Real.sin t| := by
  unfold holonomy
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  simp [Real.norm_eq_abs]

theorem finiteFillingCost_eq (t : ℝ) : finiteFillingCost t = (2 * |Real.sin t|)⁻¹ := by
  unfold finiteFillingCost
  rw [holonomy_norm]

theorem fold_filling_identity (t : ℝ) (hs : Real.sin t ≠ 0) :
    foldHeight t * finiteFillingCost t ^ 2 = 1 / 4 := by
  rw [finiteFillingCost_eq]
  unfold foldHeight
  have ha : |Real.sin t| ≠ 0 := abs_ne_zero.mpr hs
  field_simp
  nlinarith [sq_abs (Real.sin t)]

theorem holonomy_ne_zero (t : ℝ) (hs : Real.sin t ≠ 0) : holonomy t ≠ 0 := by
  rw [← norm_ne_zero_iff, holonomy_norm]
  exact mul_ne_zero (by norm_num) (abs_ne_zero.mpr hs)

theorem filling_minimum (t : ℝ) (hs : Real.sin t ≠ 0) :
    holonomy t * (holonomy t)⁻¹ = 1 ∧
      ‖(holonomy t)⁻¹‖ = finiteFillingCost t ∧
        ∀ c : ℂ, holonomy t * c = 1 → finiteFillingCost t = ‖c‖ := by
  have hv := holonomy_ne_zero t hs
  refine ⟨mul_inv_cancel₀ hv, by simp [finiteFillingCost], ?_⟩
  intro c hc
  have hc' : c = (holonomy t)⁻¹ := by
    apply mul_left_cancel₀ hv
    rw [hc, mul_inv_cancel₀ hv]
  rw [hc']
  simp [finiteFillingCost]

theorem sin_bound_from_phase_distance (t : ℝ) (k : ℤ) :
    |Real.sin t| ≤ Real.pi * |t / Real.pi - k| := by
  have h := Real.abs_sin_sub_sin_le t ((k : ℝ) * Real.pi)
  rw [Real.sin_int_mul_pi, sub_zero] at h
  have he : t - k * Real.pi = Real.pi * (t / Real.pi - k) := by
    field_simp
  calc
    |Real.sin t| ≤ |t - k * Real.pi| := h
    _ = Real.pi * |t / Real.pi - k| := by
      rw [he, abs_mul, abs_of_pos Real.pi_pos]

theorem shrinking_fold_bound (t δ : ℝ) (_hδ : 0 < δ) (k : ℤ)
    (hk : |t / Real.pi - k| < δ) :
    foldHeight t < (Real.pi * δ) ^ 2 := by
  have hs : |Real.sin t| < Real.pi * δ :=
    (sin_bound_from_phase_distance t k).trans_lt (mul_lt_mul_of_pos_left hk Real.pi_pos)
  unfold foldHeight
  nlinarith [sq_abs (Real.sin t), abs_nonneg (Real.sin t)]

theorem growing_filling_bound (t δ : ℝ) (hδ : 0 < δ) (k : ℤ)
    (hk : |t / Real.pi - k| < δ) (hs : Real.sin t ≠ 0) :
    (2 * Real.pi * δ)⁻¹ < finiteFillingCost t := by
  rw [finiteFillingCost_eq]
  have hh : |Real.sin t| < Real.pi * δ :=
    (sin_bound_from_phase_distance t k).trans_lt (mul_lt_mul_of_pos_left hk Real.pi_pos)
  apply (inv_lt_inv₀ (by positivity : 0 < 2 * Real.pi * δ)
    (mul_pos (by norm_num) (abs_pos.mpr hs))).mpr
  linarith

/-- The input is explicit; this does not formalize or assume Matomaki as a new axiom. -/
theorem infinite_prime_fold_approach_of_diophantine (δ : ℕ → ℝ)
    (hδ : ∀ p, p.Prime → 0 < δ p)
    (h : Set.Infinite {p : ℕ | p.Prime ∧
      ∃ k : ℤ, |(p : ℝ) / Real.pi - k| < δ p}) :
    Set.Infinite {p : ℕ | p.Prime ∧ 0 < foldHeight p ∧
      foldHeight p < (Real.pi * δ p) ^ 2 ∧
        (2 * Real.pi * δ p)⁻¹ < finiteFillingCost p} := by
  apply Set.Infinite.mono (s := {p : ℕ | p.Prime ∧
      ∃ k : ℤ, |(p : ℝ) / Real.pi - k| < δ p}) _ h
  rintro p ⟨hp, k, hk⟩
  have hs := sin_natCast_ne_zero p hp.pos
  exact ⟨hp, sq_pos_of_ne_zero hs,
    shrinking_fold_bound p (δ p) (hδ p hp) k hk,
    growing_filling_bound p (δ p) (hδ p hp) k hk hs⟩

end
end PrimeSphericalFold.Arithmetic

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let names := (env.constants.toList.map Prod.fst).filter fun name =>
    name.toString.startsWith "PrimeSphericalFold.Arithmetic."
  if names.isEmpty then throwError "No arithmetic declarations found"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    unless (axioms.filter fun ax => !allowed.contains ax).isEmpty do
      throwError "Forbidden axioms in {name}: {axioms}"
    logInfo m!"{name}: {axioms}"
  logInfo m!"PASS: {names.length} arithmetic declarations; only standard axioms"
