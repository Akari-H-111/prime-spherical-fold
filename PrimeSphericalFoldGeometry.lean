import PrimeSphericalFold

/-!
# Complete fibers and smooth geometry

The circle phase is intrinsic: distinct real angles differing by a period
are one point, and the radius-zero vertex is outside the domain.
-/

namespace PrimeSphericalFold
noncomputable section

def phaseSurface (p : PhasePoint) : ℝ × ℝ × ℝ :=
  (p.radius * p.s * p.c, p.radius * p.s ^ 2, p.radius * p.c)

theorem phaseSurface_radius_squared (p : PhasePoint) :
    normSq3 (phaseSurface p) = p.radius ^ 2 := by
  dsimp [normSq3, phaseSurface]
  calc
    _ = p.radius ^ 2 * (p.c ^ 2 + p.s ^ 2) ^ 2 -
        p.radius ^ 2 * p.c ^ 2 * (p.c ^ 2 + p.s ^ 2 - 1) := by ring
    _ = p.radius ^ 2 := by rw [p.unit]; ring

@[ext] theorem PhasePoint.ext' {a b : PhasePoint}
    (hr : a.radius = b.radius) (hc : a.c = b.c) (hs : a.s = b.s) : a = b := by
  cases a
  cases b
  cases hr
  cases hc
  cases hs
  rfl

/-- All fibers: one point, except the two opposite phases over the positive y-axis. -/
theorem phaseSurface_fiber_iff (a b : PhasePoint) :
    phaseSurface a = phaseSurface b ↔ a = b ∨
      (a.radius = b.radius ∧ a.c = 0 ∧ b.c = 0 ∧
        ((a.s = 1 ∧ b.s = -1) ∨ (a.s = -1 ∧ b.s = 1))) := by
  constructor
  · intro h
    have hsq := congrArg normSq3 h
    rw [phaseSurface_radius_squared, phaseSurface_radius_squared] at hsq
    have hr : a.radius = b.radius := by
      nlinarith [a.radius_pos, b.radius_pos]
    have hz := congrArg (fun q : ℝ × ℝ × ℝ => q.2.2) h
    have hx := congrArg (fun q : ℝ × ℝ × ℝ => q.1) h
    change a.radius * a.c = b.radius * b.c at hz
    change a.radius * a.s * a.c = b.radius * b.s * b.c at hx
    rw [← hr] at hz hx
    have hc : a.c = b.c := mul_left_cancel₀ (ne_of_gt a.radius_pos) hz
    by_cases hs : a.s = b.s
    · exact Or.inl (PhasePoint.ext' hr hc hs)
    · right
      have hfactor : a.radius * a.c * (a.s - b.s) = 0 := by
        rw [← hc] at hx
        nlinarith [hx]
      have hc0 : a.c = 0 := by
        rcases mul_eq_zero.mp hfactor with h | h
        · exact (mul_eq_zero.mp h).resolve_left (ne_of_gt a.radius_pos)
        · exact (hs (sub_eq_zero.mp h)).elim
      have hb0 : b.c = 0 := hc.symm.trans hc0
      have haunit := a.unit
      have hbunit := b.unit
      rw [hc0] at haunit
      rw [hb0] at hbunit
      have ha : a.s = 1 ∨ a.s = -1 := by
        have : (a.s - 1) * (a.s + 1) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h | h <;> [left; right] <;> linarith
      have hb : b.s = 1 ∨ b.s = -1 := by
        have : (b.s - 1) * (b.s + 1) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h | h <;> [left; right] <;> linarith
      refine ⟨hr, hc0, hb0, ?_⟩
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact (hs (ha.trans hb.symm)).elim
      · exact Or.inl ⟨ha, hb⟩
      · exact Or.inr ⟨ha, hb⟩
      · exact (hs (ha.trans hb.symm)).elim
  · rintro (rfl | ⟨hr, ha, hb, hs⟩)
    · rfl
    · rcases hs with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;>
        simp [phaseSurface, ha, hb, ha', hb', hr]

end
end PrimeSphericalFold
