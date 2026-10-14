import PrimeSphericalFold
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Tactic.FunProp

/-!
# Smooth global coordinates on the standard cylinder

The source uses the existing analytic structure on the complex unit circle,
not a smooth structure transported from the desired coordinate equivalence.
-/

namespace PrimeSphericalFold
noncomputable section
open scoped ContDiff Topology Manifold
open Set ChartedSpace
attribute [local instance] finrank_real_complex_fact'

def positiveOpen : TopologicalSpace.Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩
abbrev PositiveRadius := positiveOpen
def puncturedOpen : TopologicalSpace.Opens (ℝ × ℝ) :=
  ⟨{q | q ≠ (0, 0)}, isClosed_singleton.isOpen_compl⟩
abbrev SmoothPlane := puncturedOpen
abbrev Cylinder := PositiveRadius × Circle
abbrev cylinderModel := (𝓘(ℝ, ℝ)).prod (𝓡 1)

def cylinderToPhase (p : Cylinder) : PhasePoint where
  radius := p.1.1
  c := (p.2 : ℂ).re
  s := (p.2 : ℂ).im
  radius_pos := p.1.2
  unit := by
    have h := Circle.normSq_coe p.2
    rw [Complex.normSq_apply] at h
    nlinarith [h]

def phaseToCylinder (p : PhasePoint) : Cylinder :=
  (⟨p.radius, p.radius_pos⟩, ⟨⟨p.c, p.s⟩, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [Complex.norm_def]
    have h : Complex.normSq ⟨p.c, p.s⟩ = 1 := by
      rw [Complex.normSq_mk]
      nlinarith [p.unit]
    rw [h, Real.sqrt_one]⟩)

def cylinderPhaseEquiv : Cylinder ≃ PhasePoint where
  toFun := cylinderToPhase
  invFun := phaseToCylinder
  left_inv p := by
    apply Prod.ext
    · rfl
    · apply Circle.ext
      apply Complex.ext <;> rfl
  right_inv p := by cases p; rfl

def smoothCoordinateEquiv : Cylinder ≃ SmoothPlane :=
  cylinderPhaseEquiv.trans globalCoordinateEquiv

theorem cylinder_radius_smooth :
    ContMDiff cylinderModel 𝓘(ℝ, ℝ) ∞ (fun p : Cylinder => p.1.1) :=
  contMDiff_subtype_val.comp contMDiff_fst

theorem cylinder_phase_smooth :
    ContMDiff cylinderModel 𝓘(ℝ, ℂ) ∞ (fun p : Cylinder => (p.2 : ℂ)) :=
  (contMDiff_coe_sphere (E := ℂ) (n := 1)).comp contMDiff_snd

theorem cylinder_c_smooth :
    ContMDiff cylinderModel 𝓘(ℝ, ℝ) ∞ (fun p : Cylinder => (p.2 : ℂ).re) :=
  Complex.reCLM.contMDiff.comp cylinder_phase_smooth

theorem cylinder_s_smooth :
    ContMDiff cylinderModel 𝓘(ℝ, ℝ) ∞ (fun p : Cylinder => (p.2 : ℂ).im) :=
  Complex.imCLM.contMDiff.comp cylinder_phase_smooth

theorem cylinder_sqrt_radius_smooth :
    ContMDiff cylinderModel 𝓘(ℝ, ℝ) ∞ (fun p : Cylinder => Real.sqrt p.1.1) := by
  intro p
  exact (Real.contDiffAt_sqrt (x := p.1.1) (ne_of_gt p.1.2)).comp_contMDiffAt
    (f := fun p : Cylinder => p.1.1) (cylinder_radius_smooth p)

theorem smoothCoordinate_toFun :
    ContMDiff cylinderModel 𝓘(ℝ, ℝ × ℝ) ∞ smoothCoordinateEquiv := by
  apply (ContMDiff.subtypeVal_comp_iff puncturedOpen _).mp
  apply (contMDiff_prod_module_iff _).mpr
  exact ⟨cylinder_radius_smooth.mul cylinder_c_smooth,
    cylinder_sqrt_radius_smooth.mul cylinder_s_smooth⟩

theorem inverseRadius_contDiffAt (q : PuncturedPlane) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => inverseRadius z.1 z.2) q.1 := by
  have hdisc : 0 < q.1.2 ^ 4 + 4 * q.1.1 ^ 2 := by
    by_cases hx : q.1.1 = 0
    · have hy : q.1.2 ≠ 0 := by
        intro hy
        exact q.2 (Prod.ext hx hy)
      positivity
    · positivity
  unfold inverseRadius
  apply ContDiffAt.div_const
  apply ContDiffAt.add (by fun_prop)
  exact (by fun_prop : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => z.2 ^ 4 + 4 * z.1 ^ 2) q.1).sqrt
    (ne_of_gt hdisc)

theorem plane_radius_smooth :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞
      (fun q : SmoothPlane => inverseRadius q.1.1 q.1.2) := by
  intro q
  exact (inverseRadius_contDiffAt q).comp_contMDiffAt (contMDiff_subtype_val q)

theorem smoothCoordinate_invFun :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) cylinderModel ∞ smoothCoordinateEquiv.symm := by
  have hval : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (Subtype.val : SmoothPlane → ℝ × ℝ) := contMDiff_subtype_val
  have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).contMDiff.comp hval
  have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).contMDiff.comp hval
  have hr := plane_radius_smooth
  have hsqrt : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞
      (fun q : SmoothPlane => Real.sqrt (inverseRadius q.1.1 q.1.2)) := by
    intro q
    exact (Real.contDiffAt_sqrt (x := inverseRadius q.1.1 q.1.2)
      (ne_of_gt (inverseRadius_pos q))).comp_contMDiffAt
        (f := fun q : SmoothPlane => inverseRadius q.1.1 q.1.2) (hr q)
  have hc := hx.div₀ hr (fun q => ne_of_gt (inverseRadius_pos q))
  have hs := hy.div₀ hsqrt (fun q => ne_of_gt (Real.sqrt_pos.2 (inverseRadius_pos q)))
  have hcomplex : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) ∞
      (fun q : SmoothPlane =>
        (⟨q.1.1 / inverseRadius q.1.1 q.1.2,
          q.1.2 / Real.sqrt (inverseRadius q.1.1 q.1.2)⟩ : ℂ)) := by
    have hmk : ContDiff ℝ ∞
        (fun z : ℝ × ℝ => (z.1 : ℂ) + (z.2 : ℂ) * Complex.I) :=
      (Complex.ofRealCLM.contDiff.comp contDiff_fst).add
        ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)
    have hp : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
        (fun q : SmoothPlane =>
          (q.1.1 / inverseRadius q.1.1 q.1.2,
           q.1.2 / Real.sqrt (inverseRadius q.1.1 q.1.2))) :=
      (contMDiff_prod_module_iff _).mpr ⟨hc, hs⟩
    convert hmk.comp_contMDiff hp using 1
    funext q
    apply Complex.ext <;> simp
  have hphase := hcomplex.codRestrict_sphere (n := 1)
    (fun q => (phaseToCylinder (fromPlane q)).2.2)
  have hrpos : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞
      (fun q : SmoothPlane => (⟨inverseRadius q.1.1 q.1.2, inverseRadius_pos q⟩ : PositiveRadius)) :=
    (ContMDiff.subtypeVal_comp_iff positiveOpen _).mp hr
  exact hrpos.prodMk hphase

/-- The explicit global coordinate equivalence is a genuine smooth diffeomorphism. -/
def globalDiffeomorph : Cylinder ≃ₘ⟮cylinderModel, 𝓘(ℝ, ℝ × ℝ)⟯ SmoothPlane where
  toEquiv := smoothCoordinateEquiv
  contMDiff_toFun := smoothCoordinate_toFun
  contMDiff_invFun := smoothCoordinate_invFun

end
end PrimeSphericalFold
