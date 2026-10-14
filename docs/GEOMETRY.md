# Geometry theorem scope

## Requirements and authoritative declarations

| Requirement | Evidence in source |
| --- | --- |
| Standard positive-radius cylinder | `PositiveRadius`, `Cylinder`, `cylinderModel`; the circle uses the existing Mathlib sphere atlas. |
| A: smooth immersion | `cylinderSurface_smooth`, `cylinderSurface_immersion`; the latter is injectivity of the actual `mfderiv`. |
| B: exhaustive fibers | `phaseSurface_fiber_iff`, `cylinderSurface_fiber_iff`, `multiple_fibers_iff_positive_y_axis`, `double_line_exact_fiber`, `poles_distinct`. |
| B: all branch transversality | `all_double_fibers_tangent_span`: the ranges of the two actual manifold derivatives have supremum equal to the full ambient vector space. `all_double_fibers_transverse_determinant` also gives three independent tangent-image directions. |
| C: actual critical locus | `IsCritical`, `cylinder_critical_coordinate_iff`, `cylinder_critical_iff`. Criticality is noninjectivity of the actual manifold derivative. |
| C: smooth fold normal form | `HasWhitneyFoldAt`, `cylinder_whitney_fold`, `all_critical_points_are_whitney_folds`. |
| C: critical values | `critical_values_iff`: exactly `(x,0)` with `x != 0`. |
| D: smooth embedding | `positiveDiagonal_smooth`, `positiveDiagonal_embedding`, `positiveDiagonal_mfderiv_injective`; `positiveDiagonal_radius` supplies a continuous left inverse through the radius observable. |
| E: global smooth diffeomorphism | `globalDiffeomorph`, `smoothCoordinate_toFun`, `smoothCoordinate_invFun`, `cylinder_global_fold_equation`. |
| Original formula identification | `cylinderSurface_angleLift`, `cylinderObservation_angleLift`, `cylinderCoordinate_angleLift`. |
| Integrated theorem | `complete_geometry`. |
| Proof trust and placeholders | `PrimeSphericalFoldAudit.lean`; all local companion declarations are transitively audited. |

Smoothness plus injective derivative is the finite-dimensional immersion
criterion used here. The source explicitly proves that criterion, rather than
asserting a hand-computed Jacobian is the derivative. Smoothness, topological
embedding, and injective manifold derivative establish the smooth-embedding
claim for the diagonal curve.

`HasWhitneyFoldAt` is an independent definition for this manifold source.
It requires a genuine smooth diffeomorphism from the entire source cylinder
to an open planar set, a smooth target diffeomorphism, both centered at the
chosen point/value, and the exact square-map equation. This is stronger than
merely providing local coordinates. It does not import or claim definitional
identity with the historical Stokes predicate.

## Key construction

Write a point of the circle as `(c,s)` with `c^2+s^2=1`. The explicit map is

```
H(r,c,s) = (r*c, sqrt(r)*s) = (xi,eta)
R(xi,eta) = (eta^2 + sqrt(eta^4 + 4*xi^2))/2
H^-1(xi,eta) = (R, xi/R, eta/sqrt(R))
```

The inverse radius and discriminant are strictly positive off the origin.
This provides the required nonzero denominators and smooth square roots on
the precise domain. Both directions are proved smooth on the standard
manifolds, independently of the algebraic equivalence.

In these global coordinates the surface and observation are

```
K(xi,eta) = (xi*eta/sqrt(R), eta^2, xi)
O = (xi,eta^2)
```

For immersion, if `eta != 0`, the y and z derivative coordinates detect both
input components. If `eta = 0`, puncturedness forces `xi != 0`, and the
x derivative detects the remaining component. Thus no radius-zero or
origin case is silently admitted.

At the two double-line phases, the coordinate tangent images are
`(s,0,1)` and `(0,2*sqrt(r)*s,0)`, with `s=1` or `s=-1`.
The three selected actual tangent-image vectors have determinant `4*sqrt(r)`.
An explicit linear combination of these vectors proves that the two tangent
planes together span R^3.

At a critical point, `eta=0`, centering the source by `H(p)` and translating
the target by the observation of `p` gives the exact normal form
`(xi-xi0, eta^2)`. The source image is an open translated punctured plane
containing zero. The double-line phases `c=0` are regular observation points;
they differ from the fold phases `s=0`.

## Boundaries

The radius-zero vertex is excluded. These geometry results alone do not
prove arithmetic asymptotics or RH. See the separate arithmetic claim ledger
for exact Lean results, written corollaries using external classical inputs,
and numerical diagnostics.
