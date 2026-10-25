import IsingBulk.Joint.Transverse.CurveCoordinates
import IsingBulk.Anisotropic.RegularEdges.LeadingCoefficient
import IsingBulk.Anisotropic.RegularEdges.UpperIntegratedJets
import IsingBulk.Tail.BoundedWeightAnalyticIntegral

/-! # Actual full-site coefficients for arbitrary holomorphic transverse data
The complete constrained angular integral is constructed directly. No fixed real
ratio and no physical-continuation premise occurs in the coefficient or its jets.
-/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open IsingBulk.Anisotropic.RegularEdges Set Filter Metric MeasureTheory
open scoped Topology BigOperators

def complexDensity {N : ℕ} (b : ℝ) (B S : ℂ → ℂ) (u : ℂ) (q : Fin N → ℂ) : ℂ :=
  ((B u)^(N.choose 2)*(S u)⁻¹^N *
    (∏ i, 2*edgeComplexRoot b B u (q i)/(1-edgeComplexRoot b B u (q i)^2)) *
    (∏ ij∈firstStrictPairs N,
      angularRootPair (edgeComplexRoot b B u (q ij.1)) (edgeComplexRoot b B u (q ij.2))
        (q ij.1) (q ij.2))) *
    ((1+∏ i,edgeComplexRoot b B u (q i))/(1-∏ i,edgeComplexRoot b B u (q i)))

@[simp] theorem complexDensity_real {N : ℕ} (b : ℝ) (B S : ℂ → ℂ) (u : ℂ) (q : Fin N → ℝ) :
    complexDensity b B S u (fun i => (q i:ℂ)) = edgeAngularDensity b B S u q := by
  simp only [complexDensity,edgeComplexRoot_real,edgeAngularDensity,edgeAngularWeight,edgeRootProduct]

theorem edgeRoot_norm_lt_one {b : ℝ} {B : ℂ → ℂ} {u : ℂ}
    (hu : 0 < u.im) (hB : 0 < (B u).im) (q : ℝ) :
    ‖edgeParamRoot b B u q‖ < 1 := by
  have h := Transverse.dispersion_im_pos (b := b) hu hB q
  change 0 < (edgeParamW b B u q).im at h
  rw [edgeParamRoot,continuedRoot_eq_interiorRoot h]
  exact interiorRoot_norm_lt_one h

/-- Joint analyticity in the actual curve coordinate and every complex angle. -/
theorem complexDensity_joint_analyticAt {N : ℕ} (hN : 0 < N)
    {b : ℝ} {B S : ℂ → ℂ} {u : ℂ}
    (hBa : AnalyticAt ℂ B u) (hSa : AnalyticAt ℂ S u)
    (hu : 0 < u.im) (hB : 0 < (B u).im) (hS : S u ≠ 0) (q : Fin N → ℝ) :
    AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => complexDensity b B S x.1 x.2)
      (u,fun i => (q i:ℂ)) := by
  let p := (u,fun i => (q i:ℂ))
  have dq (i : Fin N) : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => x.2 i) p :=
    (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).analyticAt _ |>.comp analyticAt_snd
  have dB : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => B x.1) p :=
    hBa.comp (x := p) analyticAt_fst
  have dS : AnalyticAt ℂ (fun x : ℂ × (Fin N → ℂ) => S x.1) p :=
    hSa.comp (x := p) analyticAt_fst
  have dr (i : Fin N) : AnalyticAt ℂ
      (fun x : ℂ × (Fin N → ℂ) => edgeComplexRoot b B x.1 (x.2 i)) p := by
    have him := Transverse.dispersion_im_pos (b := b) hu hB (q i)
    apply AnalyticAt.fun_comp_of_eq
      (f := fun x : ℂ × (Fin N → ℂ) => (b:ℂ)+x.1+B x.1*(1-Complex.cos (x.2 i)))
      (g := continuedRoot) (continuedRoot_analyticAt (Or.inl (Or.inl him)))
      ((analyticAt_const.add analyticAt_fst).add
        (dB.mul (analyticAt_const.sub (Complex.analyticAt_cos.comp (dq i)))))
    simp [dispersion,Complex.ofReal_cos,p]
  have hn (i : Fin N) : ‖edgeComplexRoot b B u (q i:ℂ)‖ < 1 := by
    simpa using edgeRoot_norm_lt_one (b := b) hu hB (q i)
  have hpair (i j : Fin N) : 1-edgeComplexRoot b B u (q i:ℂ)*edgeComplexRoot b B u (q j:ℂ)≠0 :=
    one_sub_mul_ne_zero_of_norm_lt_one (hn i) (hn j)
  have hZ : 1-∏ i,edgeComplexRoot b B u (q i:ℂ)≠0 :=
    one_sub_coordinateProduct_ne_zero hN hn
  have dZ := Finset.univ.analyticAt_fun_prod (fun i _ => dr i)
  unfold complexDensity
  refine (((((dB.pow _).mul ((dS.inv hS).pow _)).mul ?_).mul ?_)).mul
    ((analyticAt_const.add dZ).div (analyticAt_const.sub dZ) hZ)
  · apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact (analyticAt_const.mul (dr i)).div (analyticAt_const.sub ((dr i).pow 2))
      (by simpa only [pow_two] using hpair i i)
  · apply (firstStrictPairs N).analyticAt_fun_prod
    intro ij _
    exact ((((analyticAt_const.mul (dr ij.1)).mul (dr ij.2)).mul
      ((Complex.analyticAt_sin.comp (((dq ij.1).sub (dq ij.2)).div_const)).pow 2))).div
        ((analyticAt_const.sub ((dr ij.1).mul (dr ij.2))).pow 2) (pow_ne_zero _ (hpair ij.1 ij.2))

/-- `n` is the number of independent angles; particle number is `n+1`.
The normalization is the original factorial and exactly `n` angular measures. -/
def angularCoefficient (n : ℕ) (b : ℝ) (B S : ℂ → ℂ) (u : ℂ) : ℂ :=
  edgeCoefficientNormalization n *
    ∫ q in edgeCenteredCube n, edgeAngularDensity b B S u (shapeExtend q)

section Interior
variable {b : ℝ} {B S : ℂ → ℂ} {U : Set ℂ}
variable (hU : IsOpen U) (hBa : AnalyticOnNhd ℂ B U) (hSa : AnalyticOnNhd ℂ S U)
  (hu : ∀ u ∈ U, 0 < u.im) (hBi : ∀ u ∈ U, 0 < (B u).im) (hS : ∀ u ∈ U, S u ≠ 0)
include hU hBa hSa hu hBi hS

/-- All genuine derivatives pass through the complete constrained integral. -/
theorem angularCoefficient_iteratedDeriv (n j : ℕ) {u : ℂ} (huU : u ∈ U) :
    iteratedDeriv j (angularCoefficient n b B S) u =
      edgeCoefficientNormalization n * edgeFullDerivativeIntegral (n := n) b B S j u := by
  let K := edgeCenteredCube n
  let psi : (Fin n → ℝ) → (Fin (n+1) → ℂ) := fun q i => ((shapeExtend q i:ℝ):ℂ)
  let C := edgeCoefficientNormalization n
  let F : ℂ × (Fin (n+1) → ℂ) → ℂ := fun p => complexDensity b B S p.1 p.2
  have hp : Continuous psi := by unfold psi shapeExtend; fun_prop
  have hF : ∀ v ∈ U, ∀ q ∈ K, AnalyticAt ℂ F (v,psi q) := by
    intro v hv q _
    exact complexDensity_joint_analyticAt (by omega) (hBa v hv) (hSa v hv)
      (hu v hv) (hBi v hv) (hS v hv) (shapeExtend q)
  have he : angularCoefficient n b B S = (fun v => ∫ q in K, C*F (v,psi q)) := by
    funext v
    simp only [angularCoefficient,K,C,F,psi,complexDensity_real,integral_const_mul]
  rw [he]
  have hj := compact_bounded_weight_integral_iteratedDeriv (μ := volume) (K := K)
    isCompact_Icc hU F psi hp hF (fun _ => C) aestronglyMeasurable_const
    (norm_nonneg C) (Eventually.of_forall (fun _ => le_refl ‖C‖)) j huU
  rw [hj,integral_const_mul]
  simp only [edgeFullDerivativeIntegral,edgeConstrainedJet,K,C,F,psi,complexDensity_real]

/-- Analyticity is proved from the integral, not supplied as a curve conclusion. -/
theorem angularCoefficient_analyticAt (n : ℕ) {u : ℂ} (huU : u ∈ U) :
    AnalyticAt ℂ (angularCoefficient n b B S) u := by
  let K := edgeCenteredCube n
  let psi : (Fin n → ℝ) → (Fin (n+1) → ℂ) := fun q i => ((shapeExtend q i:ℝ):ℂ)
  let F : ℂ × (Fin (n+1) → ℂ) → ℂ := fun p => complexDensity b B S p.1 p.2
  have hp : Continuous psi := by unfold psi shapeExtend; fun_prop
  have hF : ∀ v ∈ U, ∀ q ∈ K, AnalyticAt ℂ F (v,psi q) := by
    intro v hv q _
    exact complexDensity_joint_analyticAt (by omega) (hBa v hv) (hSa v hv)
      (hu v hv) (hBi v hv) (hS v hv) (shapeExtend q)
  have ha := compact_analytic_shape_integral_analyticAt (μ := volume) (K := K)
    isCompact_Icc hU F psi hp (fun _ => edgeCoefficientNormalization n) continuous_const hF huU
  simpa only [F,psi,K,complexDensity_real,integral_const_mul,angularCoefficient] using! ha
end Interior

end
end IsingBulk.Joint.RegularEdges
