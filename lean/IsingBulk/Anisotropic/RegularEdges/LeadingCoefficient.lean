import IsingBulk.Anisotropic.RegularEdges.LeadingFinite
import IsingBulk.Anisotropic.RegularEdges.PositiveIntegratedCoefficient

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour Set Filter Metric MeasureTheory
open scoped Topology BigOperators

theorem edgeAngularWeight_eq_edgeNumerator {N : ℕ} (b : ℝ) (B S : ℂ→ℂ)
    (u : ℂ) (q : Fin N→ℝ) :
    edgeAngularWeight b B S u q=edgeNumerator b B S u (List.ofFn q) := by
  rw [edgeNumerator_eq_indexed]
  simp [edgeAngularWeight,firstStrictPairs,Finset.prod_filter,Fintype.prod_prod_type]

theorem complexAngularDensity_eq_edgeAngularDensity {N : ℕ}
    {lam b : ℝ} {B S : ℂ→ℂ} {z u : ℂ}
    (hB : B u=spectralT lam z/spectralS z) (hS : S u=spectralS z)
    (he : edgeMapV lam 1 z=(b:ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im)
    (q : Fin N→ℝ) :
    complexAngularDensity lam z (fun i => (q i:ℂ))=edgeAngularDensity b B S u q := by
  unfold complexAngularDensity edgeAngularDensity
  rw [edgeAngularWeight_eq_edgeNumerator,complexAngularWeight_eq_edgeNumerator hB hS he hu hBi]
  simp_rw [transferRoot_eq_edgeParamRoot hB he hu hBi]
  rfl

def edgeCoefficientNormalization (n : ℕ) : ℂ :=
  ((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n

def edgeCoefficientLeading (n k : ℕ) (b : ℝ) (B S : ℂ→ℂ) : ℂ :=
  edgeCoefficientNormalization n*edgeFullLeadingCoefficient n k b B S

theorem edgeCoefficientNormalization_ne_zero (n : ℕ) : edgeCoefficientNormalization n≠0 := by
  have hf : ((n+1).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (n+1)
  exact mul_ne_zero (inv_ne_zero hf) (pow_ne_zero _ (inv_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))

section Chart
variable {lam b : ℝ} {U : Set ℂ} {zeta B S : ℂ→ℂ}
variable (hU : IsOpen U) (ha : AnalyticOnNhd ℂ zeta U)
  (hz : ∀u∈U,zeta u∉spectralSet lam) (hs : ∀u∈U,spectralS (zeta u)≠0)
  (hB : ∀u∈U,B u=spectralT lam (zeta u)/spectralS (zeta u))
  (hS : ∀u∈U,S u=spectralS (zeta u))
  (he : ∀u∈U,edgeMapV lam 1 (zeta u)=(b:ℂ)+u)
  (hup : ∀u∈U,0<u.im) (hBi : ∀u∈U,0<(B u).im)

include hU ha hz hs hB hS he hup hBi

theorem unscaledAngularCoefficient_fullJet_eq (n j : ℕ) {u : ℂ} (hu : u∈U) :
    iteratedDeriv j (fun v => unscaledAngularCoefficient n lam (zeta v)) u=
      edgeCoefficientNormalization n*edgeFullDerivativeIntegral (n := n) b B S j u := by
  rw [unscaledAngularCoefficient_comp_iteratedDeriv n j hU ha hz hs hu]
  unfold edgeCoefficientNormalization edgeFullDerivativeIntegral edgeCenteredCube
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro q
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [hU.mem_nhds hu] with v hv
  exact complexAngularDensity_eq_edgeAngularDensity (hB v hv) (hS v hv)
    (he v hv) (hup v hv) (hBi v hv) (physicalDependentAngles n q)

theorem unscaledAngularCoefficient_first_leading_limit {n k a : ℕ} (ha' : 0<a)
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    (hb : |b|<1) (hBa : AnalyticAt ℂ B 0) (hBi0 : 0<(B 0).im)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hres : continuedRoot (b:ℂ)^(n+1)=1)
    (hin : ∀ᶠ t : ℝ in 𝓝[>] 0,Complex.I*(t:ℂ)^2∈U) :
    Tendsto (fun t : ℝ => (t^a) •
      iteratedDeriv k (fun v => unscaledAngularCoefficient n lam (zeta v)) (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 (edgeCoefficientLeading n k b B S)) := by
  have hh := (edgeFullDerivativeIntegral_leading_limit ha' hbalance hmajorant hb hBa hBi0 hSa hS0 hres).const_mul
    (edgeCoefficientNormalization n)
  apply hh.congr'
  filter_upwards [hin] with t ht
  rw [unscaledAngularCoefficient_fullJet_eq hU ha hz hs hB hS he hup hBi n k ht]
  rw [mul_smul_comm]

theorem unscaledAngularCoefficient_first_lower_limit {n k a j : ℕ} (ha' : 0<a) (hj : j<k)
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    (hb : |b|<1) (hBa : AnalyticAt ℂ B 0) (hBi0 : 0<(B 0).im)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hres : continuedRoot (b:ℂ)^(n+1)=1)
    (hin : ∀ᶠ t : ℝ in 𝓝[>] 0,Complex.I*(t:ℂ)^2∈U) :
    Tendsto (fun t : ℝ => (t^a) •
      iteratedDeriv j (fun v => unscaledAngularCoefficient n lam (zeta v)) (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 0) := by
  have hh := (edgeFullDerivativeIntegral_lower_limit ha' hj hbalance hmajorant hb hBa hBi0 hSa hS0 hres).const_mul
    (edgeCoefficientNormalization n)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hin] with t ht
  rw [unscaledAngularCoefficient_fullJet_eq hU ha hz hs hB hS he hup hBi n j ht]
  rw [mul_smul_comm]

end Chart
end
end IsingBulk.Anisotropic.RegularEdges
