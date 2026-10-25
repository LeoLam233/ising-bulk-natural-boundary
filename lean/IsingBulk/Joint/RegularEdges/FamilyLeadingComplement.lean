import IsingBulk.Joint.RegularEdges.FamilyLeadingActualLocal
import IsingBulk.Joint.RegularEdges.FamilyFiniteComplement

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges MeasureTheory Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Common complement bounds imply joint scaled vanishing, allowing the
complex family parameter to vary simultaneously with the inward coordinate. -/
theorem compact_family_complement_joint_limit {n a : ℕ} (ha : 0<a)
    {b : ℝ} (B S : ℂ × E → ℂ) (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    {R : ℝ} (hR : 0<R) (j : ℕ) (eta₀ : E) :
    Tendsto (fun p : ℝ × E => (p.1^a) • edgeComplementDerivativeIntegral (n:=n)
      b (fun u=>B (u,p.2)) (fun u=>S (u,p.2)) j R (Complex.I*(p.1:ℂ)^2))
      (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀)) (𝓝 0) := by
  obtain ⟨δ,C,hδ,_hC,hbound⟩ := compact_family_complement_integral_bound (n:=n) B S hb hQ hB hBi hS hS0 hR j
  have ht : Tendsto (fun p : ℝ × E => p.1) (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀)) (𝓝 0) :=
    continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun p : ℝ × E => Complex.I*(p.1:ℂ)^2)
      (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀)) (𝓝 0) := by
    simpa using! ((Complex.continuous_ofReal.continuousAt.tendsto.comp ht).pow 2).const_mul Complex.I
  apply squeeze_zero_norm' (a:=fun p : ℝ × E => ‖p.1^a‖*C)
  · filter_upwards [self_mem_nhdsWithin,
      hu.norm.eventually (eventually_lt_nhds (by simpa using hδ))] with p hp hup
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hbound p.2 hp.2 _ hup) (norm_nonneg _)
  · simpa [zero_pow (Nat.ne_of_gt ha)] using! ((ht.pow a).norm.mul_const C)

/-- The exact leading coefficient is continuous in the complex parameter on
the given family, even for nonconstant B and S. -/
theorem family_leadingCoefficient_continuousOn {n k : ℕ} {b : ℝ}
    (B S : ℂ × E → ℂ) (hb : |b|<1) {Q : Set E}
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1)
    (hperiod : ContinuousOn (shapePeriod n k ((n+1)/Real.sqrt (1-b^2))) {c : ℂ | 0<c.re}) :
    ContinuousOn (fun eta=>edgeCoefficientLeading n k b (fun u=>B (u,eta)) (fun u=>S (u,eta))) Q := by
  have he : (fun eta=>edgeCoefficientLeading n k b (fun u=>B (u,eta)) (fun u=>S (u,eta)))=
      fun eta=>independentLeadingAmplitude n k b (B (0,eta),S (0,eta)) := by
    funext eta
    exact edgeCoefficientLeading_eq_center n k hb hres _ _
  rw [he]
  intro eta heta
  exact ((independentLeadingAmplitude_continuousAt hb hres hperiod (hBi eta heta) (hS0 eta heta)).comp
    (((hB eta heta).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt).prodMk
      ((hS eta heta).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt))).continuousWithinAt

end
end IsingBulk.Joint.RegularEdges
