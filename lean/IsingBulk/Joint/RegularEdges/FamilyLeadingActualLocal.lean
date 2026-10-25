import IsingBulk.Joint.RegularEdges.FamilyLeadingLocal
import IsingBulk.Joint.RegularEdges.FamilyLeadingUniform
import IsingBulk.Joint.RegularEdges.CompactLeadingAmplitude

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges MeasureTheory Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def normalizedActualLocalDerivative (n k : ℕ) (b : ℝ) (B S : ℂ→ℂ) (R t : ℝ) : ℂ :=
  edgeCoefficientNormalization n * ((Real.sqrt (n+1))⁻¹ •
    edgeActualLocalDerivativeIntegral (n:=n) b B S k R t)

/-- Joint, not merely fiberwise, convergence of the actual local derivative
integral with the exact physical angular normalization. -/
theorem compact_family_actualLocal_joint_limit {n k a : ℕ}
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    {b : ℝ} (B S : ℂ × E → ℂ) (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    ∃R : ℝ,0<R ∧ R≤Real.pi ∧ ∀R' : ℝ,0<R' → R'≤R → ∀eta₀∈Q,
      Tendsto (fun p : ℝ × E => (p.1^a) • normalizedActualLocalDerivative n k b
        (fun u=>B (u,p.2)) (fun u=>S (u,p.2)) R' p.1)
        (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀))
        (𝓝 (edgeCoefficientLeading n k b (fun u=>B (u,eta₀)) (fun u=>S (u,eta₀)))) := by
  obtain ⟨R,hR,hRπ,hlim⟩ := compact_family_localJet_joint_limit hbalance hmajorant B S hb hQ hB hBi hS hS0 hres
  obtain ⟨r,δ,hr,hδ,hrπ,heq⟩ := compact_family_actualLocal_eq (n:=n) B S hb hQ hB hBi hS hS0
  refine ⟨min R r,lt_min hR hr,(min_le_left _ _).trans hRπ,?_⟩
  intro R' hR' hR'R eta₀ heta₀
  have hh := ((hlim R' hR' (hR'R.trans (min_le_left _ _)) eta₀ heta₀).const_smul
    ((Real.sqrt (n+1))⁻¹)).const_mul (edgeCoefficientNormalization n)
  have hh' : Tendsto (fun p : ℝ × E => (p.1^a) • (edgeCoefficientNormalization n *
      ((Real.sqrt (n+1))⁻¹ • edgeLocalJetIntegral (n:=n) b (fun u=>B (u,p.2)) (fun u=>S (u,p.2)) k R' p.1)))
      (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀))
      (𝓝 (edgeCoefficientLeading n k b (fun u=>B (u,eta₀)) (fun u=>S (u,eta₀)))) := by
    convert hh using 1
    · funext p
      simp only [Complex.real_smul]
      ring
    · rfl
  apply hh'.congr'
  have ht : Tendsto (fun p : ℝ × E => p.1) (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀)) (𝓝 0) :=
    continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,ht.eventually (eventually_lt_nhds hδ)] with p hp hpt
  rw [normalizedActualLocalDerivative,heq p.2 hp.2 R' hR' (hR'R.trans (min_le_right _ _)) k p.1 hp.1 hpt]

/-- Uniform scaled leading limit over every compact complex admissible family.
All cutoff radii and epsilon-delta radii precede the family parameter. -/
theorem compact_family_actualLocal_uniform_limit {n k a : ℕ}
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    {b : ℝ} (B S : ℂ × E → ℂ) (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1)
    (hperiod : ContinuousOn (shapePeriod n k ((n+1)/Real.sqrt (1-b^2))) {c : ℂ | 0<c.re}) :
    ∃R : ℝ,0<R ∧ R≤Real.pi ∧ ∀R' : ℝ,0<R' → R'≤R →
      ∀ε : ℝ,0<ε → ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ →
        ‖(t^a) • normalizedActualLocalDerivative n k b (fun u=>B (u,eta)) (fun u=>S (u,eta)) R' t-
          edgeCoefficientLeading n k b (fun u=>B (u,eta)) (fun u=>S (u,eta))‖<ε := by
  obtain ⟨R,hR,hRπ,hlim⟩ := compact_family_actualLocal_joint_limit hbalance hmajorant B S hb hQ hB hBi hS hS0 hres
  refine ⟨R,hR,hRπ,?_⟩
  intro R' hR' hR'R
  apply compact_joint_limit_uniform hQ ?_ (hlim R' hR' hR'R)
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
