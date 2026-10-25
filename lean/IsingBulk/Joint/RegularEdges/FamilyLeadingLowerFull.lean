import IsingBulk.Joint.RegularEdges.FamilyLeadingLowerLocal
import IsingBulk.Joint.RegularEdges.FamilyLeadingFull

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges MeasureTheory Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Joint, not merely fiberwise, convergence of the actual local derivative
integral with the exact physical angular normalization. -/
theorem compact_family_lowerActualLocal_joint_limit {n k a j : ℕ} (hj : j<k)
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    {b : ℝ} (B S : ℂ × E → ℂ) (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    ∃R : ℝ,0<R ∧ R≤Real.pi ∧ ∀R' : ℝ,0<R' → R'≤R → ∀eta₀∈Q,
      Tendsto (fun p : ℝ × E => (p.1^a) • normalizedActualLocalDerivative n j b
        (fun u=>B (u,p.2)) (fun u=>S (u,p.2)) R' p.1)
        (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀))
        (𝓝 0) := by
  obtain ⟨R,hR,hRπ,hlim⟩ := compact_family_lowerLocalJet_joint_limit hj hbalance hmajorant B S hb hQ hB hBi hS hS0 hres
  obtain ⟨r,δ,hr,hδ,hrπ,heq⟩ := compact_family_actualLocal_eq (n:=n) B S hb hQ hB hBi hS hS0
  refine ⟨min R r,lt_min hR hr,(min_le_left _ _).trans hRπ,?_⟩
  intro R' hR' hR'R eta₀ heta₀
  have hh := ((hlim R' hR' (hR'R.trans (min_le_left _ _)) eta₀ heta₀).const_smul
    ((Real.sqrt (n+1))⁻¹)).const_mul (edgeCoefficientNormalization n)
  have hh' : Tendsto (fun p : ℝ × E => (p.1^a) • (edgeCoefficientNormalization n *
      ((Real.sqrt (n+1))⁻¹ • edgeLocalJetIntegral (n:=n) b (fun u=>B (u,p.2)) (fun u=>S (u,p.2)) j R' p.1)))
      (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀))
      (𝓝 0) := by
    convert hh using 1
    · funext p
      simp only [Complex.real_smul]
      ring
    · simp only [smul_zero,mul_zero]
  apply hh'.congr'
  have ht : Tendsto (fun p : ℝ × E => p.1) (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀)) (𝓝 0) :=
    continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,ht.eventually (eventually_lt_nhds hδ)] with p hp hpt
  rw [normalizedActualLocalDerivative,heq p.2 hp.2 R' hR' (hR'R.trans (min_le_right _ _)) j p.1 hp.1 hpt]

/-- The complete angular coefficient, including its full lattice resolvent,
has the joint scaled leading limit. No local term substitutes for it. -/
theorem compact_family_lowerFullCoefficient_joint_limit {n k a j : ℕ} (ha : 0<a) (hj : j<k)
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    {b : ℝ} (B S : ℂ × E → ℂ) (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    ∀eta₀∈Q,Tendsto (fun p : ℝ × E => (p.1^a) •
      iteratedDeriv j (angularCoefficient n b (fun u=>B (u,p.2)) (fun u=>S (u,p.2)))
        (Complex.I*(p.1:ℂ)^2)) (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀))
      (𝓝 0) := by
  obtain ⟨R,hR,hRπ,hlim⟩ := compact_family_lowerActualLocal_joint_limit hj hbalance hmajorant B S hb hQ hB hBi hS hS0 hres
  obtain ⟨δ,hδ,hdecomp⟩ := compact_family_full_decomposition (n:=n) B S hb hQ hB hBi hS hS0 hR hRπ j
  obtain ⟨r,hr,hjet⟩ := compact_family_coefficient_jet_identity B S b hQ hB hBi hS hS0
  intro eta₀ heta₀
  have hcomp := (compact_family_complement_joint_limit (n:=n) ha B S hb hQ hB hBi hS hS0 hR j eta₀).const_mul
    (edgeCoefficientNormalization n)
  have hh := (hlim R hR le_rfl eta₀ heta₀).add hcomp
  simp only [mul_zero,add_zero] at hh
  have ht : Tendsto (fun p : ℝ × E => p.1) (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀)) (𝓝 0) :=
    continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin,
    ht.eventually (eventually_lt_nhds (lt_min hδ (Real.sqrt_pos.mpr hr)))] with p hp hpt
  have htsq : p.1^2<r := by
    have hl := hpt.trans_le (min_le_right _ _)
    nlinarith [Real.sq_sqrt hr.le,show 0<p.1 from hp.1]
  have hu : ‖Complex.I*(p.1:ℂ)^2‖<r := by simpa using htsq
  have hi : 0<(Complex.I*(p.1:ℂ)^2).im := by
    simp only [←Complex.ofReal_pow,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
    exact sq_pos_of_pos hp.1
  rw [hjet p.2 hp.2 _ hu hi n j,
    hdecomp p.2 hp.2 p.1 hp.1 (hpt.trans_le (min_le_left _ _)),
    normalizedActualLocalDerivative]
  simp only [Complex.real_smul]
  ring

/-- Genuine uniform full-coefficient asymptotics on a compact complex family.
This is the explicit epsilon-delta form of uniform convergence. -/
theorem compact_family_lowerFullCoefficient_uniform_limit {n k a j : ℕ} (ha : 0<a) (hj : j<k)
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    {b : ℝ} (B S : ℂ × E → ℂ) (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    ∀ε : ℝ,0<ε → ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ →
      ‖(t^a) • iteratedDeriv j (angularCoefficient n b (fun u=>B (u,eta)) (fun u=>S (u,eta)))
          (Complex.I*(t:ℂ)^2)‖<ε := by
  simpa only [sub_zero] using compact_joint_limit_uniform hQ (continuousOn_const : ContinuousOn (fun _ : E => (0:ℂ)) Q)
    (compact_family_lowerFullCoefficient_joint_limit ha hj hbalance hmajorant B S hb hQ hB hBi hS hS0 hres)


end
end IsingBulk.Joint.RegularEdges
