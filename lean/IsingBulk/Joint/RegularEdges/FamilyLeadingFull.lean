import IsingBulk.Joint.RegularEdges.FamilyLeadingComplement
import IsingBulk.Joint.RegularEdges.FamilyFiniteDecomposition

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges MeasureTheory Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complete angular coefficient, including its full lattice resolvent,
has the joint scaled leading limit. No local term substitutes for it. -/
theorem compact_family_fullCoefficient_joint_limit {n k a : ℕ} (ha : 0<a)
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    {b : ℝ} (B S : ℂ × E → ℂ) (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    ∀eta₀∈Q,Tendsto (fun p : ℝ × E => (p.1^a) •
      iteratedDeriv k (angularCoefficient n b (fun u=>B (u,p.2)) (fun u=>S (u,p.2)))
        (Complex.I*(p.1:ℂ)^2)) (𝓝[Ioi (0:ℝ) ×ˢ Q] (0,eta₀))
      (𝓝 (edgeCoefficientLeading n k b (fun u=>B (u,eta₀)) (fun u=>S (u,eta₀)))) := by
  obtain ⟨R,hR,hRπ,hlim⟩ := compact_family_actualLocal_joint_limit hbalance hmajorant B S hb hQ hB hBi hS hS0 hres
  obtain ⟨δ,hδ,hdecomp⟩ := compact_family_full_decomposition (n:=n) B S hb hQ hB hBi hS hS0 hR hRπ k
  obtain ⟨r,hr,hjet⟩ := compact_family_coefficient_jet_identity B S b hQ hB hBi hS hS0
  intro eta₀ heta₀
  have hcomp := (compact_family_complement_joint_limit (n:=n) ha B S hb hQ hB hBi hS hS0 hR k eta₀).const_mul
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
  rw [hjet p.2 hp.2 _ hu hi n k,
    hdecomp p.2 hp.2 p.1 hp.1 (hpt.trans_le (min_le_left _ _)),
    normalizedActualLocalDerivative]
  simp only [Complex.real_smul]
  ring

/-- Genuine uniform full-coefficient asymptotics on a compact complex family.
This is the explicit epsilon-delta form of uniform convergence. -/
theorem compact_family_fullCoefficient_uniform_limit {n k a : ℕ} (ha : 0<a)
    (hbalance : n+a+(n+1)*n=2*(k+1)) (hmajorant : Integrable (@shapeMajorant n k))
    {b : ℝ} (B S : ℂ × E → ℂ) (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1)
    (hperiod : ContinuousOn (shapePeriod n k ((n+1)/Real.sqrt (1-b^2))) {c : ℂ | 0<c.re}) :
    ∀ε : ℝ,0<ε → ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ →
      ‖(t^a) • iteratedDeriv k (angularCoefficient n b (fun u=>B (u,eta)) (fun u=>S (u,eta)))
          (Complex.I*(t:ℂ)^2)-edgeCoefficientLeading n k b (fun u=>B (u,eta)) (fun u=>S (u,eta))‖<ε :=
  compact_joint_limit_uniform hQ
    (family_leadingCoefficient_continuousOn B S hb hB hBi hS hS0 hres hperiod)
    (compact_family_fullCoefficient_joint_limit ha hbalance hmajorant B S hb hQ hB hBi hS hS0 hres)

/-- Even-particle family limit: all model integrability and continuity premises
are discharged from the exact resonance degree. -/
theorem even_compact_family_fullCoefficient_uniform_limit {n k : ℕ} (hn : 1≤n)
    (hdegree : n-1+(n+1)*n=2*k) {b : ℝ} (B S : ℂ × E → ℂ) (hb : |b|<1)
    {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    ∀ε : ℝ,0<ε → ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ →
      ‖t • iteratedDeriv k (angularCoefficient n b (fun u=>B (u,eta)) (fun u=>S (u,eta)))
          (Complex.I*(t:ℂ)^2)-edgeCoefficientLeading n k b (fun u=>B (u,eta)) (fun u=>S (u,eta))‖<ε := by
  have hb' := abs_lt.mp hb
  have hP : 0<(n+1:ℝ)/Real.sqrt (1-b^2) := div_pos (by positivity) (Real.sqrt_pos.mpr (by nlinarith))
  simpa only [pow_one] using compact_family_fullCoefficient_uniform_limit (a:=1) (by omega)
    (by omega) (shapeMajorant_integrable hn hdegree) B S hb hQ hB hBi hS hS0 hres
    (even_shapePeriod_continuousOn hn hdegree hP)

/-- Odd-particle family limit, retaining the exact integer-power branch and
all physical normalization constants. -/
theorem odd_compact_family_fullCoefficient_uniform_limit {n m : ℕ} (hn : 1≤n)
    (hdegree : n-1+(n+1)*n=2*m+1) {b : ℝ} (B S : ℂ × E → ℂ) (hb : |b|<1)
    {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)=1) :
    ∀ε : ℝ,0<ε → ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀t : ℝ,0<t → t<δ →
      ‖(t^2) • iteratedDeriv (m+1) (angularCoefficient n b (fun u=>B (u,eta)) (fun u=>S (u,eta)))
          (Complex.I*(t:ℂ)^2)-edgeCoefficientLeading n (m+1) b (fun u=>B (u,eta)) (fun u=>S (u,eta))‖<ε := by
  have hb' := abs_lt.mp hb
  have hP : 0<(n+1:ℝ)/Real.sqrt (1-b^2) := div_pos (by positivity) (Real.sqrt_pos.mpr (by nlinarith))
  exact compact_family_fullCoefficient_uniform_limit (a:=2) (by omega)
    (by omega) (shapeMajorant_odd_integrable hn hdegree) B S hb hQ hB hBi hS hS0 hres
    (odd_shapePeriod_continuousOn hn hdegree hP)

end
end IsingBulk.Joint.RegularEdges
