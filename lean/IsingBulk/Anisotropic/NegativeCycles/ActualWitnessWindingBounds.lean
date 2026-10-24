import IsingBulk.Anisotropic.NegativeCycles.ActualWitnessPoleBounds
import IsingBulk.Anisotropic.NegativeDominance.ActualHigherWinding
import IsingBulk.Anisotropic.NegativeDominance.ActualHighEntropy

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeDominance
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators

/-- Every actual physical-decomposition witness has the higher-winding bound;
no separately constructed pole is substituted. -/
theorem actualWitness_higher_winding_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hrB : AnalyticAt ℂ rootB 0)
    (hB0 : B 0≠0) (hr0 : rootB 0≠0) (rP CP : ℝ) (hrP : 0<rP) :
    ∃r C : ℝ,0<r ∧ 0<C ∧ ∃N0 : ℕ,∀n : ℕ,N0≤n → 2≤n → Odd (n+1) → ∀d : ℝ,
      |d|<r → |d|≤Real.pi → 3*Real.pi/(n+1)≤|d| →
      ∀P : UniformProjectedWitness B phi hphi (n+1) (d:ℂ) rP CP,
      ∀s : ℝ,s≤r^2 → ∀j : ℕ,4*alpha (n+1)≤j →
        ‖∫x in centeredInnerSet n d s,
          constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j (complexify n x)‖≤
          Real.exp (C*(n+1)^2)*(1/2:ℝ)^(j/2)*
            ‖model (B (tau (n+1))) (rootB (tau (n+1)))
              (hessianFactor (B (tau (n+1))) (Real.cos phi) (Real.sin phi) (n+1))
              (Real.sin phi) (n+1) j‖ := by
  obtain ⟨r,M,c,hr,hM,hc,hpole⟩ := actualWitness_pole_beta_integral_bound B rootB phi hphi hB hrB hB0 rP CP hrP
  obtain ⟨C,hC,hOver⟩ := physical_higherWindingOverhead_entropy B rootB phi M c hB hB0
    hrB.continuousAt hr0 hphi hM hc
  have he : ∀ᶠ N : ℕ in atTop,
      higherWindingOverhead M c (B (tau N)) (rootB (tau N))
        (hessianFactor (B (tau N)) (Real.cos phi) (Real.sin phi) N) (Real.sin phi) N≤Real.exp (C*(N : ℝ)^2) ∧
      B (tau N)≠0 ∧ rootB (tau N)≠0 ∧ hessianFactor (B (tau N)) (Real.cos phi) (Real.sin phi) N≠0 := by
    filter_upwards [hOver,tau_complex_tendsto_zero.eventually (hB.continuousAt.eventually_ne hB0),
      tau_complex_tendsto_zero.eventually (hrB.continuousAt.eventually_ne hr0),hessianFactor_eventually_nonzero B phi hB]
      with N hN hb hr' hH using ⟨hN,hb,hr',hH⟩
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp he
  refine ⟨r,C,hr,hC,N0,?_⟩
  intro n hn0 hn ho d hd hdπ hdw
  have hu := higher_winding_tau_gap (n+1) (by omega) d hdπ (by simpa using hdw)
  have htfirst := tau_pos (n+1) (by omega)
  have ht : 0<1-Real.cos d := lt_of_lt_of_le (by positivity : 0<2*tau (n+1)) hu
  intro P s hs j hj
  have hest := hpole n hn ho d hd ht P (centeredInnerSet n d s)
    (centeredInnerSet_measurable n d s)
    (centeredInnerSet_subset_smallConstrainedEnergyBall n d s r hs) (fun _=>1)
    (fun _ _=>by norm_num) j (by omega)
  simp only [one_mul] at hest
  have hN := hN0 (n+1) (by omega)
  have hbeta := higher_winding_beta_model_bound M c (B (tau (n+1))) (rootB (tau (n+1)))
    (hessianFactor (B (tau (n+1))) (Real.cos phi) (Real.sin phi) (n+1)) (Real.sin phi)
    ho (by omega) hj (by linarith) hc hN.2.1 hN.2.2.1 hN.2.2.2 hphi hu
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hN.1 (show 0≤(1/2 : ℝ)^(j/2) by positivity))
    (norm_nonneg (model (B (tau (n+1))) (rootB (tau (n+1)))
      (hessianFactor (B (tau (n+1))) (Real.cos phi) (Real.sin phi) (n+1)) (Real.sin phi) (n+1) j))
  exact hest.trans (by simpa using hbeta.trans hbound)


/-- The all-order entropy estimate on the exact centered physical sector,
using the same actual P.T as the residue decomposition. -/
theorem actualWitness_high_pole_entropy_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hrB : AnalyticAt ℂ rootB 0)
    (hB0 : B 0≠0) (rP CP : ℝ) (hrP : 0<rP) :
    ∃ρ C : ℝ,0<ρ ∧ ρ≤1 ∧ 0<C ∧ ∀n : ℕ,1≤n → ∀d : ℝ,
      |d|<ρ → Real.pi/((n+1:ℕ):ℝ)≤|d| →
      ∀P : UniformProjectedWitness B phi hphi (n+1) (d:ℂ) rP CP,
      ∀s : ℝ,s≤ρ^2 → ∀j : ℕ,
        ‖∫x in centeredInnerSet n d s,
          constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j (complexify n x)‖≤
          Real.exp (2*j*Real.log (n+1)-(n+1:ℝ)^2/2*Real.log (n+1)+C*(n+1:ℝ)^2) := by
  obtain ⟨ρ,M,c,hρ,hρ1,hM,hc,hbound⟩ :=
    actualWitness_high_pole_integral_bound B rootB phi hphi hB hrB hB0 rP CP hrP
  obtain ⟨C,hC,hentropy⟩ := highPoleEnvelope_entropy M c hM hc
  refine ⟨ρ,C,hρ,hρ1,hC,?_⟩
  intro n hn d hd hw P s hs j
  have hh := hbound n hn d hd hw P (centeredInnerSet n d s)
    (centeredInnerSet_subset_smallConstrainedEnergyBall n d s ρ hs) (fun _=>1)
    (fun _ _=>by norm_num) j
  simp only [one_mul] at hh
  apply hh.trans
  simpa only [highPoleEnvelope,Nat.cast_add,Nat.cast_one] using hentropy (n+1) (by omega) j

end IsingBulk.Anisotropic.NegativeCycles
