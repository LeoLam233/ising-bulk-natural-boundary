import IsingBulk.Joint.Negative.FamilyWindingWitness
import IsingBulk.Joint.Negative.FamilyWindingOverhead
import IsingBulk.Anisotropic.NegativeCycles.ActualWitnessWindingBounds
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open IsingBulk.Anisotropic.NegativeCycles
namespace IsingBulk.Joint.Negative
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeDominance
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators

/-- Every actual physical-decomposition witness has the higher-winding bound;
no separately constructed pole is substituted. -/
theorem compact_family_witness_higher_winding (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hrB : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta))
    (hB0 : ∀eta∈Q,B (0,eta)≠0) (hr0 : ∀eta∈Q,rootB (0,eta)≠0) (rP CP : ℝ) (hrP : 0<rP) :
    ∃r C : ℝ,0<r ∧ 0<C ∧ ∃N0 : ℕ,∀eta∈Q,∀n : ℕ,N0≤n → 2≤n → Odd (n+1) → ∀d : ℝ,
      |d|<r → |d|≤Real.pi → 3*Real.pi/(n+1)≤|d| →
      ∀P : UniformProjectedWitness (familyMember B eta) phi hphi (n+1) (d:ℂ) rP CP,
      ∀s : ℝ,s≤r^2 → ∀j : ℕ,4*alpha (n+1)≤j →
        ‖∫x in centeredInnerSet n d s,
          constrainedResidueDensity (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T j (complexify n x)‖≤
          Real.exp (C*(n+1)^2)*(1/2:ℝ)^(j/2)*
            ‖model (familyMember B eta (tau (n+1))) (familyMember rootB eta (tau (n+1)))
              (hessianFactor (familyMember B eta (tau (n+1))) (Real.cos phi) (Real.sin phi) (n+1))
              (Real.sin phi) (n+1) j‖ := by
  obtain ⟨r,M,c,hr,hM,hc,hpole⟩ := compact_family_witness_beta_integral B rootB phi hphi hQ hB hrB hB0 rP CP hrP
  obtain ⟨C,hC,hOver⟩ := compact_family_winding_overhead B rootB phi M c hQ hB hB0 hrB hr0 hphi hM hc
  obtain ⟨L,_hL,hlogs⟩ := compact_family_winding_log_bounds B rootB phi hQ hB hB0 hrB hr0
  have he : ∀ᶠN : ℕ in atTop,∀eta∈Q,
      higherWindingOverhead M c (B (tau N,eta)) (rootB (tau N,eta))
        (hessianFactor (B (tau N,eta)) (Real.cos phi) (Real.sin phi) N) (Real.sin phi) N≤Real.exp (C*(N:ℝ)^2) ∧
      B (tau N,eta)≠0 ∧ rootB (tau N,eta)≠0 ∧ hessianFactor (B (tau N,eta)) (Real.cos phi) (Real.sin phi) N≠0 := by
    filter_upwards [hOver,hlogs] with N hN hl eta heta
    have hh := hl eta heta
    exact ⟨hN eta heta,hh.1,hh.2.1,hh.2.2.1⟩
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp he
  refine ⟨r,C,hr,hC,N0,?_⟩
  intro eta heta n hn0 hn ho d hd hdπ hdw
  have hu := higher_winding_tau_gap (n+1) (by omega) d hdπ (by simpa using hdw)
  have htfirst := tau_pos (n+1) (by omega)
  have ht : 0<1-Real.cos d := lt_of_lt_of_le (by positivity : 0<2*tau (n+1)) hu
  intro P s hs j hj
  have hest := hpole eta heta n hn ho d hd ht P (centeredInnerSet n d s)
    (centeredInnerSet_measurable n d s)
    (centeredInnerSet_subset_smallConstrainedEnergyBall n d s r hs) (fun _=>1)
    (fun _ _=>by norm_num) j (by omega)
  simp only [one_mul] at hest
  have hN := hN0 (n+1) (by omega) eta heta
  have hbeta := higher_winding_beta_model_bound M c (familyMember B eta (tau (n+1))) (familyMember rootB eta (tau (n+1)))
    (hessianFactor (familyMember B eta (tau (n+1))) (Real.cos phi) (Real.sin phi) (n+1)) (Real.sin phi)
    ho (by omega) hj (by linarith) hc hN.2.1 hN.2.2.1 hN.2.2.2 hphi hu
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hN.1 (show 0≤(1/2 : ℝ)^(j/2) by positivity))
    (norm_nonneg (model (familyMember B eta (tau (n+1))) (familyMember rootB eta (tau (n+1)))
      (hessianFactor (familyMember B eta (tau (n+1))) (Real.cos phi) (Real.sin phi) (n+1)) (Real.sin phi) (n+1) j))
  exact hest.trans (by simpa using hbeta.trans hbound)


/-- The all-order entropy estimate on the exact centered physical sector,
using the same actual P.T as the residue decomposition. -/
theorem compact_family_witness_high_entropy (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hrB : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta))
    (hB0 : ∀eta∈Q,B (0,eta)≠0) (rP CP : ℝ) (hrP : 0<rP) :
    ∃ρ C : ℝ,0<ρ ∧ ρ≤1 ∧ 0<C ∧ ∀eta∈Q,∀n : ℕ,1≤n → ∀d : ℝ,
      |d|<ρ → Real.pi/((n+1:ℕ):ℝ)≤|d| →
      ∀P : UniformProjectedWitness (familyMember B eta) phi hphi (n+1) (d:ℂ) rP CP,
      ∀s : ℝ,s≤ρ^2 → ∀j : ℕ,
        ‖∫x in centeredInnerSet n d s,
          constrainedResidueDensity (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T j (complexify n x)‖≤
          Real.exp (2*j*Real.log (n+1)-(n+1:ℝ)^2/2*Real.log (n+1)+C*(n+1:ℝ)^2) := by
  obtain ⟨ρ,M,c,hρ,hρ1,hM,hc,hbound⟩ :=
    compact_family_witness_high_integral B rootB phi hphi hQ hB hrB hB0 rP CP hrP
  obtain ⟨C,hC,hentropy⟩ := highPoleEnvelope_entropy M c hM hc
  refine ⟨ρ,C,hρ,hρ1,hC,?_⟩
  intro eta heta n hn d hd hw P s hs j
  have hh := hbound eta heta n hn d hd hw P (centeredInnerSet n d s)
    (centeredInnerSet_subset_smallConstrainedEnergyBall n d s ρ hs) (fun _=>1)
    (fun _ _=>by norm_num) j
  simp only [one_mul] at hh
  apply hh.trans
  simpa only [highPoleEnvelope,Nat.cast_add,Nat.cast_one] using hentropy (n+1) (by omega) j

end IsingBulk.Joint.Negative
