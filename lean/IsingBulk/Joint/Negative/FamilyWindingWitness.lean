import IsingBulk.Joint.Negative.FamilyWindingBetaIntegrand
import IsingBulk.Joint.Negative.FamilyWindingIntegrand
import IsingBulk.Anisotropic.NegativeCycles.ActualWitnessPoleBounds

noncomputable section
namespace IsingBulk.Joint.Negative
open Set Filter Metric MeasureTheory IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeCycles IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
theorem projectedWitness_uniform_small_all (phi : ℝ) (hphi : Real.sin phi≠0)
    (r C ε : ℝ) (hr : 0<r) (hε : 0<ε) :
    ∃ρ : ℝ,0<ρ ∧ ρ≤r ∧ ρ≤ε ∧ ∀B : ℂ→ℂ,∀n : ℕ, ∀d : ℂ,‖d‖<ρ →
      ∀P : UniformProjectedWitness B phi hphi n d r C,
      ∀v : Config n,‖v‖<ρ →
        poleEquation B phi hphi d (P.T v) v=0 ∧ ‖P.T v‖<ε := by
  have ht : ContinuousAt (fun d : ℂ=>1-Complex.cos d) 0 := by fun_prop
  have he : ∀ᶠd : ℂ in 𝓝 0,‖1-Complex.cos d‖<ε/2 :=
    ht.norm.eventually_lt continuousAt_const (by simpa using half_pos hε)
  obtain ⟨a,ha,has⟩ := Metric.mem_nhds_iff.mp he
  let ρ := min a (min r (ε/4))
  have hρ : 0<ρ := lt_min ha (lt_min hr (by positivity))
  have hρa : ρ≤a := min_le_left _ _
  have hρr : ρ≤r := (min_le_right _ _).trans (min_le_left _ _)
  have hρε : ρ≤ε/4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ,hρ,hρr,by linarith,?_⟩
  intro B n d hd P v hv
  have hv2 : ‖v‖<2*r := by linarith
  refine ⟨(P.t_pole v hv2).1,?_⟩
  have htau := has (show d∈ball (0:ℂ) a by simpa using hd.trans_le hρa)
  change ‖1-Complex.cos d‖<ε/2 at htau
  have hl := P.t_lip v 0 hv2 (by simpa using (show 0<2*r by positivity))
  rw [P.t_zero,sub_zero] at hl
  have hh := norm_le_norm_sub_add (P.T v) (1-Complex.cos d)
  linarith


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The beta integral bound for the SAME actual P.T used by the physical winding
decomposition, uniformly for every projected witness. -/
theorem compact_family_witness_beta_integral (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hrB : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta))
    (hB0 : ∀eta∈Q,B (0,eta)≠0) (rP CP : ℝ) (hrP : 0<rP) :
    ∃ρ M c : ℝ,0<ρ ∧ 1≤M ∧ 0<c ∧ ∀eta∈Q,∀n : ℕ,2≤n → Odd (n+1) → ∀d : ℝ,
      |d|<ρ → 0<1-Real.cos d →
      ∀P : UniformProjectedWitness (familyMember B eta) phi hphi (n+1) (d:ℂ) rP CP,
      ∀S : Set (Fin n→ℝ),MeasurableSet S → S⊆smallConstrainedEnergyBall n ρ →
      ∀χ : (Fin n→ℝ)→ℂ,(∀x∈S,‖χ x‖≤1) → ∀j : ℕ,alpha (n+1)≤j →
        ‖∫x in S,χ x*constrainedResidueDensity (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T j (complexify n x)‖≤
          (2*M^(1+alpha (n+1)+(n+1)+(n+1).choose 2)/(c*(n+1)))*
            constrainedBetaValue (n+1) j (1-Real.cos d) (1/(4*(n+1))) := by
  obtain ⟨δ,M,c,hδ,hM,hc,hcoef⟩ := compact_family_pole_beta_integrand_bound B rootB phi hphi hQ hB hrB hB0
  obtain ⟨ρ,hρ,_hρr,hρδ,hpole⟩ := projectedWitness_uniform_small_all phi hphi rP CP δ hrP hδ
  refine ⟨ρ,M,c,hρ,hM,hc,?_⟩
  intro eta heta n hn ho d hd hτ P S hSm hS χ hχ j hj
  simp_rw [constrainedResidueDensity_eq_poleTaylorIntegrand]
  apply norm_integral_constrained_beta_bound ho hn j hj (1-Real.cos d) (1/(4*(n+1)))
    hτ (by positivity) S hSm _ _ (by positivity)
  intro x hx
  have hv := complexShape_norm_lt hρ x (hS hx)
  have hTv := hpole (familyMember B eta) (n+1) (d:ℂ) (by simpa using hd) P (complexShape x) hv
  have hh := hcoef eta heta n d P.T x (hd.trans_le hρδ) hTv.2
    (fun i=>by
      have hi := (norm_le_pi_norm (complexShape x) i).trans_lt (hv.trans_le hρδ)
      simpa only [complexShape,Complex.norm_real,Real.norm_eq_abs] using hi) hTv.1 hτ j
  calc
    _≤‖poleTaylorIntegrand (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T j (complexShape x)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ x hx)
    _≤_ := hh

/-- The all-order high-particle envelope for every actual P.T, without a beta
integrability restriction or an existential replacement pole. -/
theorem compact_family_witness_high_integral (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hrB : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta))
    (hB0 : ∀eta∈Q,B (0,eta)≠0) (rP CP : ℝ) (hrP : 0<rP) :
    ∃ρ M c : ℝ,0<ρ ∧ ρ≤1 ∧ 1≤M ∧ 0<c ∧ ∀eta∈Q,∀n : ℕ,1≤n → ∀d : ℝ,
      |d|<ρ → Real.pi/((n+1:ℕ):ℝ)≤|d| →
      ∀P : UniformProjectedWitness (familyMember B eta) phi hphi (n+1) (d:ℂ) rP CP,
      ∀S : Set (Fin n→ℝ),S⊆smallConstrainedEnergyBall n ρ →
      ∀χ : (Fin n→ℝ)→ℂ,(∀x∈S,‖χ x‖≤1) → ∀j : ℕ,
        ‖∫x in S,χ x*constrainedResidueDensity (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T j (complexify n x)‖≤
          (2*M^(1+alpha (n+1)+(n+1)+(n+1).choose 2)/(c*(n+1))*
            ((n+1:ℝ)^2/2)^(j+1))*
          Real.exp (-((n+1:ℝ)^2)/2*Real.log (n+1)+10*(n+1:ℝ)^2) := by
  obtain ⟨δ,M,c,hδ,hM,hc,hcoef⟩ := compact_family_pole_integrand_bound B rootB phi hphi hQ hB hrB hB0
  obtain ⟨a,ha,_har,haδ,hpole⟩ := projectedWitness_uniform_small_all phi hphi rP CP δ hrP hδ
  let ρ := min a 1
  have hρ : 0<ρ := lt_min ha (by norm_num)
  have hρa : ρ≤a := min_le_left _ _
  have hρδ : ρ≤δ := hρa.trans haδ
  refine ⟨ρ,M,c,hρ,min_le_right _ _,hM,hc,?_⟩
  intro eta heta n hn d hd hwind P S hS χ hχ j
  simp_rw [constrainedResidueDensity_eq_poleTaylorIntegrand]
  let K : ℝ := 2*M^(1+alpha (n+1)+(n+1)+(n+1).choose 2)/(c*(n+1))*((n+1:ℝ)^2/2)^(j+1)
  have hK : 0≤K := by dsimp [K]; positivity
  apply norm_integral_vandermonde_ball_bound hn S
    (hS.trans (smallConstrainedEnergyBall_subset hρ.le (min_le_right _ _))) _ K hK
  intro x hx
  have hv := complexShape_norm_lt hρ x (hS hx)
  have hTv := hpole (familyMember B eta) (n+1) (d:ℂ) (by simpa using hd.trans_le hρa) P (complexShape x) (hv.trans_le hρa)
  have hh := hcoef eta heta (n+1) (by omega) d P.T (shapeExtend x) (hd.trans_le hρδ) hTv.2
    (fun i=>by
      have hi := (norm_le_pi_norm (complexShape x) i).trans_lt (hv.trans_le hρδ)
      simpa only [complexShape,Complex.norm_real,Real.norm_eq_abs] using hi)
    (complexShape_zeroMean x) hTv.1 hwind j
  have hχmul : ‖χ x*poleTaylorIntegrand (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T j (complexShape x)‖≤
      ‖poleTaylorIntegrand (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T j (complexShape x)‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ x hx)
  apply hχmul.trans
  change ‖poleTaylorIntegrand (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T j
    (fun i=>((shapeExtend x i:ℝ):ℂ))‖≤K*‖vandermonde (fun i=>((shapeExtend x i:ℝ):ℂ))‖^2
  simpa only [K,Nat.cast_add,Nat.cast_one,mul_comm,mul_left_comm,mul_assoc] using hh

end IsingBulk.Joint.Negative
