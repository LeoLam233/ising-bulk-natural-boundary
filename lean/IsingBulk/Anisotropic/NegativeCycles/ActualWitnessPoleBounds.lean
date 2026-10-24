import IsingBulk.Anisotropic.NegativeCycles.CenteredInnerGeometry
import IsingBulk.Anisotropic.NegativeCycles.ActualIntegralTransport
import IsingBulk.Anisotropic.NegativeDominance.PoleBetaIntegral
import IsingBulk.Anisotropic.NegativeDominance.HighPoleIntegral

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeDominance
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators

/-- Smallness of every actual projected pole follows directly from its Lipschitz
bound and exact center. No identification of different chosen poles is needed. -/
theorem projectedWitness_uniform_small (B : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (r C ε : ℝ) (hr : 0<r) (hε : 0<ε) :
    ∃ρ : ℝ,0<ρ ∧ ρ≤r ∧ ρ≤ε ∧ ∀n : ℕ, ∀d : ℂ,‖d‖<ρ →
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
  intro n d hd P v hv
  have hv2 : ‖v‖<2*r := by linarith
  refine ⟨(P.t_pole v hv2).1,?_⟩
  have htau := has (show d∈ball (0:ℂ) a by simpa using hd.trans_le hρa)
  change ‖1-Complex.cos d‖<ε/2 at htau
  have hl := P.t_lip v 0 hv2 (by simpa using (show 0<2*r by positivity))
  rw [P.t_zero,sub_zero] at hl
  have hh := norm_le_norm_sub_add (P.T v) (1-Complex.cos d)
  linarith

@[simp] theorem constrainedResidueDensity_eq_poleTaylorIntegrand {n : ℕ}
    (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ)
    (T : Config (n+1)→ℂ) (j : ℕ) (q : Fin n→ℝ) :
    constrainedResidueDensity B rootB phi hphi d T j (complexify n q)=
      poleTaylorIntegrand B rootB phi hphi d T j (complexShape q) := by
  simp only [constrainedResidueDensity,poleTaylorIntegrand,freeChartCLM_eq_shapeExtend,
    shapeExtend_complexify]
  rfl

theorem centeredInnerSet_subset_smallConstrainedEnergyBall (n : ℕ) (d s ρ : ℝ)
    (hs : s≤ρ^2) : centeredInnerSet n d s⊆smallConstrainedEnergyBall n ρ := by
  intro q hq
  change constrainedSquaredRadius q<s-(n+1:ℕ)*d^2 at hq
  change squaredRadius (shapeExtend q)<ρ^2
  change constrainedSquaredRadius q<ρ^2
  have hn : 0≤(n+1:ℕ)*(d^2:ℝ) := by positivity
  linarith

/-- The beta integral bound for the SAME actual P.T used by the physical winding
decomposition, uniformly for every projected witness. -/
theorem actualWitness_pole_beta_integral_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hrB : AnalyticAt ℂ rootB 0)
    (hB0 : B 0≠0) (rP CP : ℝ) (hrP : 0<rP) :
    ∃ρ M c : ℝ,0<ρ ∧ 1≤M ∧ 0<c ∧ ∀n : ℕ,2≤n → Odd (n+1) → ∀d : ℝ,
      |d|<ρ → 0<1-Real.cos d →
      ∀P : UniformProjectedWitness B phi hphi (n+1) (d:ℂ) rP CP,
      ∀S : Set (Fin n→ℝ),MeasurableSet S → S⊆smallConstrainedEnergyBall n ρ →
      ∀χ : (Fin n→ℝ)→ℂ,(∀x∈S,‖χ x‖≤1) → ∀j : ℕ,alpha (n+1)≤j →
        ‖∫x in S,χ x*constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j (complexify n x)‖≤
          (2*M^(1+alpha (n+1)+(n+1)+(n+1).choose 2)/(c*(n+1)))*
            constrainedBetaValue (n+1) j (1-Real.cos d) (1/(4*(n+1))) := by
  obtain ⟨δ,M,c,hδ,hM,hc,hcoef⟩ := poleTaylorIntegrand_beta_uniform_bound B rootB phi hphi hB hrB hB0
  obtain ⟨ρ,hρ,_hρr,hρδ,hpole⟩ := projectedWitness_uniform_small B phi hphi rP CP δ hrP hδ
  refine ⟨ρ,M,c,hρ,hM,hc,?_⟩
  intro n hn ho d hd hτ P S hSm hS χ hχ j hj
  simp_rw [constrainedResidueDensity_eq_poleTaylorIntegrand]
  apply norm_integral_constrained_beta_bound ho hn j hj (1-Real.cos d) (1/(4*(n+1)))
    hτ (by positivity) S hSm _ _ (by positivity)
  intro x hx
  have hv := complexShape_norm_lt hρ x (hS hx)
  have hTv := hpole (n+1) (d:ℂ) (by simpa using hd) P (complexShape x) hv
  have hh := hcoef n d P.T x (hd.trans_le hρδ) hTv.2
    (fun i=>by
      have hi := (norm_le_pi_norm (complexShape x) i).trans_lt (hv.trans_le hρδ)
      simpa only [complexShape,Complex.norm_real,Real.norm_eq_abs] using hi) hTv.1 hτ j
  calc
    _≤‖poleTaylorIntegrand B rootB phi hphi (d:ℂ) P.T j (complexShape x)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ x hx)
    _≤_ := hh

/-- The all-order high-particle envelope for every actual P.T, without a beta
integrability restriction or an existential replacement pole. -/
theorem actualWitness_high_pole_integral_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hrB : AnalyticAt ℂ rootB 0)
    (hB0 : B 0≠0) (rP CP : ℝ) (hrP : 0<rP) :
    ∃ρ M c : ℝ,0<ρ ∧ ρ≤1 ∧ 1≤M ∧ 0<c ∧ ∀n : ℕ,1≤n → ∀d : ℝ,
      |d|<ρ → Real.pi/((n+1:ℕ):ℝ)≤|d| →
      ∀P : UniformProjectedWitness B phi hphi (n+1) (d:ℂ) rP CP,
      ∀S : Set (Fin n→ℝ),S⊆smallConstrainedEnergyBall n ρ →
      ∀χ : (Fin n→ℝ)→ℂ,(∀x∈S,‖χ x‖≤1) → ∀j : ℕ,
        ‖∫x in S,χ x*constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j (complexify n x)‖≤
          (2*M^(1+alpha (n+1)+(n+1)+(n+1).choose 2)/(c*(n+1))*
            ((n+1:ℝ)^2/2)^(j+1))*
          Real.exp (-((n+1:ℝ)^2)/2*Real.log (n+1)+10*(n+1:ℝ)^2) := by
  obtain ⟨δ,M,c,hδ,hM,hc,hcoef⟩ := poleTaylorIntegrand_uniform_bound B rootB phi hphi hB hrB hB0
  obtain ⟨a,ha,_har,haδ,hpole⟩ := projectedWitness_uniform_small B phi hphi rP CP δ hrP hδ
  let ρ := min a 1
  have hρ : 0<ρ := lt_min ha (by norm_num)
  have hρa : ρ≤a := min_le_left _ _
  have hρδ : ρ≤δ := hρa.trans haδ
  refine ⟨ρ,M,c,hρ,min_le_right _ _,hM,hc,?_⟩
  intro n hn d hd hwind P S hS χ hχ j
  simp_rw [constrainedResidueDensity_eq_poleTaylorIntegrand]
  let K : ℝ := 2*M^(1+alpha (n+1)+(n+1)+(n+1).choose 2)/(c*(n+1))*((n+1:ℝ)^2/2)^(j+1)
  have hK : 0≤K := by dsimp [K]; positivity
  apply norm_integral_vandermonde_ball_bound hn S
    (hS.trans (smallConstrainedEnergyBall_subset hρ.le (min_le_right _ _))) _ K hK
  intro x hx
  have hv := complexShape_norm_lt hρ x (hS hx)
  have hTv := hpole (n+1) (d:ℂ) (by simpa using hd.trans_le hρa) P (complexShape x) (hv.trans_le hρa)
  have hh := hcoef (n+1) (by omega) d P.T (shapeExtend x) (hd.trans_le hρδ) hTv.2
    (fun i=>by
      have hi := (norm_le_pi_norm (complexShape x) i).trans_lt (hv.trans_le hρδ)
      simpa only [complexShape,Complex.norm_real,Real.norm_eq_abs] using hi)
    (complexShape_zeroMean x) hTv.1 hwind j
  have hχmul : ‖χ x*poleTaylorIntegrand B rootB phi hphi (d:ℂ) P.T j (complexShape x)‖≤
      ‖poleTaylorIntegrand B rootB phi hphi (d:ℂ) P.T j (complexShape x)‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ x hx)
  apply hχmul.trans
  change ‖poleTaylorIntegrand B rootB phi hphi (d:ℂ) P.T j
    (fun i=>((shapeExtend x i:ℝ):ℂ))‖≤K*‖vandermonde (fun i=>((shapeExtend x i:ℝ):ℂ))‖^2
  simpa only [K,Nat.cast_add,Nat.cast_one,mul_comm,mul_left_comm,mul_assoc] using hh

end IsingBulk.Anisotropic.NegativeCycles
