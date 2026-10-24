import IsingBulk.Anisotropic.NegativeNormalForm.UniformRootBounds
import IsingBulk.Anisotropic.NegativeDominance.ResonanceScale

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.NegativeNormalForm Set Filter Metric
open scoped BigOperators Topology
set_option maxHeartbeats 800000

/-- One scalar neighborhood gives positivity of every genuine real-angular
pole energy, uniformly before the particle number is chosen. -/
theorem actual_pole_real_energy_lower (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0) :
    ∃ δ : ℝ,0<δ ∧ ∀ n : ℕ, n≠0 → ∀ d : ℝ, ∀ t : ℂ, ∀ v : Fin n → ℝ,
      |d|<δ → ‖t‖<δ → (∀ i, |v i|<δ) →
      ZeroMean (fun i => (v i : ℂ)) →
      poleEquation B phi hphi (d : ℂ) t (fun i => (v i : ℂ))=0 →
      1-Real.cos d+(∑ i,(v i)^2)/(4*(n : ℝ))≤t.re := by
  have hh := centralHessian_analyticAt_zero B phi hB
  have hq := phaseParameterQuotient_joint_origin_analyticAt B phi hphi hB
  have hq0 : phaseParameterQuotient B phi hphi 0 0≠0 := by
    have he := phaseParameterQuotient_center B phi hphi 0 (by simpa using hB)
    simp only [Complex.cos_zero,sub_self] at he
    rw [he]
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hphi) Complex.I_ne_zero)) hB0
  have hha : AnalyticAt ℂ (fun p : ScalarTriple => centralHessian B phi p.2.1) 0 :=
    hh.comp_of_eq (f := fun p : ScalarTriple => p.2.1) (analyticAt_fst.comp analyticAt_snd) rfl
  have hqa : AnalyticAt ℂ (fun p : ScalarTriple => phaseParameterQuotient B phi hphi p.2.1 p.1) 0 :=
    hq.fun_comp_of_eq (f := fun p : ScalarTriple => (p.1,p.2.1)) (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)) rfl
  let E : ScalarTriple → ℂ := fun p =>
    centralHessian B phi p.2.1*phaseEnergy B phi hphi p.2.1 p.1 p.2.2
  have hEa : AnalyticAt ℂ E 0 := hha.mul (phaseEnergy_triple_analyticAt B phi hphi hB hB0)
  have hE0 : E 0=1 := by
    have he := phaseEnergy_center B phi hphi 0 (by simpa using hB) (by simpa using hB0)
      (by simp [centralHessian_zero])
    simpa only [E,Prod.fst_zero,Prod.snd_zero,centralHessian_zero,Complex.cos_zero,sub_self,one_mul] using he
  have he : ∀ᶠ p in 𝓝 (0 : ScalarTriple),
      centralHessian B phi p.2.1≠0 ∧ phaseParameterQuotient B phi hphi p.2.1 p.1≠0 ∧
      ‖E p-1‖≤(1/2 : ℝ) := by
    have hsmall : ∀ᶠ p in 𝓝 (0 : ScalarTriple), ‖E p-1‖<(1/2 : ℝ) :=
      (hEa.continuousAt.sub continuousAt_const).norm.eventually_lt_const (by change ‖E 0-1‖<(1/2 : ℝ); rw [hE0,sub_self,norm_zero]; norm_num)
    filter_upwards [hha.continuousAt.eventually_ne (show centralHessian B phi (0 : ℂ)≠(0 : ℂ) by simp [centralHessian_zero]),
      hqa.continuousAt.eventually_ne hq0,hsmall] with p hp hqp hep
    exact ⟨hp,hqp,hep.le⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ,hδ,?_⟩
  intro n hn d t v hd ht hv hmean hpole
  have hmem (x : ℝ) (hx : |x|<δ) : (t,((d : ℂ),(x : ℂ)))∈ball (0 : ScalarTriple) δ := by
    simpa only [mem_ball,dist_zero_right,Prod.norm_def,Complex.norm_real,Real.norm_eq_abs,max_lt_iff]
      using And.intro ht (And.intro hd hx)
  have hbase := hball (hmem 0 (by simpa using hδ))
  have hex := phaseSeparableMap_exact hn B phi hphi (d : ℂ) t (fun i => (v i : ℂ))
    hmean hbase.1 hbase.2.1 hpole
  rw [phaseSeparableMap,quadratic_separableMap] at hex
  have hnc : (n : ℂ)≠0 := by exact_mod_cast hn
  have henergy : (2*(n : ℂ))*(t-(1-Complex.cos (d : ℂ)))=
      ∑ i,(v i : ℂ)^2*E (t,((d : ℂ),(v i : ℂ))) := by
    rw [hex]
    calc
      _ = centralHessian B phi (d : ℂ)*
          ∑ i,(v i : ℂ)^2*phaseEnergy B phi hphi (d : ℂ) t (v i : ℂ) := by
        field_simp
        rfl
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [E]
        ring
  rw [show (2 : ℂ)*(n : ℂ)=((2*(n : ℝ) : ℝ) : ℂ) by push_cast; rfl] at henergy
  simp only [←Complex.ofReal_pow] at henergy
  have hreal := congrArg Complex.re henergy
  simp [Complex.mul_re] at hreal
  simp only [←Complex.ofReal_pow,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
    Finset.sum_const_zero,sub_zero,Complex.cos_ofReal_re] at hreal
  have hEreal (i : Fin n) : (1/2 : ℝ)≤(E (t,((d : ℂ),(v i : ℂ)))).re := by
    have he' := (hball (hmem (v i) (hv i))).2.2
    have hab := (Complex.abs_re_le_norm (E (t,((d : ℂ),(v i : ℂ)))-1)).trans he'
    simp only [Complex.sub_re,Complex.one_re] at hab
    linarith [(abs_le.mp hab).1]
  have hsum : (∑ i,(v i)^2)/2≤∑ i,(v i)^2*(E (t,((d : ℂ),(v i : ℂ)))).re := by
    calc
      _ = ∑ i,(v i)^2*(1/2 : ℝ) := by rw [←Finset.sum_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hEreal i) (sq_nonneg _))
  have hnR : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hdiv : (∑ i,(v i)^2)/(4*(n : ℝ))≤t.re-(1-Real.cos d) := by
    apply (div_le_iff₀ (by positivity : 0<4*(n : ℝ))).mpr
    nlinarith only [hreal,hsum]
  linarith

/-- Every noncentral odd winding has at least the first-winding real gap. -/
theorem one_sub_cos_winding_lower (n : ℕ) (hn : n≠0) (d : ℝ)
    (hd : |d|≤Real.pi) (hwind : Real.pi/(n : ℝ)≤|d|) :
    2/(n : ℝ)^2≤1-Real.cos d := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsq : (Real.pi/(n : ℝ))^2≤d^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (by positivity : 0≤Real.pi/(n : ℝ)) hwind 2
  calc
    _ = (2/Real.pi^2)*(Real.pi/(n : ℝ))^2 := by field_simp
    _ ≤ (2/Real.pi^2)*d^2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ ≤ 1-Real.cos d := by linarith [Real.cos_le_one_sub_mul_cos_sq hd]

end
end IsingBulk.Anisotropic.NegativeDominance
