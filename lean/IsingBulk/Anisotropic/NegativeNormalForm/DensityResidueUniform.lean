import IsingBulk.Anisotropic.NegativeNormalForm.DensityResidueBudget

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter IsingBulk.First IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
set_option maxHeartbeats 1800000

/-- A fixed-radius, dimension-uniform bound for the original complete scalar
residue ratio. The growing-order budget is derived from every actual factor. -/
theorem exists_uniform_regularResidue_envelope (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0)
    (hroot : AnalyticAt ℂ rootB 0) (hrootn : rootB 0≠0) :
    ∃ r K : ℝ, 0<r ∧ 0<K ∧ ∀ n : ℕ, n≠0 → ∀ d : ℂ, ∀ T : Config n→ℂ,
      T 0=1-Complex.cos d → ∀ v : Config n,
      ‖T v‖<r → ‖1-Complex.cos d‖<r → ‖d‖<r → ‖v‖<r →
      let H := (n:ℝ)^2*‖T v-(1-Complex.cos d)‖+
        (n:ℝ)*‖d‖*Real.sqrt ((n:ℝ)*absoluteEnergy v)+(n:ℝ)*absoluteEnergy v
      ‖regularResidue B rootB phi hphi d T v/regularResidue B rootB phi hphi d T 0‖≤Real.exp (K*H) ∧
      ‖regularResidue B rootB phi hphi d T v/regularResidue B rootB phi hphi d T 0-1‖≤K*H*Real.exp (K*H) := by
  obtain ⟨rB,KB,hrB,hKB,hBc⟩ := analytic_parameter_ratio_control B hB hBn
  obtain ⟨rR,KR,hrR,hKR,hRc⟩ := analytic_parameter_ratio_control rootB hroot hrootn
  obtain ⟨rO,KO,hrO,hKO,hOc⟩ := residueOneBodyRatio_control B phi hphi hB
  obtain ⟨rP,KP,hrP,hKP,hPc⟩ := residuePairRatio_control B phi hphi hB
  obtain ⟨rG,KG,hrG,hKG,hGc⟩ := poleParameterDerivative_inverse_uniform B phi hphi hB hBn
  obtain ⟨rA,hrA,hAc⟩ := Metric.mem_nhds_iff.mp hB.eventually_analyticAt
  let r := min rB (min rR (min rO (min rP (min rG rA))))
  have hr : 0<r := by dsimp [r]; positivity
  have hrs : r≤rB ∧ r≤rR ∧ r≤rO ∧ r≤rP ∧ r≤rG ∧ r≤rA := by
    have hh : r≤min rB (min rR (min rO (min rP (min rG rA)))) := le_rfl
    simpa only [le_min_iff] using hh
  let K := KR+KB+KO+3*KP+KG
  refine ⟨r,K,hr,by dsimp [K]; positivity,?_⟩
  intro n hn d T hT v ht ht₀ hd hv
  let t := T v
  let e := ‖t-(1-Complex.cos d)‖
  let q := absoluteEnergy v
  let s := Real.sqrt ((n:ℝ)*q)
  let H := (n:ℝ)^2*e+(n:ℝ)*‖d‖*s+(n:ℝ)*q
  have hq : 0≤q := absoluteEnergy_nonneg v
  have he : 0≤e := norm_nonneg _
  have hs : 0≤s := Real.sqrt_nonneg _
  have hi (i : Fin n) : ‖v i‖<r := (norm_le_pi_norm v i).trans_lt hv
  have hAt : AnalyticAt ℂ B (1-Complex.cos d) := hAc (by simpa using ht₀.trans_le hrs.2.2.2.2.2)
  let a := rootB t/rootB (1-Complex.cos d)
  let b := (B t/B (1-Complex.cos d))^alpha n
  let c := ∏i,residueOneBodyRatio B phi hphi (t,(d,v i))
  let p := ∏ij∈firstStrictPairs n,residuePairRatio B phi hphi t d (v ij.1) (v ij.2)
  let g := ((n:ℂ)*centralParameterSlope B phi d)/poleParameterDerivative B phi hphi d t v
  let A := KR*e
  let BB := (alpha n:ℝ)*(KB*e)
  let C := KO*((n:ℝ)*e+‖d‖*s+q)
  let PP := KP*((n:ℝ)^2*e+2*(n:ℝ)*‖d‖*s+3*(n:ℝ)*q)
  let G := KG*(e+(‖d‖*s+q)/(n:ℝ))
  have hA : 0≤A := by dsimp [A]; positivity
  have hBB : 0≤BB := by dsimp [BB]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  have hPP : 0≤PP := by dsimp [PP]; positivity
  have hG : 0≤G := by dsimp [G]; positivity
  have ha := scalar_relative_envelope a A hA
    (hRc t (1-Complex.cos d) (ht.trans_le hrs.2.1) (ht₀.trans_le hrs.2.1)).2
  have hb := power_relative_envelope (B t/B (1-Complex.cos d)) (KB*e) (alpha n)
    (hBc t (1-Complex.cos d) (ht.trans_le hrs.1) (ht₀.trans_le hrs.1)).2
  have hcsum : (∑i,‖residueOneBodyRatio B phi hphi (t,(d,v i))-1‖)≤C :=
    residue_oneBody_error_sum v _ KO e ‖d‖ hKO.le (norm_nonneg d)
      (fun i => hOc t d (v i) (ht.trans_le hrs.2.2.1) (ht₀.trans_le hrs.2.2.1)
        (hd.trans_le hrs.2.2.1) ((hi i).trans_le hrs.2.2.1))
  have hc := finite_product_relative_envelope Finset.univ
    (fun i => residueOneBodyRatio B phi hphi (t,(d,v i))) C hcsum
  have hpsum : (∑ij∈firstStrictPairs n,‖residuePairRatio B phi hphi t d (v ij.1) (v ij.2)-1‖)≤PP := by
    apply pair_error_sum_bound hn v (fun i j => residuePairRatio B phi hphi t d (v i) (v j)) KP e ‖d‖ hKP.le (norm_nonneg d)
    intro i j
    have hh := hPc t d (v i) (v j) (ht.trans_le hrs.2.2.2.1) (ht₀.trans_le hrs.2.2.2.1)
      (hd.trans_le hrs.2.2.2.1) ((hi i).trans_le hrs.2.2.2.1) ((hi j).trans_le hrs.2.2.2.1)
    exact hh.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (div_nonneg hq (Nat.cast_nonneg n))) hKP.le)
  have hp := finite_product_relative_envelope (firstStrictPairs n)
    (fun ij => residuePairRatio B phi hphi t d (v ij.1) (v ij.2)) PP hpsum
  have hgactual := hGc n hn t d v (ht.trans_le hrs.2.2.2.2.1) (ht₀.trans_le hrs.2.2.2.2.1)
    (hd.trans_le hrs.2.2.2.2.1) (hv.trans_le hrs.2.2.2.2.1)
  have hge : ‖g-1‖≤G := by
    apply hgactual.2.2.trans
    dsimp [G,e,q,s]
    gcongr
    exact sum_norm_le_sqrt_energy v
  have hg := scalar_relative_envelope g G hG hge
  have hpre := three_factor_exponential_error a b c A BB C hA hBB hC ha.1 hb.1 hc.1 ha.2 hb.2 hc.2
  have hall := three_factor_exponential_error (a*b*c) p g (A+BB+C) PP G
    (by positivity) hPP hG hpre.1 hp.1 hg.1 hpre.2 hp.2 hg.2
  have budget := residue_energy_budget hn he (norm_nonneg d) hq
  have hbudget : A+BB+C+PP+G≤K*H := by
    have h1 := mul_le_mul_of_nonneg_left budget.1 hKR.le
    have h2 := mul_le_mul_of_nonneg_left budget.2.1 hKB.le
    have h3 := mul_le_mul_of_nonneg_left budget.2.2.1 hKO.le
    have h4 := mul_le_mul_of_nonneg_left budget.2.2.2.1 hKP.le
    have h5 := mul_le_mul_of_nonneg_left budget.2.2.2.2 hKG.le
    dsimp [A,BB,C,PP,G,K,H,s,q,e] at ⊢ h1 h2 h3 h4 h5
    nlinarith
  rw [regularResidue_ratio_factorization B rootB phi hphi d T hT hAt v]
  exact exponential_envelope_mono (a*b*c*p*g) (by positivity) hbudget hall.1 hall.2

end
end IsingBulk.Anisotropic.NegativeNormalForm
