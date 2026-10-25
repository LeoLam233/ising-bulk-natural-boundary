import IsingBulk.Joint.Transverse.FamilyPhysicalIdentity
import IsingBulk.Joint.RegularEdges.FamilyPrefactoredParity

/-! # Uniform leading singularities of the literal complete physical families -/
namespace IsingBulk.Joint.Transverse
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic IsingBulk.Joint.RegularEdges IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- Equal actual physical families on one common upper tube have equal jets
on the common inward path, simultaneously for every derivative order. -/
theorem family_upper_identity_inward_jets {Q : Set E} {F G : E→ℂ→ℂ} {δ : ℝ} (hδ : 0<δ)
    (heq : ∀eta∈Q,∀u : ℂ,‖u‖<δ → 0<u.im → F eta u=G eta u) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,∀eta∈Q,∀j : ℕ,
      iteratedDeriv j (F eta) (Complex.I*(t:ℂ)^2)=iteratedDeriv j (G eta) (Complex.I*(t:ℂ)^2) := by
  have htend : Tendsto (fun t : ℝ=>Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((by fun_prop : Continuous (fun t : ℝ=>Complex.I*(t:ℂ)^2)).tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [htend.eventually (ball_mem_nhds _ hδ),self_mem_nhdsWithin] with t ht htpos
  intro eta heta j
  have hu : ‖Complex.I*(t:ℂ)^2‖<δ := by simpa using ht
  have hi : 0<(Complex.I*(t:ℂ)^2).im := by
    simp only [←Complex.ofReal_pow,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
    exact sq_pos_of_pos htpos
  have hh : F eta =ᶠ[𝓝 (Complex.I*(t:ℂ)^2)] G eta := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hu,
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hi] with u hu hi
    exact heq eta heta u hu hi
  exact hh.iteratedDeriv_eq j

/-- Full high-temperature physical leading asymptotics on every compact
joint holomorphic normalized family. All side, normalization, finite-prefix,
particle-weight, prefactor and differentiated-tail facts are proved internally. -/
theorem positive_high_compact_family_leading {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier highDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(transferB (curve (0,eta))).im) (hb : |b|<1)
    (hprime : b∈primePhaseCosines)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,positiveParameter b (curve (u,eta))=u) :
    ∃q k : ℕ,∃c : ℝ,1≤q ∧ 2*k+1=(2*q+1)^2 ∧ 0<c ∧
      (∀eta∈Q,c≤‖positiveHighLeading (2*q) k b curve eta‖) ∧
      (∀j≤k,TendstoUniformlyOn (fun (t : ℝ) eta=>(t^2) • iteratedDeriv j
        (fun u=>FormFactors.highNormalizedBulk (curve (u,eta))) (Complex.I*(t:ℂ)^2))
        (fun eta=>if j=k then positiveHighLeading (2*q) k b curve eta else 0) (𝓝[>] (0:ℝ)) Q) ∧
      (∀M : ℝ,∀ᶠ t : ℝ in 𝓝[>] 0,∀eta∈Q,M<‖iteratedDeriv k
        (fun u=>FormFactors.highNormalizedBulk (curve (u,eta))) (Complex.I*(t:ℂ)^2)‖) := by
  obtain ⟨q,k,hq,hcritical,hres,hearly⟩ := primeCosine_first_odd hprime
  let B : ℂ × E→ℂ := fun q=>transferB (curve q)
  let V : ℂ × E→ℂ := fun q=>positiveParticleScale (curve q)
  let W : ℂ × E→ℂ := fun q=>positiveHighMultiplier (curve q)
  let L : E→ℂ := fun eta=>edgeCoefficientLeading (2*q) k b (fun u=>B (u,eta)) (fun u=>V (u,eta))
  have hBa : ∀eta∈Q,AnalyticAt ℂ B (0,eta) := fun eta heta=>transferB_family_analyticAt (hc eta heta) (hS eta heta)
  have hVa : ∀eta∈Q,AnalyticAt ℂ V (0,eta) := fun eta heta=>positiveParticleScale_family_analyticAt (hc eta heta) (hS eta heta) (hB eta heta)
  have hV0 : ∀eta∈Q,V (0,eta)≠0 := fun eta heta=>div_ne_zero (hS eta heta)
    (positiveParticleRoot_ne_zero (hS eta heta) (hB eta heta))
  have hWa : ∀eta∈Q,AnalyticAt ℂ W (0,eta) := fun eta heta=>positiveHighMultiplier_family_analyticAt (hc eta heta) (hK eta heta).1 (hp eta heta) (hS eta heta) (hB eta heta)
  have hW0 : ∀eta∈Q,W (0,eta)≠0 := fun eta heta=>div_ne_zero (FormFactors.highPrefactor_ne_zero _) (positiveParticleRoot_ne_zero (hS eta heta) (hB eta heta))
  obtain ⟨c₀,hc₀,hbase,hlimits,_⟩ := odd_compact_family_parity_first_singularity B V hb hQ hBa hB hVa hV0 hq hcritical hres hearly
  have hb' := abs_lt.mp hb
  have hQpos : 0<((2*q:ℕ)+1:ℝ)/Real.sqrt (1-b^2) :=
    div_pos (by positivity) (Real.sqrt_pos.mpr (by nlinarith))
  obtain ⟨hk,hdeg⟩ := odd_first_degree hq hcritical
  have hperiod : ContinuousOn (shapePeriod (2*q) k ((2*q+1)/Real.sqrt (1-b^2))) {c : ℂ | 0<c.re} := by
    have hh := odd_shapePeriod_continuousOn (by omega : 1≤2*q) hdeg hQpos
    simpa only [Nat.sub_add_cancel hk,Nat.cast_mul,Nat.cast_ofNat] using hh
  have hLc : ContinuousOn L Q := family_leadingCoefficient_continuousOn B V hb hBa hB hVa hV0
    hres (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hperiod)
  have hLn : ∀eta∈Q,L eta≠0 := by
    intro eta heta hz
    have hh := hbase eta heta
    change c₀≤‖L eta‖ at hh
    rw [hz,norm_zero] at hh
    linarith
  have hWc : ContinuousOn (fun eta=>W (0,eta)) Q := fun eta heta=>
    ((hWa eta heta).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  obtain ⟨c,hcpos,hbound⟩ := compact_nonzero_norm_lower_bound hQ (hWc.mul hLc)
    (fun eta heta=>mul_ne_zero (hW0 eta heta) (hLn eta heta))
  have hpref := compact_prefactored_parity_all_limits B V W hb hQ hBa hB hVa hV0 hWa hLc
    (a:=2) hlimits
  obtain ⟨δ,hδ,hid⟩ := compact_family_positive_high_parity_identity curve hQ hc hK hS hp hB hb hn
  have hjet := family_upper_identity_inward_jets hδ hid
  have hactual : ∀j≤k,TendstoUniformlyOn (fun (t : ℝ) eta=>(t^2) • iteratedDeriv j
      (fun u=>FormFactors.highNormalizedBulk (curve (u,eta))) (Complex.I*(t:ℂ)^2))
      (fun eta=>if j=k then positiveHighLeading (2*q) k b curve eta else 0) (𝓝[>] (0:ℝ)) Q := by
    intro j hj
    have hh := hpref j hj
    change TendstoUniformlyOn _ _ _ Q at hh
    apply hh.congr
    filter_upwards [hjet] with t ht
    intro eta heta
    dsimp only
    rw [ht eta heta j]
  refine ⟨q,k,c,hq,hcritical,hcpos,hbound,hactual,?_⟩
  apply uniform_scaled_leading_unbounded (g := positiveHighLeading (2*q) k b curve) hcpos hbound (a:=2) (by omega)
  simpa only [ite_true,Complex.real_smul] using hactual k le_rfl

/-- Full low-temperature physical leading asymptotics on every compact
joint holomorphic normalized family. All side, normalization, finite-prefix,
particle-weight, prefactor and differentiated-tail facts are proved internally. -/
theorem positive_low_compact_family_leading {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier lowDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(transferB (curve (0,eta))).im) (hb : |b|<1)
    (hprime : b∈primePhaseCosines)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,positiveParameter b (curve (u,eta))=u) :
    ∃q k : ℕ,∃c : ℝ,2*(k+1)=(2*q+2)^2 ∧ 0<c ∧
      (∀eta∈Q,c≤‖positiveLowLeading (2*q+1) k b curve eta‖) ∧
      (∀j≤k,TendstoUniformlyOn (fun (t : ℝ) eta=>t • iteratedDeriv j
        (fun u=>FormFactors.lowNormalizedBulk (curve (u,eta))) (Complex.I*(t:ℂ)^2))
        (fun eta=>if j=k then positiveLowLeading (2*q+1) k b curve eta else 0) (𝓝[>] (0:ℝ)) Q) ∧
      (∀M : ℝ,∀ᶠ t : ℝ in 𝓝[>] 0,∀eta∈Q,M<‖iteratedDeriv k
        (fun u=>FormFactors.lowNormalizedBulk (curve (u,eta))) (Complex.I*(t:ℂ)^2)‖) := by
  obtain ⟨q,k,hcritical,hres,hearly⟩ := primeCosine_first_even hprime
  let B : ℂ × E→ℂ := fun q=>transferB (curve q)
  let V : ℂ × E→ℂ := fun q=>positiveParticleScale (curve q)
  let W : ℂ × E→ℂ := fun q=>FormFactors.lowPrefactor (curve q)
  let L : E→ℂ := fun eta=>edgeCoefficientLeading (2*q+1) k b (fun u=>B (u,eta)) (fun u=>V (u,eta))
  have hBa : ∀eta∈Q,AnalyticAt ℂ B (0,eta) := fun eta heta=>transferB_family_analyticAt (hc eta heta) (hS eta heta)
  have hVa : ∀eta∈Q,AnalyticAt ℂ V (0,eta) := fun eta heta=>positiveParticleScale_family_analyticAt (hc eta heta) (hS eta heta) (hB eta heta)
  have hV0 : ∀eta∈Q,V (0,eta)≠0 := fun eta heta=>div_ne_zero (hS eta heta)
    (positiveParticleRoot_ne_zero (hS eta heta) (hB eta heta))
  have hWa : ∀eta∈Q,AnalyticAt ℂ W (0,eta) := fun eta heta=>((lowPrefactor_boundary_analyticAt (hK eta heta).1 (hp eta heta)).comp (hc eta heta))
  have hW0 : ∀eta∈Q,W (0,eta)≠0 := fun eta heta=>FormFactors.lowPrefactor_ne_zero _
  obtain ⟨c₀,hc₀,hbase,hlimits,_⟩ := even_compact_family_parity_first_singularity B V hb hQ hBa hB hVa hV0 hcritical hres hearly
  have hb' := abs_lt.mp hb
  have hQpos : 0<((2*q+1:ℕ)+1:ℝ)/Real.sqrt (1-b^2) :=
    div_pos (by positivity) (Real.sqrt_pos.mpr (by nlinarith))
  have hperiod := even_shapePeriod_continuousOn (by omega : 1≤2*q+1) (even_first_degree hcritical) hQpos
  have hLc : ContinuousOn L Q := family_leadingCoefficient_continuousOn B V hb hBa hB hVa hV0
    (by simpa only [Nat.add_assoc] using hres) (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hperiod)
  have hLn : ∀eta∈Q,L eta≠0 := by
    intro eta heta hz
    have hh := hbase eta heta
    change c₀≤‖L eta‖ at hh
    rw [hz,norm_zero] at hh
    linarith
  have hWc : ContinuousOn (fun eta=>W (0,eta)) Q := fun eta heta=>
    ((hWa eta heta).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  obtain ⟨c,hcpos,hbound⟩ := compact_nonzero_norm_lower_bound hQ (hWc.mul hLc)
    (fun eta heta=>mul_ne_zero (hW0 eta heta) (hLn eta heta))
  have hpref := compact_prefactored_parity_all_limits B V W hb hQ hBa hB hVa hV0 hWa hLc
    (a:=1) (by simpa only [pow_one] using hlimits)
  obtain ⟨δ,hδ,hid⟩ := compact_family_positive_low_parity_identity curve hQ hc hK hS hp hB hb hn
  have hjet := family_upper_identity_inward_jets hδ hid
  have hactual : ∀j≤k,TendstoUniformlyOn (fun (t : ℝ) eta=>t • iteratedDeriv j
      (fun u=>FormFactors.lowNormalizedBulk (curve (u,eta))) (Complex.I*(t:ℂ)^2))
      (fun eta=>if j=k then positiveLowLeading (2*q+1) k b curve eta else 0) (𝓝[>] (0:ℝ)) Q := by
    intro j hj
    have hh := hpref j hj
    simp only [pow_one] at hh
    apply hh.congr
    filter_upwards [hjet] with t ht
    intro eta heta
    dsimp only
    rw [ht eta heta j]
  refine ⟨q,k,c,hcritical,hcpos,hbound,hactual,?_⟩
  apply uniform_scaled_leading_unbounded (g := positiveLowLeading (2*q+1) k b curve) hcpos hbound (a:=1) (by omega)
  simpa only [ite_true,Complex.real_smul,pow_one] using hactual k le_rfl

end
end IsingBulk.Joint.Transverse
