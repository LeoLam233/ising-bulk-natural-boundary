import IsingBulk.Tail.SectorIntegralDecomposition

/-! Fixed smooth angular partitions may be retained through the complete
real homotopy interval. The complex parameter never changes the partition. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

def weightedCurrentShapeSlice (N : ℕ) (f : SelectorFunctions) (r tau : ℝ)
    (w : CurrentShape N → ℂ) (lam : ℝ) (s : ℂ) : ℂ :=
  ∫ theta in angleBox N, w (lam,theta)*pulledDensity f r tau lam s theta

theorem weightedCurrentShapeSlice_interval_jets (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau)
    (w : CurrentShape N → ℂ) (hw : Continuous w) (j : ℕ) {s : ℂ}
    (hs : s ∈ dampingDomain r) :
    IntervalIntegrable (fun lam => iteratedDeriv j (weightedCurrentShapeSlice N f r tau w lam) s) volume 0 1 ∧
    iteratedDeriv j (fun z => ∫ lam : ℝ in 0..1, weightedCurrentShapeSlice N f r tau w lam z) s =
      ∫ lam : ℝ in 0..1, iteratedDeriv j (weightedCurrentShapeSlice N f r tau w lam) s := by
  let U := dampingDomain r
  let K := currentShapeDomain N
  let mu : Measure (CurrentShape N) := volume.prod volume
  let psi := currentJointPoint N f r tau
  let chi : CurrentShape N → ℂ := fun p => w p*(N.factorial:ℂ)⁻¹*
    (2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*(angularJacobian f tau p.1 p.2).det
  let F := continuedContourDensity N
  let G := fun z => ∫ p in K, chi p*F (z,psi p) ∂mu
  have hU : IsOpen U := dampingDomain_isOpen r
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hpsi : Continuous psi := currentJointPoint_continuous N f r tau hf.p_smooth.continuous hf.m_smooth.continuous
  have hJ : Continuous (fun p : CurrentShape N => angularJacobian f tau p.1 p.2) :=
    (angularJacobian_joint_contDiff f tau hf.p_smooth hf.m_smooth).continuous
  have hchi : Continuous chi := by dsimp [chi]; fun_prop
  have hupper (z : ℂ) (hz : z ∈ U) (p : CurrentShape N) (hp : p ∈ K) (i : Fin N) :
      0 < (sourceW z (psi p i)).im := by
    have hb := sourceW_upper_of_margin hr hr1 hz.2 (deformedPoint_zero_norm f hr.le tau p.2 i)
    exact hb.trans_le (deformed_sourceW_im_ge hN f hr htau hp.1.1 p.2 z
      hf.p_nonneg hf.m_nonneg hf.p_zero hf.m_zero i)
  have hF (z : ℂ) (hz : z ∈ U) (p : CurrentShape N) (hp : p ∈ K) : AnalyticAt ℂ F (z,psi p) := by
    have hY := homotopy_y_gap_nonzero hN f hr hr1 htau hp.1.1 p.2 hf.p_nonneg hf.m_le_one
    have hZ : 1-coordinateProduct (fun i => selectedContinuedRoot z (psi p i)) ≠ 0 := by
      apply one_sub_coordinateProduct_ne_zero hN
      intro i
      unfold selectedContinuedRoot
      rw [continuedRoot_eq_interiorRoot (hupper z hz p hp i)]
      exact interiorRoot_norm_lt_one (hupper z hz p hp i)
    exact continuedContourDensity_analyticAt hz.1 (deformedPoint_nonzero f hr.ne' tau p.1 p.2)
      (fun i => Or.inl (Or.inl (hupper z hz p hp i))) hY hZ
  have hpoint (z : ℂ) (hz : z ∈ U) (p : CurrentShape N) (hp : p ∈ K) :
      w p*pulledDensity f r tau p.1 z p.2=chi p*F (z,psi p) := by
    rw [← continuedPulledDensity_eq_original f r tau p.1 z p.2 (hupper z hz p hp)]
    dsimp [chi,F,psi,currentJointPoint,continuedPulledDensity,continuedContourDensity]
    ring
  have hcont (k : ℕ) (z : ℂ) (hz : z ∈ U) :
      ContinuousOn (fun p => chi p*jointParameterJet F k (z,psi p)) K := by
    apply hchi.continuousOn.mul
    intro p hp
    exact ((jointParameterJet_analyticAt (hF z hz p hp) k).continuousAt.comp
      (f := fun p => (z,psi p)) (continuous_const.prodMk hpsi).continuousAt).continuousWithinAt
  have hinner (k : ℕ) (z : ℂ) (hz : z ∈ U) (lam : ℝ) (hlam : lam ∈ Icc (0:ℝ) 1) :
      (∫ theta in angleBox N, chi (lam,theta)*jointParameterJet F k (z,psi (lam,theta))) =
        iteratedDeriv k (weightedCurrentShapeSlice N f r tau w lam) z := by
    let gl := fun v => ∫ theta in angleBox N, chi (lam,theta)*F (v,psi (lam,theta))
    have he : weightedCurrentShapeSlice N f r tau w lam =ᶠ[𝓝 z] gl := by
      filter_upwards [hU.mem_nhds hz] with v hv
      apply setIntegral_congr_fun measurableSet_Icc
      intro theta htheta
      exact hpoint v hv (lam,theta) ⟨hlam,htheta⟩
    rw [he.iteratedDeriv_eq k]
    have hj := compact_analytic_shape_integral_iteratedDeriv (μ := volume)
      isCompact_Icc hU F (fun theta => psi (lam,theta))
      (hpsi.comp (continuous_const.prodMk continuous_id)) (fun theta => chi (lam,theta))
      (hchi.comp (continuous_const.prodMk continuous_id))
      (fun v hv theta htheta => hF v hv (lam,theta) ⟨hlam,htheta⟩) k z hz
    simpa only [gl,jointParameterJet_eq,iteratedDeriv_eq_iterate,angleBox] using hj.symm
  have hprod (k : ℕ) (z : ℂ) (hz : z ∈ U) :
      (∫ p in K, chi p*jointParameterJet F k (z,psi p) ∂mu) =
        ∫ lam : ℝ in 0..1, iteratedDeriv k (weightedCurrentShapeSlice N f r tau w lam) z := by
    have hint : IntegrableOn (fun p => chi p*jointParameterJet F k (z,psi p)) K mu :=
      ContinuousOn.integrableOn_compact hK (hcont k z hz)
    change (∫ p in Icc (0:ℝ) 1 ×ˢ angleBox N, chi p*jointParameterJet F k (z,psi p) ∂(volume.prod volume)) = _
    rw [setIntegral_prod _ hint]
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro lam hlam
    exact hinner k z hz lam hlam
  have he : (fun z => ∫ lam : ℝ in 0..1, weightedCurrentShapeSlice N f r tau w lam z) =ᶠ[𝓝 s] G := by
    filter_upwards [hU.mem_nhds hs] with z hz
    simpa only [G,jointParameterJet,Function.iterate_zero_apply,iteratedDeriv_zero] using (hprod 0 z hz).symm
  have hjint : IntegrableOn (fun p => chi p*jointParameterJet F j (s,psi p)) K mu :=
    ContinuousOn.integrableOn_compact hK (hcont j s hs)
  have hjprod : Integrable (fun p : CurrentShape N => chi p*jointParameterJet F j (s,psi p))
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict (angleBox N))) := by
    rw [Measure.prod_restrict]
    exact hjint
  have houter : IntegrableOn (fun lam => iteratedDeriv j (weightedCurrentShapeSlice N f r tau w lam) s)
      (Icc (0:ℝ) 1) := by
    apply hjprod.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with lam hlam
    exact hinner j s hs lam hlam
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mpr
    (houter.mono_set Ioc_subset_Icc_self),?_⟩
  rw [he.iteratedDeriv_eq j]
  have hj := compact_analytic_shape_integral_iteratedDeriv (μ := mu) hK hU F psi hpsi chi hchi hF j s hs
  calc
    _ = ∫ p in K, chi p*jointParameterJet F j (s,psi p) ∂mu := by
      simpa only [G,K,currentShapeDomain,angleBox,jointParameterJet_eq,iteratedDeriv_eq_iterate] using hj
    _ = _ := hprod j s hs


theorem currentSectorIntegral_intervalIntegrable (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (q : Fin N)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (label : Option (Fin N × (Fin N → Fin 3))) (j : ℕ) {s : ℂ}
    (hs : s ∈ dampingDomain r) :
    IntervalIntegrable (fun lam => iteratedDeriv j
      (currentSectorIntegral N f r tau lam q b outer inner ho hi label) s) volume 0 1 := by
  let w : CurrentShape N → ℂ := fun p => namedCurrentMultiplier f tau q p.2 *
    (sectorPartitionWeight b outer inner ho hi label p.2:ℂ)
  have hw : Continuous w := ((namedCurrentMultiplier_continuous f hf tau q).comp continuous_snd).mul
    (Complex.continuous_ofReal.comp ((sectorPartitionWeight_smooth b outer inner ho hi label).continuous.comp continuous_snd))
  exact (weightedCurrentShapeSlice_interval_jets N hN f hf hr hr1 htau w hw j hs).1

def smallCurrentSectorIntegral (N : ℕ) (f : SelectorFunctions) (r tau cut : ℝ) (q : Fin N)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner)
    (label : Option (Fin N × (Fin N → Fin 3))) (j : ℕ) (s : ℂ) : ℂ :=
  ∫ lam : ℝ in 0..cut, iteratedDeriv j
    (currentSectorIntegral N f r tau lam q b outer inner ho hi label) s

theorem small_named_current_sector_decomposition (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau cut : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hcut : cut ∈ Icc (0:ℝ) 1) (q : Fin N)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (j : ℕ) {s : ℂ}
    (hs : s ∈ dampingDomain r) :
    (∫ lam : ℝ in 0..cut, iteratedDeriv j (actualNamedCurrentIntegral N f r tau lam q) s) =
      ∑ label, smallCurrentSectorIntegral N f r tau cut q b outer inner ho hi label j s := by
  have hint (label : Option (Fin N × (Fin N → Fin 3))) :
      IntervalIntegrable (fun lam => iteratedDeriv j
        (currentSectorIntegral N f r tau lam q b outer inner ho hi label) s) volume 0 cut := by
    apply (currentSectorIntegral_intervalIntegrable N hN f hf hr hr1 htau q b outer inner ho hi label j hs).mono_set
    rw [uIcc_of_le hcut.1,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact Icc_subset_Icc le_rfl hcut.2
  unfold smallCurrentSectorIntegral
  rw [← intervalIntegral.integral_finsetSum (fun label _ => hint label)]
  apply intervalIntegral.integral_congr
  intro lam hlam
  have hl : 0 ≤ lam := by
    rw [uIcc_of_le hcut.1] at hlam
    exact hlam.1
  exact namedCurrent_sector_derivative N hN f hf hr hr1 htau hl q b outer inner ho hi s hs j


theorem small_current_sector_decomposition (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r tau cut : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (htau : 0 ≤ tau) (hcut : cut ∈ Icc (0:ℝ) 1)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (j : ℕ) {s : ℂ}
    (hs : s ∈ dampingDomain r) :
    (∫ lam : ℝ in 0..cut, differentiatedCurrentSlice N f r tau lam j s) =
      ∑ q : Fin N, ∑ label, smallCurrentSectorIntegral N f r tau cut q b outer inner ho hi label j s := by
  have hint (q : Fin N) : IntervalIntegrable (fun lam =>
      iteratedDeriv j (actualNamedCurrentIntegral N f r tau lam q) s) volume 0 cut := by
    have hh := (weightedCurrentShapeSlice_interval_jets N hN f hf hr hr1 htau
      (fun p : CurrentShape N => namedCurrentMultiplier f tau q p.2)
      ((namedCurrentMultiplier_continuous f hf tau q).comp continuous_snd) j hs).1
    apply hh.mono_set
    rw [uIcc_of_le hcut.1,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    exact Icc_subset_Icc le_rfl hcut.2
  calc
    _ = ∫ lam : ℝ in 0..cut, ∑ q : Fin N,
        iteratedDeriv j (actualNamedCurrentIntegral N f r tau lam q) s := by
      apply intervalIntegral.integral_congr
      intro lam hlam
      have hl : 0 ≤ lam := by rw [uIcc_of_le hcut.1] at hlam; exact hlam.1
      unfold differentiatedCurrentSlice
      apply Finset.sum_congr rfl
      intro q _
      exact ((actualNamedCurrentIntegral_analytic_jets N hN f hr hr1 htau hl q
        hf.p_smooth hf.m_smooth hf.a_smooth hf.p_nonneg hf.m_nonneg hf.m_le_one
        hf.p_zero hf.m_zero).2 j s hs).symm
    _ = ∑ q : Fin N, ∫ lam : ℝ in 0..cut,
        iteratedDeriv j (actualNamedCurrentIntegral N f r tau lam q) s :=
      intervalIntegral.integral_finsetSum (fun q _ => hint q)
    _ = _ := Finset.sum_congr rfl (fun q _ =>
      small_named_current_sector_decomposition N hN f hf hr hr1 htau hcut q b outer inner ho hi j hs)

end
end IsingBulk.Tail
