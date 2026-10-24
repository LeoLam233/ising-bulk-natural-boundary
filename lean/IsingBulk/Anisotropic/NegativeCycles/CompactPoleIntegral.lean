import IsingBulk.Anisotropic.NegativeCycles.PoleTaylorCoefficient
import IsingBulk.First.CompactIntegralHolomorphic

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open IsingBulk.First Set Filter Metric MeasureTheory
open scoped Topology

theorem compact_nonzero_uniform_gap {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {T : X→ℂ} (hT : ContinuousOn T K)
    (hne : ∀x∈K,T x≠0) : ∃r : ℝ,0<r ∧ ∀x∈K,r≤‖T x‖ := by
  by_cases hnon : K.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hnon hT.norm
    exact ⟨‖T x‖,norm_pos_iff.mpr (hne x hx),fun y hy=>hmin hy⟩
  · refine ⟨1,by norm_num,?_⟩
    intro x hx
    exact (hnon ⟨x,hx⟩).elim

theorem pole_iterated_derivative (a T t : ℂ) (j : ℕ) :
    iteratedDeriv j (fun s : ℂ=>a/(T-s)) t=(j.factorial:ℂ)*a/(T-t)^(j+1) := by
  simp only [div_eq_mul_inv,iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_comp_const_sub]
  dsimp only
  rw [smul_eq_mul,iteratedDeriv_eq_iterate,iter_deriv_inv']
  dsimp only
  have hz : (-1-(j:ℤ))=-((j+1:ℕ):ℤ) := by omega
  rw [hz,zpow_neg,zpow_natCast]
  have hsgn : (-1:ℂ)^j*(-1)^j=1 := by rw [←mul_pow]; norm_num
  linear_combination a*(j.factorial:ℂ)*((T-t)^(j+1))⁻¹*hsgn

/-- A genuine compact pole integral: compactness proves the common pole-free
parameter disk, all integration/derivative exchanges, and the exact coefficients.
The amplitude and pole location need only be continuous on the compact set. -/
theorem compact_pole_integral_analytic_taylor
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {K : Set X} (hK : IsCompact K) {a T : X→ℂ}
    (ha : ContinuousOn a K) (hT : ContinuousOn T K) (hne : ∀x∈K,T x≠0) :
    ∃r : ℝ,0<r ∧ (∀x∈K,r≤‖T x‖) ∧
      AnalyticOnNhd ℂ (fun t=>∫x in K,a x/(T x-t) ∂μ) (ball 0 r) ∧
      (∀t,‖t‖<r → IntegrableOn (fun x=>a x/(T x-t)) K μ) ∧
      (∀j : ℕ,IntegrableOn (fun x=>a x/(T x)^(j+1)) K μ ∧
        iteratedDeriv j (fun t=>∫x in K,a x/(T x-t) ∂μ) 0/(j.factorial:ℂ)=
          ∫x in K,a x/(T x)^(j+1) ∂μ) := by
  obtain ⟨r,hr,hgap⟩ := compact_nonzero_uniform_gap hK hT hne
  have hden (t : ℂ) (ht : t∈ball (0:ℂ) r) (x : X) (hx : x∈K) : T x-t≠0 := by
    intro he
    have heq := sub_eq_zero.mp he
    have ht' : ‖t‖<r := by simpa using ht
    have hg := hgap x hx
    rw [heq] at hg
    exact (not_lt_of_ge hg) ht'
  let H : ℕ→ℂ→X→ℂ := fun j t x=>iteratedDeriv j (fun s=>a x/(T x-s)) t
  have hform (j : ℕ) (t : ℂ) (x : X) : H j t x=(j.factorial:ℂ)*a x/(T x-t)^(j+1) :=
    pole_iterated_derivative (a x) (T x) t j
  have hcont (j : ℕ) : ContinuousOn (fun p : ℂ×X=>H j p.1 p.2) (ball 0 r ×ˢ K) := by
    simp_rw [hform]
    apply ContinuousOn.div
    · exact continuousOn_const.mul (ha.comp continuous_snd.continuousOn (fun _ hp=>hp.2))
    · exact ((hT.comp continuous_snd.continuousOn (fun _ hp=>hp.2)).sub continuous_fst.continuousOn).pow _
    · intro p hp
      exact pow_ne_zero _ (hden p.1 hp.1 p.2 hp.2)
  have hder (j : ℕ) (t : ℂ) (ht : t∈ball (0:ℂ) r) (x : X) (hx : x∈K) :
      HasDerivAt (fun s=>H j s x) (H (j+1) t x) t := by
    have hA : AnalyticAt ℂ (fun s : ℂ=>a x/(T x-s)) t :=
      analyticAt_const.div (analyticAt_const.sub analyticAt_id) (hden t ht x hx)
    simpa only [H,iteratedDeriv_eq_iterate,Function.iterate_succ',Function.comp_def] using
      (hA.iterated_deriv j).differentiableAt.hasDerivAt
  have hzero : (fun t=>∫x in K,H 0 t x ∂μ)=(fun t=>∫x in K,a x/(T x-t) ∂μ) := by
    simp only [H,iteratedDeriv_zero]
  refine ⟨r,hr,hgap,?_,?_,?_⟩
  · intro t ht
    rw [←hzero]
    exact compact_joint_jet_integral_analyticAt hK isOpen_ball H hcont hder ht
  · intro t ht
    have hc : ContinuousOn (fun x=>a x/(T x-t)) K :=
      ha.div (hT.sub continuousOn_const) (fun x hx=>hden t (by simpa using ht) x hx)
    exact hc.integrableOn_compact hK
  · intro j
    have hi : IntegrableOn (fun x=>a x/(T x)^(j+1)) K μ :=
      (ha.div (hT.pow _) (fun x hx=>pow_ne_zero _ (hne x hx))).integrableOn_compact hK
    refine ⟨hi,?_⟩
    have hj := compact_joint_jet_integral_iteratedDeriv (μ := μ) hK isOpen_ball H hcont hder j 0
      (by simpa using hr)
    simp only [←iteratedDeriv_eq_iterate,hzero] at hj
    rw [hj,←integral_div]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact pole_normalized_taylor_coefficient (a x) (T x) (hne x hx) j

/-- The compact pole theorem also applies to every subset of the compact set,
including open ellipsoids; no compactness of the integration subset is needed. -/
theorem restricted_compact_pole_integral_analytic_taylor
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {K E : Set X} (hK : IsCompact K) (hEK : E⊆K) {a T : X→ℂ}
    (ha : ContinuousOn a K) (hT : ContinuousOn T K) (hne : ∀x∈K,T x≠0) :
    ∃r : ℝ,0<r ∧ (∀x∈K,r≤‖T x‖) ∧
      AnalyticOnNhd ℂ (fun t=>∫x in E,a x/(T x-t) ∂μ) (ball 0 r) ∧
      (∀t,‖t‖<r → IntegrableOn (fun x=>a x/(T x-t)) E μ) ∧
      (∀j : ℕ,IntegrableOn (fun x=>a x/(T x)^(j+1)) E μ ∧
        iteratedDeriv j (fun t=>∫x in E,a x/(T x-t) ∂μ) 0/(j.factorial:ℂ)=
          ∫x in E,a x/(T x)^(j+1) ∂μ) := by
  have h := compact_pole_integral_analytic_taylor (μ := μ.restrict E) hK ha hT hne
  simpa only [IntegrableOn,Measure.restrict_restrict hK.measurableSet,
    inter_eq_right.mpr hEK] using h

end
end IsingBulk.Anisotropic.NegativeCycles
