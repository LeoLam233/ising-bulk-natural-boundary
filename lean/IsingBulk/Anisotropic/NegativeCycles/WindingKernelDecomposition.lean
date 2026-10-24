import IsingBulk.Anisotropic.NegativeCycles.PhysicalIntegralPartition

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory Metric
open scoped BigOperators
set_option maxHeartbeats 1500000

theorem centeredInnerSet_eq_empty_of_le (n : ℕ) {d s : ℝ} (hs : s≤(n+1:ℕ)*d^2) :
    centeredInnerSet n d s=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hq0 := constrainedSquaredRadius_nonneg q
  change constrainedSquaredRadius q<s-(n+1:ℕ)*d^2 at hq
  linarith

theorem inactive_centeredKernelIntegral (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (m : ℕ) {d s : ℝ} (hs : s≤(2*m+1:ℕ)*d^2) :
    centeredKernelIntegral B rootB phi hphi m d s=0 := by
  funext t
  simp only [centeredKernelIntegral,centeredInnerSet_eq_empty_of_le (2*m) hs,setIntegral_empty,Pi.zero_apply]

theorem exists_winding_kernel_decomposition (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hrB : AnalyticAt ℂ rootB 0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃(R₀ : ℂ→ℂ) (ρ c σ K M : ℝ),0<ρ ∧ 0<c ∧ 0<σ ∧ 0<K ∧ 1≤M ∧
      ∀m : ℕ, ∀s : ℝ,s<σ →
      ∀P : (k : Fin (2*m+2)) → (2*m+1:ℕ)*(windingMean (2*m) k)^2<s →
        UniformProjectedWitness B phi hphi (2*m+1) (windingMean (2*m) k:ℂ) r C,
      ∀_J : (k : Fin (2*m+2)) → (hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s) →
        UniformCorrectionWitness B phi hphi (2*m+1) (windingMean (2*m) k:ℂ) r C (P k hk) R,
      ∀j : ℕ,
      (∑k : Fin (2*m+2),iteratedDeriv j
        (centeredKernelIntegral B rootB phi hphi m (windingMean (2*m) k) s) 0/(j.factorial:ℂ))=
      (∑k : Fin (2*m+2),if hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s then
        ∫q in centeredInnerSet (2*m) (windingMean (2*m) k) s,
          constrainedResidueDensity B rootB phi hphi (windingMean (2*m) k:ℂ) (P k hk).T j
            (complexify (2*m) q) else 0)+
      (∑k : Fin (2*m+2),if hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s then
        iteratedDeriv j (centeredInnerRemainder B rootB phi hphi R₀ m (windingMean (2*m) k) s
          (P k hk).T) 0/(j.factorial:ℂ) else 0) ∧
      (∀k hk,‖iteratedDeriv j (centeredInnerRemainder B rootB phi hphi R₀ m (windingMean (2*m) k) s
          (P k hk).T) 0/(j.factorial:ℂ)‖≤
        ((volume (centeredInnerSet (2*m) (windingMean (2*m) k) s)).toReal*(K*remainderGaussianEnvelope M m))/
          ((c/(2*m+1:ℕ))/2)^j) := by
  obtain ⟨R₀,ρ,c,σ,K,M,hρ,hc,hσ,hK,hM,hw⟩ :=
    exists_centered_kernel_taylor B rootB phi hphi hB hB0 hrB r C R hr hR hRr
  refine ⟨R₀,ρ,c,min σ (ρ^2),K,M,hρ,hc,lt_min hσ (sq_pos_of_pos hρ),hK,hM,?_⟩
  intro m s hs P J j
  have hd (k : Fin (2*m+2)) (hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s) :
      |windingMean (2*m) k|<ρ := by
    have hN : (1:ℝ)≤(2*m+1:ℕ) := by exact_mod_cast (by omega : 1≤2*m+1)
    have hsq := sq_nonneg (windingMean (2*m) k)
    have hsρ := hs.trans_le (min_le_right σ (ρ^2))
    rw [abs_lt]
    constructor <;> nlinarith
  constructor
  · rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    by_cases hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s
    · simp only [dite_eq_left hk]
      exact (hw m (windingMean (2*m) k) (hd k hk) (odd_windingMean_ne_zero m k)
        (P k hk) (J k hk) s (hs.trans_le (min_le_left _ _))).2.2 j |>.2
    · simp only [dite_eq_right hk,inactive_centeredKernelIntegral B rootB phi hphi m (le_of_not_gt hk),
        add_zero]
      change iteratedDeriv j (fun _ : ℂ => (0:ℂ)) 0/(j.factorial:ℂ)=0
      simp only [iteratedDeriv_fun_const_zero,zero_div]
  · intro k hk
    exact (hw m (windingMean (2*m) k) (hd k hk) (odd_windingMean_ne_zero m k)
      (P k hk) (J k hk) s (hs.trans_le (min_le_left _ _))).2.1 j

end IsingBulk.Anisotropic.NegativeCycles
