import IsingBulk.Preferred22.CollectiveDifference
import IsingBulk.Preferred22.CollectiveNeighborhood

/-! The actual anisotropic neighborhood geometry, exposing its true R
margin for the finite-block pair-diagonal factors. The proof is the same
source pair perturbation argument as CollectiveNeighborhood, with its
intermediate geometric conclusion retained explicitly. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferred_collective_scaled_geometry {N : ℕ} (hN : 0<N)
    (center s₀ s : ℂ) (q q' : Fin N → ℂ) (D : Set ℂ)
    (R κ C c r d dmax η : ℝ)
    (_hR : 0<R) (hκ : 0<κ) (hC : 1≤C) (_hc : 0<c) (hr : 0<r)
    (hd : 0<d) (hdmax : d≤dmax) (hη : 0<η) (hη1 : η≤1)
    (hηR : η≤R/2) (hηκ : η*dmax≤κ) (hηr : η≤r/(16*C^2))
    (hD : Convex ℝ D)
    (hs₀ : ‖s₀-center‖≤R/2)
    (hqmargin : ∀ i, closedBall (q i) κ⊆D)
    (hU : ∀ t z, ‖t-center‖≤R → z∈D →
      AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (t,z))
    (_hB : ∀ t, ‖t-center‖≤R → AnalyticAt ℂ preferredMovingBranch t)
    (hv : ∀ t z, ‖t-center‖≤R → z∈D → ‖preferredSourceUQ t z‖≤C)
    (_hdot : ∀ t z, ‖t-center‖≤R → z∈D → ‖preferredSourceUDot t z‖≤C)
    (_hc₀ : ∀ t, ‖t-center‖≤R → ‖deriv preferredMovingBranch t‖≤C)
    (_hcurv : ∀ t z, ‖t-center‖≤R → z∈D → c≤(deriv (preferredSourceUQ t) z).re)
    (hpair : ∀ i j, ‖preferredMovingInverse s₀ (q i)-preferredMovingInverse s₀ (q j)‖≤C*d)
    (hpairD : ∀ t i j, ‖t-center‖≤R →
      ‖deriv (fun v => preferredMovingInverse v (q i)-preferredMovingInverse v (q j)) t‖≤C*d)
    (hbaseR : r*d^2≤‖collectiveDenominator (fun i => preferredMovingInverse s₀ (q i))‖)
    (hs : ‖s-s₀‖≤η/(N:ℝ)^2) (hqq : ‖q'-q‖≤η*d/(N:ℝ)^2) :
    ‖s-center‖≤R ∧ (∀ i,q' i∈D) ∧
      r*d^2/2≤‖collectiveDenominator (fun i => preferredMovingInverse s (q' i))‖ := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hn2 : (1:ℝ)≤(N:ℝ)^2 := one_le_pow₀ hn1
  have hC0 : 0<C := lt_of_lt_of_le (by norm_num) hC
  have hdmax0 : 0<dmax := hd.trans_le hdmax
  have hq (i : Fin N) : q i∈D := hqmargin i (mem_closedBall_self hκ.le)
  have hqs : ‖q'-q‖≤κ := by
    calc
      _ ≤ η*d/(N:ℝ)^2 := hqq
      _ ≤ η*d := div_le_self (by positivity) hn2
      _ ≤ η*dmax := mul_le_mul_of_nonneg_left hdmax hη.le
      _ ≤ κ := hηκ
  have hq' (i : Fin N) : q' i∈D := by
    apply hqmargin i
    change dist (q' i) (q i)≤κ
    rw [dist_eq_norm]
    exact (norm_le_pi_norm (q'-q) i).trans hqs
  have hs' : ‖s-center‖≤R := by
    have hstep : ‖s-s₀‖≤R/2 := hs.trans
      ((div_le_self hη.le hn2).trans hηR)
    have hh := norm_add_le (s-s₀) (s₀-center)
    rw [sub_add_sub_cancel] at hh
    linarith
  have hs₀' : ‖s₀-center‖≤R := hs₀.trans (by linarith)
  have hdiff (i j : Fin N) :
      ‖(preferredMovingInverse s (q' i)-preferredMovingInverse s (q' j))-
        (preferredMovingInverse s₀ (q i)-preferredMovingInverse s₀ (q j))‖≤3*C*η*d/(N:ℝ)^2 := by
    have hp := preferred_parameter_pair_lipschitz s₀ s center (q i) (q j) R (C*d)
      (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs₀')
      (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs')
      (fun t ht => ⟨hU t (q i) (by simpa only [Metric.mem_closedBall,dist_eq_norm] using ht) (hq i),
        hU t (q j) (by simpa only [Metric.mem_closedBall,dist_eq_norm] using ht) (hq j)⟩)
      (fun t ht => hpairD t i j (by simpa only [Metric.mem_closedBall,dist_eq_norm] using ht))
    have hqp := preferred_inverse_pair_perturbation s q q' D C hC0.le hD
      (fun z hz => (AnalyticAt.comp (f:=fun x : ℂ => (s,x))
        (g:=fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (hU s z hs' hz)
        (analyticAt_const.prod analyticAt_id)).differentiableAt)
      (hv s · hs') hq hq' i j
    have htri := norm_add_le
      ((preferredMovingInverse s (q' i)-preferredMovingInverse s (q' j))-
        (preferredMovingInverse s (q i)-preferredMovingInverse s (q j)))
      ((preferredMovingInverse s (q i)-preferredMovingInverse s (q j))-
        (preferredMovingInverse s₀ (q i)-preferredMovingInverse s₀ (q j)))
    rw [sub_add_sub_cancel] at htri
    calc
      _ ≤ 2*C*‖q'-q‖+(C*d)*‖s-s₀‖ := htri.trans (add_le_add hqp hp)
      _ ≤ 2*C*(η*d/(N:ℝ)^2)+(C*d)*(η/(N:ℝ)^2) := by gcongr
      _ = _ := by ring
  have hRp := collectiveDenominator_scaled_margin hN
    (fun i => preferredMovingInverse s₀ (q i)) (fun i => preferredMovingInverse s (q' i))
    C d r η hC0 hd hr hη hη1 hηr hpair hdiff hbaseR
  exact ⟨hs',hq',hRp⟩


theorem preferred_collective_difference_scaled_neighborhood {N : ℕ} (hN : 0<N)
    (center s₀ s : ℂ) (q q' : Fin N → ℂ) (D : Set ℂ)
    (R κ C c r d dmax η : ℝ)
    (_hR : 0<R) (hκ : 0<κ) (hC : 1≤C) (hc : 0<c) (hr : 0<r)
    (hd : 0<d) (hdmax : d≤dmax) (hη : 0<η) (hη1 : η≤1)
    (hηR : η≤R/2) (hηκ : η*dmax≤κ) (hηr : η≤r/(16*C^2))
    (hD : Convex ℝ D)
    (hs₀ : ‖s₀-center‖≤R/2)
    (hqmargin : ∀ i, closedBall (q i) κ⊆D)
    (hU : ∀ t z, ‖t-center‖≤R → z∈D →
      AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (t,z))
    (hB : ∀ t, ‖t-center‖≤R → AnalyticAt ℂ preferredMovingBranch t)
    (hv : ∀ t z, ‖t-center‖≤R → z∈D → ‖preferredSourceUQ t z‖≤C)
    (hdot : ∀ t z, ‖t-center‖≤R → z∈D → ‖preferredSourceUDot t z‖≤C)
    (hc₀ : ∀ t, ‖t-center‖≤R → ‖deriv preferredMovingBranch t‖≤C)
    (hcurv : ∀ t z, ‖t-center‖≤R → z∈D → c≤(deriv (preferredSourceUQ t) z).re)
    (hpair : ∀ i j, ‖preferredMovingInverse s₀ (q i)-preferredMovingInverse s₀ (q j)‖≤C*d)
    (hpairD : ∀ t i j, ‖t-center‖≤R →
      ‖deriv (fun v => preferredMovingInverse v (q i)-preferredMovingInverse v (q j)) t‖≤C*d)
    (hbaseR : r*d^2≤‖collectiveDenominator (fun i => preferredMovingInverse s₀ (q i))‖)
    (M : ℝ) (hM : 0≤M)
    (hPairD : ∀ t q r z : ℂ,‖t-center‖≤R → q∈D → r∈D → z∈D →
      ‖preferredCollectivePairDifference t q r z‖≤M)
    (i j : Fin N)
    (hs : ‖s-s₀‖≤η/(N:ℝ)^2) (hqq : ‖q'-q‖≤η*d/(N:ℝ)^2) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredCollectiveDifferenceFactor z.1 z.2 i j) (s,q') ∧
      ‖preferredCollectiveDifferenceFactor s q' i j‖≤
        (2*C*(1+C)*M/r)*(N:ℝ)^2/d^2 := by
  obtain ⟨hs',hq',hRp⟩ := preferred_collective_scaled_geometry hN center s₀ s q q' D R κ C c r d dmax η
    _hR hκ hC hc hr hd hdmax hη hη1 hηR hηκ hηr hD hs₀ hqmargin hU hB hv hdot hc₀ hcurv
    hpair hpairD hbaseR hs hqq
  have hC0 : 0≤C := zero_le_one.trans hC
  have hRne : collectiveDenominator (fun a => preferredMovingInverse s (q' a))≠0 := by
    intro hz
    rw [hz,norm_zero] at hRp
    have hh : 0<r*d^2/2 := by positivity
    linarith
  refine ⟨preferredCollectiveDifferenceFactor_analyticAt_of_curvature s q' i j D c hc hD
    (hU s · hs') (hB s hs') (hcurv s · hs') hq' hRne,?_⟩
  have hdotSum : ‖∑ a,preferredSourceUDot s (q' a)‖≤(N:ℝ)*C :=
    (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (s := Finset.univ) (fun a _ => hdot s (q' a) hs' (hq' a)))
  have hvSum : ‖∑ a,preferredSourceUQ s (q' a)‖≤(N:ℝ)*C :=
    (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (s := Finset.univ) (fun a _ => hv s (q' a) hs' (hq' a)))
  have hE : ‖collectiveResidual (fun a => preferredSourceUDot s (q' a))
      (fun a => preferredSourceUQ s (q' a)) (-deriv preferredMovingBranch s)‖≤(N:ℝ)*(C*(1+C)) := by
    unfold collectiveResidual
    calc
      _ ≤ ‖∑ a,preferredSourceUDot s (q' a)‖+
          ‖deriv preferredMovingBranch s‖*‖∑ a,preferredSourceUQ s (q' a)‖ := by
        simpa only [norm_neg,norm_mul] using norm_sub_le
          (-(∑ a,preferredSourceUDot s (q' a)))
          ((-deriv preferredMovingBranch s)*(∑ a,preferredSourceUQ s (q' a)))
      _ ≤ (N:ℝ)*C+C*((N:ℝ)*C) := add_le_add hdotSum
        (mul_le_mul (hc₀ s hs') hvSum (norm_nonneg _) hC0)
      _ = _ := by ring
  have hh := preferredCollectiveDifferenceFactor_bound s q' i j (by positivity : 0≤C*(1+C))
    hM (half_pos hr) hd hE (by nlinarith [hRp])
    (fun a => hPairD s (q' i) (q' j) (q' a) hs' (hq' i) (hq' j) (hq' a))
  apply hh.trans_eq
  ring

end
end IsingBulk.Preferred22
