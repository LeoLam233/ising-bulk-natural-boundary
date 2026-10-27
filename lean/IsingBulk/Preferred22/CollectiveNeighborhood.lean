import IsingBulk.Preferred22.CollectiveBounds
import IsingBulk.Preferred22.AnalyticCauchyBounds

/-! Actual analytic neighborhoods of the residual collective field.
The anisotropic scales preserve the diameter square in R under parameter
variation, while allowing the required polynomial dependence on N. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Compactness bounds the literal Uq, Udot and moving-branch derivative
simultaneously on the complete constructed right domain. -/
theorem preferred_compact_collective_bounds (d : PreferredBranchData) (ρ c : ℝ)
    (D : Set ℂ) (hρ : 0<ρ) (hDc : IsCompact D)
    (hg : ∀ s q r : ℂ, ‖s-preferredSelectedPoint d‖<ρ → q∈D → r∈D →
      PreferredRightRegularPoint c s q r) :
    ∃ L : ℝ, 1≤L ∧ ∀ s q : ℂ, ‖s-preferredSelectedPoint d‖≤ρ/2 → q∈D →
      ‖preferredSourceUQ s q‖≤L ∧ ‖preferredSourceUDot s q‖≤L ∧
      ‖deriv preferredMovingBranch s‖≤L := by
  let X := closedBall (preferredSelectedPoint d) (ρ/2) ×ˢ D
  let F : ℂ × ℂ → ℂ × (ℂ × ℂ) := fun z =>
    (preferredSourceUQ z.1 z.2,(preferredSourceUDot z.1 z.2,deriv preferredMovingBranch z.1))
  have hX : IsCompact X := (isCompact_closedBall _ _).prod hDc
  have hFc : ContinuousOn F X := by
    intro z hz
    have hs : ‖z.1-preferredSelectedPoint d‖≤ρ/2 := by
      simpa only [Metric.mem_closedBall,dist_eq_norm] using hz.1
    have hh := hg z.1 z.2 z.2 (by linarith) hz.2 hz.2
    have hv := preferredSourceUQ_analyticAt_of_joint z.1 z.2 hh.2.1
    have hd := preferredSourceUDot_analyticAt_of_joint z.1 z.2 hh.2.1
    exact (hv.continuousAt.prodMk (hd.continuousAt.prodMk
      (hh.1.deriv.continuousAt.comp continuousAt_fst))).continuousWithinAt
  obtain ⟨M,hM⟩ := hX.exists_bound_of_continuousOn hFc
  let L := max M 1
  refine ⟨L,le_max_right _ _,?_⟩
  intro s q hs hq
  have hz : (s,q)∈X := ⟨by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs,hq⟩
  have hh := (hM (s,q) hz).trans (le_max_left M 1)
  change max ‖preferredSourceUQ s q‖
    (max ‖preferredSourceUDot s q‖ ‖deriv preferredMovingBranch s‖)≤L at hh
  exact ⟨(le_max_left _ _).trans hh,
    (le_max_left _ _).trans ((le_max_right _ _).trans hh),
    (le_max_right _ _).trans ((le_max_right _ _).trans hh)⟩

/-- True parameter variation of a fixed pair of inverse values. -/
theorem preferred_parameter_pair_lipschitz (s₀ s center q r : ℂ) (R A : ℝ)
    (hs₀ : s₀∈closedBall center R) (hs : s∈closedBall center R)
    (hU : ∀ t∈closedBall center R,
      AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (t,q) ∧
      AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (t,r))
    (hA : ∀ t∈closedBall center R,
      ‖deriv (fun v => preferredMovingInverse v q-preferredMovingInverse v r) t‖≤A) :
    ‖(preferredMovingInverse s q-preferredMovingInverse s r)-
      (preferredMovingInverse s₀ q-preferredMovingInverse s₀ r)‖≤A*‖s-s₀‖ := by
  apply (convex_closedBall center R).norm_image_sub_le_of_norm_hasDerivWithin_le _ hA hs₀ hs
  intro t ht
  have hq := AnalyticAt.comp (f:=fun v : ℂ => (v,q))
    (g:=fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (hU t ht).1
    (analyticAt_id.prod analyticAt_const)
  have hr := AnalyticAt.comp (f:=fun v : ℂ => (v,r))
    (g:=fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (hU t ht).2
    (analyticAt_id.prod analyticAt_const)
  exact (hq.sub hr).differentiableAt.hasDerivAt.hasDerivWithinAt

/-- Perturbing all q coordinates in the supremum norm costs only twice the
one-body Uq bound for any pair, independently of particle count. -/
theorem preferred_inverse_pair_perturbation {N : ℕ} (s : ℂ) (q q' : Fin N → ℂ)
    (D : Set ℂ) (L : ℝ) (hL : 0≤L) (hD : Convex ℝ D)
    (hU : ∀ z∈D, DifferentiableAt ℂ (preferredMovingInverse s) z)
    (hv : ∀ z∈D, ‖preferredSourceUQ s z‖≤L)
    (hq : ∀ i, q i∈D) (hq' : ∀ i, q' i∈D) (i j : Fin N) :
    ‖(preferredMovingInverse s (q' i)-preferredMovingInverse s (q' j))-
      (preferredMovingInverse s (q i)-preferredMovingInverse s (q j))‖≤2*L*‖q'-q‖ := by
  have hpair (k : Fin N) : ‖preferredMovingInverse s (q' k)-preferredMovingInverse s (q k)‖≤L*‖q'-q‖ := by
    have hh := hD.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hU z hz).hasDerivAt.hasDerivWithinAt) hv (hq k) (hq' k)
    exact hh.trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm (q'-q) k) hL)
  calc
    _ = ‖(preferredMovingInverse s (q' i)-preferredMovingInverse s (q i))-
        (preferredMovingInverse s (q' j)-preferredMovingInverse s (q j))‖ := by congr 1; ring
    _ ≤ ‖preferredMovingInverse s (q' i)-preferredMovingInverse s (q i)‖+
        ‖preferredMovingInverse s (q' j)-preferredMovingInverse s (q j)‖ := norm_sub_le _ _
    _ ≤ 2*L*‖q'-q‖ := by linarith [hpair i,hpair j]

/-- A quantitative actual R margin on the anisotropic neighborhood. The
pair perturbation estimate retains d² and the radius costs only N². -/
theorem collectiveDenominator_scaled_margin {N : ℕ} (hN : 0<N)
    (u v : Fin N → ℂ) (C d r η : ℝ)
    (hC : 0<C) (hd : 0<d) (hr : 0<r) (hη : 0<η) (hη1 : η≤1)
    (hηr : η≤r/(16*C^2))
    (hu : ∀ i j, ‖u i-u j‖≤C*d)
    (hdiff : ∀ i j, ‖(v i-v j)-(u i-u j)‖≤3*C*η*d/(N:ℝ)^2)
    (hR : r*d^2≤‖collectiveDenominator u‖) :
    r*d^2/2≤‖collectiveDenominator v‖ := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hn2 : (1:ℝ)≤(N:ℝ)^2 := one_le_pow₀ hn1
  have hsmall : 3*C*η*d/(N:ℝ)^2≤3*C*d := by
    calc
      _ ≤ 3*C*η*d := div_le_self (by positivity) hn2
      _ = (3*C*d)*η := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hη1
  have hb := collectiveDenominator_perturbation u v (C*d) (3*C*η*d/(N:ℝ)^2)
    (by positivity) (by positivity) hu hdiff
  have hbound : ‖collectiveDenominator v-collectiveDenominator u‖≤r*d^2/2 := by
    calc
      _ ≤ (N:ℝ)^2*(2*(C*d)+3*C*d)*(3*C*η*d/(N:ℝ)^2)/2 := by
        exact hb.trans (by gcongr)
      _ = (15/2:ℝ)*C^2*η*d^2 := by field_simp; ring
      _ ≤ r*d^2/2 := by
        have hh := (le_div_iff₀ (by positivity : 0<16*C^2)).mp hηr
        nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg d)]
  have htri := norm_sub_le (collectiveDenominator v) (collectiveDenominator v-collectiveDenominator u)
  rw [sub_sub_cancel] at htri
  linarith

/-- Actual B is analytic and quantitatively bounded throughout one
anisotropic neighborhood of a source configuration. The parameter radius
does not shrink with diameter; the q radius has precisely one diameter. -/
theorem preferred_collective_scaled_neighborhood {N : ℕ} (hN : 0<N)
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
    (hs : ‖s-s₀‖≤η/(N:ℝ)^2) (hqq : ‖q'-q‖≤η*d/(N:ℝ)^2) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredResidualCollective z.1 z.2) (s,q') ∧
      ‖preferredResidualCollective s q'‖≤
        (C*dmax+8*C^3*(1+C)/(c*r))*(N:ℝ)^2/d := by
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
  have hRne : collectiveDenominator (fun i => preferredMovingInverse s (q' i))≠0 := by
    intro hz
    rw [hz,norm_zero] at hRp
    have : 0<r*d^2/2 := by positivity
    linarith
  refine ⟨preferredResidualCollective_analyticAt_of_curvature s q' D c hc hD
    (hU s · hs') (hB s hs') (hcurv s · hs') hq' hRne,?_⟩
  have hp' (i j : Fin N) :
      ‖preferredMovingInverse s (q' i)-preferredMovingInverse s (q' j)‖≤(4*C)*d := by
    have hδ : 3*C*η*d/(N:ℝ)^2≤3*C*d := by
      calc
        _ ≤ 3*C*η*d := div_le_self (by positivity) hn2
        _ = (3*C*d)*η := by ring
        _ ≤ _ := mul_le_of_le_one_right (by positivity) hη1
    have hh := norm_add_le
      ((preferredMovingInverse s (q' i)-preferredMovingInverse s (q' j))-
        (preferredMovingInverse s₀ (q i)-preferredMovingInverse s₀ (q j)))
      (preferredMovingInverse s₀ (q i)-preferredMovingInverse s₀ (q j))
    rw [sub_add_cancel] at hh
    nlinarith [hdiff i j,hpair i j]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hh := preferredResidualCollective_norm_bound s q' D C c (4*C) (r/2) d
    hC0.le hc (by positivity) (half_pos hr) hd hD hq' (hU s · hs')
    (hv s · hs') (fun i => hdot s (q' i) hs' (hq' i)) (hc₀ s hs')
    (hcurv s · hs') hp' (by nlinarith [hRp]) i
  have hscale : C≤C*dmax*(N:ℝ)^2/d := by
    apply (le_div_iff₀ hd).mpr
    calc
      C*d ≤ C*dmax := mul_le_mul_of_nonneg_left hdmax hC0.le
      _ ≤ C*dmax*(N:ℝ)^2 := le_mul_of_one_le_right (by positivity) hn2
  calc
    _ ≤ C+(N:ℝ)^2*C*(1+C)*(4*C)*C/(c*(r/2)*d) := hh
    _ ≤ C*dmax*(N:ℝ)^2/d+(N:ℝ)^2*C*(1+C)*(4*C)*C/(c*(r/2)*d) := add_le_add hscale le_rfl
    _ = _ := by field_simp; ring

end
end IsingBulk.Preferred22
