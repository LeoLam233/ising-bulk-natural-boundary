import IsingBulk.Anisotropic.NegativeNormalForm.UniformRootBounds
import IsingBulk.Anisotropic.NegativeNormalForm.Homotopy

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm Set Filter Metric
open scoped BigOperators Topology
set_option maxHeartbeats 800000

theorem norm_quadratic_coordinate_root_error {n : ℕ} (v S : Config n) {e : ℝ}
    (he : 0≤e) (hS : ∀i, ‖S i-1‖≤e) :
    ‖quadratic (fun i => v i*S i)-quadratic v‖≤e*(e+2)*absoluteEnergy v := by
  have hsq (i : Fin n) : ‖S i^2-1‖≤e*(e+2) := by
    have ha : ‖S i+1‖≤e+2 := by
      calc
        _ = ‖(S i-1)+2‖ := by congr 1; ring
        _ ≤ ‖S i-1‖+‖(2:ℂ)‖ := norm_add_le _ _
        _ ≤ e+2 := by simpa using add_le_add_right (hS i) 2
    calc
      _ = ‖(S i-1)*(S i+1)‖ := by congr 1; ring
      _ ≤ e*(e+2) := by rw [norm_mul]; exact mul_le_mul (hS i) ha (norm_nonneg _) he
  have hid : quadratic (fun i => v i*S i)-quadratic v=∑i,v i^2*(S i^2-1) := by
    simp only [quadratic,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid]
  calc
    _ ≤ ∑i,‖v i^2*(S i^2-1)‖ := norm_sum_le _ _
    _ ≤ ∑i,‖v i‖^2*(e*(e+2)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,norm_pow]
      exact mul_le_mul_of_nonneg_left (hsq i) (sq_nonneg _)
    _ = _ := by simp only [absoluteEnergy,←Finset.sum_mul]; ring

theorem pole_quadratic_comparison_of_scalar_bounds {n : ℕ} (hn : n≠0)
    (B : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config n)
    (hm : ZeroMean v) (hh : centralHessian B phi d≠0)
    (ha : phaseParameterQuotient B phi hphi d t≠0)
    (hp : poleEquation B phi hphi d t v=0)
    (hhb : ‖centralHessian B phi d-1‖≤1/256)
    (hs : ∀i, ‖Complex.sqrt (phaseEnergy B phi hphi d t (v i))-1‖≤1/256) :
    ‖t-(1-Complex.cos d)-quadratic v/(2*n)‖≤absoluteEnergy v/(64*n) := by
  let h := centralHessian B phi d
  let S : Config n := fun i => Complex.sqrt (phaseEnergy B phi hphi d t (v i))
  let q := quadratic (fun i => v i*S i)
  have hq : ‖q-quadratic v‖≤(3/256)*absoluteEnergy v := by
    have ht := norm_quadratic_coordinate_root_error v S (by norm_num : (0:ℝ)≤1/256) hs
    exact ht.trans (by nlinarith [absoluteEnergy_nonneg v])
  have hhn : ‖h‖≤2 := by
    have ht := norm_sub_norm_le h 1
    simp only [norm_one] at ht
    change ‖h-1‖≤1/256 at hhb
    linarith
  have he := phaseSeparableMap_exact hn B phi hphi d t v hm hh ha hp
  change t-(1-Complex.cos d)=h/(2*n)*q at he
  have hd : ‖h*q-quadratic v‖≤(7/256)*absoluteEnergy v := by
    have hid : h*q-quadratic v=h*(q-quadratic v)+(h-1)*quadratic v := by ring
    rw [hid]
    calc
      _ ≤ ‖h‖*‖q-quadratic v‖+‖h-1‖*‖quadratic v‖ := by simpa only [norm_mul] using norm_add_le (h*(q-quadratic v)) ((h-1)*quadratic v)
      _ ≤ 2*((3/256)*absoluteEnergy v)+(1/256)*absoluteEnergy v := add_le_add
        (mul_le_mul hhn hq (norm_nonneg _) (by norm_num))
        (mul_le_mul hhb (norm_quadratic_le v) (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  rw [he]
  have hid : h/(2*(n:ℂ))*q-quadratic v/(2*n)=(h*q-quadratic v)/(2*n) := by ring
  rw [hid,norm_div,norm_mul]
  norm_num only [Complex.norm_natCast, Complex.norm_ofNat]
  have hnR : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  apply (div_le_div_of_nonneg_right hd (by positivity)).trans
  field_simp
  nlinarith [absoluteEnergy_nonneg v]

/-- Scalar analyticity discharges every comparison premise on one N-independent neighborhood. -/
theorem pole_quadratic_comparison_uniform (B : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) :
    ∃r : ℝ,0<r ∧ ∀n : ℕ, n≠0 → ∀d t : ℂ, ∀v : Config n,
      ‖d‖<r → ‖t‖<r → (∀i, ‖v i‖<r) → ZeroMean v →
      poleEquation B phi hphi d t v=0 →
      ‖t-(1-Complex.cos d)-quadratic v/(2*n)‖≤absoluteEnergy v/(64*n) := by
  obtain ⟨r,L,hr,_hL,hs,_hLip⟩ := phaseRootEnergy_uniform_small B phi hphi hB hBn
    (1/256) (by norm_num)
  have hqa := phaseParameterQuotient_joint_origin_analyticAt B phi hphi hB
  have hq0 : phaseParameterQuotient B phi hphi 0 0≠0 := by
    have hc := phaseParameterQuotient_center B phi hphi 0 (by simpa using hB)
    simp only [Complex.cos_zero,sub_self] at hc
    rw [hc]
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero)) hBn
  obtain ⟨a,ha,hqn⟩ := Metric.mem_nhds_iff.mp (hqa.continuousAt.eventually_ne hq0)
  have hh : ∀ᶠ d : ℂ in 𝓝 0,
      ‖centralHessian B phi d-1‖<1/256 ∧ centralHessian B phi d≠0 := by
    apply Filter.Eventually.and _ (centralHessian_eventually_nonzero B phi hB)
    exact ((centralHessian_analyticAt_zero B phi hB).continuousAt.sub continuousAt_const).norm.eventually_lt
      continuousAt_const (by change ‖centralHessian B phi 0-1‖<(1/256:ℝ); rw [centralHessian_zero]; norm_num)
  obtain ⟨b,hb,hhs⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨min r (min a b),lt_min hr (lt_min ha hb),?_⟩
  intro n hn d t v hd ht hv hm hp
  have hdR := hd.trans_le (min_le_left _ _)
  have htR := ht.trans_le (min_le_left _ _)
  have hdA := hd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htA := ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdB := hd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hhd := hhs (show d∈ball (0:ℂ) b by simpa using hdB)
  apply pole_quadratic_comparison_of_scalar_bounds hn B phi hphi d t v hm hhd.2
  · exact @hqn (t,d) (show (t,d)∈ball ((0:ℂ),(0:ℂ)) a by
      simpa only [mem_ball,Prod.dist_eq,dist_zero_right,max_lt_iff] using And.intro htA hdA)
  · exact hp
  · exact hhd.1.le
  · intro i
    exact (hs (t,(d,v i)) (max_lt htR (max_lt hdR
      ((hv i).trans_le (min_le_left _ _))))).2

end IsingBulk.Anisotropic.NegativeCycles
