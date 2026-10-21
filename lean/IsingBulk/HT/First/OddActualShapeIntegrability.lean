import IsingBulk.First.ActualShapeNeighborhood
import IsingBulk.HT.First.OddRemainderLimit

/-! Absolute integrability at each positive ε, without an even-degree
hypothesis. A fixed-ball polynomial majorant suffices for every pole order. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex MeasureTheory Set Filter Metric IsingBulk.First

/-- Positive damping yields absolute integrability on every fixed support
ball, independently of the singular derivative index and particle parity. -/
theorem shape_cutoff_pole_integrable_positive_gap {n : ℕ} (hn : 1 ≤ n)
    (ell : ℕ) (A D chi : ShapeSpace n → ℂ) (R : ℝ) {epsilon M c : ℝ}
    (he : 0 < epsilon) (hM : 0 ≤ M) (hc : 0 < c)
    (hchi : Continuous chi) (hchib : ∀ x,‖chi x‖ ≤ 1)
    (hchis : ∀ x,chi x ≠ 0 → ‖x‖ < R)
    (hAcont : ContinuousOn A (ball 0 R)) (hDcont : ContinuousOn D (ball 0 R))
    (hAbound : ∀ x ∈ ball 0 R,‖A x‖ ≤ M)
    (hDbound : ∀ x ∈ ball 0 R,c*(epsilon+‖x‖^2) ≤ ‖D x‖) :
    Integrable (fun x => (shapeVandermondeSq x:ℂ)*chi x*A x/(D x)^ell) := by
  have hg : 0 < c*epsilon := mul_pos hc he
  have hgap (x : ShapeSpace n) (hx : x ∈ ball 0 R) : c*epsilon ≤ ‖D x‖ := by
    have hb := hDbound x hx
    nlinarith [mul_nonneg hc.le (sq_nonneg ‖x‖)]
  have hv : IntegrableOn (shapeVandermondeSq (n := n)) (ball 0 R) := by
    simpa using shape_power_integrableOn hn (ell := 0) (by omega) R
  have hi := hv.const_mul (M/(c*epsilon)^ell)
  have hq : ContinuousOn
      (fun x => (shapeVandermondeSq x:ℂ)*chi x*A x/(D x)^ell) (ball 0 R) := by
    apply (((Complex.continuous_ofReal.comp (shapeVandermondeSq_continuous n)).continuousOn.mul
      hchi.continuousOn).mul hAcont).div (hDcont.pow ell)
    intro x hx
    exact pow_ne_zero _ (norm_pos_iff.mp (hg.trans_le (hgap x hx)))
  have hlocal : IntegrableOn
      (fun x => (shapeVandermondeSq x:ℂ)*chi x*A x/(D x)^ell) (ball 0 R) := by
    apply hi.mono' (hq.aestronglyMeasurable measurableSet_ball)
    filter_upwards [self_mem_ae_restrict measurableSet_ball] with x hx
    have ha : ‖chi x*A x‖ ≤ M := by
      rw [norm_mul]
      exact (mul_le_mul (hchib x) (hAbound x hx) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul M)
    have hh := norm_shape_pole_le (k := ell) hM hg x (chi x*A x) (D x) ha (hgap x hx)
    convert hh using 1 <;> ring
  apply hlocal.integrable_of_forall_notMem_eq_zero
  intro x hx
  have hz : chi x = 0 := by
    by_contra hh
    exact hx (mem_ball_zero_iff.mpr (hchis x hh))
  simp only [hz,mul_zero,zero_mul,zero_div]

/-- Both generated pole terms are absolutely integrable before splitting the
actual differentiated post-mean density. -/
theorem actual_pole_shapes_integrable {n : ℕ} (hn : 1 ≤ n)
    (a : OrderedChartData) (k : ℕ)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R : ℝ,0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → (∀ x,‖chi x‖ ≤ 1) → (∀ x,chi x ≠ 0 → ‖x‖ < R) →
      ∀ epsilon ∈ Ioo 0 R,
        Integrable (fun x => (shapeVandermondeSq x:ℂ)*chi x*intrinsicLeadingAmplitude a k (epsilon,x)/
          (actualShapeDenominator a epsilon x)^(k+1)) ∧
        Integrable (fun x => (shapeVandermondeSq x:ℂ)*chi x*intrinsicRemainderAmplitude a k (epsilon,x)/
          (actualShapeDenominator a epsilon x)^k) := by
  obtain ⟨rA,M,hrA,hM,hA⟩ := intrinsic_actual_uniform_neighborhood (n := n) a k
  obtain ⟨c,rD,hc,hrD,hD⟩ := actualShapeDenominator_uniform_lower (n := n) a hb
  let R := min rA rD
  refine ⟨R,lt_min hrA hrD,?_⟩
  intro chi hchi hchib hchis epsilon he
  have hdata (x : ShapeSpace n) (hx : x ∈ ball 0 R) :=
    hA epsilon x (by rw [abs_of_pos he.1]; exact he.2.trans_le (min_le_left _ _))
      ((by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖ < R).trans_le (min_le_left _ _))
  have hDc : ContinuousOn (actualShapeDenominator a epsilon) (ball 0 R) := fun x hx =>
    ((hdata x hx).2.2.1.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hDb (x : ShapeSpace n) (hx : x ∈ ball 0 R) :=
    hD epsilon x he.1 (he.2.trans_le (min_le_right _ _))
      ((by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖ < R).trans_le (min_le_right _ _))
  constructor
  · exact shape_cutoff_pole_integrable_positive_gap hn (k+1) _ _ chi R he.1 hM.le hc hchi hchib hchis
      (fun x hx => ((hdata x hx).1.comp
        (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
      hDc (fun x hx => (hdata x hx).2.2.2.1) hDb
  · exact shape_cutoff_pole_integrable_positive_gap hn k _ _ chi R he.1 hM.le hc hchi hchib hchis
      (fun x hx => ((hdata x hx).2.1.comp
        (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
      hDc (fun x hx => (hdata x hx).2.2.2.2) hDb

end
end IsingBulk.HT.First
