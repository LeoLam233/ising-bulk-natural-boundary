import IsingBulk.HT22.First.LocalLimit.Scaling
import IsingBulk.HT.First.OddRemainderLimit
import IsingBulk.HT.First.OddActualShapeIntegrability

/-! The lower-pole remainder is negligible at the F001 epsilon^{-1} scale.
Only the generic radial majorant is reused; actual hypotheses are proved. -/
namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex MeasureTheory Set Filter Metric IsingBulk.First
open IsingBulk.HT.First
open scoped Topology
set_option maxHeartbeats 1000000

theorem equalAngle_remainder_shape_limit {n : ℕ} (hn : 1≤n) (ho : Odd (n+1))
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) :
    let a := equalAngleRegularData α hα hαπ hc
    let k := derivativeOrder (n+1)
    ∃ R : ℝ, 0<R ∧ ∀ χ : ShapeSpace n → ℂ,
      Continuous χ → (∀ x,‖χ x‖≤1) → (∀ x,χ x≠0 → ‖x‖<R) →
      Tendsto (fun ε : ℝ => ε • ∫ x : ShapeSpace n,
        (shapeVandermondeSq x:ℂ)*χ x*Regular.intrinsicRemainderAmplitude a k (ε,x)/
          (Regular.actualShapeDenominator a ε x)^k) (𝓝[>] 0) (𝓝 0) := by
  dsimp only
  let a := equalAngleRegularData α hα hαπ hc
  let k := derivativeOrder (n+1)
  have hp3 : 3≤n+1 := by obtain ⟨m,hm⟩ := ho; omega
  have hk : 1≤k := derivativeOrder_pos ho hp3
  have hdegree : n-1+(n+1)*n=2*k-1 := by
    simpa only [Nat.add_sub_cancel] using odd_shape_radial_exponent ho hp3
  obtain ⟨rA,M,hrA,hM,hA⟩ := Regular.intrinsic_actual_uniform_neighborhood (n:=n) a k
  obtain ⟨c,rD,hc0,hrD,hD⟩ := Regular.actualShapeDenominator_uniform_lower (n:=n) a ha
  let R := min rA rD
  have hR : 0<R := lt_min hrA hrD
  refine ⟨R,hR,?_⟩
  intro χ hχ hχb hχs
  have hdata (ε : ℝ) (he : ε ∈ Ioo 0 R) (x : ShapeSpace n) (hx : x ∈ ball 0 R) :=
    hA ε x (by rw [abs_of_pos he.1];exact he.2.trans_le (min_le_left _ _))
      ((by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖<R).trans_le (min_le_left _ _))
  have ht := odd_remainder_setIntegral_epsilon_limit hn hk hdegree
    (fun ε x => χ x*Regular.intrinsicRemainderAmplitude a k (ε,x))
    (fun ε x => Regular.actualShapeDenominator a ε x) (R:=R) hM.le hc0 hR
    (fun ε he => hχ.continuousOn.mul (fun x hx =>
      ((hdata ε he x hx).2.1.comp
        (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt))
    (fun ε he x hx => ((hdata ε he x hx).2.2.1.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
    (fun ε he x hx => by
      rw [norm_mul]
      exact (mul_le_mul (hχb x) (hdata ε he x hx).2.2.2.2
        (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul M))
    (fun ε he x hx => hD ε x he.1 (he.2.trans_le (min_le_right _ _))
      ((by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖<R).trans_le (min_le_right _ _)))
  apply ht.congr'
  exact Eventually.of_forall fun ε => by
    dsimp only
    congr 1
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    · intro x hx
      have hz : χ x=0 := by
        by_contra hh
        exact hx (mem_ball_zero_iff.mpr (hχs x hh))
      simp only [hz,zero_mul,mul_zero,zero_div]

/-- Both terms of the generated pole decomposition are genuinely integrable
for each positive epsilon before taking their limiting sum. -/
theorem equalAngle_pole_integrable {n : ℕ} (hn : 1≤n)
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) (k : ℕ) :
    let a := equalAngleRegularData α hα hαπ hc
    ∃ R : ℝ, 0<R ∧ ∀ χ : ShapeSpace n → ℂ,
      Continuous χ → (∀ x,‖χ x‖≤1) → (∀ x,χ x≠0 → ‖x‖<R) →
      ∀ ε ∈ Ioo 0 R,
        Integrable (fun x => (shapeVandermondeSq x:ℂ)*χ x*
          Regular.intrinsicLeadingAmplitude a k (ε,x)/(Regular.actualShapeDenominator a ε x)^(k+1)) ∧
        Integrable (fun x => (shapeVandermondeSq x:ℂ)*χ x*
          Regular.intrinsicRemainderAmplitude a k (ε,x)/(Regular.actualShapeDenominator a ε x)^k) := by
  dsimp only
  let a := equalAngleRegularData α hα hαπ hc
  obtain ⟨rA,M,hrA,hM,hA⟩ := Regular.intrinsic_actual_uniform_neighborhood (n:=n) a k
  obtain ⟨c,rD,hc0,hrD,hD⟩ := Regular.actualShapeDenominator_uniform_lower (n:=n) a ha
  let R := min rA rD
  refine ⟨R,lt_min hrA hrD,?_⟩
  intro χ hχ hχb hχs ε he
  have hdata (x : ShapeSpace n) (hx : x ∈ ball 0 R) :=
    hA ε x (by rw [abs_of_pos he.1];exact he.2.trans_le (min_le_left _ _))
      ((by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖<R).trans_le (min_le_left _ _))
  have hDc : ContinuousOn (Regular.actualShapeDenominator a ε) (ball 0 R) := fun x hx =>
    ((hdata x hx).2.2.1.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hDb (x : ShapeSpace n) (hx : x ∈ ball 0 R) :=
    hD ε x he.1 (he.2.trans_le (min_le_right _ _))
      ((by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖<R).trans_le (min_le_right _ _))
  constructor
  · exact shape_cutoff_pole_integrable_positive_gap hn (k+1) _ _ χ R he.1 hM.le hc0 hχ hχb hχs
      (fun x hx => ((hdata x hx).1.comp
        (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
      hDc (fun x hx => (hdata x hx).2.2.2.1) hDb
  · exact shape_cutoff_pole_integrable_positive_gap hn k _ _ χ R he.1 hM.le hc0 hχ hχb hχs
      (fun x hx => ((hdata x hx).2.1.comp
        (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
      hDc (fun x hx => (hdata x hx).2.2.2.2) hDb

end
end IsingBulk.HT22.LocalLimit
