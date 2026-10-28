import IsingBulk.HT22.First.EqualAngleData
import IsingBulk.First.RegularShapeSource
import IsingBulk.HT.First.RegularOddDensityCenter
import IsingBulk.HT.First.OddShapeCutoffLimit
import IsingBulk.HT.First.OddLimitTransfer

/-! A new F001 equal-angle highest-pole proof from continuity, the actual
nonlinear gap and the generic dominated-convergence theorem. No old actual
local or complete FIRST-asymptotic theorem is invoked. -/
namespace IsingBulk.HT22.LocalLimit
noncomputable section
open Complex MeasureTheory Set Filter Metric IsingBulk.First IsingBulk.First.Regular
open IsingBulk.HT.First
open scoped Topology
set_option maxHeartbeats 1000000

theorem equalAngle_Ds (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi)
    (hc : Real.cos α≠0) (N : ℕ) :
    (equalAngleRegularData α hα hαπ hc).Ds N =
      2*(N:ℂ)*exp (-(α:ℂ)*I) := by
  have hs : (Real.sin α:ℂ)≠0 := ofReal_ne_zero.mpr
    (Real.sin_pos_of_pos_of_lt_pi hα hαπ).ne'
  dsimp [equalAngleRegularData,RegularChartData.Ds]
  rw [show -I*(α:ℂ)=-(α:ℂ)*I by ring]
  field_simp

/-- The physical pole numerator at the equal-angle center retains exactly
its odd phase and the free-coordinate 2pi normalization. -/
theorem equalAngle_highest_pole_center {n : ℕ} (ho : Odd (n+1))
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) :
    2*(Real.pi:ℂ)*IsingBulk.First.Regular.intrinsicLeadingAmplitude
      (equalAngleRegularData α hα hαπ hc) (derivativeOrder (n+1))
      (0,(0:ShapeSpace n)) =
      -I*(equalAngleAmplitude (n+1) α:ℂ)*((derivativeOrder (n+1)).factorial:ℂ)*
        (2*(n+1:ℂ))^(derivativeOrder (n+1))*
          exp (-(α:ℂ)*I)^(derivativeOrder (n+1)) := by
  let a := equalAngleRegularData α hα hαπ hc
  have hcent := IsingBulk.HT.First.Regular.actualLeadingAmplitude_odd_center
    a n (derivativeOrder (n+1)) ho ha ha
  have hK := equalAngleAmplitude_eq_K (Nat.succ_pos n) α hα hαπ hc
  have hKc := congrArg (fun x : ℝ => (x:ℂ)) hK
  simp only [ofReal_mul,ofReal_ofNat] at hKc
  have hsign : (-1:ℂ)^(derivativeOrder (n+1))=1 := by
    obtain ⟨m,hm⟩ := derivativeOrder_four_dvd ho
    rw [hm,pow_mul]
    norm_num
  change 2*(Real.pi:ℂ)*IsingBulk.First.Regular.actualLeadingAmplitude a n
    (derivativeOrder (n+1)) (IsingBulk.First.Regular.intrinsicRadialEmbedding a (0,0))=_
  rw [IsingBulk.First.Regular.intrinsicRadialEmbedding_zero,hcent,hsign]
  dsimp [a]
  rw [equalAngle_Ds,hKc,mul_pow]
  push_cast
  ring

/-- Actual highest-pole scaling on the equal-angle chart. The fixed support
radius is constructed from analytic source bounds and the genuine gap.
All nontrivial DCT hypotheses are discharged internally. -/
theorem equalAngle_leading_shape_limit {n : ℕ} (hn : 1≤n) (ho : Odd (n+1))
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0)
    (ha : exp (-(n+1:ℂ)*(α:ℂ)*I)=1) :
    let a := equalAngleRegularData α hα hαπ hc
    let k := derivativeOrder (n+1)
    ∃ R : ℝ, 0<R ∧ ∀ χ : ShapeSpace n → ℂ,
      Continuous χ → χ 0=1 → (∀ x,‖χ x‖≤1) →
      (∀ x,χ x≠0 → ‖x‖<R) →
      Tendsto (fun ε : ℝ => ε • ∫ x : ShapeSpace n,
        (shapeVandermondeSq x:ℂ)*χ x*
          IsingBulk.First.Regular.intrinsicLeadingAmplitude a k (ε,x)/
          (IsingBulk.First.Regular.actualShapeDenominator a ε x)^(k+1))
        (𝓝[>] 0) (𝓝 (
          IsingBulk.First.Regular.intrinsicLeadingAmplitude a k (0,(0:ShapeSpace n))*
          shapePeriodIntrinsic n k (2*(n+1)) (-I*(Real.cos α/Real.sin α)))) := by
  dsimp only
  let a := equalAngleRegularData α hα hαπ hc
  let k := derivativeOrder (n+1)
  have hp3 : 3≤n+1 := by obtain ⟨m,hm⟩ := ho; omega
  have hk : 1≤k := derivativeOrder_pos ho hp3
  have hdegree : n-1+(n+1)*n=2*k-1 := by
    simpa only [Nat.add_sub_cancel] using odd_shape_radial_exponent ho hp3
  obtain ⟨rA,M,hrA,hM,hA⟩ := IsingBulk.First.Regular.intrinsic_actual_uniform_neighborhood (n:=n) a k
  obtain ⟨c,rD,hc0,hrD,hD⟩ := IsingBulk.First.Regular.actualShapeDenominator_uniform_lower (n:=n) a ha
  let R := min rA rD
  have hR : 0<R := lt_min hrA hrD
  refine ⟨R,hR,?_⟩
  intro χ hχ hχ0 hχb hχs
  let lam₀ := min 1 R
  have hlam₀ : 0<lam₀ := lt_min zero_lt_one hR
  have hlam (lam : ℝ) (hl : lam ∈ Ioo 0 lam₀) : 0<lam^2 ∧ lam^2<R := by
    have hl1 : lam<1 := hl.2.trans_le (min_le_left _ _)
    have hlR : lam<R := hl.2.trans_le (min_le_right _ _)
    exact ⟨sq_pos_of_pos hl.1,by nlinarith [hl.1]⟩
  have hdata (lam : ℝ) (hl : lam ∈ Ioo 0 lam₀) (x : ShapeSpace n) (hx : x ∈ ball 0 R) :=
    hA (lam^2) x (by rw [abs_of_nonneg (sq_nonneg _)]; exact (hlam lam hl).2.trans_le (min_le_left _ _))
      ((by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖<R).trans_le (min_le_left _ _))
  have hApoint (x : ShapeSpace n) :
      Tendsto (fun lam : ℝ => IsingBulk.First.Regular.intrinsicLeadingAmplitude a k (lam^2,lam • x))
        (𝓝[>] 0) (𝓝 (IsingBulk.First.Regular.intrinsicLeadingAmplitude a k (0,(0:ShapeSpace n)))) := by
    have hp : Tendsto (fun lam : ℝ => (lam^2,lam • x)) (𝓝[>] 0) (𝓝 (0,0)) := by
      have hcont : Continuous (fun lam : ℝ => (lam^2,lam • x)) := by fun_prop
      simpa using (hcont.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    exact (IsingBulk.First.Regular.intrinsicLeadingAmplitude_continuousAt_zero a k).tendsto.comp hp
  have hlim := postMean_odd_shape_cutoff_limit hn hk hdegree
    (fun lam x => IsingBulk.First.Regular.intrinsicLeadingAmplitude a k (lam^2,x))
    (fun lam x => IsingBulk.First.Regular.actualShapeDenominator a (lam^2) x) χ
    (IsingBulk.First.Regular.intrinsicLeadingAmplitude a k (0,(0:ShapeSpace n)))
    hR (a.Q_pos (Nat.succ_pos n)) a.d_ne_zero hM.le hc0 hlam₀ hχ hχ0 hχb hχs
    (fun lam hl x hx => ((hdata lam hl x hx).1.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
    (fun lam hl x hx => ((hdata lam hl x hx).2.2.1.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
    (fun lam hl x hx => (hdata lam hl x hx).2.2.2.1)
    (fun lam hl x hx => hD (lam^2) x (hlam lam hl).1
      ((hlam lam hl).2.trans_le (min_le_right _ _))
      ((by simpa only [mem_ball,dist_zero_right] using hx : ‖x‖<R).trans_le (min_le_right _ _)))
    hApoint (IsingBulk.First.Regular.actualShapeDenominator_scale_limit a ha)
  have he := normalized_epsilon_limit_of_scale_limit
    (F := fun ε : ℝ => ∫ x : ShapeSpace n,
      (shapeVandermondeSq x:ℂ)*χ x*IsingBulk.First.Regular.intrinsicLeadingAmplitude a k (ε,x)/
        (IsingBulk.First.Regular.actualShapeDenominator a ε x)^(k+1)) hlim
  simpa only [a,k,equalAngleRegularData_Q,equalAngleRegularData_d,ofReal_div,Nat.cast_succ] using he

end
end IsingBulk.HT22.LocalLimit
