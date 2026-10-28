import IsingBulk.HT22.Transport.FieldNeighborhood.Perturbation
import IsingBulk.Preferred22.AnalyticCauchyBounds

/-! # A quantitative ball for the actual HT22 mixed residual

The inputs are explicit bounds on original inverse coordinate differences,
their first derivatives, and the inverse t-derivative. No bound on the
residual or on reciprocal covariance jets is assumed. Geometric discharge
of these original-inverse estimates is a separate required obligation.
-/
namespace IsingBulk.HT22
noncomputable section
open Set Metric Geometry
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

abbrev SourcePoint (N : ℕ) := ℂ × (Fin N → ℂ)

def sourceInverseCoordinate {N : ℕ} (i : Fin N) (z : SourcePoint N) : ℂ :=
  regularInverse z.1 (z.2 i)

def sourceInverseVCoordinate {N : ℕ} (i : Fin N) (z : SourcePoint N) : ℂ :=
  sourceInverseV z.1 (z.2 i)

theorem sourceInverseCoordinate_analyticAt {N : ℕ} (x : SourcePoint N) (i : Fin N)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (x.1,x.2 i)) :
    AnalyticAt ℂ (sourceInverseCoordinate i) x := by
  have hp : AnalyticAt ℂ (fun z : SourcePoint N => (z.1,z.2 i)) x :=
    analyticAt_fst.prod ((((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt x))
  exact AnalyticAt.comp (f := fun z : SourcePoint N => (z.1,z.2 i))
    (g := fun z : ℂ × ℂ => regularInverse z.1 z.2) hU hp

theorem sourceInverseVCoordinate_analyticAt {N : ℕ} (x : SourcePoint N) (i : Fin N)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (x.1,x.2 i)) :
    AnalyticAt ℂ (sourceInverseVCoordinate i) x := by
  have hp : AnalyticAt ℂ (fun z : SourcePoint N => (z.1,z.2 i)) x :=
    analyticAt_fst.prod ((((ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt x))
  exact AnalyticAt.comp (f := fun z : SourcePoint N => (z.1,z.2 i))
    (g := fun z : ℂ × ℂ => sourceInverseV z.1 z.2)
    (inverseV_joint_analytic x.1 (x.2 i) hU) hp

/-- The original inverse-pair jet bounds imply an honest residual ball,
with radius proportional to d/N² and no inverse-temperature cutoff loss. -/
theorem sourceResidual_scaled_ball {N : ℕ} (hN : 0<N) (x : SourcePoint N)
    (C H d c η : ℝ) (hC : 0<C) (hH : 0<H) (hd : 0<d) (hc : 0<c)
    (hη : 0<η) (hη1 : η≤1) (hηc : η≤c/(4*C^2))
    (hU : ∀ y∈closedBall x (η*d/(N:ℝ)^2), ∀ i,
      AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (y.1,y.2 i))
    (hD1 : ∀ y∈closedBall x (η*d/(N:ℝ)^2), ∀ i j,
      ‖fderiv ℂ (fun z => sourceInverseCoordinate i z-sourceInverseCoordinate j z) y‖≤C*H)
    (hE1 : ∀ y∈closedBall x (η*d/(N:ℝ)^2), ∀ i j,
      ‖fderiv ℂ (fun z => sourceInverseVCoordinate i z-sourceInverseVCoordinate j z) y‖≤C)
    (hA : ∀ y∈closedBall x (η*d/(N:ℝ)^2), ∀ i, ‖sourceInverseT y.1 (y.2 i)‖≤C)
    (hD0 : ∀ i j, ‖sourceInverseCoordinate i x-sourceInverseCoordinate j x‖≤C*H*d)
    (hE0 : ∀ i j, ‖sourceInverseVCoordinate i x-sourceInverseVCoordinate j x‖≤C*d)
    (hR0 : c*H*d^2≤‖sourceCovariance x.1 x.2‖) :
    AnalyticOnNhd ℂ (fun z : SourcePoint N => sourceResidual z.1 z.2)
      (ball x (η*d/(N:ℝ)^2)) ∧
    ∀ y∈ball x (η*d/(N:ℝ)^2), ‖sourceResidual y.1 y.2‖≤
      (4*C^2/c)*(N:ℝ)^2/d := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hn2 : (1:ℝ)≤(N:ℝ)^2 := one_le_pow₀ hn1
  have hradius : 0<η*d/(N:ℝ)^2 := by positivity
  have hx : x∈closedBall x (η*d/(N:ℝ)^2) := mem_closedBall_self hradius.le
  have hpoint (y : SourcePoint N) (hy : y∈ball x (η*d/(N:ℝ)^2)) :
      AnalyticAt ℂ (fun z : SourcePoint N => sourceResidual z.1 z.2) y ∧
      ‖sourceResidual y.1 y.2‖≤(4*C^2/c)*(N:ℝ)^2/d := by
    have hyc := ball_subset_closedBall hy
    have hdist : ‖y-x‖≤η*d/(N:ℝ)^2 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hyc
    have hdu (i j : Fin N) :
        ‖(sourceInverseCoordinate i y-sourceInverseCoordinate j y)-
          (sourceInverseCoordinate i x-sourceInverseCoordinate j x)‖≤C*H*η*d/(N:ℝ)^2 := by
      have hl := (convex_closedBall x (η*d/(N:ℝ)^2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z hz => ((sourceInverseCoordinate_analyticAt z i (hU z hz i)).sub
          (sourceInverseCoordinate_analyticAt z j (hU z hz j))).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
        (fun z hz => hD1 z hz i j) hx hyc
      exact hl.trans (by calc
        _ ≤ (C*H)*(η*d/(N:ℝ)^2) := mul_le_mul_of_nonneg_left hdist (by positivity)
        _ = _ := by ring)
    have hdv (i j : Fin N) :
        ‖(sourceInverseVCoordinate i y-sourceInverseVCoordinate j y)-
          (sourceInverseVCoordinate i x-sourceInverseVCoordinate j x)‖≤C*η*d/(N:ℝ)^2 := by
      have hl := (convex_closedBall x (η*d/(N:ℝ)^2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z hz => ((sourceInverseVCoordinate_analyticAt z i (hU z hz i)).sub
          (sourceInverseVCoordinate_analyticAt z j (hU z hz j))).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
        (fun z hz => hE1 z hz i j) hx hyc
      exact hl.trans (by calc
        _ ≤ C*(η*d/(N:ℝ)^2) := mul_le_mul_of_nonneg_left hdist hC.le
        _ = _ := by ring)
    have hmargin := mixedCovariance_scaled_margin hN
      (fun i => sourceInverseCoordinate i x) (fun i => sourceInverseVCoordinate i x)
      (fun i => sourceInverseCoordinate i y) (fun i => sourceInverseVCoordinate i y)
      C H d c η hC hH hd hc hη hη1 hηc hD0 hE0 hdu hdv hR0
    have hRn : sourceCovariance y.1 y.2 ≠ 0 := by
      intro hz
      change c*H*d^2/2≤‖sourceCovariance y.1 y.2‖ at hmargin
      rw [hz, norm_zero] at hmargin
      have hpos : 0<c*H*d^2/2 := by positivity
      linarith
    refine ⟨sourceResidual_analyticAt y.1 y.2 (hU y hyc) hRn, ?_⟩
    have hsmall : C*H*η*d/(N:ℝ)^2≤C*H*d := by
      calc
        _ ≤ C*H*η*d := div_le_self (by positivity) hn2
        _ = (C*H*d)*η := by ring
        _ ≤ _ := mul_le_of_le_one_right (by positivity) hη1
    have hp (i j : Fin N) : ‖sourceInverseCoordinate i y-sourceInverseCoordinate j y‖≤2*C*H*d := by
      have ht := norm_sub_le (sourceInverseCoordinate i y-sourceInverseCoordinate j y-
        (sourceInverseCoordinate i x-sourceInverseCoordinate j x))
        (-(sourceInverseCoordinate i x-sourceInverseCoordinate j x))
      simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at ht
      linarith [hdu i j, hD0 i j]
    have hb := mixedCollectiveField_norm_bound
      (fun i => sourceInverseCoordinate i y) (fun i => sourceInverseVCoordinate i y)
      (fun i => sourceInverseT y.1 (y.2 i)) C (2*C*H*d) (c*H*d^2/2)
      hC.le (by positivity) (by positivity) hp (hA y hyc) hmargin
    convert hb using 1 <;> first | rfl | (field_simp; ring)
  exact ⟨fun y hy => (hpoint y hy).1, fun y hy => (hpoint y hy).2⟩

/-- Cauchy turns the actual residual ball into all fixed joint jet bounds.
The dimensional dependence is the explicit polynomial N^(2m+2). -/
theorem sourceResidual_joint_jets_of_ball {N : ℕ} (hN : 0<N) (x : SourcePoint N)
    (η d M : ℝ) (hη : 0<η) (hd : 0<d)
    (hf : AnalyticOnNhd ℂ (fun z : SourcePoint N => sourceResidual z.1 z.2)
      (ball x (η*d/(N:ℝ)^2)))
    (hb : ∀ y∈ball x (η*d/(N:ℝ)^2), ‖sourceResidual y.1 y.2‖≤M*(N:ℝ)^2/d)
    (m : ℕ) :
    ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => sourceResidual z.1 z.2) x‖≤
      (IsingBulk.Preferred22.cauchyJetConstant m*M/η^m)*(N:ℝ)^(2*m+2)/d^(m+1) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have h := IsingBulk.Preferred22.analytic_iteratedFDeriv_center_bound
    (fun z : SourcePoint N => sourceResidual z.1 z.2) x (η*d/(N:ℝ)^2)
    (M*(N:ℝ)^2/d) (by positivity) hf hb m
  convert h using 1
  rw [pow_add, pow_mul, div_pow, mul_pow, pow_succ d]
  field_simp

end
end IsingBulk.HT22
