import IsingBulk.HT22.Transport.FieldNeighborhood.SourcePairDerivatives

/-! # Verifiable original-inverse inputs for the residual neighborhood

Bounded joint first jets of the literal inverse partials and convex inverse
domains imply the needed small original pair quantities. No derivative of
mean/diameter/scale is taken.
-/
namespace IsingBulk.HT22
noncomputable section
open Set Metric Geometry
set_option backward.isDefEq.respectTransparency false

/-- Ut differences are small on the original convex inverse domain. -/
theorem inverseT_pair_lipschitz (t v w : ℂ) (D : Set ℂ) (C : ℝ)
    (hD : Convex ℝ D) (hv : v∈D) (hw : w∈D)
    (hU : ∀ q∈D, AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,q))
    (hjet : ∀ q∈D, ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseT z.1 z.2) (t,q)‖≤C) :
    ‖sourceInverseT t w-sourceInverseT t v‖≤C*‖w-v‖ := by
  let S : Set (ℂ × ℂ) := {t} ×ˢ D
  have hS : Convex ℝ S := (convex_singleton t).prod hD
  have hs : ∀ z∈S, HasFDerivWithinAt (fun p : ℂ × ℂ => sourceInverseT p.1 p.2)
      (fderiv ℂ (fun p : ℂ × ℂ => sourceInverseT p.1 p.2) z) S z := by
    rintro ⟨s,q⟩ ⟨hs,hq⟩
    have he : s=t := hs
    subst s
    exact (inverseT_joint_analytic t q (hU q hq)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hb : ∀ z∈S, ‖fderiv ℂ (fun p : ℂ × ℂ => sourceInverseT p.1 p.2) z‖≤C := by
    rintro ⟨s,q⟩ ⟨hs,hq⟩
    have he : s=t := hs
    subst s
    exact hjet q hq
  have hh := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le hs hb
    (show (t,v)∈S from ⟨rfl,hv⟩) (show (t,w)∈S from ⟨rfl,hw⟩)
  simpa only [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using hh

/-- The small base value of Uv persists on an H-sized joint ball, using
only the first joint jet of the original inverse-V partial. -/
theorem sourceInverseV_small_on_ball {N : ℕ} (x y : SourcePoint N) (i : Fin N)
    (ρ C H : ℝ) (hρ : 0≤ρ) (hρH : ρ≤H) (hC : 0≤C)
    (hy : y∈closedBall x ρ)
    (hU : ∀ z∈closedBall x ρ,
      AnalyticAt ℂ (fun p : ℂ × ℂ => regularInverse p.1 p.2) (z.1,z.2 i))
    (hjet : ∀ z∈closedBall x ρ,
      ‖fderiv ℂ (fun p : ℂ × ℂ => sourceInverseV p.1 p.2) (z.1,z.2 i)‖≤C)
    (hbase : ‖sourceInverseV x.1 (x.2 i)‖≤C*H) :
    ‖sourceInverseV y.1 (y.2 i)‖≤2*C*H := by
  have hh := (convex_closedBall x ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (sourceInverseVCoordinate_analyticAt z i (hU z hz)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => sourceInverseVCoordinate_fderiv_bound z i C hC (hU z hz) (hjet z hz))
    (mem_closedBall_self hρ) hy
  have hd : ‖y-x‖≤ρ := by simpa only [mem_closedBall, dist_eq_norm] using hy
  have hdiff : ‖sourceInverseV y.1 (y.2 i)-sourceInverseV x.1 (x.2 i)‖≤C*H :=
    hh.trans (mul_le_mul_of_nonneg_left (hd.trans hρH) hC)
  have htri := norm_sub_le (sourceInverseV y.1 (y.2 i)-sourceInverseV x.1 (x.2 i))
    (-sourceInverseV x.1 (x.2 i))
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
  linarith

/-- The actual complex residual's joint jets follow from original inverse
one-body data. This is conditional on the explicitly listed geometric
source bounds, which must be discharged for the physical contour. -/
theorem sourceResidual_joint_jets_of_original_data {N : ℕ} (hN : 0<N)
    (x : SourcePoint N) (C H d c η : ℝ)
    (hC : 0<C) (hH : 0<H) (hd : 0<d) (hc : 0<c) (hdH : d≤H)
    (hη : 0<η) (hη1 : η≤1) (hηc : η≤c/(4*(3*C)^2))
    (hU : ∀ y∈closedBall x (η*d/(N:ℝ)^2), ∀ i,
      AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (y.1,y.2 i))
    (hV : ∀ y∈closedBall x (η*d/(N:ℝ)^2), ∀ i, ‖sourceInverseV y.1 (y.2 i)‖≤C*H)
    (hTdiff : ∀ y∈closedBall x (η*d/(N:ℝ)^2), ∀ i j,
      ‖sourceInverseT y.1 (y.2 i)-sourceInverseT y.1 (y.2 j)‖≤C*d)
    (hVjet : ∀ y∈closedBall x (η*d/(N:ℝ)^2), ∀ i,
      ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseV z.1 z.2) (y.1,y.2 i)‖≤C)
    (hT : ∀ y∈closedBall x (η*d/(N:ℝ)^2), ∀ i, ‖sourceInverseT y.1 (y.2 i)‖≤C)
    (hD0 : ∀ i j, ‖sourceInverseCoordinate i x-sourceInverseCoordinate j x‖≤C*H*d)
    (hE0 : ∀ i j, ‖sourceInverseVCoordinate i x-sourceInverseVCoordinate j x‖≤C*d)
    (hR0 : c*H*d^2≤‖sourceCovariance x.1 x.2‖) (m : ℕ) :
    ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => sourceResidual z.1 z.2) x‖≤
      (IsingBulk.Preferred22.cauchyJetConstant m*(36*C^2/c)/η^m)*
        (N:ℝ)^(2*m+2)/d^(m+1) := by
  have hball := sourceResidual_scaled_ball hN x (3*C) H d c η
    (by positivity) hH hd hc hη hη1 hηc hU
    (fun y hy i j => sourceInversePair_fderiv_bound y i j C H d hC.le hH.le hdH
      (hU y hy) (hV y hy) (hTdiff y hy i j))
    (fun y hy i j => (sourceInverseVPair_fderiv_bound y i j C hC.le (hU y hy) (hVjet y hy)).trans
      (by linarith))
    (fun y hy i => (hT y hy i).trans (by linarith))
    (fun i j => (hD0 i j).trans (by nlinarith [show 0≤C*H*d by positivity]))
    (fun i j => (hE0 i j).trans (by nlinarith [show 0≤C*d by positivity])) hR0
  have hbound : ∀ y∈ball x (η*d/(N:ℝ)^2), ‖sourceResidual y.1 y.2‖≤(36*C^2/c)*(N:ℝ)^2/d := by
    intro y hy
    convert hball.2 y hy using 1; ring
  exact sourceResidual_joint_jets_of_ball hN x η d (36*C^2/c) hη hd hball.1 hbound m

end
end IsingBulk.HT22
