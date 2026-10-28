import IsingBulk.HT22.Transport.FieldNeighborhood.BaseDifferences

/-! # Actual mixed-residual jets from primitive inverse geometry

This final local interface exposes only the genuine analytic inverse on a
convex source domain, its original first-partial jet bounds, the base small
inverse-V scale, the coordinate diameter, and the protected covariance.
All other pair, reciprocal, neighborhood and residual jet estimates are
proved dependencies. The physical contour must still supply these primitive
geometric inputs; this theorem does not assume that it does.
-/
namespace IsingBulk.HT22
noncomputable section
open Set Metric Geometry
set_option backward.isDefEq.respectTransparency false

theorem sourceResidual_joint_jets_of_base_inverse_geometry {N : ℕ} (hN : 0<N)
    (x : SourcePoint N) (D : Set ℂ) (C H d c η : ℝ)
    (hC : 0<C) (hH : 0<H) (hd : 0<d) (hc : 0<c) (hdH : d≤H)
    (hη : 0<η) (hη1 : η≤1) (hηc : η≤c/(4*(18*C)^2))
    (hD : Convex ℝ D)
    (hinside : ∀ i, closedBall (x.2 i) (η*d/(N:ℝ)^2) ⊆ D)
    (hU : ∀ t q, ‖t-x.1‖≤η*d/(N:ℝ)^2 → q∈D →
      AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,q))
    (hVjet : ∀ t q, ‖t-x.1‖≤η*d/(N:ℝ)^2 → q∈D →
      ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseV z.1 z.2) (t,q)‖≤C)
    (hTjet : ∀ t q, ‖t-x.1‖≤η*d/(N:ℝ)^2 → q∈D →
      ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseT z.1 z.2) (t,q)‖≤C)
    (hT : ∀ t q, ‖t-x.1‖≤η*d/(N:ℝ)^2 → q∈D → ‖sourceInverseT t q‖≤C)
    (hV0 : ∀ i, ‖sourceInverseV x.1 (x.2 i)‖≤C*H)
    (hdiam : ∀ i j, ‖x.2 i-x.2 j‖≤d)
    (hR0 : c*H*d^2≤‖sourceCovariance x.1 x.2‖) (m : ℕ) :
    ‖iteratedFDeriv ℂ m (fun z : SourcePoint N => sourceResidual z.1 z.2) x‖≤
      (IsingBulk.Preferred22.cauchyJetConstant m*(1296*C^2/c)/η^m)*
        (N:ℝ)^(2*m+2)/d^(m+1) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hr : 0<η*d/(N:ℝ)^2 := by positivity
  have ht : ‖x.1-x.1‖≤η*d/(N:ℝ)^2 := by simpa only [sub_self, norm_zero] using hr.le
  have hmem (i : Fin N) : x.2 i∈D := hinside i (mem_closedBall_self hr.le)
  have hD0 (i j : Fin N) :
      ‖sourceInverseCoordinate i x-sourceInverseCoordinate j x‖≤(2*C)*H*d :=
    regularInverse_pair_small x.1 (x.2 j) (x.2 i) D C H d hC.le hH.le hd.le hdH hD
      (hmem j) (hmem i) (hdiam i j) (fun q hq => hU x.1 q ht hq)
      (fun q hq => hVjet x.1 q ht hq) (hV0 j)
  have hE0 (i j : Fin N) :
      ‖sourceInverseVCoordinate i x-sourceInverseVCoordinate j x‖≤(2*C)*d := by
    have he := inverseV_pair_lipschitz x.1 (x.2 j) (x.2 i) D C hD (hmem j) (hmem i)
      (fun q hq => hU x.1 q ht hq) (fun q hq => hVjet x.1 q ht hq)
    exact he.trans ((mul_le_mul_of_nonneg_left (hdiam i j) hC.le).trans
      (by nlinarith [mul_nonneg hC.le hd.le]))
  have hηc' : η≤c/(4*(9*(2*C))^2) := by convert hηc using 1; ring
  have hj := sourceResidual_joint_jets_of_convex_inverse_domain hN x D (2*C) H d c η
    (by positivity) hH hd hc hdH hη hη1 hηc' hD hinside hU
    (fun t q ht hq => (hVjet t q ht hq).trans (by linarith))
    (fun t q ht hq => (hTjet t q ht hq).trans (by linarith))
    (fun t q ht hq => (hT t q ht hq).trans (by linarith))
    (fun i => (hV0 i).trans (by nlinarith [mul_nonneg hC.le hH.le]))
    hdiam hD0 hE0 hR0 m
  convert hj using 1; ring

end
end IsingBulk.HT22
