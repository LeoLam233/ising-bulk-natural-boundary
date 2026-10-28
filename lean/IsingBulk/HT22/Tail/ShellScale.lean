import IsingBulk.HT22.Tail.NumericalEnvelopes

/-! # Exact scale algebra for the F001 near/far split

The diameter r and fixed mean scale T are frozen before these comparisons;
no derivative is taken of a shell radius, a mean, or a shell cutoff.
-/
namespace IsingBulk.HT22
noncomputable section

/-- F001's regular-coordinate scale on a fixed mean slice. -/
def shellCoordinateScale (μ r eps : ℝ) : ℝ :=
  r / Real.sqrt (|μ|+r+eps)

theorem shellCoordinateScale_pos (μ : ℝ) {r eps : ℝ}
    (hr : 0 < r) (heps : 0 ≤ eps) : 0 < shellCoordinateScale μ r eps := by
  unfold shellCoordinateScale
  have hT : 0 < |μ|+r+eps := by positivity
  exact div_pos hr (Real.sqrt_pos.mpr hT)

/-- Δ≤sqrt(T), including means on either side of the branch. -/
theorem shellCoordinateScale_le_sqrt (μ : ℝ) {r eps : ℝ}
    (hr : 0 < r) (heps : 0 ≤ eps) :
    shellCoordinateScale μ r eps ≤ Real.sqrt (|μ|+r+eps) := by
  unfold shellCoordinateScale
  have hT : 0 < |μ|+r+eps := by positivity
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hT), ← pow_two, Real.sq_sqrt hT.le]
  linarith [abs_nonneg μ]

/-- The far-scale condition forces a genuinely positive angular diameter,
uniformly in the mean, particle order and epsilon. -/
theorem shellCoordinateScale_far_diameter {μ r eps δ : ℝ}
    (hr : 0 < r) (heps : 0 ≤ eps) (hδ : 0 ≤ δ)
    (hfar : δ ≤ shellCoordinateScale μ r eps) : δ^2 ≤ r := by
  have hT : 0 < |μ|+r+eps := by positivity
  have hsq := Real.sq_sqrt hT.le
  have hbound : δ*Real.sqrt (|μ|+r+eps) ≤ r :=
    (le_div_iff₀ (Real.sqrt_pos.mpr hT)).mp hfar
  have hbound2 := pow_le_pow_left₀ (mul_nonneg hδ (Real.sqrt_nonneg _)) hbound 2
  rw [mul_pow, hsq] at hbound2
  have hTr : r ≤ |μ|+r+eps := by linarith [abs_nonneg μ]
  nlinarith [sq_nonneg δ, mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hTr)]

/-- The exact extreme-pair cost and the N−2 remaining independent one-body
integrations together yield Δ^(N−3).  The indexing N=n+3 avoids natural
subtraction in the identity, including the smallest three-particle case. -/
theorem extreme_pair_remaining_scale_identity (n : ℕ) {r T : ℝ}
    (hr : 0 < r) (hT : 0 < T) :
    (Real.sqrt T/r)*(r/Real.sqrt T)^(n+1)=(r/Real.sqrt T)^n := by
  have hs : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  rw [pow_succ]
  field_simp

/-- Restoring the full squared Vandermonde gives the exact F001 exponent,
not the LT linear-in-N large-order exponent. -/
theorem full_product_coarea_scale_identity (n j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (δ^((n+3)*(n+2))/δ^(2*j))*δ^n =
      δ^(((n+3:ℕ):ℝ)^2-2*(j:ℝ)-3) := by
  have hexp : ((n+3:ℕ):ℝ)^2-2*(j:ℝ)-3=
      (((n+3)*(n+2):ℕ):ℝ)+(n:ℝ)-((2*j:ℕ):ℝ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_sub hδ, Real.rpow_add hδ,
    Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast]
  ring

/-- The threshold comparison retains every derivative loss.  It is a
numerical inequality only; it does not replace the density estimate. -/
theorem near_shell_threshold_bound {C δ : ℝ} (hC : 0 ≤ C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsmall : C*δ ≤ 1/2)
    {j k : ℕ} (hjk : j ≤ k) (N : ℕ) :
    C^(N^2)*δ^((N:ℝ)^2-2*(j:ℝ)-3) ≤
      δ^(-2*(k:ℝ)-3)*nearOrderEnvelope N := by
  have hbase : (C*δ)^(N^2) ≤ (1/2:ℝ)^(N^2) :=
    pow_le_pow_left₀ (mul_nonneg hC hδ.le) hsmall _
  have hder : δ^(-2*(j:ℝ)-3) ≤ δ^(-2*(k:ℝ)-3) := by
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
    have hjk' : (j:ℝ) ≤ k := by exact_mod_cast hjk
    linarith
  have heq : C^(N^2)*δ^((N:ℝ)^2-2*(j:ℝ)-3)=
      (C*δ)^(N^2)*δ^(-2*(j:ℝ)-3) := by
    rw [show (N:ℝ)^2-2*(j:ℝ)-3=((N^2:ℕ):ℝ)+(-2*(j:ℝ)-3) by push_cast; ring,
      Real.rpow_add hδ, Real.rpow_natCast, mul_pow]
    ring
  rw [heq]
  simpa only [nearOrderEnvelope, mul_comm] using
    mul_le_mul hbase hder (Real.rpow_nonneg hδ.le _) (by positivity : 0≤(1/2:ℝ)^(N^2))

end
end IsingBulk.HT22
