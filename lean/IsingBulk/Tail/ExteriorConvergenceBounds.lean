import IsingBulk.First.GlobalResidueRoot
import IsingBulk.First.ContourNormBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.Compact

/-! Appendix C's exponential global inverse-product bounds. These are actual
root/product estimates, not assumptions of normal convergence. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Filter
open scoped Topology
open scoped BigOperators

/-- The quadratic trace bounds the inverse root; no artificial uniform-in-N
bound is assigned to the product of inverse roots. -/
theorem quadratic_inverse_norm_bound {W z : ℂ} {M q : ℝ}
    (hroot : z^2 - 2*W*z + 1 = 0) (hW : ‖W‖ ≤ M) (hz : ‖z‖ ≤ q) :
    ‖z⁻¹‖ ≤ 2*M+q := by
  have ht := quadratic_root_trace hroot
  have he : z⁻¹ = 2*W-z := by linear_combination ht
  rw [he]
  calc
    ‖2*W-z‖ ≤ ‖2*W‖+‖z‖ := norm_sub_le _ _
    _ = 2*‖W‖+‖z‖ := by simp
    _ ≤ 2*M+q := by linarith

/-- Appendix C lower root bound, with positivity certified by the nonzero root. -/
theorem quadratic_root_lower_bound {W z : ℂ} {M q : ℝ}
    (hroot : z^2 - 2*W*z + 1 = 0) (hW : ‖W‖ ≤ M) (hz : ‖z‖ ≤ q) :
    0 < 2*M+q ∧ (2*M+q)⁻¹ ≤ ‖z‖ := by
  have hb := quadratic_inverse_norm_bound hroot hW hz
  have hz0 := quadratic_root_ne_zero hroot
  have hp : 0 < ‖z⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hz0)
  have hpos : 0 < 2*M+q := hp.trans_le hb
  refine ⟨hpos, ?_⟩
  rw [norm_inv] at hb
  exact (inv_le_comm₀ hpos (norm_pos_iff.mpr hz0)).mpr hb

theorem coordinateProduct_inverse_norm_le {N : ℕ} {z : Fin N → ℂ} {C : ℝ}
    (_hC : 0 ≤ C) (hz : ∀ i, ‖(z i)⁻¹‖ ≤ C) :
    ‖(coordinateProduct z)⁻¹‖ ≤ C^N := by
  simp only [coordinateProduct, ← Finset.prod_inv_distrib, norm_prod]
  calc
    ∏ i, ‖(z i)⁻¹‖ ≤ ∏ _i : Fin N, C :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hz i)
    _ = C^N := by simp

/-- The exact exponential bound required by the corrected Appendix C. -/
theorem inverse_global_numerator_norm_le {N : ℕ} {z y : Fin N → ℂ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hz : ∀ i, ‖(z i)⁻¹‖ ≤ A) (hy : ∀ i, ‖(y i)⁻¹‖ ≤ B) :
    ‖(coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹‖ ≤ 2*(max A B)^N := by
  calc
    _ ≤ ‖(coordinateProduct z)⁻¹‖+‖(coordinateProduct y)⁻¹‖ := norm_add_le _ _
    _ ≤ A^N+B^N := add_le_add (coordinateProduct_inverse_norm_le hA hz)
      (coordinateProduct_inverse_norm_le hB hy)
    _ ≤ (max A B)^N+(max A B)^N := add_le_add
      (pow_le_pow_left₀ hA (le_max_left _ _) _) (pow_le_pow_left₀ hB (le_max_right _ _) _)
    _ = _ := by ring

/-- Actual global roots inherit the quadratic inverse estimate. -/
theorem globalRoot_inverse_norm_le {s y : ℂ} {M q : ℝ}
    (hW : ‖sourceW s y‖ ≤ M) (hz : ‖globalRoot s y‖ ≤ q) :
    ‖(globalRoot s y)⁻¹‖ ≤ 2*M+q :=
  quadratic_inverse_norm_bound (interiorRoot_quadratic (sourceW s y)) hW hz

/-- Uniform global denominator gap, valid for all orders at least two. -/
theorem coordinateProduct_gap {N : ℕ} (hN : 2 ≤ N) {z : Fin N → ℂ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hz : ∀ i, ‖z i‖ ≤ q) :
    1-q^2 ≤ ‖1-coordinateProduct z‖ := by
  have hp : ‖coordinateProduct z‖ ≤ q^N := by
    simp only [coordinateProduct, norm_prod]
    calc
      ∏ i, ‖z i‖ ≤ ∏ _i : Fin N, q :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hz i)
      _ = q^N := by simp
  have he := pow_le_pow_of_le_one hq0 hq1.le hN
  have hn := norm_sub_norm_le (1:ℂ) (coordinateProduct z)
  simp only [norm_one] at hn
  linarith

/-- The factorial estimate follows directly from one nonnegative exponential
series term, so no asymptotic Stirling input is required. -/
theorem factorial_lower_exp (N : ℕ) : ((N:ℝ)/Real.exp 1)^N ≤ (N.factorial:ℝ) := by
  have ht := Real.pow_div_factorial_le_exp (N:ℝ) (Nat.cast_nonneg N) N
  have he : Real.exp (N:ℝ) = (Real.exp 1)^N := by
    simp
  rw [he, div_le_iff₀ (by positivity : (0:ℝ) < N.factorial)] at ht
  rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < (Real.exp 1)^N)]
  nlinarith

/-- A compact collection of actual admissible roots has a strict common
subradius. The parameter set may be any compact exterior chart satisfying
the displayed original-contour damping margin. -/
theorem compact_globalRoot_subradius {K : Set ℂ} (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hs : ∀ s ∈ K, s ≠ 0)
    (hm : ∀ s ∈ K, r⁻¹-r < (sourceS s).im) :
    ∃ q, 0 < q ∧ q < r ∧ ∀ s ∈ K, ∀ y : ℂ, ‖y‖=r → ‖globalRoot s y‖ ≤ q := by
  let L : Set (ℂ × ℂ) := K ×ˢ Metric.sphere 0 r
  have hL : IsCompact L := hK.prod (isCompact_sphere 0 r)
  have hc : ContinuousOn (fun p : ℂ × ℂ => ‖globalRoot p.1 p.2‖) L := by
    intro p hp
    have hy : ‖p.2‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hp.2
    have hy0 : p.2 ≠ 0 := norm_ne_zero_iff.mp (by rw [hy]; exact hr.ne')
    exact (globalRoot_joint_continuousAt (hs p.1 hp.1) hy0
      (sourceW_upper_of_margin hr hr1 (hm p.1 hp.1) hy)).norm.continuousWithinAt
  by_cases hn : L.Nonempty
  · obtain ⟨p,hp,hmax⟩ := hL.exists_isMaxOn hn hc
    have hy : ‖p.2‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hp.2
    have hb := globalRoot_inside_radius hr hr1 (hm p.1 hp.1) hy
    refine ⟨(‖globalRoot p.1 p.2‖+r)/2, ?_, by linarith, ?_⟩
    · positivity
    · intro s hsk y hy
      have hmem : (s,y) ∈ L := ⟨hsk, by simpa [Metric.mem_sphere, dist_zero_right] using hy⟩
      have hle := hmax hmem
      change ‖globalRoot s y‖ ≤ ‖globalRoot p.1 p.2‖ at hle
      linarith
  · refine ⟨r/2, by positivity, by linarith, ?_⟩
    intro s hsk y hy
    exact False.elim (hn ⟨(s,y),hsk,by simpa [Metric.mem_sphere, dist_zero_right] using hy⟩)

/-- Dispersion is uniformly bounded on a compact parameter set and the
actual fixed y circle. -/
theorem compact_sourceW_bound {K : Set ℂ} (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) (hs : ∀ s ∈ K, s ≠ 0) :
    ∃ M, 0 ≤ M ∧ ∀ s ∈ K, ∀ y : ℂ, ‖y‖=r → ‖sourceW s y‖ ≤ M := by
  have hc : ContinuousOn (fun p : ℂ × ℂ => sourceW p.1 p.2)
      (K ×ˢ Metric.sphere 0 r) := by
    intro p hp
    have hy : ‖p.2‖=r := by simpa [Metric.mem_sphere, dist_zero_right] using hp.2
    have hy0 : p.2 ≠ 0 := norm_ne_zero_iff.mp (by rw [hy]; exact hr.ne')
    apply ContinuousAt.continuousWithinAt
    unfold sourceW sourceS
    exact (continuousAt_fst.add (continuousAt_fst.inv₀ (hs p.1 hp.1))).sub
      ((continuousAt_snd.add (continuousAt_snd.inv₀ hy0)).div_const 2)
  obtain ⟨M,hM⟩ := (hK.prod (isCompact_sphere 0 r)).exists_bound_of_continuousOn hc
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro s hsk y hy
  exact (hM (s,y) ⟨hsk,by simpa [Metric.mem_sphere, dist_zero_right] using hy⟩).trans
    (le_max_left _ _)

/-- The compact inverse-root constant is constructed from the actual
quadratic equation and compact dispersion bound. -/
theorem compact_globalRoot_inverse_bound {K : Set ℂ} (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (hs : ∀ s ∈ K, s ≠ 0)
    (hm : ∀ s ∈ K, r⁻¹-r < (sourceS s).im) :
    ∃ A, 0 < A ∧ ∀ s ∈ K, ∀ y : ℂ, ‖y‖=r → ‖(globalRoot s y)⁻¹‖ ≤ A := by
  obtain ⟨M,hM0,hM⟩ := compact_sourceW_bound hK hr hs
  refine ⟨2*M+r, by positivity, ?_⟩
  intro s hsk y hy
  exact globalRoot_inverse_norm_le (hM s hsk y hy)
    (globalRoot_inside_radius hr hr1 (hm s hsk) hy).le

/-- The source majorant is summable for every fixed compact-set constant. -/
theorem sqrt_majorant_summable (C : ℝ) :
    Summable (fun N : ℕ => (C / Real.sqrt N)^N) := by
  have ht : Filter.Tendsto (fun N : ℕ => C / Real.sqrt N)
      Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)))
  have he : ∀ᶠ N : ℕ in Filter.atTop, ‖C / Real.sqrt N‖ ≤ (1/2:ℝ) := by
    have hn := ht.norm
    have h := hn.eventually (gt_mem_nhds (by norm_num : ‖(0:ℝ)‖ < 1/2))
    exact h.mono (fun N hN => le_of_lt (by simpa using hN))
  apply (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)).of_norm_bounded_eventually_nat
  filter_upwards [he] with N hN
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hN N

/-- Constants and fixed Cauchy derivative losses preserve summability. -/
theorem cauchy_sqrt_majorant_summable (C C₀ d : ℝ) (j : ℕ) :
    Summable (fun N : ℕ => (j.factorial:ℝ)*d⁻¹^j*C₀*(C / Real.sqrt N)^N) :=
  (sqrt_majorant_summable C).mul_left _

end
end IsingBulk.Tail
