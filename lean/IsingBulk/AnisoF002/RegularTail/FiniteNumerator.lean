import IsingBulk.AnisoF002.RegularTail.SinePair
import IsingBulk.AnisoF002.RegularTail.VandermondeBlock

/-!
# Actual finite-particle numerator and retained-factor extension

The numerator below contains every one-body and every complete canceled
pair from frozen/published `eq:fullangular` and `eq:cancelpair`. `b` is the
chosen local square root of B; its Nth power is retained explicitly.
No site sum, particle sum, contour deformation, or differentiated-tail
estimate is asserted here. The analytic quotient is constructed at all
zeros of the retained sine block rather than defined by pointwise division.
-/

namespace IsingBulk.AnisoF002.RegularTail
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.Isotropic
open scoped BigOperators

def spectralOneBodyF002 (lam : ℝ) (z : ℂ) (q : ℝ) : ℂ :=
  2 * spectralSmallRootF002 lam z q / (1 - spectralSmallRootF002 lam z q ^ 2)

def fullRootNumeratorF002 {N : ℕ} (lam : ℝ) (z b : ℂ) (q : Fin N → ℝ) : ℂ :=
  b ^ N * (∏ i, spectralOneBodyF002 lam z (q i)) *
    ∏ ij ∈ indexPairs N, spectralCanceledPairF002 lam z (q ij.1) (q ij.2)

def embeddedSineBlock {N : ℕ} (m : ℕ) (q : Fin N → ℝ) : ℂ :=
  ∏ ij ∈ indexPairs N, if ij.1.val < m ∧ ij.2.val < m then
    ((Real.sin ((q ij.1 - q ij.2) / 2) ^ 2 : ℝ) : ℂ) else 1

def retainedNumeratorQuotientF002 {N : ℕ} (m : ℕ)
    (lam : ℝ) (z b : ℂ) (q : Fin N → ℝ) : ℂ :=
  b ^ N * (∏ i, spectralOneBodyF002 lam z (q i)) *
    ∏ ij ∈ indexPairs N, if ij.1.val < m ∧ ij.2.val < m then
      spectralSinePairCoefficientF002 lam z (q ij.1) (q ij.2)
    else spectralCanceledPairF002 lam z (q ij.1) (q ij.2)

/-- The embedded product is exactly the frozen first-m sine Vandermonde,
with each unordered pair occurring once and the original factor 1/2. -/
theorem embeddedSineBlock_eq_retainedSineBlock {m N : ℕ} (hm : m ≤ N)
    (q : Fin N → ℝ) :
    embeddedSineBlock m q = (retainedSineBlock (fun i : Fin m => q (i.castLE hm)) : ℂ) := by
  unfold embeddedSineBlock retainedSineBlock
  rw [Complex.ofReal_prod]
  rw [← Finset.prod_filter]
  symm
  apply Finset.prod_bij (fun ij _ => (ij.1.castLE hm, ij.2.castLE hm))
  · intro ij hij
    simp only [Finset.mem_filter, indexPairs, Finset.mem_product, Finset.mem_univ,
      true_and] at hij ⊢
    exact ⟨hij, ij.1.isLt, ij.2.isLt⟩
  · intro a ha b hb he
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun p : Fin N × Fin N => p.1.val) he
    · apply Fin.ext
      exact congrArg (fun p : Fin N × Fin N => p.2.val) he
  · intro ij hij
    simp only [Finset.mem_filter, indexPairs, Finset.mem_product, Finset.mem_univ,
      true_and] at hij
    let a : Fin m := ⟨ij.1.val, hij.2.1⟩
    let b : Fin m := ⟨ij.2.val, hij.2.2⟩
    refine ⟨(a, b), ?_, ?_⟩
    · simp only [indexPairs, Finset.mem_filter, Finset.mem_product,
        Finset.mem_univ, true_and]
      change ij.1.val < ij.2.val
      exact hij.1
    · apply Prod.ext <;> apply Fin.ext <;> rfl
  · intro ij _
    rfl

/-- Exact factorization for all N and m, including every retained collision
locus. Later bounds must apply to this actual quotient. -/
theorem fullRootNumeratorF002_retained_factorization {N : ℕ} (m : ℕ)
    (lam : ℝ) (z b : ℂ) (q : Fin N → ℝ) :
    fullRootNumeratorF002 lam z b q =
      embeddedSineBlock m q * retainedNumeratorQuotientF002 m lam z b q := by
  have he : ∀ ij ∈ indexPairs N,
      spectralCanceledPairF002 lam z (q ij.1) (q ij.2) =
        (if ij.1.val < m ∧ ij.2.val < m then
          ((Real.sin ((q ij.1 - q ij.2) / 2) ^ 2 : ℝ) : ℂ) else (1 : ℂ)) *
        (if ij.1.val < m ∧ ij.2.val < m then
          spectralSinePairCoefficientF002 lam z (q ij.1) (q ij.2)
        else spectralCanceledPairF002 lam z (q ij.1) (q ij.2)) := by
    intro ij _
    split_ifs
    · rw [spectralCanceledPairF002_factorization]
      ring
    · simp
  unfold fullRootNumeratorF002 embeddedSineBlock retainedNumeratorQuotientF002
  rw [Finset.prod_congr rfl he, Finset.prod_mul_distrib]
  ring

theorem spectralOneBodyF002_analyticAt {lam : ℝ} {z : ℂ} (q : ℝ)
    (hz : z ∉ spectralSetF002 lam) :
    AnalyticAt ℂ (fun w => spectralOneBodyF002 lam w q) z := by
  have hq := spectralSmallRootF002_analyticAt q hz
  have hden := pair_root_denominator_ne_zero (spectralSmallRootF002_spec q hz).2
    (spectralSmallRootF002_spec q hz).2
  unfold spectralOneBodyF002
  exact (analyticAt_const.mul hq).div (analyticAt_const.sub (hq.pow 2))
    (by simpa only [pow_two] using hden)

theorem fullRootNumeratorF002_analyticAt {N : ℕ} {lam : ℝ} {z : ℂ}
    (b : ℂ → ℂ) (q : Fin N → ℝ) (hb : AnalyticAt ℂ b z)
    (hz : z ∉ spectralSetF002 lam) (hS : spectralS z ≠ 0) :
    AnalyticAt ℂ (fun w => fullRootNumeratorF002 lam w (b w) q) z := by
  unfold fullRootNumeratorF002
  exact ((hb.pow N).mul (Finset.univ.analyticAt_fun_prod fun i _ =>
    spectralOneBodyF002_analyticAt (q i) hz)).mul
    ((indexPairs N).analyticAt_fun_prod fun ij _ =>
      spectralCanceledPairF002_analyticAt (q ij.1) (q ij.2) hz hS)

/-- All fixed finite blocks have their actual analytic extension through
the complete collision set, without deleting angles from the domain. -/
theorem retainedNumeratorQuotientF002_analyticAt {N : ℕ} (m : ℕ)
    {lam : ℝ} {z : ℂ} (b : ℂ → ℂ) (q : Fin N → ℝ) (hb : AnalyticAt ℂ b z)
    (hz : z ∉ spectralSetF002 lam) (hS : spectralS z ≠ 0) :
    AnalyticAt ℂ (fun w => retainedNumeratorQuotientF002 m lam w (b w) q) z := by
  unfold retainedNumeratorQuotientF002
  apply ((hb.pow N).mul (Finset.univ.analyticAt_fun_prod fun i _ =>
    spectralOneBodyF002_analyticAt (q i) hz)).mul
  apply Finset.analyticAt_fun_prod
  intro ij _
  split_ifs
  · exact spectralSinePairCoefficientF002_analyticAt (q ij.1) (q ij.2) hz hS
  · exact spectralCanceledPairF002_analyticAt (q ij.1) (q ij.2) hz hS

end
end IsingBulk.AnisoF002.RegularTail
