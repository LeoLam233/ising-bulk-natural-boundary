import IsingBulk.Joint.Isotropic.LowCovering
import IsingBulk.Joint.FormFactors.Normalized

namespace IsingBulk.Joint
noncomputable section
open FormFactors

/-- Literal contour construction depends only on the three spectral coefficients. -/
theorem contourRadius_eq_of_data {K L : Coupling}
    (hs : S K = S L) (ht : T K = T L) (ha : A K = A L) :
    contourRadius K = contourRadius L := by
  classical
  let chooseRadius (P : ℝ → Prop) : ℝ := if h : ∃ r, P r then Classical.choose h else 1/2
  have hp : ContourAnnulus K = ContourAnnulus L := by
    funext r
    simp only [ContourAnnulus, FormFactors.dispersion, hs,ht,ha]
  exact congrArg chooseRadius hp

theorem unscaledFullCoefficient_eq_of_data {K L : Coupling}
    (hs : S K = S L) (ht : T K = T L) (ha : A K = A L) (N : ℕ) :
    unscaledFullCoefficient N K = unscaledFullCoefficient N L := by
  simp only [unscaledFullCoefficient, contourRadius_eq_of_data hs ht ha,
    unscaledFullCoefficientAtRadius, fullDensity, commonDensity, FormFactors.dispersion, hs,ht,ha]

theorem highNormalizedBulk_eq_of_data {K L : Coupling}
    (hs : S K = S L) (ht : T K = T L) (ha : A K = A L) :
    highNormalizedBulk K = highNormalizedBulk L := by
  have hp : p K = p L := by simp only [p, hs,ht]
  simp only [highNormalizedBulk,highPrefactor,hp,unscaledFullCoefficient_eq_of_data hs ht ha]

theorem lowNormalizedBulk_eq_of_data {K L : Coupling}
    (hs : S K = S L) (ht : T K = T L) (ha : A K = A L) :
    lowNormalizedBulk K = lowNormalizedBulk L := by
  have hp : p K = p L := by simp only [p, hs,ht]
  simp only [lowNormalizedBulk,lowPrefactor,hp,unscaledFullCoefficient_eq_of_data hs ht ha]

/-- On the diagonal, A=1+s², so equality of sinh suffices; no choice of inverse
is allowed to change the actual normalized susceptibility. -/
theorem diagonal_low_eq_of_sinh_eq {z w : ℂ} (he : Complex.sinh z = Complex.sinh w) :
    lowNormalizedBulk (ratioSlice 1 z) = lowNormalizedBulk (ratioSlice 1 w) := by
  apply lowNormalizedBulk_eq_of_data
  · exact he
  · simpa only [T,ratioSlice,Complex.ofReal_one,one_mul] using he
  · simp only [A,ratioSlice,Complex.ofReal_one,one_mul,← pow_two,Complex.cosh_sq,he]

theorem diagonal_high_eq_of_sinh_eq {z w : ℂ} (he : Complex.sinh z = Complex.sinh w) :
    highNormalizedBulk (ratioSlice 1 z) = highNormalizedBulk (ratioSlice 1 w) := by
  apply highNormalizedBulk_eq_of_data
  · exact he
  · simpa only [T,ratioSlice,Complex.ofReal_one,one_mul] using he
  · simp only [A,ratioSlice,Complex.ofReal_one,one_mul,← pow_two,Complex.cosh_sq,he]

theorem low_bulk_deck_invariant (z : ℂ) (n : ℤ) :
    lowNormalizedBulk (ratioSlice 1 (z+n*(2*Real.pi*Complex.I))) =
      lowNormalizedBulk (ratioSlice 1 z) := by
  apply diagonal_low_eq_of_sinh_eq
  rw [sinh_eq_joukowski_exp, sinh_eq_joukowski_exp,
    Complex.exp_eq_exp_iff_exists_int.mpr ⟨n,rfl⟩]

end
end IsingBulk.Joint
