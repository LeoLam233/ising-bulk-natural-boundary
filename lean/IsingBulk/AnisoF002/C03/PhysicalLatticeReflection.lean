import IsingBulk.AnisoF002.C03.PhysicalRealFactors

/-!
# Both signs of the original lattice Fourier displacement

The simultaneous measure-preserving reflection of every angular variable
is proved for the original finite iterated integral.  The real complete
numerator is invariant, and the integer Fourier character changes sign.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors IsingBulk.First
open scoped BigOperators

def reflectedAngles {N : ℕ} (q : Fin N → ℝ) : Fin N → ℝ := fun i => 2 * Real.pi - q i

theorem reflectedAngles_cons {N : ℕ} (u : ℝ) (q : Fin N → ℝ) :
    reflectedAngles (Fin.cons u q) = Fin.cons (2 * Real.pi - u) (reflectedAngles q) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem multiAngleIntegral_reflected (N : ℕ) (f : (Fin N → ℝ) → ℂ) :
    multiAngleIntegral N (fun q => f (reflectedAngles q)) = multiAngleIntegral N f := by
  induction N with
  | zero =>
    simp only [multiAngleIntegral]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [multiAngleIntegral, reflectedAngles_cons]
    have hi (q : Fin n → ℝ) :
        (∫ u : ℝ in 0..2 * Real.pi, f (Fin.cons (2 * Real.pi - u) (reflectedAngles q))) =
          ∫ u : ℝ in 0..2 * Real.pi, f (Fin.cons u (reflectedAngles q)) := by
      rw [intervalIntegral.integral_comp_sub_left (fun u => f (Fin.cons u (reflectedAngles q)))]
      simp only [sub_self, sub_zero]
    simp_rw [hi]
    exact ih (fun q => ∫ u : ℝ in 0..2 * Real.pi, f (Fin.cons u q))

theorem published_gamma_reflected {N : ℕ} (B C : ℝ) (q : Fin N → ℝ) (i : Fin N) :
    gamma B C (reflectedAngles q i) = gamma B C (q i) := by
  simp only [gamma, reflectedAngles, Real.cos_two_pi_sub]

theorem published_weight_reflected {N : ℕ} (B C : ℝ) (q : Fin N → ℝ) :
    angularWeight B C (reflectedAngles q) = angularWeight B C q := by
  have hp (i j : Fin N) : (reflectedAngles q i - reflectedAngles q j) / 2 =
      -((q i - q j) / 2) := by unfold reflectedAngles; ring
  simp only [angularWeight, FormFactors.pairProduct, published_gamma_reflected,
    hp, Real.sin_neg, neg_div, neg_sq]

theorem published_rootProduct_reflected {N : ℕ} (B C : ℝ) (q : Fin N → ℝ) :
    rootProduct B C (reflectedAngles q) = rootProduct B C q := by
  simp only [rootProduct, FormFactors.root, published_gamma_reflected]

theorem integer_fourier_reflected {N : ℕ} (k : ℤ) (q : Fin N → ℝ) :
    Complex.exp (Complex.I * (k : ℂ) * ∑ i, (reflectedAngles q i : ℂ)) =
      Complex.exp (Complex.I * (-k : ℂ) * ∑ i, (q i : ℂ)) := by
  have hs : (∑ i, (reflectedAngles q i : ℂ)) =
      (N : ℂ) * (2 * (Real.pi : ℂ)) - ∑ i, (q i : ℂ) := by
    simp only [reflectedAngles, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hs]
  have he : Complex.I * (k : ℂ) * ((N : ℂ) * (2 * (Real.pi : ℂ)) - ∑ i, (q i : ℂ)) =
      ((k * (N : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
        Complex.I * (-k : ℂ) * ∑ i, (q i : ℂ) := by push_cast; ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- The original signed Fourier convention is preserved by an actual finite
change of variables, without assuming a reflection law for correlations. -/
theorem literal_latticeCoefficient_reflect_second (N : ℕ) (B C : ℝ) (m k : ℤ) :
    latticeCoefficient N B C (m, -k) = latticeCoefficient N B C (m, k) := by
  unfold latticeCoefficient
  congr 1
  rw [← multiAngleIntegral_reflected N (fun q =>
    ((angularWeight B C q * rootProduct B C q ^ m.natAbs : ℝ) : ℂ) *
      Complex.exp (Complex.I * (k : ℂ) * ∑ i, (q i : ℂ)))]
  congr 1
  funext q
  simp only [published_weight_reflected, published_rootProduct_reflected,
    integer_fourier_reflected, Complex.ofReal_mul, Complex.ofReal_pow, Int.cast_neg]

end
end IsingBulk.AnisoF002.RegularTail.C03
