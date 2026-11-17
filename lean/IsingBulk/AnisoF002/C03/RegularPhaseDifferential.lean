import IsingBulk.AnisoF002.C03.RegularResonance

/-!
# Exact regular-edge collision phase and its temperature derivative

The phase is the same principal logarithm already used on the entire real
cycle.  Its derivative follows from the unsquared dispersion identity,
and its collision value lies in the fixed principal logarithm strip.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter
open scoped Topology

theorem upperEdgePhase_cos {φ : ℝ} (hφ : 0 < φ) (hπ : φ < Real.pi) :
    upperEdgePhase (Real.cos φ : ℂ) = (φ : ℂ) * Complex.I := by
  rw [upperEdgePhase, upperEdgeRoot_cos hφ hπ,
    Complex.log_exp (by simpa using neg_lt_neg hπ)
      (by simp only [Complex.mul_im, Complex.neg_re, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.neg_im, Complex.ofReal_im, Complex.I_re,
          mul_zero, add_zero]; linarith [Real.pi_pos])]
  ring

theorem upperEdgePhase_hasDerivAt {W : ℂ} (hW : 1 - W ^ 2 ∈ Complex.slitPlane) :
    HasDerivAt upperEdgePhase (1 / Complex.sinh (upperEdgePhase W)) W := by
  have hd := (upperEdgePhase_analyticAt hW).differentiableAt.hasDerivAt
  have he : (fun w => Complex.cosh (upperEdgePhase w)) = (fun w : ℂ => w) := by
    funext w
    exact upperEdgePhase_cosh w
  have hv : Complex.sinh (upperEdgePhase W) * deriv upperEdgePhase W = 1 := by
    have hh := hd.ccosh.deriv
    rw [he, deriv_id''] at hh
    exact hh.symm
  have hs : Complex.sinh (upperEdgePhase W) ≠ 0 := by
    intro hs
    rw [hs, zero_mul] at hv
    exact zero_ne_one hv
  have hv' : deriv upperEdgePhase W = 1 / Complex.sinh (upperEdgePhase W) := by
    apply (eq_div_iff hs).mpr
    simpa only [mul_comm] using hv
  rwa [hv'] at hd

def regularComplexPhase (b : ℝ) (a : ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  edgeJointPhase (affineEdgeCenter b) a (p.1, Complex.cos p.2)

theorem regularComplexPhase_cosh (b : ℝ) (a : ℂ → ℂ) (p : ℂ × ℂ) :
    Complex.cosh (regularComplexPhase b a p) =
      (b : ℂ) + p.1 + a p.1 * (1 - Complex.cos p.2) := upperEdgePhase_cosh _

theorem regularComplexPhase_even (b : ℝ) (a : ℂ → ℂ) (t q : ℂ) :
    regularComplexPhase b a (t, -q) = regularComplexPhase b a (t, q) := by
  simp [regularComplexPhase, Complex.cos_neg]

theorem regularComplexPhase_real (b : ℝ) (a : ℂ → ℂ) (t : ℂ) (q : ℝ) :
    regularComplexPhase b a (t, (q : ℂ)) =
      edgeAnglePhase (affineEdgeCenter b) a t q := by
  simp only [regularComplexPhase, edgeAnglePhase, Complex.ofReal_cos]

theorem regularComplexPhase_zero_angle (b : ℝ) (a : ℂ → ℂ) (t : ℂ) :
    regularComplexPhase b a (t, 0) = upperEdgePhase ((b : ℂ) + t) := by
  simp [regularComplexPhase, edgeJointPhase, affineEdgeCenter]

theorem regularComplexPhase_analyticAt_zero {b : ℝ} {a : ℂ → ℂ}
    (hb : |b| < 1) (ha : AnalyticAt ℂ a 0) :
    AnalyticAt ℂ (regularComplexPhase b a) (0, 0) := by
  have hW : 1 - (b : ℂ) ^ 2 ∈ Complex.slitPlane :=
    edge_discriminant_slit (Or.inr ⟨rfl, hb⟩)
  have hin : AnalyticAt ℂ (fun p : ℂ × ℂ =>
      (b : ℂ) + p.1 + a p.1 * (1 - Complex.cos p.2)) (0, 0) :=
    (analyticAt_const.add analyticAt_fst).add
      ((ha.comp (f := fun p : ℂ × ℂ => p.1) analyticAt_fst).mul
        (analyticAt_const.sub (Complex.analyticAt_cos.comp analyticAt_snd)))
  exact (upperEdgePhase_analyticAt hW).comp_of_eq hin (by simp [affineEdgeCenter])

theorem regularComplexPhase_temperature_hasDerivAt {b : ℝ} (a : ℂ → ℂ)
    (hb : |b| < 1) :
    HasDerivAt (fun t => regularComplexPhase b a (t, 0))
      (1 / Complex.sinh (upperEdgePhase (b : ℂ))) 0 := by
  have hW : 1 - (b : ℂ) ^ 2 ∈ Complex.slitPlane :=
    edge_discriminant_slit (Or.inr ⟨rfl, hb⟩)
  have hd := (upperEdgePhase_hasDerivAt hW).comp_of_eq (0 : ℂ)
      ((hasDerivAt_id (0 : ℂ)).const_add (b : ℂ)) (by simp)
  simpa only [Function.comp_def, id_eq, mul_one, regularComplexPhase_zero_angle] using hd

theorem regularComplexPhase_temperature_fderiv {b : ℝ} {a : ℂ → ℂ}
    (hb : |b| < 1) (ha : AnalyticAt ℂ a 0) :
    fderiv ℂ (regularComplexPhase b a) (0, 0) (1, 0) =
      1 / Complex.sinh (upperEdgePhase (b : ℂ)) := by
  have hg := regularComplexPhase_analyticAt_zero hb ha
  have hc := hg.differentiableAt.hasFDerivAt.comp_hasDerivAt
    (f := fun t : ℂ => (t, (0 : ℂ))) (0 : ℂ)
    ((hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const (0 : ℂ) (0 : ℂ)))
  exact hc.unique (regularComplexPhase_temperature_hasDerivAt a hb)

theorem regularComplexPhase_collision_temperature {φ : ℝ} {a : ℂ → ℂ}
    (hφ : 0 < φ) (hπ : φ < Real.pi) (ha : AnalyticAt ℂ a 0) :
    regularComplexPhase (Real.cos φ) a (0, 0) = (φ : ℂ) * Complex.I ∧
      fderiv ℂ (regularComplexPhase (Real.cos φ) a) (0, 0) (1, 0) =
        -Complex.I / (Real.sin φ : ℂ) ∧
      fderiv ℂ (regularComplexPhase (Real.cos φ) a) (0, 0) (1, 0) ≠ 0 := by
  have hs : Real.sin φ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ hπ)
  have hsC : (Real.sin φ : ℂ) ≠ 0 := by exact_mod_cast hs
  have hb : |Real.cos φ| < 1 := by
    apply (sq_lt_one_iff_abs_lt_one _).mp
    nlinarith [Real.sin_sq_add_cos_sq φ, sq_pos_of_ne_zero hs]
  have hc : regularComplexPhase (Real.cos φ) a (0, 0) = (φ : ℂ) * Complex.I := by
    rw [regularComplexPhase_zero_angle, add_zero, upperEdgePhase_cos hφ hπ]
  have hd : fderiv ℂ (regularComplexPhase (Real.cos φ) a) (0, 0) (1, 0) =
      -Complex.I / (Real.sin φ : ℂ) := by
    rw [regularComplexPhase_temperature_fderiv hb ha, upperEdgePhase_cos hφ hπ,
      Complex.sinh_mul_I, ← Complex.ofReal_sin]
    field_simp
    simp [Complex.I_sq]
  exact ⟨hc, hd, hd ▸ div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hsC⟩

end
end IsingBulk.AnisoF002.RegularTail.C03
