import IsingBulk.AnisoF002.C03.RegularCollisionJetBound
import IsingBulk.AnisoF002.C03.RegularCollisionRationalMajorant

/-!
# The actual scaled real-cycle collision integrand

The complex analytic blow-up is restricted to positive real s. The
result is identified with every temperature derivative of the complete
original real-angle density and bounded by the full Vandermonde rational
weight. The inward path is epsilon=s² throughout.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators

theorem retainedSineBlock_le_vandermonde {N : ℕ} (x : Fin N → ℝ) :
    retainedSineBlock x ≤ ‖edgeVandermondeSquared (complexAngles x)‖ := by
  simp only [retainedSineBlock, edgeVandermondeSquared, norm_prod, norm_pow,
    complexAngles, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  apply Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
  intro ij _
  have hs := Real.sin_sq_le_sq (x := (x ij.1 - x ij.2) / 2)
  nlinarith [sq_nonneg (x ij.1 - x ij.2)]

theorem retainedSineBlock_scaled_bound {N : ℕ} (x : Fin N → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    retainedSineBlock (fun i => s * x i) ≤
      s ^ (2 * N.choose 2) * ‖edgeVandermondeSquared (complexAngles x)‖ := by
  have h := retainedSineBlock_le_vandermonde (fun i => s * x i)
  have he : complexAngles (fun i => s * x i) = fun i => (s : ℂ) * complexAngles x i := by
    funext i
    simp only [complexAngles, Complex.ofReal_mul]
  rw [he, edgeVandermondeSquared_scaling, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hs] at h
  exact h

theorem angularQuadratic_mul {N : ℕ} (x : Fin N → ℝ) (s : ℝ) :
    angularQuadratic (fun i => s * x i) = s ^ 2 * angularQuadratic x := by
  simp only [angularQuadratic, mul_pow, Finset.mul_sum]

theorem flatConstrainedAngles_mul {n : ℕ} (x : Fin n → ℝ) (s : ℝ) :
    flatConstrainedAngles (fun i => s * x i) = fun i => s * flatConstrainedAngles x i := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [flatConstrainedAngles, Fin.snoc_last, ← Finset.mul_sum, mul_neg]
  · simp only [flatConstrainedAngles, Fin.snoc_castSucc]

def collisionScaledJet {N : ℕ} (b : ℝ) (a : ℂ → ℂ) (j : ℕ) (s : ℝ)
    (x : Fin N → ℝ) : ℂ :=
  ((s : ℂ) ^ (2 * j + 2) / (s : ℂ) ^ (2 * N.choose 2)) *
    iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u (fun i => s * x i))
      (((s ^ 2 : ℝ) : ℂ) * Complex.I)

def collisionLeadingJet {N : ℕ} (b : ℝ) (a : ℂ → ℂ) (j : ℕ) (x : Fin N → ℝ) : ℂ :=
  (2 * edgeVandermondeSquared (complexAngles x) *
    edgeCollisionNumerator (affineEdgeCenter b) a ((0 : ℂ), (0 : Fin N → ℂ)) /
      deriv upperEdgePhase (b : ℂ)) *
    ((-1 : ℂ) ^ j * (j.factorial : ℂ) * (N : ℂ) ^ j /
      ((N : ℂ) * Complex.I + a 0 / 2 * ∑ i, (x i : ℂ) ^ 2) ^ (j + 1))

theorem collisionScaledJet_eq_filled {N : ℕ} (b : ℝ) (a : ℂ → ℂ) (j : ℕ)
    {s : ℝ} (hs : s ≠ 0) (x : Fin N → ℝ) (hres : upperEdgeRoot (b : ℂ) ^ N = 1) :
    collisionScaledJet b a j s x =
      iteratedDeriv j (fun t => collisionBlowupDensity b a (complexAngles x) ((s : ℂ), t))
        Complex.I := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hd : (fun u => edgeFullDensity (affineEdgeCenter b) a u (fun i => s * x i)) =
      (fun u => edgeJointDensity (affineEdgeCenter b) a (u, fun i => (s : ℂ) * complexAngles x i)) := by
    funext u
    rw [← edgeJointDensity_real]
    congr 2
    funext i
    simp only [complexAngles, Complex.ofReal_mul]
  rw [collisionScaledJet, hd, Complex.ofReal_pow]
  exact collisionBlowupDensity_jet_quotient b a (complexAngles x) (s : ℂ) Complex.I hsC hres j

theorem collisionScaledJet_limit {N : ℕ} {b : ℝ} {a : ℂ → ℂ}
    (d : RegularEdgeControl (affineEdgeCenter b) a) (hN : 0 < N)
    (hb : |b| < 1) (ha : 0 < (a 0).im) (hres : upperEdgeRoot (b : ℂ) ^ N = 1)
    (x : Fin N → ℝ) (j : ℕ) :
    Tendsto (fun s : ℝ => collisionScaledJet b a j s x) (𝓝[>] (0 : ℝ))
      (𝓝 (collisionLeadingJet b a j x)) := by
  have han := collisionBlowupDensity_analytic d hb (complexAngles x) Complex.I
    (collisionBlowupTotal_center_ne_zero hN hb ha x)
  have hc := (second_parameter_jet_continuous han j).comp
    (f := fun s : ℝ => (s : ℂ)) Complex.continuous_ofReal.continuousAt
  have hl := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [Function.comp_def, Complex.ofReal_zero] at hl
  rw [collisionBlowupDensity_jet_center] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (collisionScaledJet_eq_filled b a j (ne_of_gt hs) x hres).symm

namespace RegularEdgeCompleteControl
variable {b : ℝ} {a : ℂ → ℂ} (d : RegularEdgeCompleteControl b a)

theorem collisionScaledJet_uniform_bound {N : ℕ} (hN : 0 < N) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s → s ^ 2 ≤ d.eps0 → s ^ 2 ≤ 1 →
      ∀ x : Fin N → ℝ, (∀ i, |s * x i| ≤ Real.pi) →
        ‖collisionScaledJet b a j s x‖ ≤
          C * ‖edgeVandermondeSquared (complexAngles x)‖ / (1 + angularQuadratic x) ^ (j + 1) := by
  obtain ⟨C, hC, hbound⟩ := d.fullDensity_principal_jet_bound hN j
  refine ⟨C, hC, ?_⟩
  intro s hs hs0 hs1 x hx
  have he := hbound (s ^ 2) (sq_pos_of_pos hs) hs0 hs1 (fun i => s * x i) hx
  have hV := retainedSineBlock_scaled_bound x hs.le
  have hden : s ^ 2 + angularQuadratic (fun i => s * x i) =
      s ^ 2 * (1 + angularQuadratic x) := by rw [angularQuadratic_mul]; ring
  have hq : 0 < 1 + angularQuadratic x := by linarith [angularQuadratic_nonneg x]
  have hsc : 0 ≤ s ^ (2 * j + 2) / s ^ (2 * N.choose 2) := by positivity
  rw [collisionScaledJet, norm_mul, norm_div, norm_pow, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hs.le]
  calc
    (s ^ (2 * j + 2) / s ^ (2 * N.choose 2)) *
        ‖iteratedDeriv j (fun u => edgeFullDensity (affineEdgeCenter b) a u (fun i => s * x i))
          (((s ^ 2 : ℝ) : ℂ) * Complex.I)‖ ≤
        (s ^ (2 * j + 2) / s ^ (2 * N.choose 2)) *
          (C * retainedSineBlock (fun i => s * x i) /
            (s ^ 2 + angularQuadratic (fun i => s * x i)) ^ (j + 1)) :=
      mul_le_mul_of_nonneg_left he hsc
    _ ≤ (s ^ (2 * j + 2) / s ^ (2 * N.choose 2)) *
        (C * (s ^ (2 * N.choose 2) * ‖edgeVandermondeSquared (complexAngles x)‖) /
          (s ^ 2 * (1 + angularQuadratic x)) ^ (j + 1)) := by
      rw [hden]
      gcongr
    _ = C * ‖edgeVandermondeSquared (complexAngles x)‖ / (1 + angularQuadratic x) ^ (j + 1) := by
      rw [show 2 * j + 2 = 2 * (j + 1) by omega, pow_mul, mul_pow]
      field_simp

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
