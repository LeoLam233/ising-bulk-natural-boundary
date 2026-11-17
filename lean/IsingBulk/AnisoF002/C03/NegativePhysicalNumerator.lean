import IsingBulk.AnisoF002.C03.NegativeDensityAnalytic

/-!
# Identification with the complete canonical spectral numerator

The local winding numerator is exactly the full canonical-root numerator
at q_i = pi + d + v_i, with the literal independent-angle normalization.
The physical small-root identity is retained explicitly in the statement;
it is supplied by the constructed inward phase, not by a model kernel.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry
  IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.Isotropic
open scoped BigOperators

theorem completeNegativeNumerator_canonical {n : ℕ} (lam : ℝ) (z t : ℂ)
    (b : ℂ → ℂ) (g : ℂ × ℂ → ℂ) (d : ℝ) (v : Fin n → ℝ)
    (hγ : ∀ i, spectralSmallRootF002 lam z (Real.pi + d + v i) =
      Complex.exp (-g (t, (d : ℂ) + (v i : ℂ))))
    (hb : b t ^ 2 = spectralT lam z / spectralS z) :
    fullRootNumeratorF002 lam z (b t) (fun i => Real.pi + d + v i) /
        windingNormalization n =
      completeNegativeNumerator n b g (d : ℂ) t (fun i => (v i : ℂ)) := by
  rw [fullRootNumeratorF002_log_branch lam z (b t)
    (fun i => Real.pi + d + v i) (fun i => g (t, (d : ℂ) + (v i : ℂ))) hγ hb]
  have hsin (ij : Fin n × Fin n) :
      (Real.sin (((Real.pi + d + v ij.1) - (Real.pi + d + v ij.2)) / 2) : ℂ) =
        Complex.sin (((v ij.1 : ℂ) - (v ij.2 : ℂ)) / 2) := by
    rw [show ((Real.pi + d + v ij.1) - (Real.pi + d + v ij.2)) / 2 =
      (v ij.1 - v ij.2) / 2 by ring]
    push_cast
    rfl
  simp_rw [hsin]
  unfold completeNegativeNumerator
  ring

end
end IsingBulk.AnisoF002.NegativeHT
