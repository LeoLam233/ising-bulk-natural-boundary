import IsingBulk.First.LocalizedDouble

/-! Exact compatible decomposition of the actual normalized double integral,
before any x localization or residue operation. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory

theorem localizedDoubleFormFactor_add (N : ℕ) (hN : 0 < N) (r : ℝ) (s : ℂ)
    (z : ℂ → ℂ)
    (h : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => z (anglePoint r (θ i))))
    (u v : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hu : Continuous u) (hv : Continuous v) :
    localizedDoubleFormFactor N r s (fun p => u p+v p) =
      localizedDoubleFormFactor N r s u + localizedDoubleFormFactor N r s v := by
  have hi := localizedDoubleAngleDensity_integrable N hN r s z h u hu
  have hj := localizedDoubleAngleDensity_integrable N hN r s z h v hv
  have he : localizedDoubleAngleDensity r s (fun p => u p+v p) =
      fun p => localizedDoubleAngleDensity r s u p+localizedDoubleAngleDensity r s v p := by
    funext p
    simp only [localizedDoubleAngleDensity, Complex.ofReal_add]
    ring
  unfold localizedDoubleFormFactor
  rw [he, integral_add hi hj]
  ring

theorem localizedDoubleFormFactor_partition (N : ℕ) (hN : 0 < N) (r : ℝ) (s : ℂ)
    (z : ℂ → ℂ)
    (h : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => z (anglePoint r (θ i))))
    (u v : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hu : Continuous u) (hv : Continuous v) :
    doubleFormFactor N r s = localizedDoubleFormFactor N r s u +
      localizedDoubleFormFactor N r s v + localizedDoubleFormFactor N r s (fun p => 1-u p-v p) := by
  have he : (fun p => (u p+v p)+(1-u p-v p)) = (fun _ => (1:ℝ)) := by
    funext p
    ring
  have hrem : Continuous (fun p => 1-u p-v p) := (continuous_const.sub hu).sub hv
  rw [doubleFormFactor_eq_product_integral N hN r s z h, ← he]
  calc
    _ = localizedDoubleFormFactor N r s (fun p => u p+v p) +
        localizedDoubleFormFactor N r s (fun p => 1-u p-v p) := by
      exact localizedDoubleFormFactor_add N hN r s z h
        (fun p => u p+v p) (fun p => 1-u p-v p) (hu.add hv) hrem
    _ = _ := by rw [localizedDoubleFormFactor_add N hN r s z h u v hu hv]

/-- The selected weights have only y-angle arguments; all x integrations remain
unweighted. The complement is the literal remaining angular density. -/
theorem compatible_localization_identity (N : ℕ) (hN : 0 < N) (r : ℝ) (s : ℂ)
    (z : ℂ → ℂ)
    (h : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => z (anglePoint r (θ i))))
    (u v : (Fin N → ℝ) → ℝ) (hu : Continuous u) (hv : Continuous v) :
    doubleFormFactor N r s = weightedDoubleFormFactor N r s u +
      weightedDoubleFormFactor N r s v +
      localizedDoubleFormFactor N r s (fun p => 1-u p.2-v p.2) := by
  rw [weightedDoubleFormFactor_eq_product_integral N hN r s z h u hu,
    weightedDoubleFormFactor_eq_product_integral N hN r s z h v hv]
  exact localizedDoubleFormFactor_partition N hN r s z h _ _
    (hu.comp continuous_snd) (hv.comp continuous_snd)

end
end IsingBulk.First
