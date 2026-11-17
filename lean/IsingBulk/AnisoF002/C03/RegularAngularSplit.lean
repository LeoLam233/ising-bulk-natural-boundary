import IsingBulk.AnisoF002.C03.RegularCompleteTail
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Exact independence of the retained-block angular splitting

Concatenation preserves the normalized angular probability measures.
Consequently the coefficient written with a retained block is the same
N-1-variable constrained coefficient for every choice of block size.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology

def angularAppendEquiv (m k : ℕ) :
    ((Fin m → ℝ) × (Fin k → ℝ)) ≃ᵐ (Fin (m + k) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin k => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (m + k) => ℝ) finSumFinEquiv)

theorem angularAppendEquiv_apply (m k : ℕ) (p : (Fin m → ℝ) × (Fin k → ℝ)) :
    angularAppendEquiv m k p = Fin.append p.1 p.2 := by
  ext i
  induction i using Fin.addCases with
  | left i =>
    simp [angularAppendEquiv, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
    rfl
  | right i =>
    simp [angularAppendEquiv, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
    rfl

theorem angularAppendEquiv_volume (m k : ℕ) :
    MeasurePreserving (angularAppendEquiv m k) volume volume :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin (m + k) => ℝ) finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin k => ℝ))

theorem angularAppendEquiv_preimage_box (m k : ℕ) :
    angularAppendEquiv m k ⁻¹' regularAngularBox (m + k) =
      regularAngularBox m ×ˢ regularAngularBox k := by
  ext p
  simp only [Set.mem_preimage, angularAppendEquiv_apply, regularAngularBox, Set.mem_Icc,
    Set.mem_prod, Pi.le_def]
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨⟨fun i => by simpa using hl (Fin.castAdd k i),
      fun i => by simpa using hu (Fin.castAdd k i)⟩,
      ⟨fun i => by simpa using hl (Fin.natAdd m i),
        fun i => by simpa using hu (Fin.natAdd m i)⟩⟩
  · rintro ⟨⟨hl, hu⟩, ⟨hl', hu'⟩⟩
    exact ⟨Fin.addCases (fun i => by simpa using hl i) (fun i => by simpa using hl' i),
      Fin.addCases (fun i => by simpa using hu i) (fun i => by simpa using hu' i)⟩

theorem angularAppendEquiv_probability (m k : ℕ) :
    MeasurePreserving (angularAppendEquiv m k)
      ((regularAngularProbability m).prod (regularAngularProbability k))
      (regularAngularProbability (m + k)) := by
  have h := (angularAppendEquiv_volume m k).restrict_preimage
    (regularAngularBox_compact (m + k)).measurableSet
  rw [angularAppendEquiv_preimage_box] at h
  have hs := h.smul_measure (ENNReal.ofReal ((2 * Real.pi) ^ (m + k)))⁻¹
  unfold regularAngularProbability
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.prod_restrict]
  convert hs using 1
  congr 1
  rw [pow_add, ENNReal.ofReal_mul (pow_nonneg (by positivity) m), ENNReal.mul_inv]
  · exact Or.inr ENNReal.ofReal_ne_top
  · exact Or.inl ENNReal.ofReal_ne_top

theorem regularAngularProbability_integral_append (m k : ℕ) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : (Fin (m + k) → ℝ) → F) :
    ∫ p, f (Fin.append p.1 p.2) ∂(regularAngularProbability m).prod (regularAngularProbability k) =
      ∫ q, f q ∂regularAngularProbability (m + k) := by
  simpa only [angularAppendEquiv_apply] using (angularAppendEquiv_probability m k).integral_comp' f

def flatConstrainedAngles {n : ℕ} (q : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc q (-(∑ i, q i))

theorem splitConstrainedAngles_eq_flat {m k : ℕ} (q : Fin m → ℝ) (y : Fin k → ℝ) :
    splitConstrainedAngles q y = flatConstrainedAngles (Fin.append q y) := by
  unfold splitConstrainedAngles flatConstrainedAngles
  rw [Fin.append_snoc]
  congr 1
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, neg_add_rev]
  ring

/-- The index n is the number of independent angles; this coefficient
has exactly n+1 particles. -/
def edgeParticleCoefficient (c a : ℂ → ℂ) (n : ℕ) (t : ℂ) : ℂ :=
  ((n + 1).factorial : ℂ)⁻¹ *
    ∫ q, edgeFullDensity c a t (flatConstrainedAngles q) ∂regularAngularProbability n

theorem edgeConstrainedCoefficient_eq_particle (c a : ℂ → ℂ) (m k : ℕ) :
    edgeConstrainedCoefficient c a m k = edgeParticleCoefficient c a (m + k) := by
  funext t
  unfold edgeConstrainedCoefficient edgeParticleCoefficient
  simp_rw [splitConstrainedAngles_eq_flat]
  congr 1
  exact regularAngularProbability_integral_append m k
    (fun q => edgeFullDensity c a t (flatConstrainedAngles q))

end
end IsingBulk.AnisoF002.RegularTail.C03
