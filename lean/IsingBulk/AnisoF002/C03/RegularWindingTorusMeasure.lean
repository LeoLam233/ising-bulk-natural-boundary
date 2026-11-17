import IsingBulk.AnisoF002.C03.RegularCollisionIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.Integral

/-!
# Exact translation of the independent-angle torus measure

The finite product fundamental-domain proof applies to arbitrary periodic
integrands, including the literal inner-cutoff indicator.  It does not
require an unjustified continuity assertion at the cutoff boundary.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped BigOperators

abbrev WindingPeriodLattice (n : ℕ) := Fin n → AddSubgroup.zmultiples (2 * Real.pi)

def windingPeriodBox (n : ℕ) (c : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.univ.pi (fun i => Ioc (c i) (c i + 2 * Real.pi))

theorem windingPeriodBox_measurable (n : ℕ) (c : Fin n → ℝ) :
    MeasurableSet (windingPeriodBox n c) := by
  exact (measurableSet_pi Set.countable_univ).mpr (Or.inl (fun _ _ => measurableSet_Ioc))

theorem windingPeriodBox_fundamental (n : ℕ) (c : Fin n → ℝ) :
    IsAddFundamentalDomain (WindingPeriodLattice n) (windingPeriodBox n c) volume := by
  classical
  apply IsAddFundamentalDomain.mk' (windingPeriodBox_measurable n c).nullMeasurableSet
  intro x
  have hi (i : Fin n) : ∃! g : AddSubgroup.zmultiples (2 * Real.pi),
      (g : ℝ) + x i ∈ Ioc (c i) (c i + 2 * Real.pi) := by
    obtain ⟨k, hk, hku⟩ := existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos (x i) (c i)
    refine ⟨⟨k • (2 * Real.pi), AddSubgroup.zsmul_mem_zmultiples _ _⟩, ?_, ?_⟩
    · simpa only [add_comm] using hk
    · intro g hg
      obtain ⟨l, hl⟩ := AddSubgroup.mem_zmultiples_iff.mp g.property
      have hlm : x i + l • (2 * Real.pi) ∈ Ioc (c i) (c i + 2 * Real.pi) := by
        simpa only [hl, add_comm] using hg
      have he := hku l hlm
      apply Subtype.ext
      exact hl.symm.trans (congrArg (fun j : ℤ => j • (2 * Real.pi)) he)
  choose g hg hu using hi
  refine ⟨g, ?_, ?_⟩
  · exact fun i _ => hg i
  · intro h hh
    funext i
    exact hu i (h i) (hh i (Set.mem_univ i))

theorem windingPeriodBox_integral_eq (n : ℕ) (f : (Fin n → ℝ) → ℂ)
    (hf : ∀ k : Fin n → ℤ, ∀ x : Fin n → ℝ,
      f (fun i => x i + (k i : ℝ) * (2 * Real.pi)) = f x)
    (c d : Fin n → ℝ) :
    (∫ x in windingPeriodBox n c, f x) = ∫ x in windingPeriodBox n d, f x := by
  let : VAddInvariantMeasure (WindingPeriodLattice n) (Fin n → ℝ) volume :=
    ⟨fun g s _ => measure_preimage_add (volume : Measure (Fin n → ℝ)) (fun i => (g i : ℝ)) s⟩
  apply (windingPeriodBox_fundamental n c).setIntegral_eq (windingPeriodBox_fundamental n d)
  intro g x
  choose k hk using fun i => AddSubgroup.mem_zmultiples_iff.mp (g i).property
  have he : g +ᵥ x = fun i => x i + (k i : ℝ) * (2 * Real.pi) := by
    funext i
    change (g i : ℝ) + x i = _
    rw [← hk i, zsmul_eq_mul, add_comm]
  rw [he]
  exact hf k x

theorem windingPeriodBox_centered_ae (n : ℕ) :
    windingPeriodBox n (fun _ => -Real.pi) =ᵐ[volume] regularAngularBox n := by
  rw [volume_pi]
  simpa only [windingPeriodBox, regularAngularBox,
    show -Real.pi + 2 * Real.pi = Real.pi by ring] using
    (Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin n => (volume : Measure ℝ))
      (f := fun _ => -Real.pi) (g := fun _ => Real.pi))

theorem windingPeriodBox_add_preimage (n : ℕ) (c d : Fin n → ℝ) :
    (fun x : Fin n → ℝ => x + d) ⁻¹' windingPeriodBox n (c + d) = windingPeriodBox n c := by
  ext x
  simp only [windingPeriodBox, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ioc, Pi.add_apply]
  constructor
  · intro h i
    have h := h i
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro h i
    have h := h i
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem windingPeriodBox_integral_add (n : ℕ) (f : (Fin n → ℝ) → ℂ)
    (c d : Fin n → ℝ) :
    (∫ x in windingPeriodBox n c, f (x + d)) = ∫ x in windingPeriodBox n (c + d), f x := by
  have h := (measurePreserving_add_right (volume : Measure (Fin n → ℝ)) d).setIntegral_preimage_emb
    (MeasurableEquiv.addRight d).measurableEmbedding f (windingPeriodBox n (c + d))
  rwa [windingPeriodBox_add_preimage] at h

theorem regularAngularBox_integral_shift_measurable (n : ℕ) (f : (Fin n → ℝ) → ℂ)
    (hf : ∀ k : Fin n → ℤ, ∀ x : Fin n → ℝ,
      f (fun i => x i + (k i : ℝ) * (2 * Real.pi)) = f x)
    (c : Fin n → ℝ) :
    (∫ x in regularAngularBox n, f (x + c)) = ∫ x in regularAngularBox n, f x := by
  rw [← setIntegral_congr_set (windingPeriodBox_centered_ae n),
    ← setIntegral_congr_set (windingPeriodBox_centered_ae n)]
  rw [windingPeriodBox_integral_add]
  exact windingPeriodBox_integral_eq n f hf _ _

end
end IsingBulk.AnisoF002.NegativeHT
