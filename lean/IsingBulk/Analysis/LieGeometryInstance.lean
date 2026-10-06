import IsingBulk.Analysis.LieGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-! A concrete geometric instance: a circle punctured at its seam, exhausted
by closed intervals strictly inside one angular period. The two retained
endpoints have the actual boundary orientation toward the removed arcs. -/
namespace IsingBulk.Lie
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

abbrev circleCoordinate : AngularSpace 0 ≃ₜ ℝ := Homeomorph.piUnique (fun _ : Fin 1 => ℝ)

theorem circleCoordinate_apply (x : AngularSpace 0) : circleCoordinate x = x 0 := by
  change x default = x 0
  congr 1

theorem mem_constant_interval (a b : ℝ) (x : AngularSpace 0) :
    x ∈ Icc (fun _ => a) (fun _ => b) ↔ x 0 ∈ Icc a b := by
  simp [Set.mem_Icc, Pi.le_def, Fin.forall_fin_one]

theorem interval_puncture_endpoints {a b L H : ℝ} (ha : L < a) (hab : a ≤ b) (hb : b < H) :
    a ∈ frontier (Icc L H \ Icc a b) ∧ b ∈ frontier (Icc L H \ Icc a b) := by
  have hl : Ico L a ⊆ Icc L H \ Icc a b := by
    intro x hx
    exact ⟨⟨hx.1, by linarith [hx.2]⟩, fun h => (not_lt_of_ge h.1) hx.2⟩
  have hr : Ioc b H ⊆ Icc L H \ Icc a b := by
    intro x hx
    exact ⟨⟨by linarith [hx.1], hx.2⟩, fun h => (not_lt_of_ge h.2) hx.1⟩
  constructor
  · refine ⟨closure_mono hl ?_, fun h => (interior_subset h).2 ⟨le_rfl, hab⟩⟩
    rw [closure_Ico ha.ne]
    exact ⟨ha.le, le_rfl⟩
  · refine ⟨closure_mono hr ?_, fun h => (interior_subset h).2 ⟨hab, le_rfl⟩⟩
    rw [closure_Ioc hb.ne]
    exact ⟨le_rfl, hb.le⟩

def intervalPunctureCut (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 2 * Real.pi) :
    PeriodicBoxCut 0 (fun _ => 0) (fun _ => 2 * Real.pi) where
  count := 1
  lower := fun _ _ => a
  upper := fun _ _ => b
  ordered := fun _ _ => hab
  inside := by
    intro r x hx
    exact ⟨fun i => ha.le.trans (hx.1 i), fun i => (hx.2 i).trans hb.le⟩
  disjoint := fun r t h => False.elim (h (Subsingleton.elim r t))
  puncture := fun _ => true
  mate := Equiv.refl _
  puncture_mate := fun _ => rfl
  matched := by intro f h; contradiction
  puncture_boundary := by
    intro f _ x hx
    obtain ⟨y, _, rfl⟩ := hx
    have he : (Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 2 * Real.pi) \
        ⋃ _ : Fin 1, Icc (fun _ => a) (fun _ => b)) =
        circleCoordinate ⁻¹' (Icc 0 (2 * Real.pi) \ Icc a b) := by
      ext x
      simp only [Set.mem_sdiff, mem_iUnion, exists_const, mem_preimage, circleCoordinate_apply]
      exact and_congr (mem_constant_interval _ _ x) (not_congr (mem_constant_interval _ _ x))
    rw [he, ← circleCoordinate.preimage_frontier]
    simp only [mem_preimage, circleCoordinate_apply]
    have hi : f.2.1 = 0 := by omega
    change (@Fin.insertNth 0 (fun _ => ℝ) f.2.1
      (faceHeight (fun _ _ => a) (fun _ _ => b) f) y) 0 ∈ _
    rw [hi]
    simp only [Fin.insertNth_apply_same]
    cases h : f.2.2
    · simpa [faceHeight, h] using (interval_puncture_endpoints ha hab hb).1
    · simpa [faceHeight, h] using (interval_puncture_endpoints ha hab hb).2

theorem intervalPunctureCut_domain (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 2 * Real.pi) :
    (intervalPunctureCut a b ha hab hb).domain =
      {x : AngularSpace 0 | a ≤ x 0 ∧ x 0 ≤ b} := by
  ext x
  simp only [PeriodicBoxCut.domain, intervalPunctureCut, mem_iUnion, exists_const, mem_ofPred_eq]
  exact mem_constant_interval a b x

def seamRadius (k : ℕ) : ℝ := Real.pi / (k + 2)

theorem seamRadius_bounds (k : ℕ) : 0 < seamRadius k ∧ seamRadius k < Real.pi := by
  constructor
  · exact div_pos Real.pi_pos (by positivity)
  · unfold seamRadius
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < k + 2)]
    nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) k]

theorem seamRadius_antitone : Antitone seamRadius := by
  intro k l h
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 2)

theorem seamRadius_tendsto : Tendsto seamRadius atTop (𝓝 0) := by
  have h := (tendsto_add_atTop_iff_nat 2).2 (tendsto_const_div_atTop_nhds_zero_nat Real.pi)
  change Tendsto (fun k : ℕ => Real.pi / (k + 2)) atTop (𝓝 0)
  simpa using h

def seamCut (k : ℕ) : PeriodicBoxCut 0 (fun _ => 0) (fun _ => 2 * Real.pi) :=
  intervalPunctureCut (seamRadius k) (2 * Real.pi - seamRadius k)
    (seamRadius_bounds k).1 (by linarith [(seamRadius_bounds k).2])
    (by linarith [(seamRadius_bounds k).1])

theorem seamCut_domain (k : ℕ) : (seamCut k).domain =
    {x : AngularSpace 0 | seamRadius k ≤ x 0 ∧ x 0 ≤ 2 * Real.pi - seamRadius k} :=
  intervalPunctureCut_domain _ _ _ _ _

theorem seamCut_monotone : Monotone (fun k => (seamCut k).domain) := by
  intro k l h x hx
  dsimp only at hx ⊢
  rw [seamCut_domain] at hx ⊢
  exact ⟨(seamRadius_antitone h).trans hx.1, by linarith [hx.2, seamRadius_antitone h]⟩

theorem seamCut_covers : (⋃ k, (seamCut k).domain) =
    {x : AngularSpace 0 | 0 < x 0 ∧ x 0 < 2 * Real.pi} := by
  ext x
  simp only [mem_iUnion, seamCut_domain, mem_ofPred_eq]
  constructor
  · rintro ⟨k, h1, h2⟩
    exact ⟨lt_of_lt_of_le (seamRadius_bounds k).1 h1, by linarith [(seamRadius_bounds k).1]⟩
  · intro hx
    have h1 := seamRadius_tendsto.eventually_lt_const hx.1
    have h2 := seamRadius_tendsto.eventually_lt_const (sub_pos.mpr hx.2)
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    exact ⟨k, hk1.le, by linarith⟩

def puncturedCircle : PuncturedTorus 0 where
  lower := fun _ => 0
  upper := fun _ => 2 * Real.pi
  period := fun _ => by simp
  regular := {x | Real.sin (x 0 / 2) ≠ 0}
  regular_open := isOpen_ne_fun (Real.continuous_sin.comp ((continuous_apply 0).div_const 2)) continuous_const
  regular_periodic := by
    intro z x
    change Real.sin (x 0 / 2) ≠ 0 ↔ Real.sin ((x 0 + 2 * Real.pi * (z 0 : ℝ)) / 2) ≠ 0
    rw [show (x 0 + 2 * Real.pi * (z 0 : ℝ)) / 2 = x 0 / 2 + (z 0 : ℝ) * Real.pi by ring,
      Real.sin_add_int_mul_pi]
    simp [zpow_ne_zero]
  cut := seamCut
  monotone := seamCut_monotone
  covers := by
    rw [seamCut_covers]
    ext x
    rw [mem_inter_iff, mem_constant_interval]
    change (0 < x 0 ∧ x 0 < 2 * Real.pi) ↔
      (0 ≤ x 0 ∧ x 0 ≤ 2 * Real.pi) ∧ Real.sin (x 0 / 2) ≠ 0
    constructor
    · intro hx
      exact ⟨⟨hx.1.le, hx.2.le⟩,
        (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'⟩
    · rintro ⟨⟨hlo, hhi⟩, hn⟩
      constructor
      · apply lt_of_le_of_ne hlo
        intro he
        apply hn
        simp [← he]
      · apply lt_of_le_of_ne hhi
        intro he
        apply hn
        simp [he]

theorem puncturedCircle_domain : puncturedCircle.domain =
    {x : AngularSpace 0 | 0 < x 0 ∧ x 0 < 2 * Real.pi} := by
  rw [PuncturedTorus.domain, ← puncturedCircle.covers]
  exact seamCut_covers

end
end IsingBulk.Lie
