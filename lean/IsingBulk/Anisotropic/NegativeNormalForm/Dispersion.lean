import IsingBulk.Anisotropic.NegativeNormalForm.PhaseBranch
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The genuine negative-edge dispersion and its physical local phase.
This isolates the analytic scalar function used in the all-particle construction. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

/-- The local inverse-cosh branch at the prescribed physical phase. -/
def edgePhase (phi : ℝ) (hphi : Real.sin phi ≠ 0) : ℂ → ℂ :=
  Classical.choose (exists_edge_phase phi hphi)

theorem edgePhase_spec (phi : ℝ) (hphi : Real.sin phi ≠ 0) :
    AnalyticAt ℂ (edgePhase phi hphi) (Real.cos phi : ℂ) ∧
      edgePhase phi hphi (Real.cos phi : ℂ) = (phi : ℂ) * Complex.I ∧
      (∀ᶠ w in nhds (Real.cos phi : ℂ), Complex.cosh (edgePhase phi hphi w) = w) ∧
      HasDerivAt (edgePhase phi hphi) ((Real.sin phi : ℂ) * Complex.I)⁻¹
        (Real.cos phi : ℂ) :=
  Classical.choose_spec (exists_edge_phase phi hphi)

/-- Equation (4.1), with the varying anisotropy ratio retained. -/
def negativeDispersion (B : ℂ → ℂ) (b t delta : ℂ) : ℂ :=
  b + B t * (t - 1 + Complex.cos delta)

/-- Equation (4.3), defined via the actual local inverse theorem. -/
def negativePhase (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0)
    (t delta : ℂ) : ℂ :=
  edgePhase phi hphi (negativeDispersion B (Real.cos phi) t delta)

theorem negativeDispersion_even (B : ℂ → ℂ) (b t delta : ℂ) :
    negativeDispersion B b t (-delta) = negativeDispersion B b t delta := by
  simp [negativeDispersion]

theorem negativePhase_even (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0)
    (t delta : ℂ) :
    negativePhase B phi hphi t (-delta) = negativePhase B phi hphi t delta := by
  simp [negativePhase, negativeDispersion_even]

theorem negativeDispersion_center (B : ℂ → ℂ) (b d : ℂ) :
    negativeDispersion B b (1 - Complex.cos d) d = b := by
  simp [negativeDispersion]

theorem negativePhase_center (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0)
    (d : ℂ) :
    negativePhase B phi hphi (1 - Complex.cos d) d = (phi : ℂ) * Complex.I := by
  rw [negativePhase, negativeDispersion_center]
  exact (edgePhase_spec phi hphi).2.1

/-- No derivative of B survives at the resonant centre. -/
theorem negativeDispersion_hasDerivAt_center (B : ℂ → ℂ) (b d B' : ℂ)
    (hB : HasDerivAt B B' (1 - Complex.cos d)) :
    HasDerivAt (fun t => negativeDispersion B b t d)
      (B (1 - Complex.cos d)) (1 - Complex.cos d) := by
  have hid := ((hasDerivAt_id (1 - Complex.cos d)).sub_const 1).add_const (Complex.cos d)
  convert! (hB.mul hid).const_add b using 1
  simp

/-- The true one-body t derivative at every resonant centre. -/
theorem negativePhase_hasDerivAt_center (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d B' : ℂ)
    (hB : HasDerivAt B B' (1 - Complex.cos d)) :
    HasDerivAt (fun t => negativePhase B phi hphi t d)
      (((Real.sin phi : ℂ) * Complex.I)⁻¹ * B (1 - Complex.cos d))
      (1 - Complex.cos d) := by
  have hg := (edgePhase_spec phi hphi).2.2.2
  have hw := negativeDispersion_hasDerivAt_center B (Real.cos phi) d B' hB
  rw [← negativeDispersion_center B (Real.cos phi) d] at hg
  exact hg.comp (1 - Complex.cos d) hw

/-- Joint holomorphy of the genuine two-variable phase at each resonant centre.
This uses the scalar inverse constructed above, not a branch assumption. -/
theorem negativePhase_analyticAt_center (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1 - Complex.cos d)) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2)
      (1 - Complex.cos d, d) := by
  have hW : AnalyticAt ℂ (fun z : ℂ × ℂ => negativeDispersion B (Real.cos phi) z.1 z.2)
      (1 - Complex.cos d, d) := by
    exact analyticAt_const.add ((hB.comp (f := fun z : ℂ × ℂ => z.1) analyticAt_fst).mul
      ((analyticAt_fst.sub analyticAt_const).add (Complex.analyticAt_cos.comp (f := fun z : ℂ × ℂ => z.2) analyticAt_snd)))
  have hg := (edgePhase_spec phi hphi).1
  rw [← negativeDispersion_center B (Real.cos phi) d] at hg
  exact hg.comp (f := fun z : ℂ × ℂ => negativeDispersion B (Real.cos phi) z.1 z.2) hW

/-- Angular derivative of the actual dispersion, with B held at the local t. -/
theorem negativeDispersion_hasDerivAt_delta (B : ℂ → ℂ) (b t delta : ℂ) :
    HasDerivAt (negativeDispersion B b t) (-B t * Complex.sin delta) delta := by
  convert! (((Complex.hasDerivAt_cos delta).const_add (t-1)).const_mul (B t)).const_add b
    using 1
  ring

/-- Angular derivative of the physical phase at the central configuration. -/
theorem negativePhase_hasDerivAt_delta_center (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) :
    HasDerivAt (negativePhase B phi hphi (1 - Complex.cos d))
      (((Real.sin phi : ℂ) * Complex.I)⁻¹ * (-B (1 - Complex.cos d) * Complex.sin d)) d := by
  have hg := (edgePhase_spec phi hphi).2.2.2
  rw [← negativeDispersion_center B (Real.cos phi) d] at hg
  exact hg.comp d (negativeDispersion_hasDerivAt_delta B (Real.cos phi) (1 - Complex.cos d) d)

/-- A single jointly holomorphic bidisk is constructed before any particle
number is chosen. This is the common scalar analytic input to Lemma 4.1. -/
theorem negativePhase_fixed_bidisk (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (hB : AnalyticAt ℂ B 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ t delta : ℂ, ‖t‖ < r → ‖delta‖ < r →
      AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2) (t, delta) := by
  have ha := negativePhase_analyticAt_center B phi hphi 0 (by simpa using hB)
  simp only [Complex.cos_zero, sub_self] at ha
  obtain ⟨r, hr, hball⟩ := ha.exists_ball_analyticOnNhd
  refine ⟨r, hr, fun t delta ht hd => hball (t, delta) ?_⟩
  change dist (t, delta) (0 : ℂ × ℂ) < r
  simpa only [dist_zero_right, Prod.norm_def, max_lt_iff] using And.intro ht hd

end
end IsingBulk.Anisotropic.NegativeNormalForm
