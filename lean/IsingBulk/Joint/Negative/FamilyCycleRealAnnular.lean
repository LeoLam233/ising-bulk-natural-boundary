import IsingBulk.Joint.Negative.FamilyCycleAnnularResidue
import IsingBulk.Anisotropic.NegativeCycles.RealAnnularIntegralBound

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles Set Filter MeasureTheory Metric
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1500000

theorem compact_family_real_annular_integral_bound (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hroot : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta))
    (hBn : ∀ eta∈Q, B (0,eta)≠0) (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃ρ M c : ℝ,0<ρ ∧ 1≤M ∧ 0<c ∧ ∀ eta∈Q, ∀m j : ℕ, ∀d : ℝ, |d|<ρ →
      ∀P : UniformProjectedWitness (familyMember B eta) phi hphi (2*m+1) (d:ℂ) r C,
      ∀_J : UniformCorrectionWitness (familyMember B eta) phi hphi (2*m+1) (d:ℂ) r C P R,
      ∀σ : ℝ,0<σ → ∀S : Set (Fin (2*m)→ℝ), MeasurableSet S →
      (∀q∈S,σ≤constrainedSquaredRadius q ∧ constrainedSquaredRadius q≤ρ^2) →
      ∀χ : (Fin (2*m)→ℝ)→ℂ,(∀q∈S,‖χ q‖≤1) →
      ‖∫q in S,χ q*constrainedResidueDensity (familyMember B eta) (familyMember rootB eta) phi hphi (d:ℂ) P.T j (complexify (2*m) q)‖≤
        ((2*((M*M^m)*M^(2*m+1)*(1/2:ℝ)^((2*m+1).choose 2))/(c*(2*m+1:ℕ)))*
          ((8*(2*m+1:ℕ):ℝ)/σ)^(j+1))*(2*ρ)^(2*m) := by
  obtain ⟨ρ,M,c,hρ,hM,hc,hres⟩ := compact_family_homotopy_residue_bound B rootB phi hphi hQ hB hroot hBn r C R hr hR hRr
  refine ⟨ρ,M,c,hρ,hM,hc,?_⟩
  intro eta heta m j d hd P J σ hσ S hS hSQ χ hχ
  let B := familyMember B eta
  let rootB := familyMember rootB eta
  let F := (2*((M*M^m)*M^(2*m+1)*(1/2:ℝ)^((2*m+1).choose 2))/(c*(2*m+1:ℕ)))*
    ((8*(2*m+1:ℕ):ℝ)/σ)^(j+1)
  have hF : 0≤F := by dsimp [F]; positivity
  let cube := Icc (fun _ : Fin (2*m) => -ρ) (fun _ => ρ)
  have hsub : S⊆cube := by
    intro q hq
    have hh := (constrainedSquaredRadius_coordinates_le q hρ.le (hSQ q hq).2).1
    constructor
    · intro i; exact (abs_le.mp (hh i)).1
    · intro i; exact (abs_le.mp (hh i)).2
  have hcube : volume cube<⊤ := isCompact_Icc.measure_lt_top
  have hfin : volume S<⊤ := (measure_mono hsub).trans_lt hcube
  let _ : IsFiniteMeasure (volume.restrict S) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hbound : ∀q∈S,‖χ q*constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j (complexify (2*m) q)‖≤F := by
    intro q hq
    have hy := norm_shapeExtend_complexify_le q hρ.le (hSQ q hq).2
    have hh := hres eta heta m j d hd P J (shapeExtend q)
      (by simpa only [←shapeExtend_complexify] using hy) (sum_shapeExtend q)
      σ hσ (hSQ q hq).1 0 (by constructor <;> norm_num)
    simp only [correctedHomotopy,Complex.ofReal_zero,zero_smul,add_zero,←shapeExtend_complexify] at hh
    have hf : ‖constrainedResidueDensity B rootB phi hphi (d:ℂ) P.T j (complexify (2*m) q)‖≤F := by
      simpa only [constrainedResidueDensity,freeChartCLM_eq_shapeExtend] using hh
    rw [norm_mul]
    exact (mul_le_mul (hχ q hq) hf (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul _)
  have hi := norm_integral_le_of_norm_le_const (μ := volume.restrict S)
    ((ae_restrict_mem hS).mono hbound)
  have hvol : (volume cube).toReal=(2*ρ)^(2*m) := by
    rw [Real.volume_Icc_pi_toReal (show (fun _ : Fin (2*m) => -ρ)≤(fun _ => ρ) by intro _; linarith)]
    simp [sub_neg_eq_add,two_mul]
  have hm := ENNReal.toReal_mono hcube.ne (measure_mono hsub)
  rw [hvol] at hm
  apply le_trans _ (mul_le_mul_of_nonneg_left hm hF)
  simpa only [Measure.real,Measure.restrict_apply_univ] using hi


end
end IsingBulk.Joint.Negative
