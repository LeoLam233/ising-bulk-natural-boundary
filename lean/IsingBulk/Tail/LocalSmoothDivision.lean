import IsingBulk.Tail.CompactSmoothDivision
import IsingBulk.Tail.CompactSupportLie
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace IsingBulk.Tail
noncomputable section
open Set Filter Function
open scoped Topology ContDiff
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Real-smooth Hadamard division on an arbitrary open source neighborhood.
Only a local germ is claimed; no uniform derivative bound is extracted. -/
theorem smooth_hadamard_division_near (D : (ℝ × ℝ) × P → ℂ)
    {U : Set ((ℝ × ℝ) × P)} (hU : IsOpen U)
    (hD : ∀ z ∈ U, ContDiffAt ℝ ∞ D z)
    (hdiag : ∀ y p, ((y,y),p) ∈ U → D ((y,y),p)=0)
    {z : (ℝ × ℝ) × P} (hz : z ∈ U) :
    ∃ C : (ℝ × ℝ) × P → ℂ, ContDiffAt ℝ ∞ C z ∧
      ∀ᶠ v in 𝓝 z, D v = (v.1.1-v.1.2 : ℝ) • C v := by
  obtain ⟨w,hwU,hwcompact,hw,hw01,hwz⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hU.mem_nhds hz)
  let F : (ℝ × ℝ) × P → ℂ := fun v => (w v:ℂ)*D v
  have hF : ContDiff ℝ ∞ F :=
    weighted_contDiff_of_tsupport w D hw (fun v hv => hD v (hwU hv))
  have hFdiag : ∀ y p, F ((y,y),p)=0 := by
    intro y p
    by_cases hw0 : w ((y,y),p)=0
    · simp [F,hw0]
    · have hmem : ((y,y),p) ∈ U := hwU (subset_tsupport w hw0)
      simp [F,hdiag y p hmem]
  obtain ⟨C0,hC0,hCF⟩ := smooth_hadamard_division F hF hFdiag
  let C : (ℝ × ℝ) × P → ℂ := fun v => C0 v/(w v:ℂ)
  have hwc : ContDiff ℝ ∞ (fun v => (w v:ℂ)) := Complex.ofRealCLM.contDiff.comp hw
  have hwzne : (w z:ℂ) ≠ 0 := by simp [hwz]
  have hC : ContDiffAt ℝ ∞ C z := by
    simpa [C,div_eq_mul_inv] using hC0.contDiffAt.mul (hwc.contDiffAt.inv hwzne)
  refine ⟨C,hC,?_⟩
  have hne : ∀ᶠ v in 𝓝 z, (w v:ℂ) ≠ 0 := hwc.continuous.continuousAt.eventually_ne hwzne
  filter_upwards [hne] with v hv
  have he := hCF v
  dsimp [F] at he
  dsimp [C]
  apply (mul_left_cancel₀ hv)
  calc
    _ = ((v.1.1-v.1.2:ℝ):ℂ)*C0 v := he
    _ = _ := by field_simp

end
end IsingBulk.Tail
