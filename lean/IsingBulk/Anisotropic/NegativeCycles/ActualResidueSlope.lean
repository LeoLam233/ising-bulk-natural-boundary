import IsingBulk.Anisotropic.NegativeCycles.PhysicalPoleSubtraction
import IsingBulk.Anisotropic.NegativeNormalForm.PoleNewton

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm
open scoped BigOperators

/-- Actual residue denominators grow linearly with N on one common neighborhood. -/
theorem poleParameterDerivative_uniform_lower (B : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0) :
    ∃r c : ℝ,0<r ∧ 0<c ∧ ∀N : ℕ, N≠0 → ∀d t : ℂ, ∀v : Config N,
      ‖t‖<r → (∀i, ‖d+v i‖<r) →
      c*N≤‖poleParameterDerivative B phi hphi d t v‖ := by
  obtain ⟨r,hr,hs⟩ := negativePhase_uniform_slope B phi hphi hB hB0
  let c0 := centralParameterSlope B phi 0
  have hc0 : c0≠0 := centralParameterSlope_ne_zero B phi hphi 0 (by simpa using hB0)
  refine ⟨r,‖c0‖/2,hr,div_pos (norm_pos_iff.mpr hc0) (by norm_num),?_⟩
  intro N hN d t v ht hv
  have ha i := (hs t (d+v i) ht (hv i)).1
  have hb i := (hs t (d+v i) ht (hv i)).2
  let a := mean (fun i => phaseParameterSlope B phi hphi (t,d+v i))
  have he : ‖a-c0‖≤‖c0‖/4 := norm_mean_sub_le hN _ c0 (by positivity) hb
  have hal : ‖c0‖/2≤‖a‖ := by
    have h := norm_sub_norm_le c0 a
    rw [norm_sub_rev] at h
    change ‖c0‖-‖a‖≤‖a-c0‖ at h
    linarith [norm_nonneg c0]
  have hn : (N:ℂ)≠0 := by exact_mod_cast hN
  have hh := (poleAverage_hasDerivAt B phi hphi d t v ha).mul_const (N:ℂ)
  have hfun : (fun u => poleAverage B phi hphi d u v*(N:ℂ))=
      (fun u => poleEquation B phi hphi d u v) := by
    funext u
    exact div_mul_cancel₀ _ hn
  rw [hfun] at hh
  unfold poleParameterDerivative
  rw [hh.deriv,norm_mul,Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right hal (Nat.cast_nonneg N)

end IsingBulk.Anisotropic.NegativeCycles
