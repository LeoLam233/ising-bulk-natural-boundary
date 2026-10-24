import IsingBulk.Anisotropic.NegativeCycles.ActualPoleComparison
import IsingBulk.Anisotropic.NegativeCycles.AnnularPoleSector
import IsingBulk.Anisotropic.NegativeNormalForm.UniformNearIdentity

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm Set
open scoped BigOperators

def correctedHomotopy {n : ℕ} {B : ℂ→ℂ} {phi : ℝ} {hphi : Real.sin phi≠0}
    {d : ℂ} {r C R : ℝ} (P : UniformProjectedWitness B phi hphi n d r C)
    (J : UniformCorrectionWitness B phi hphi n d r C P R) (s : ℝ) (y : Config n) : Config n :=
  y+(s:ℂ) • (P.V (J.W y)-y)

/-- A genuine positive sector for the actual pole on the entire corrected-map homotopy.
The radius is chosen before the particle dimension and before the winding sector. -/
theorem actualHomotopy_pole_uniform_sector (B : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0)
    (r C R : ℝ) (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    ∃δ : ℝ,0<δ ∧ δ≤R/2 ∧ ∀n : ℕ, n≠0 → ∀d : ℝ, ‖(d:ℂ)‖<δ →
      ∀P : UniformProjectedWitness B phi hphi n (d:ℂ) r C,
      ∀J : UniformCorrectionWitness B phi hphi n (d:ℂ) r C P R,
      ∀v : Fin n→ℝ, ‖fun i => (v i:ℂ)‖≤δ → (∑i,v i)=0 →
      ∀s : ℝ,s∈Icc (-1/2:ℝ) (3/2) →
        1-Real.cos d+(∑i,v i^2)/(8*n)≤
          (P.T (correctedHomotopy P J s (fun i => (v i:ℂ)))).re := by
  obtain ⟨a,ha,_har,hcmp⟩ := actualPole_quadratic_comparison_uniform B phi hphi hB hBn r C hr
  let δ := min (a/4) (R/4)
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  have hδa : δ≤a/4 := min_le_left _ _
  have hδR : δ≤R/4 := min_le_right _ _
  refine ⟨δ,hδ,by linarith,?_⟩
  intro n hn d hd P J v hv hm s hs
  let y : Config n := fun i => (v i:ℂ)
  have hy : ‖y‖≤R/2 := by dsimp only [y]; linarith
  have hmy : ZeroMean y := by
    change (∑i,(v i:ℂ))=0
    exact_mod_cast hm
  have hw := J.w_inverse y hy
  have hmw := hw.2.2.2 hmy
  have hpv := P.v_inverse (J.W y) (hw.1.trans hRr)
  have hmv := (hpv.2.2.2 hmw).1
  have he := (J.corrected_energy_bounds hn B phi hphi (d:ℂ) r C R P hRr y hy hmy).2
  have hsup := ((J.corrected_bounds B phi hphi (d:ℂ) r C R P hr hR hRr).2 y hy).2
  have hsn : ‖(s:ℂ)‖≤3/2 := by
    simp only [Complex.norm_real,Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith [hs.1,hs.2]
  have hH : ‖correctedHomotopy P J s y‖<a := by
    have hadd := norm_add_le y ((s:ℂ) • (P.V (J.W y)-y))
    rw [norm_smul] at hadd
    have hmul := mul_le_mul hsn hsup (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)
    change ‖correctedHomotopy P J s y‖≤_ at hadd
    change ‖y‖≤δ at hv
    nlinarith [norm_nonneg y]
  have hmH : ZeroMean (correctedHomotopy P J s y) := by
    simp only [correctedHomotopy,ZeroMean,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      Pi.sub_apply,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum]
    rw [hmy,hmv]
    ring
  apply straightConfig_pole_re_lower hn v (P.V (J.W y)-y) s d _ hs
  · simpa only [y,absoluteEnergy_real] using he
  · exact hcmp n hn (d:ℂ) (by linarith) P (correctedHomotopy P J s y) hH hmH

end IsingBulk.Anisotropic.NegativeCycles
