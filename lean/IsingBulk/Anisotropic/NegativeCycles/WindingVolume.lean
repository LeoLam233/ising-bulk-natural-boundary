import IsingBulk.Anisotropic.NegativeCycles.WindingCompact
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators

theorem winding_energy_sublevel_subset_box (n : ℕ) (k : Fin (n+2))
    {σ R : ℝ} (hR : 0≤R) (hσ : σ≤R^2) :
    {v : Fin n→ℝ | (∑i,(windingAffine n k v i)^2)≤σ}⊆Icc (fun _ => -R) (fun _ => R) := by
  intro v hv
  have hi (i : Fin n) : (v i)^2≤R^2 := by
    have hh := Finset.single_le_sum
      (fun j (_ : j∈(Finset.univ : Finset (Fin (n+1)))) => sq_nonneg (windingAffine n k v j))
      (Finset.mem_univ i.castSucc)
    simpa only [windingAffine,Fin.snoc_castSucc] using hh.trans (hv.trans hσ)
  constructor <;> intro i <;> nlinarith [hi i]

theorem winding_energy_sublevel_volume (n : ℕ) (k : Fin (n+2))
    {σ R : ℝ} (hR : 0≤R) (hσ : σ≤R^2) :
    (volume {v : Fin n→ℝ | (∑i,(windingAffine n k v i)^2)≤σ}).toReal≤(2*R)^n := by
  have hm := measureReal_mono (μ := volume)
    (winding_energy_sublevel_subset_box n k hR hσ) isCompact_Icc.measure_lt_top.ne
  have hb : (volume (Icc (fun _ : Fin n => -R) (fun _ => R))).toReal=(2*R)^n := by
    rw [Real.volume_Icc_pi_toReal (by intro i; linarith)]
    simp only [sub_neg_eq_add,←two_mul,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simpa only [measureReal_def,hb] using hm

end
end IsingBulk.Anisotropic.NegativeCycles
