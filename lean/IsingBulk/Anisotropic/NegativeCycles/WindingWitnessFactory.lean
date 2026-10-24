import IsingBulk.Anisotropic.NegativeCycles.WindingArithmetic
import IsingBulk.Anisotropic.NegativeNormalForm.UniformCorrectionInverse

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm

/-- Actual projected/corrected witnesses for every active winding sector, constructed
before the Taylor order and without importing the central cap's separate factory. -/
theorem exists_winding_witness_factory (B : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0) :
    ∃R r C : ℝ,0<R ∧ 0<r ∧ 0<C ∧ 4*R≤r ∧
      ∀m : ℕ,∀s : ℝ,s≤R^2 →
      ∃P : (k : Fin (2*m+2)) → (2*m+1:ℕ)*(windingMean (2*m) k)^2<s →
        UniformProjectedWitness B phi hphi (2*m+1) (windingMean (2*m) k:ℂ) r C,
      Nonempty ((k : Fin (2*m+2)) → (hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s) →
        UniformCorrectionWitness B phi hphi (2*m+1) (windingMean (2*m) k:ℂ) r C (P k hk) R) := by
  obtain ⟨R,r,C,hR,hr,hC,hRr,hfactory⟩ := exists_uniform_correction_witness B phi hphi hB hB0
  refine ⟨R,r,C,hR,hr,hC,hRr,?_⟩
  intro m s hs
  have hh (k : Fin (2*m+2)) (hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s) :=
    hfactory (2*m+1) (by omega) (windingMean (2*m) k:ℂ)
      (by simpa only [Complex.norm_real,Real.norm_eq_abs] using active_windingMean_lt m k hR hs hk)
  choose P hP using hh
  exact ⟨P,⟨fun k hk=>Classical.choice (hP k hk)⟩⟩

end IsingBulk.Anisotropic.NegativeCycles
