import IsingBulk.Joint.Negative.FamilyCorrectionInverse
import IsingBulk.Anisotropic.NegativeCycles.WindingWitnessFactory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open Set IsingBulk.Anisotropic.NegativeCycles
namespace IsingBulk.Joint.Negative
open IsingBulk.Anisotropic.NegativeNormalForm

/-- Actual projected/corrected witnesses for every active winding sector, constructed
before the Taylor order and without importing the central cap's separate factory. -/
theorem compact_family_winding_witness_factory (B : ℂ × E→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hB0 : ∀eta∈Q,B (0,eta)≠0) :
    ∃R r C : ℝ,0<R ∧ 0<r ∧ 0<C ∧ 4*R≤r ∧
      ∀eta∈Q,∀m : ℕ,∀s : ℝ,s≤R^2 →
      ∃P : (k : Fin (2*m+2)) → (2*m+1:ℕ)*(windingMean (2*m) k)^2<s →
        UniformProjectedWitness (familyMember B eta) phi hphi (2*m+1) (windingMean (2*m) k:ℂ) r C,
      Nonempty ((k : Fin (2*m+2)) → (hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s) →
        UniformCorrectionWitness (familyMember B eta) phi hphi (2*m+1) (windingMean (2*m) k:ℂ) r C (P k hk) R) := by
  obtain ⟨R,r,C,hR,hr,hC,hRr,hfactory⟩ := compact_family_correction_witness B phi hphi hQ hB hB0
  refine ⟨R,r,C,hR,hr,hC,hRr,?_⟩
  intro eta heta m s hs
  have hh (k : Fin (2*m+2)) (hk : (2*m+1:ℕ)*(windingMean (2*m) k)^2<s) :=
    hfactory eta heta (2*m+1) (by omega) (windingMean (2*m) k:ℂ)
      (by simpa only [Complex.norm_real,Real.norm_eq_abs] using active_windingMean_lt m k hR hs hk)
  choose P hP using hh
  exact ⟨P,⟨fun k hk=>Classical.choice (hP k hk)⟩⟩

end IsingBulk.Joint.Negative
