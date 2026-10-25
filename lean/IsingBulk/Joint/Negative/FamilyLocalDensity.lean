import IsingBulk.Joint.Negative.FamilyScalar
import IsingBulk.Joint.Negative.LocalDensity

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.First IsingBulk.Tail
open IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.RegularEdges
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- One root-identity bidisk for every member of a compact complex family. -/
theorem compact_family_negativePhase_root (B : ℂ × E → ℂ) {phi : ℝ}
    (hp : 0<phi) (hpi : phi<Real.pi) (hphi : Real.sin phi≠0)
    {Q : Set E} (hQ : IsCompact Q) (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) :
    ∃r : ℝ, 0<r ∧ ∀ eta∈Q, ∀ t delta : ℂ, ‖t‖<r → ‖delta‖<r →
      continuedRoot (negativeDispersion (familyMember B eta) (Real.cos phi) t delta)=
        Complex.exp (-negativePhase (familyMember B eta) phi hphi t delta) := by
  let W : (ℂ × ℂ) × E → ℂ := fun q =>
    (Real.cos phi:ℂ)+B (q.1.1,q.2)*(q.1.1-1+Complex.cos q.1.2)
  let G : Set ((ℂ × ℂ) × E) := {q | continuedRoot (W q)=
    Complex.exp (-edgePhase phi hphi (W q))}
  have hcenter (eta : E) (heta : eta∈Q) : ((0,0),eta)∈interior G := by
    apply mem_interior_iff_mem_nhds.mpr
    have hw : AnalyticAt ℂ W ((0,0),eta) := by
      exact analyticAt_const.add (((hB eta heta).comp
        (f:=fun q : (ℂ × ℂ) × E => (q.1.1,q.2))
        ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd)).mul
        (((analyticAt_fst.comp analyticAt_fst).sub analyticAt_const).add
          (Complex.analyticAt_cos.comp (analyticAt_snd.comp analyticAt_fst))))
    have ht : Tendsto W (𝓝 ((0,0),eta)) (𝓝 (Real.cos phi:ℂ)) := by
      simpa [ContinuousAt,W] using hw.continuousAt
    exact ht.eventually (continuedRoot_eq_exp_edgePhase_eventually hp hpi hphi)
  obtain ⟨r,hr,hball⟩ := compact_product_tube (X:=ℂ × ℂ) hQ isOpen_interior hcenter
  refine ⟨r,hr,?_⟩
  intro eta heta t delta ht hd
  have hg : ((t,delta),eta)∈G := interior_subset
    (hball eta heta (t,delta) (by simpa only [Prod.norm_def,max_lt_iff] using And.intro ht hd))
  exact hg

/-- The actual root/pole-density bridge, on one local disk chosen before m. -/
theorem compact_family_local_scaled_physical_density (B : ℂ × E → ℂ) {phi : ℝ}
    (hp : 0 < phi) (hpi : phi < Real.pi) (hphi : Real.sin phi ≠ 0)
    {Q : Set E} (hQ : IsCompact Q)
    (hBa : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) :
    ∃ r : ℝ, 0 < r ∧ ∀ eta∈Q, ∀ m : ℕ, ∀ d t : ℂ, ∀ v : Config (2*m+1),
      ∀ K : Coupling, ∀ a : ℂ, ∀ rootB : ℂ → ℂ,
      ‖t‖ < r → (∀ i, ‖d+v i‖ < r) → S K ≠ 0 →
      (familyMember B eta) t = transferB K →
      transferC K + transferB K = (Real.cos phi : ℂ) + (familyMember B eta) t*t →
      a^2 = p K → a / S K = rootB t →
      Complex.exp (((2*m+1 : ℕ) : ℂ) * ((phi : ℂ) * Complex.I)) = 1 →
      a^(2*m+1) / (((2*m+1).factorial : ℂ) * (2*(Real.pi : ℂ))^(2*m)) *
        continuedAngularDensity K (fun i => (Real.pi : ℂ)+d+v i) =
          formFactorNumerator (familyMember B eta) rootB phi hphi d t v *
            cothHalf (fun u => poleEquation (familyMember B eta) phi hphi d u v) t := by
  obtain ⟨r, hr, hroot⟩ := compact_family_negativePhase_root B hp hpi hphi hQ hBa
  refine ⟨r, hr, ?_⟩
  intro eta heta m d t v K a rootB ht hv hS hB he ha har hres
  have hR : rootB t ^ 2 = (familyMember B eta) t := by
    rw [← har, div_pow, ha, hB]
    unfold p transferB
    field_simp [hS]
  apply scaled_continuedAngularDensity_eq_phase m (familyMember B eta) rootB phi hphi d t v hB har hR _ hres
  intro i
  rw [show (Real.pi : ℂ)+d+v i = (Real.pi : ℂ)+(d+v i) by ring,
    continuedTransferRoot_eq_negativeDispersion (familyMember B eta) hB he]
  exact hroot eta heta t (d+v i) ht (hv i)


end
end IsingBulk.Joint.Negative
