import IsingBulk.HT.Lie.SignedJets
import IsingBulk.HT.Lie.CollisionWeights
import IsingBulk.Tail.AllBranchExteriorCollisionPower
import IsingBulk.Analysis.JetsFieldBounds

/-!
Literal normal-flux descendants of the signed Lie source. Multiplication
by the actual time-dependent selected field adds one selected pole and
no numerator or cutoff derivative. The source's two-j filtration therefore
becomes exactly two-j-plus-one, before any surface integration.
-/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.Jets IsingBulk.Lie IsingBulk.Tail IsingBulk.Branch

/-- The actual additional field factor, with its one pole left explicit. -/
def fieldFluxTerm {N : ℕ} (T : SourceJetTerm N) (p q i : Fin N) : SourceJetTerm N :=
  {T with pole := T.pole+1
          regularPart := fun z => fieldRegularNumerator p q i z.1 z.2*T.regularPart z}

theorem fieldFluxTerm_filtration {N j : ℕ} (p q i : Fin N) (T : SourceJetTerm N)
    (hT : T ∈ sourceJetTerms p q j) :
    (fieldFluxTerm T p q i).pole+(fieldFluxTerm T p q i).cutoff.length+
      (spatialWord (fieldFluxTerm T p q i).numerator).length ≤ 2*j+1 := by
  have h := (sourceJetTerms_valid p q j T hT).1
  dsimp [fieldFluxTerm]
  omega

/-- This is an identity of actual functions on the chart, not only a
pole descriptor. The signed kernel remains simple. -/
theorem signedSourceValue_fieldFluxTerm {n : ℕ} (σ : ℂ)
    (T : SourceJetTerm (n+1)) (p q i : Fin (n+1)) (v θ : ℝ)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (s : ℂ) (u : AngularSpace n) (h : ActualJetPoint v θ p q s u) :
    signedSourceValue σ (fieldFluxTerm T p q i) p q v θ w Q s u =
      actualField v θ p q s u i*signedSourceValue σ T p q v θ w Q s u := by
  have hf : actualField v θ p q s u i =
      fieldRegularNumerator p q i s (chartMap v θ s u)/
        (chartMap v θ s u q-chartMap v θ s u p) := by
    rw [← regularSelectedField_chart p q v θ s u h.g_pos]
    exact field_one_pole p q i s (chartMap v θ s u)
      (h.sin_ne p) (h.sin_ne q) h.delta_ne h.coefficient.gsum_ne h.coefficient.den_ne
  rw [hf]
  unfold signedSourceValue chartPullback SourceJetTerm.coefficient fieldFluxTerm chartMap
  simp only [pow_succ,div_eq_mul_inv,mul_inv_rev]
  simp only [selectedDifferenceCLM,ContinuousLinearMap.comp_apply,
    sub_apply,ContinuousLinearMap.proj_apply,ContinuousLinearMap.coe_snd']
  ring

/-- Actual regular field-numerator jets are multiplied into the same
coefficient. No inverse of a pair or Vandermonde factor is introduced. -/
theorem fieldFluxTerm_regular_bound {N r : ℕ} (T : SourceJetTerm N)
    (p q i : Fin N) (z : ℂ × (Fin N → ℂ)) {C D : ℝ}
    (hscalar : ScalarBounds p q z r C) (hN : 1 ≤ N)
    (hT : JetBound T.regularPart z r D) :
    JetBound (fieldFluxTerm T p q i).regularPart z r
      (2^r*(3*2^r*C^2*N)*D) :=
  (hscalar.field hN i).mul hT

/-- The actual rational weight also absorbs the additional flux pole.
All constants precede particle number and all earlier Lie stages. -/
theorem rational_weight_absorbs_flux_terms (d : LocalBranchData)
    (M k : ℕ) (hM : 2*k+2 < M) :
    ∃ C : ℕ, 0 < C ∧ ∃ c r : ℝ, 0 < c ∧ 0 < r ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ N : ℕ, 1 ≤ N →
      ∀ p q : Fin N, ∀ u : Fin N → ℝ, (∀ i, |u i| ≤ r) → u p ≠ u q →
      ∀ j : ℕ, j ≤ k → ∀ T ∈ sourceJetTerms p q j,
      ‖cutoffJet T.cutoff (allBranchExteriorPairWeight M p q) u‖ /
        ‖originalPhase d ε (u p)-originalPhase d ε (u q)‖^(T.pole+1) ≤
      ((C:ℝ)*(N:ℝ)^C)*(c⁻¹)^(T.pole+1)/
        (allBranchExteriorDiameter u)^(T.cutoff.length+T.pole+1) := by
  obtain ⟨C,hC,c,r,hc,hr,h⟩ :=
    allBranchExterior_actual_pole_absorption d M k (by omega) (by omega)
  refine ⟨C,hC,c,r,hc,hr,?_⟩
  intro ε hε hεr N hN p q u hu hpq j hj T hT
  have hvalid := sourceJetTerms_valid p q j T hT
  have hh := h ε hε hεr N hN p q u hu hpq T.cutoff (by omega)
    (T.pole+1) (by omega)
  simpa only [Nat.add_assoc] using hh

/-- Signed source norm, keeping the contour Jacobian and the actual global
kernel in place. The only pointwise inputs bound the three regular pieces. -/
theorem signedSourceValue_norm {n : ℕ} (σ : ℂ) (T : SourceJetTerm (n+1))
    (p q : Fin (n+1)) (v θ : ℝ) (w : AngularSpace n → ℝ)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ) (u : AngularSpace n)
    (W A B : ℝ) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (hw : ‖cutoffJet T.cutoff w u‖/
      ‖selectedDifferenceCLM p q (s,chartMap v θ s u)‖^T.pole ≤ W)
    (hreg : ‖T.regularPart (s,chartMap v θ s u)‖ ≤ A)
    (hnum : ‖numeratorJet T.numerator Q (s,chartMap v θ s u)‖ ≤ B) :
    ‖signedSourceValue σ T p q v θ w Q s u‖ ≤
      W*A*B*‖chartJacobian v θ s u‖/‖signedRegularKernel σ s (chartMap v θ s u)‖ := by
  unfold signedSourceValue chartPullback SourceJetTerm.coefficient
  simp only [norm_mul,norm_div,norm_pow,Complex.norm_real]
  calc
    _ = ((‖cutoffJet T.cutoff w u‖/‖selectedDifferenceCLM p q (s,chartMap v θ s u)‖^T.pole)*
      ‖T.regularPart (s,chartMap v θ s u)‖*
      ‖numeratorJet T.numerator Q (s,chartMap v θ s u)‖)*
      ‖chartJacobian v θ s u‖/‖signedRegularKernel σ s (chartMap v θ s u)‖ := by
        unfold chartMap
        ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul (mul_le_mul hw hreg (norm_nonneg _) hW) hnum
        (norm_nonneg _) (mul_nonneg hW hA)

/-- The exact loss budget, including an arbitrary already-counted extra
field pole. This is the LT collision algebra without an even budget ceiling. -/
theorem collision_power_budget (m l s P L : ℕ)
    (horder : m+l+s ≤ L) (hP : L ≤ P) (d H W A B : ℝ)
    (hd : 0 < d) (hd1 : d ≤ 1) (hH : 1 ≤ H)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (W/d^(m+l))*A*(B*(H*d)^(P-s)) ≤ W*A*B*H^P*d^(P-L) := by
  have he : P-s=(P-(m+l+s))+(m+l) := by omega
  have hden : d^(m+l) ≠ 0 := pow_ne_zero _ hd.ne'
  have hid : (W/d^(m+l))*A*(B*(H*d)^(P-s)) =
      W*A*B*H^(P-s)*d^(P-(m+l+s)) := by
    rw [mul_pow,show d^(P-s)=d^(P-(m+l+s))*d^(m+l) by rw [← pow_add,he]]
    field_simp
  rw [hid]
  have hpowH : H^(P-s) ≤ H^P := pow_le_pow_right₀ hH (Nat.sub_le P s)
  have hpowd : d^(P-(m+l+s)) ≤ d^(P-L) :=
    pow_le_pow_of_le_one hd.le hd1 (by omega)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hpowH (by positivity)
  · exact hpowd
  · exact pow_nonneg hd.le _
  · positivity

/-- The actual signed flux descendant loses at most 2j+1 shape powers. -/
theorem signed_flux_term_collision_power {n j : ℕ} (σ : ℂ)
    (T : SourceJetTerm (n+1)) (p q i : Fin (n+1))
    (hT : T ∈ sourceJetTerms p q j) (v θ : ℝ) (s : ℂ)
    (w : AngularSpace n → ℝ) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ)
    (u : AngularSpace n) (h : ActualJetPoint v θ p q s u)
    (hP : 2*j+1 ≤ (n+1)*n)
    (H W A B : ℝ) (hH : 1 ≤ H) (hW : 0 ≤ W) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hd : 0 < allBranchExteriorDiameter u) (hd1 : allBranchExteriorDiameter u ≤ 1)
    (hw : ‖cutoffJet T.cutoff w u‖/
      ‖selectedDifferenceCLM p q (s,chartMap v θ s u)‖^(T.pole+1) ≤
        W/allBranchExteriorDiameter u^(T.pole+1+T.cutoff.length))
    (hreg : ‖(fieldFluxTerm T p q i).regularPart (s,chartMap v θ s u)‖ ≤ A)
    (hnum : ‖numeratorJet T.numerator Q (s,chartMap v θ s u)‖ ≤
      B*(H*allBranchExteriorDiameter u)^((n+1)*n-(spatialWord T.numerator).length)) :
    ‖actualField v θ p q s u i*signedSourceValue σ T p q v θ w Q s u‖ ≤
      (W*A*B*H^((n+1)*n))*allBranchExteriorDiameter u^((n+1)*n-(2*j+1))*
        (‖chartJacobian v θ s u‖/‖signedRegularKernel σ s (chartMap v θ s u)‖) := by
  rw [← signedSourceValue_fieldFluxTerm σ T p q i v θ w Q s u h]
  have hb := signedSourceValue_norm σ (fieldFluxTerm T p q i) p q v θ w Q s u
    (W/allBranchExteriorDiameter u^(T.pole+1+T.cutoff.length)) A
    (B*(H*allBranchExteriorDiameter u)^((n+1)*n-(spatialWord T.numerator).length))
    (by positivity) hA hw hreg hnum
  have hc := collision_power_budget (T.pole+1) T.cutoff.length
    (spatialWord T.numerator).length ((n+1)*n) (2*j+1)
    (fieldFluxTerm_filtration p q i T hT) hP (allBranchExteriorDiameter u) H W A B
    hd hd1 hH hW hA hB
  have hk : 0 ≤ ‖chartJacobian v θ s u‖/
      ‖signedRegularKernel σ s (chartMap v θ s u)‖ := by positivity
  apply hb.trans
  convert! mul_le_mul_of_nonneg_right hc hk using 1
  ring

end
end IsingBulk.HT.Lie
