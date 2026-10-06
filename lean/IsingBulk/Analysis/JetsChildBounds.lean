import IsingBulk.Analysis.JetsFieldBounds

/-! Finite-jet closure for each of the six existing semantic children.
The parent supplies one extra derivative. No singular coefficient is bounded. -/
namespace IsingBulk.Jets
noncomputable section

def stepScale (J M : ℕ) (F : ℝ) : ℝ :=
  1+2^J*F+((2^J)^2*F^2+(2^J)^3*M*F^2)

theorem stepScale_one_le (J M : ℕ) {F : ℝ} (hF : 0 ≤ F) : 1 ≤ stepScale J M F := by
  unfold stepScale
  have h₁ : 0 ≤ (2:ℝ)^J*F := by positivity
  have h₂ : 0 ≤ ((2:ℝ)^J)^2*F^2+((2:ℝ)^J)^3*M*F^2 := by positivity
  linarith

theorem stepScale_mono {J K M m : ℕ} {F G : ℝ} (hJ : J ≤ K) (hm : m ≤ M)
    (hF : 0 ≤ F) (hFG : F ≤ G) : stepScale J m F ≤ stepScale K M G := by
  unfold stepScale
  gcongr <;> norm_num

theorem stepScale_dimension (J M : ℕ) {B : ℝ} (hB : 0 ≤ B) (N : ℕ) (hN : 1 ≤ N) :
    stepScale J M (B*N^2) ≤ stepScale J M B*N^4 := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn₂ : (1:ℝ) ≤ (N:ℝ)^2 := one_le_pow₀ hn
  have hn₄ : (1:ℝ) ≤ (N:ℝ)^4 := one_le_pow₀ hn
  have h₂₄ : (N:ℝ)^2 ≤ (N:ℝ)^4 := by nlinarith [sq_nonneg ((N:ℝ)^2-1)]
  have hh := mul_le_mul_of_nonneg_left h₂₄ (show 0 ≤ (2:ℝ)^J*B by positivity)
  unfold stepScale
  nlinarith

theorem SourceJetTerm.child_jet_bound {N J : ℕ} (T : SourceJetTerm N) (p q : Fin N)
    (a : JetAction N) (z : ℂ × (Fin N → ℂ)) (F R : ℝ) (hF : 2 ≤ F)
    (hT : JetBound T.regularPart z (J+1) R)
    (hδ : JetBound (selectedDifferenceCLM p q) z J F)
    (hV : ∀ i, JetBound (fun t : ℂ × (Fin N → ℂ) => fieldRegularNumerator p q i t.1 t.2) z J F)
    (hB : ∀ i, JetBound (fun t : ℂ × (Fin N → ℂ) => residualRegularNumerator p q i t.1 t.2) z J F)
    (hD : JetBound (divergenceRegularNumerator p q) z J F) :
    JetBound (T.child p q a).regularPart z J (stepScale J T.pole F*R) := by
  have hR := hT.nonneg
  have hF₀ : 0 ≤ F := by linarith
  have hS := stepScale_one_le J T.pole hF₀
  have hPF : (2:ℝ)^J*F ≤ stepScale J T.pole F := by
    unfold stepScale
    have hh : 0 ≤ ((2:ℝ)^J)^2*F^2+((2:ℝ)^J)^3*T.pole*F^2 := by positivity
    linarith
  have hRR : R ≤ stepScale J T.pole F*R := le_mul_of_one_le_left hR hS
  have hprod : (2:ℝ)^J*F*R ≤ stepScale J T.pole F*R :=
    mul_le_mul_of_nonneg_right hPF hR
  have hr := hT.mono (show J ≤ J+1 by omega) le_rfl
  cases a with
  | coefficientParameter =>
    exact (hT.direction (1,0) parameterDirection_norm_le).mono le_rfl hRR
  | coefficientSpatial i =>
    have he := (JetBound.const (selectedDifferenceCLM p q (spatialDirection i)) z J).mono le_rfl
      ((selectedDifference_direction_bound p q i).trans hF)
    have hm : JetBound (fun _ : ℂ × (Fin N → ℂ) => (T.pole:ℂ)) z J (T.pole:ℝ) := by
      simpa using JetBound.const (T.pole:ℂ) z J
    have hp := (hδ.mul (hT.direction _ (spatialDirection_norm_le i))).sub ((hm.mul hr).mul he)
    have hb := (hB i).mul hp
    apply hb.mono le_rfl
    have hh : ((2:ℝ)^J)^2*F^2+((2:ℝ)^J)^3*T.pole*F^2 ≤ stepScale J T.pole F := by
      unfold stepScale
      have hh : 0 ≤ (2:ℝ)^J*F := by positivity
      linarith
    calc
      _ = (((2:ℝ)^J)^2*F^2+((2:ℝ)^J)^3*T.pole*F^2)*R := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hh hR
  | divergence => exact (hD.mul hr).mono le_rfl hprod
  | numeratorSpatial i => exact ((hB i).mul hr).mono le_rfl hprod
  | numeratorParameter => exact hr.mono le_rfl hRR
  | cutoffSpatial i => exact ((hV i).neg.mul hr).mono le_rfl hprod

/-- The budget j+r covers r output derivatives after j recurrence steps.
The primitive scalar budget is j+r+1 because div B already uses one derivative. -/
theorem sourceJetTerms_budget_bound {N : ℕ} (p q : Fin N) (j r : ℕ)
    (z : ℂ × (Fin N → ℂ)) (F : ℝ) (hF : 2 ≤ F)
    (hδ : JetBound (selectedDifferenceCLM p q) z (j+r) F)
    (hV : ∀ i, JetBound (fun t : ℂ × (Fin N → ℂ) => fieldRegularNumerator p q i t.1 t.2) z (j+r) F)
    (hB : ∀ i, JetBound (fun t : ℂ × (Fin N → ℂ) => residualRegularNumerator p q i t.1 t.2) z (j+r) F)
    (hD : JetBound (divergenceRegularNumerator p q) z (j+r) F) :
    ∀ k ≤ j, ∀ T ∈ sourceJetTerms p q k,
      JetBound T.regularPart z (j+r-k) ((stepScale (j+r) (2*j) F)^k) := by
  intro k
  induction k with
  | zero =>
    intro _ T hT
    simp only [sourceJetTerms,List.mem_singleton] at hT
    subst T
    simpa using JetBound.const (1:ℂ) z (j+r)
  | succ k ih =>
    intro hk T hT
    obtain ⟨S,hS,hT⟩ := List.mem_flatMap.mp hT
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hT
    have hparent := ih (by omega) S hS
    have he : j+r-k = (j+r-(k+1))+1 := by omega
    rw [he] at hparent
    have hbudget : j+r-(k+1) ≤ j+r := Nat.sub_le _ _
    have hb := S.child_jet_bound p q a z F _ hF hparent
      (hδ.mono hbudget le_rfl) (fun i => (hV i).mono hbudget le_rfl)
      (fun i => (hB i).mono hbudget le_rfl) (hD.mono hbudget le_rfl)
    apply hb.mono le_rfl
    have hm : S.pole ≤ 2*j := by
      have hh := (sourceJetTerms_valid p q k S hS).1
      omega
    have hs := stepScale_mono hbudget hm (show 0 ≤ F by linarith) le_rfl
    calc
      _ ≤ stepScale (j+r) (2*j) F*(stepScale (j+r) (2*j) F)^k :=
        mul_le_mul_of_nonneg_right hs (pow_nonneg
          (zero_le_one.trans (stepScale_one_le _ _ (by linarith))) k)
      _ = _ := by rw [pow_succ]; ring

end
end IsingBulk.Jets
