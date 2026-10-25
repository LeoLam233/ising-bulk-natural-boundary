import IsingBulk.Joint.Isotropic.LowCovering
import Mathlib.Topology.Covering.Deck

namespace IsingBulk.Joint
noncomputable section
open IsingBulk.Anisotropic

/-- Literal translation by an integral imaginary period on the full LT cell. -/
def lowDeckTranslation (n : ℤ) : omegaL 1 ≃ₜ omegaL 1 where
  toFun z := ⟨z.val+n*(2*Real.pi*Complex.I),(deck_mem_low_iff z n).mpr z.property⟩
  invFun z := ⟨z.val+(-n)*(2*Real.pi*Complex.I),by simpa only [Int.cast_neg] using (deck_mem_low_iff z (-n)).mpr z.property⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.add continuous_const).subtype_mk _

@[simp] theorem lowDeckTranslation_apply (n : ℤ) (z : omegaL 1) :
    (lowDeckTranslation n z : ℂ)=z.val+n*(2*Real.pi*Complex.I) := rfl

theorem lowDeckTranslation_mem (n : ℤ) : lowDeckTranslation n ∈ deck lowSinhMap := by
  apply funext
  intro z
  apply Subtype.ext
  change Complex.sinh (z.val+n*(2*Real.pi*Complex.I))=Complex.sinh z.val
  exact (sinh_fiber_low (lowDeckTranslation n z).property z.property).mpr ⟨n,rfl⟩

theorem lowDeckTranslation_injective : Function.Injective lowDeckTranslation := by
  intro n k he
  obtain ⟨z,hz,_⟩ := sinh_surjOn_low (by norm_num : 1<‖(2:ℂ)‖)
  have hz' := congrArg (fun e : omegaL 1 ≃ₜ omegaL 1 => (e ⟨z,hz⟩ : ℂ)) he
  simp only [lowDeckTranslation_apply] at hz'
  have hperiod : (2*Real.pi*Complex.I : ℂ)≠0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hi : (n:ℂ)=(k:ℂ) := mul_right_cancel₀ hperiod (add_left_cancel hz')
  exact_mod_cast hi

/-- Every deck map is one global integer translation. Fiberwise integers are
made global by uniqueness of continuous lifts on the connected source. -/
theorem low_deck_classification (g : deck lowSinhMap) :
    ∃! n : ℤ, (g : omegaL 1 ≃ₜ omegaL 1)=lowDeckTranslation n := by
  let : SimplyConnectedSpace (omegaL 1) := low_universal_covering.2
  obtain ⟨z,hz,_⟩ := sinh_surjOn_low (by norm_num : 1<‖(2:ℂ)‖)
  let z₀ : omegaL 1 := ⟨z,hz⟩
  have hs : Complex.sinh ((g : omegaL 1 ≃ₜ omegaL 1) z₀)=Complex.sinh z := by
    exact congrArg Subtype.val (congrFun g.property z₀)
  obtain ⟨n,hn⟩ := (sinh_fiber_low ((g : omegaL 1 ≃ₜ omegaL 1) z₀).property hz).mp hs
  have he : (g : omegaL 1 ≃ₜ omegaL 1)=lowDeckTranslation n := by
    apply Homeomorph.ext
    have hlift := lowSinhMap_isCoveringMap.eq_of_comp_eq
      (g : omegaL 1 ≃ₜ omegaL 1).continuous (lowDeckTranslation n).continuous
      (g.property.trans (lowDeckTranslation_mem n).symm) z₀ (Subtype.ext hn)
    exact congrFun hlift
  refine ⟨n,he,?_⟩
  intro k hk
  exact lowDeckTranslation_injective (hk.symm.trans he)

/-- The translation parametrization as an actual group homomorphism. -/
def lowDeckHom : Multiplicative ℤ →* deck lowSinhMap where
  toFun n := ⟨lowDeckTranslation n.toAdd,lowDeckTranslation_mem n.toAdd⟩
  map_one' := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro z
    apply Subtype.ext
    simp
  map_mul' n k := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro z
    apply Subtype.ext
    change z.val+((n*k).toAdd:ℂ)*(2*Real.pi*Complex.I)=
      (z.val+(k.toAdd:ℂ)*(2*Real.pi*Complex.I))+(n.toAdd:ℂ)*(2*Real.pi*Complex.I)
    change z.val+((n.toAdd+k.toAdd:ℤ):ℂ)*(2*Real.pi*Complex.I)=_
    rw [Int.cast_add]
    ring

theorem lowDeckHom_bijective : Function.Bijective lowDeckHom := by
  constructor
  · intro n k he
    have hh : lowDeckTranslation n.toAdd=lowDeckTranslation k.toAdd := congrArg Subtype.val he
    exact Multiplicative.toAdd.injective (lowDeckTranslation_injective hh)
  · intro g
    obtain ⟨n,hn,_⟩ := low_deck_classification g
    exact ⟨Multiplicative.ofAdd n,Subtype.ext hn.symm⟩

/-- The entire deck transformation group is the infinite cyclic group. -/
def lowDeckGroupEquiv : Multiplicative ℤ ≃* deck lowSinhMap :=
  MulEquiv.ofBijective lowDeckHom lowDeckHom_bijective

end
end IsingBulk.Joint
