import GroupUndecidability.Borisov.Model.Intersections
import GroupUndecidability.Borisov.Model.HNNModel

/-!
# The four-relator Borisov group as an iterated HNN extension

This file gives a public HNN model for the presentation called
`BorisovIntersections.G0`.  The orientation of the final equivalence is

```
  BorisovIntersections.G0 ≃* G0HNN.
```

The two power embeddings of the rank-two free group are

```
  rightPowerMap : d ↦ d,   e ↦ e⁴,
  leftPowerMap  : d ↦ d⁴, e ↦ e.
```

Thus each HNN stable letter satisfies `s * d = d⁴ * s` and
`s * e⁴ = e * s`, equivalently the two displayed relators in the paper.
-/

namespace Undecidability
namespace BorisovG0HNN

open Function
noncomputable section

/-! ## Public HNN-model API -/

abbrev Base := BorisovHNNModel.Base

def baseD : Base := BorisovHNNModel.d
def baseE : Base := BorisovHNNModel.e

def rightPowerMap : Base →* Base := BorisovHNNModel.alpha
def leftPowerMap : Base →* Base := BorisovHNNModel.beta

abbrev G1 := BorisovHNNModel.Stage1
abbrev G0HNN := BorisovHNNModel.Gamma3

def baseToG1 : Base →* G1 := BorisovHNNModel.of0
def g1ToG0HNN : G1 →* G0HNN := BorisovHNNModel.of1
def baseToG0HNN : Base →* G0HNN := g1ToG0HNN.comp baseToG1

def hnnD : G0HNN := BorisovHNNModel.d3
def hnnE : G0HNN := BorisovHNNModel.e3
def hnnS1 : G0HNN := BorisovHNNModel.s1_3
def hnnS2 : G0HNN := BorisovHNNModel.s2_3

theorem hnn_d_four_mul_s1 : hnnD ^ 4 * hnnS1 = hnnS1 * hnnD :=
  BorisovHNNModel.gamma3_d_four_mul_s1

theorem hnn_e_mul_s1 : hnnE * hnnS1 = hnnS1 * hnnE ^ 4 :=
  BorisovHNNModel.gamma3_e_mul_s1

theorem hnn_d_four_mul_s2 : hnnD ^ 4 * hnnS2 = hnnS2 * hnnD :=
  BorisovHNNModel.gamma3_d_four_mul_s2

theorem hnn_e_mul_s2 : hnnE * hnnS2 = hnnS2 * hnnE ^ 4 :=
  BorisovHNNModel.gamma3_e_mul_s2

/-! ## The homomorphism from the presentation to the HNN model -/

def hnnGenerator : Fin 4 → G0HNN := ![hnnD, hnnE, hnnS1, hnnS2]

private theorem hnn_sD_relation (s : G0HNN)
    (h : hnnD ^ 4 * s = s * hnnD) :
    s⁻¹ * hnnD ^ 4 * s = hnnD := by
  calc
    s⁻¹ * hnnD ^ 4 * s = s⁻¹ * (hnnD ^ 4 * s) := by
      simp only [mul_assoc]
    _ = s⁻¹ * (s * hnnD) := by rw [h]
    _ = hnnD := by simp

private theorem hnn_sE_relation (s : G0HNN)
    (h : hnnE * s = s * hnnE ^ 4) :
    s⁻¹ * hnnE * s = hnnE ^ 4 := by
  calc
    s⁻¹ * hnnE * s = s⁻¹ * (hnnE * s) := by
      simp only [mul_assoc]
    _ = s⁻¹ * (s * hnnE ^ 4) := by rw [h]
    _ = hnnE ^ 4 := by simp

private theorem hnn_relators :
    ∀ r ∈ BorisovIntersections.presentation.relSet,
      FreeGroup.lift hnnGenerator r = 1 := by
  rintro r ⟨i, rfl⟩
  fin_cases i
  · apply (Word.eval_relation_eq_one_iff hnnGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sDRelator, BorisovIntersections.dWord,
      BorisovIntersections.s1Word, hnnGenerator, mul_assoc] using
      hnn_sD_relation hnnS1 hnn_d_four_mul_s1
  · apply (Word.eval_relation_eq_one_iff hnnGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sERelator, BorisovIntersections.eWord,
      BorisovIntersections.s1Word, hnnGenerator, mul_assoc] using
      hnn_sE_relation hnnS1 hnn_e_mul_s1
  · apply (Word.eval_relation_eq_one_iff hnnGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sDRelator, BorisovIntersections.dWord,
      BorisovIntersections.s2Word, hnnGenerator, mul_assoc] using
      hnn_sD_relation hnnS2 hnn_d_four_mul_s2
  · apply (Word.eval_relation_eq_one_iff hnnGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sERelator, BorisovIntersections.eWord,
      BorisovIntersections.s2Word, hnnGenerator, mul_assoc] using
      hnn_sE_relation hnnS2 hnn_e_mul_s2

def toHNN : BorisovIntersections.G0 →* G0HNN :=
  PresentedGroup.toGroup hnn_relators

@[simp] theorem toHNN_of (i : Fin 4) :
    toHNN (PresentedGroup.of i) = hnnGenerator i :=
  PresentedGroup.toGroup.of hnn_relators

/-! ## The homomorphism from the HNN model to the presentation -/

def presentedD : BorisovIntersections.G0 := BorisovIntersections.d
def presentedE : BorisovIntersections.G0 := BorisovIntersections.e
def presentedS1 : BorisovIntersections.G0 :=
  BorisovIntersections.evalWord BorisovIntersections.s1Word
def presentedS2 : BorisovIntersections.G0 :=
  BorisovIntersections.evalWord BorisovIntersections.s2Word

@[simp] theorem presentedD_eq_of :
    presentedD = PresentedGroup.of (0 : Fin 4) := by
  simp [presentedD, BorisovIntersections.d, BorisovIntersections.evalWord,
    BorisovIntersections.dWord, FP.evalWord]

@[simp] theorem presentedE_eq_of :
    presentedE = PresentedGroup.of (1 : Fin 4) := by
  simp [presentedE, BorisovIntersections.e, BorisovIntersections.evalWord,
    BorisovIntersections.eWord, FP.evalWord]

@[simp] theorem presentedS1_eq_of :
    presentedS1 = PresentedGroup.of (2 : Fin 4) := by
  simp [presentedS1, BorisovIntersections.evalWord,
    BorisovIntersections.s1Word, FP.evalWord]

@[simp] theorem presentedS2_eq_of :
    presentedS2 = PresentedGroup.of (3 : Fin 4) := by
  simp [presentedS2, BorisovIntersections.evalWord,
    BorisovIntersections.s2Word, FP.evalWord]

private theorem presented_s1D :
    presentedS1⁻¹ * presentedD ^ 4 * presentedS1 = presentedD := by
  have h := BorisovIntersections.presentation.relator_eq_one (0 : Fin 4)
  change Word.eval (fun i : Fin 4 =>
      (PresentedGroup.of i : BorisovIntersections.G0))
    (BorisovIntersections.presentation.relator 0) = 1 at h
  have h' : Word.eval (fun i : Fin 4 =>
      (PresentedGroup.of i : BorisovIntersections.G0))
      (BorisovIntersections.sDRelator BorisovIntersections.s1Word) = 1 := by
    simpa [BorisovIntersections.presentation] using h
  change Word.eval (fun i : Fin 4 =>
      (PresentedGroup.of i : BorisovIntersections.G0))
      (Word.relation
        (Word.product [Word.inverse BorisovIntersections.s1Word,
          Word.pow BorisovIntersections.dWord 4,
          BorisovIntersections.s1Word])
        BorisovIntersections.dWord) = 1 at h'
  rw [Word.eval_relation_eq_one_iff] at h'
  rw [presentedD_eq_of, presentedS1_eq_of]
  simpa [BorisovIntersections.dWord, BorisovIntersections.s1Word,
    mul_assoc] using h'

private theorem presented_s1E :
    presentedS1⁻¹ * presentedE * presentedS1 = presentedE ^ 4 := by
  have h := BorisovIntersections.presentation.relator_eq_one (1 : Fin 4)
  change Word.eval (fun i : Fin 4 =>
      (PresentedGroup.of i : BorisovIntersections.G0))
    (BorisovIntersections.presentation.relator 1) = 1 at h
  have h' : Word.eval (fun i : Fin 4 =>
      (PresentedGroup.of i : BorisovIntersections.G0))
      (BorisovIntersections.sERelator BorisovIntersections.s1Word) = 1 := by
    simpa [BorisovIntersections.presentation] using h
  change Word.eval (fun i : Fin 4 =>
      (PresentedGroup.of i : BorisovIntersections.G0))
      (Word.relation
        (Word.product [Word.inverse BorisovIntersections.s1Word,
          BorisovIntersections.eWord, BorisovIntersections.s1Word])
        (Word.pow BorisovIntersections.eWord 4)) = 1 at h'
  rw [Word.eval_relation_eq_one_iff] at h'
  rw [presentedE_eq_of, presentedS1_eq_of]
  simpa [BorisovIntersections.eWord, BorisovIntersections.s1Word,
    mul_assoc] using h'

private theorem presented_s2D :
    presentedS2⁻¹ * presentedD ^ 4 * presentedS2 = presentedD := by
  have h := BorisovIntersections.presentation.relator_eq_one (2 : Fin 4)
  change Word.eval (fun i : Fin 4 =>
      (PresentedGroup.of i : BorisovIntersections.G0))
    (BorisovIntersections.presentation.relator 2) = 1 at h
  have h' : Word.eval (fun i : Fin 4 =>
      (PresentedGroup.of i : BorisovIntersections.G0))
      (BorisovIntersections.sDRelator BorisovIntersections.s2Word) = 1 := by
    simpa [BorisovIntersections.presentation] using h
  change Word.eval (fun i : Fin 4 =>
      (PresentedGroup.of i : BorisovIntersections.G0))
      (Word.relation
        (Word.product [Word.inverse BorisovIntersections.s2Word,
          Word.pow BorisovIntersections.dWord 4,
          BorisovIntersections.s2Word])
        BorisovIntersections.dWord) = 1 at h'
  rw [Word.eval_relation_eq_one_iff] at h'
  rw [presentedD_eq_of, presentedS2_eq_of]
  simpa [BorisovIntersections.dWord, BorisovIntersections.s2Word,
    mul_assoc] using h'

private theorem presented_s2E :
    presentedS2⁻¹ * presentedE * presentedS2 = presentedE ^ 4 := by
  have h := BorisovIntersections.presentation.relator_eq_one (3 : Fin 4)
  change Word.eval (fun i : Fin 4 =>
      (PresentedGroup.of i : BorisovIntersections.G0))
    (BorisovIntersections.presentation.relator 3) = 1 at h
  have h' : Word.eval (fun i : Fin 4 =>
      (PresentedGroup.of i : BorisovIntersections.G0))
      (BorisovIntersections.sERelator BorisovIntersections.s2Word) = 1 := by
    simpa [BorisovIntersections.presentation] using h
  change Word.eval (fun i : Fin 4 =>
      (PresentedGroup.of i : BorisovIntersections.G0))
      (Word.relation
        (Word.product [Word.inverse BorisovIntersections.s2Word,
          BorisovIntersections.eWord, BorisovIntersections.s2Word])
        (Word.pow BorisovIntersections.eWord 4)) = 1 at h'
  rw [Word.eval_relation_eq_one_iff] at h'
  rw [presentedE_eq_of, presentedS2_eq_of]
  simpa [BorisovIntersections.eWord, BorisovIntersections.s2Word,
    mul_assoc] using h'

private theorem presented_s1_mul_d :
    presentedS1 * presentedD = presentedD ^ 4 * presentedS1 := by
  calc
    presentedS1 * presentedD =
        presentedS1 * (presentedS1⁻¹ * presentedD ^ 4 * presentedS1) := by
          rw [presented_s1D]
    _ = presentedD ^ 4 * presentedS1 := by group

private theorem presented_s1_mul_e_four :
    presentedS1 * presentedE ^ 4 = presentedE * presentedS1 := by
  calc
    presentedS1 * presentedE ^ 4 =
        presentedS1 * (presentedS1⁻¹ * presentedE * presentedS1) := by
          rw [presented_s1E]
    _ = presentedE * presentedS1 := by group

private theorem presented_s2_mul_d :
    presentedS2 * presentedD = presentedD ^ 4 * presentedS2 := by
  calc
    presentedS2 * presentedD =
        presentedS2 * (presentedS2⁻¹ * presentedD ^ 4 * presentedS2) := by
          rw [presented_s2D]
    _ = presentedD ^ 4 * presentedS2 := by group

private theorem presented_s2_mul_e_four :
    presentedS2 * presentedE ^ 4 = presentedE * presentedS2 := by
  calc
    presentedS2 * presentedE ^ 4 =
        presentedS2 * (presentedS2⁻¹ * presentedE * presentedS2) := by
          rw [presented_s2E]
    _ = presentedE * presentedS2 := by group

def baseToPresented : Base →* BorisovIntersections.G0 :=
  FreeGroup.lift ![presentedD, presentedE]

@[simp] theorem baseToPresented_baseD :
    baseToPresented baseD = presentedD := by
  simp [baseToPresented, baseD, BorisovHNNModel.d]

@[simp] theorem baseToPresented_baseE :
    baseToPresented baseE = presentedE := by
  simp [baseToPresented, baseE, BorisovHNNModel.e]

private theorem power_embedding_relation
    (s : BorisovIntersections.G0)
    (hd : s * presentedD = presentedD ^ 4 * s)
    (he : s * presentedE ^ 4 = presentedE * s) (x : Base) :
    s * baseToPresented (rightPowerMap x) =
      baseToPresented (leftPowerMap x) * s := by
  have hconj :
      (MulAut.conj s).toMonoidHom.comp
          (baseToPresented.comp rightPowerMap) =
        baseToPresented.comp leftPowerMap := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i
    · change s * presentedD * s⁻¹ = presentedD ^ 4
      calc
        s * presentedD * s⁻¹ = (presentedD ^ 4 * s) * s⁻¹ := by
          rw [hd]
        _ = presentedD ^ 4 := by simp
    · change s * presentedE ^ 4 * s⁻¹ = presentedE
      calc
        s * presentedE ^ 4 * s⁻¹ = (presentedE * s) * s⁻¹ := by
          rw [he]
        _ = presentedE := by simp
  have hx := DFunLike.congr_fun hconj x
  change s * baseToPresented (rightPowerMap x) * s⁻¹ =
    baseToPresented (leftPowerMap x) at hx
  calc
    s * baseToPresented (rightPowerMap x) =
        (s * baseToPresented (rightPowerMap x) * s⁻¹) * s := by
          group
    _ = baseToPresented (leftPowerMap x) * s := by rw [hx]

private theorem first_lift_condition
    (a : BorisovHNNModel.A0) :
    presentedS1 * baseToPresented (a : Base) =
      baseToPresented (BorisovHNNModel.phi0 a : Base) * presentedS1 := by
  obtain ⟨x, rfl⟩ := BorisovHNNModel.inA0.surjective a
  simpa [rightPowerMap, leftPowerMap] using
    power_embedding_relation presentedS1 presented_s1_mul_d
    presented_s1_mul_e_four x

def g1ToPresented : G1 →* BorisovIntersections.G0 :=
  HNNExtension.lift baseToPresented presentedS1 first_lift_condition

@[simp] theorem g1ToPresented_of (x : Base) :
    g1ToPresented (baseToG1 x) = baseToPresented x := by
  simp [g1ToPresented, baseToG1, BorisovHNNModel.of0]

@[simp] theorem g1ToPresented_s1 :
    g1ToPresented BorisovHNNModel.s1 = presentedS1 := by
  simp [g1ToPresented, BorisovHNNModel.s1]

private theorem second_lift_condition
    (a : BorisovHNNModel.A1) :
    presentedS2 * g1ToPresented (a : G1) =
      g1ToPresented (BorisovHNNModel.phi1 a : G1) * presentedS2 := by
  obtain ⟨a0, rfl⟩ := BorisovHNNModel.inA1.surjective a
  obtain ⟨x, rfl⟩ := BorisovHNNModel.inA0.surjective a0
  simpa [rightPowerMap, leftPowerMap, g1ToPresented,
    BorisovHNNModel.of0] using
    power_embedding_relation presentedS2 presented_s2_mul_d
    presented_s2_mul_e_four x

def fromHNN : G0HNN →* BorisovIntersections.G0 :=
  HNNExtension.lift g1ToPresented presentedS2 second_lift_condition

@[simp] theorem fromHNN_of (x : G1) :
    fromHNN (g1ToG0HNN x) = g1ToPresented x := by
  simp [fromHNN, g1ToG0HNN, BorisovHNNModel.of1]

@[simp] theorem fromHNN_hnnD : fromHNN hnnD = presentedD := by
  change fromHNN (g1ToG0HNN (baseToG1 baseD)) = presentedD
  rw [fromHNN_of, g1ToPresented_of, baseToPresented_baseD]

@[simp] theorem fromHNN_hnnE : fromHNN hnnE = presentedE := by
  change fromHNN (g1ToG0HNN (baseToG1 baseE)) = presentedE
  rw [fromHNN_of, g1ToPresented_of, baseToPresented_baseE]

@[simp] theorem fromHNN_hnnS1 : fromHNN hnnS1 = presentedS1 := by
  change fromHNN (g1ToG0HNN BorisovHNNModel.s1) = presentedS1
  rw [fromHNN_of, g1ToPresented_s1]

@[simp] theorem fromHNN_hnnS2 : fromHNN hnnS2 = presentedS2 := by
  simp [fromHNN, hnnS2, BorisovHNNModel.s2_3]

@[simp] theorem toHNN_presentedD : toHNN presentedD = hnnD := by
  rw [presentedD_eq_of, toHNN_of]
  rfl

@[simp] theorem toHNN_presentedE : toHNN presentedE = hnnE := by
  rw [presentedE_eq_of, toHNN_of]
  rfl

@[simp] theorem toHNN_presentedS1 : toHNN presentedS1 = hnnS1 := by
  rw [presentedS1_eq_of, toHNN_of]
  rfl

@[simp] theorem toHNN_presentedS2 : toHNN presentedS2 = hnnS2 := by
  rw [presentedS2_eq_of, toHNN_of]
  rfl

theorem fromHNN_comp_toHNN :
    fromHNN.comp toHNN = MonoidHom.id BorisovIntersections.G0 := by
  apply PresentedGroup.ext
  intro i
  fin_cases i <;> simp [hnnGenerator]

private theorem toHNN_comp_g1ToPresented :
    toHNN.comp g1ToPresented = g1ToG0HNN := by
  apply HNNExtension.hom_ext
  · apply FreeGroup.ext_hom
    intro i
    fin_cases i
    · change toHNN (g1ToPresented (baseToG1 baseD)) =
        g1ToG0HNN (baseToG1 baseD)
      rw [g1ToPresented_of, baseToPresented_baseD, toHNN_presentedD]
      rfl
    · change toHNN (g1ToPresented (baseToG1 baseE)) =
        g1ToG0HNN (baseToG1 baseE)
      rw [g1ToPresented_of, baseToPresented_baseE, toHNN_presentedE]
      rfl
  · change toHNN (g1ToPresented BorisovHNNModel.s1) =
      g1ToG0HNN BorisovHNNModel.s1
    rw [g1ToPresented_s1, toHNN_presentedS1]
    rfl

theorem toHNN_comp_fromHNN :
    toHNN.comp fromHNN = MonoidHom.id G0HNN := by
  apply HNNExtension.hom_ext
  · apply MonoidHom.ext
    intro x
    change toHNN (fromHNN (g1ToG0HNN x)) = g1ToG0HNN x
    rw [fromHNN_of]
    exact DFunLike.congr_fun toHNN_comp_g1ToPresented x
  · change toHNN (fromHNN hnnS2) = hnnS2
    rw [fromHNN_hnnS2, toHNN_presentedS2]

/-- The concrete four-generator, four-relator presentation is the iterated
HNN extension above.  The forward direction sends the four presentation
generators to `hnnD`, `hnnE`, `hnnS1`, and `hnnS2`. -/
noncomputable def g0Equiv : BorisovIntersections.G0 ≃* G0HNN :=
  MonoidHom.toMulEquiv toHNN fromHNN
    fromHNN_comp_toHNN toHNN_comp_fromHNN

@[simp] theorem g0Equiv_apply (x : BorisovIntersections.G0) :
    g0Equiv x = toHNN x := rfl

end
end BorisovG0HNN
end Undecidability
