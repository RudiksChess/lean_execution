import Thesis.Prop.BridgeToFoundation

namespace Thesis.Prop

theorem eval_tr (v : Valuation) : ∀ φ : Formula, eval v φ ↔ Sat v (tr φ) := by
  intro φ
  induction φ with
  | atom s => simp [eval, tr, Sat]
  | neg p ih =>
      simp [eval, tr, Sat, ih]
  | impl p q ihp ihq =>
      simp [eval, tr, Sat, ihp, ihq]
      tauto

end Thesis.Prop
