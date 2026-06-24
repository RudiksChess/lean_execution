-- Main result: internal completeness of natural deduction (oracle-free).
import Thesis.Prop.Syntax
import Thesis.Prop.NaturalDeduction
import Thesis.Prop.Completeness
import Thesis.Prop.Main

-- Appendix (cross-validation against the Foundation library) builds as a
-- separate target `Thesis.Prop.CompletenessViaFoundation`; it is intentionally
-- not imported here because the full Mathlib + Foundation closures clash on a
-- duplicate `Matrix.map` declaration.
