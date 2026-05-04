import Lean

/-
Simp-sets are sets of lemmas/definitions to be simplified together.  They must be registered in a
module prior to their use, so we register them all here.

Modules that want to either register items in these simp-sets, or use the simp-sets, should import
this module.
-/

register_simp_attr simp_circuit
register_simp_attr simp_FreeM
register_simp_attr simp_Triple
register_simp_attr simp_ZKBuilder
register_simp_attr simp_ZKSemantics
