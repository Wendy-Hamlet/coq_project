From SimpleC.EE Require Import array_auto_goal array_auto_proof_auto array_auto_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include uint_array_strategy_proof.
  Include undef_uint_array_strategy_proof.
  Include array_shape_strategy_proof.
  Include sll_shape_strategy_proof.
  Include array_auto_proof_auto.
  Include array_auto_proof_manual.
End VC_Correctness.
