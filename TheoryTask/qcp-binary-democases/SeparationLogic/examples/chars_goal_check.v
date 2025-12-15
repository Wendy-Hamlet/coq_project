From SimpleC.EE Require Import chars_goal chars_proof_auto chars_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include char_array_strategy_proof.
  Include chars_proof_auto.
  Include chars_proof_manual.
End VC_Correctness.
