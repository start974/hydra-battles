From hydras Require Import OrdinalNotations.ON_Generic.
From Coq Require Import Relations.

Open Scope ON_scope.

Section Proofs_of_lt_succ_le.
  
  Context (A:Type)
          (lt : relation A)
          (compare : A -> A -> comparison)
          (On : ON lt compare).

  Section Proofs.
    Variables alpha beta : A.
    
    (** beta is a successor of alpha *)
    
    Hypothesis Halphabeta : Successor beta alpha.

    
    Lemma lt_succ_le : forall gamma, gamma o< beta -> gamma o<= alpha.
    Proof.
    intros gamma HGammaBeta.
    destruct (lt_eq_lt_dec gamma alpha) as [[Hlt | Heq] | Hgt].
    - now left.
    - subst. right.
    - exfalso. destruct Halphabeta as (HleqAlphaBeta, HAlphaBeta). 
      now apply (HAlphaBeta gamma).
    Qed.

  End Proofs.

End Proofs_of_lt_succ_le.



