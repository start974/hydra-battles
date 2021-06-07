From hydras Require Import OrdinalNotations.ON_Generic.
From Coq Require Import Relations.


(** Prove that, in any ordinal notation, every ordinal has 
     at most one predecessor and one successor *)

Section Proofs_of_unicity.
  
Context (A:Type)
        (lt : relation A)
        (compare : A -> A -> comparison)
        (On : ON lt compare).

(** Please remind that [Successor beta alpha] must be read as
    "[beta] is a successor of [alpha]" *)

Lemma Successor_unicity (alpha beta gamma : A):
  Successor beta alpha ->
  Successor gamma alpha ->
  gamma = beta.
Proof.
  intros (leqBetaAlpha, HBetaAlpha) (leqGammaAlpha, HGammaAlpha).
  destruct (lt_eq_lt_dec gamma beta) as [[Hlt | Heq] | Hgt].
  - exfalso. now apply (HBetaAlpha gamma).
  - assumption.
  - exfalso. now apply (HGammaAlpha beta).
Qed.

Lemma Predecessor_unicity (alpha beta gamma : A):
  Successor beta alpha ->
  Successor beta gamma ->
  gamma = alpha.
Proof.
  intros (leqBetaAlpha, HBetaAlpha) (leqBetaGamma, HBetaGamma).
  destruct (lt_eq_lt_dec gamma alpha) as [[Hlt | Heq] | Hgt].
  - exfalso. now apply (HBetaGamma alpha).
  - assumption.
  - exfalso. now apply (HBetaAlpha gamma).
Qed.
.



End Proofs_of_unicity.


