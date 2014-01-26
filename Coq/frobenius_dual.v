(** The dual Frobenius rule.
    From Andrej Bauer's YouTube tutorial:
    http://www.youtube.com/watch?v=tZRAFKIv6Js&feature=share&list=PLDD40A96C2ED54E99&index=4

    firstorder doesn't work because implication from left to right requires lem.
*)
Definition lem := forall p, p \/ ~p.
Definition frobenius := forall (A : Set) (p : A -> Prop) (q : Prop),
  (forall x : A, q \/ p x) <-> (q \/ forall x : A, p x).

Theorem lem_to_frobenius : lem -> frobenius.
Proof.
  unfold lem, frobenius.
  firstorder.
  destruct (H q).
  left.
  assumption.
  right.
  intro.
  destruct (H0 x).
  elim H1.
  assumption.
  assumption.
Qed.

Check frobenius.
Print frobenius.