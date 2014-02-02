(** The dual Frobenius rule.
    From Andrej Bauer's YouTube tutorial:
    http://www.youtube.com/watch?v=tZRAFKIv6Js&feature=share&list=PLDD40A96C2ED54E99&index=4

*)
Definition lem := forall p, p \/ ~p.
Definition frobenius := forall (A : Set) (p : A -> Prop) (q : Prop),
  (forall x : A, q \/ p x) <-> (q \/ forall x : A, p x).

Theorem lem_to_frobenius : lem -> frobenius.
Proof.
  unfold lem, frobenius.
  firstorder.
  assert (G := H q).
  destruct G.
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

(**
    `firstorder` doesn't work because the implication from left to right in this case requires lem.
    When a proof requires classical reasoning, Coq will not do it automatically.  
    Coq does intuitionistic logic automatically, but not classical logic.
*)

