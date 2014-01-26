(** A first proof with Coq (Frobenius rule)
    From Andrej Bauer's YouTube tutorial:
    http://youtu.be/z861PoZPGqk

    Note that Coq can prove this one automatically.  
    Try this instead of the proof below:

        Proof.
          firstorder.
        Qed.
  
    Then, to see what the proof looks like, evaluate the line

        Print frobenius.
*)
Theorem frobenius (A : Set) (p : A -> Prop) (q : Prop) :
  (exists x : A, q /\ p x) <-> (q /\ exists x : A, p x).
Proof.
  split.
  intros [y [H1 H2]].
  split.
  assumption.
  exists y.
  assumption.
  intros [H1 [y H2]].
  exists y.
  split; assumption.
Qed.

Check frobenius.
Print frobenius.