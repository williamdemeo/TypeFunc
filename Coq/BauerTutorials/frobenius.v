(** A first proof with Coq (Frobenius rule)
    From Andrej Bauer's YouTube tutorial:
    http://youtu.be/z861PoZPGqk

*)
Theorem frobenius (A : Set) (p : A -> Prop) (q : Prop) :
  (exists x : A, q /\ p x) <-> (q /\ exists x : A, p x).
Proof.
  split.                   (* Split the iff into two parts. *)
  intros [y [H1 H2]].      (* Introduce an instance of the antecedent. *)
                           (* That is, y in A such that q and p y. *)
  split.                   (* Split the consequent. *)
  assumption.              (* First subgoal is q, but that is a hyp. *)
  exists y.                (* For next subgoal, exists x : A, p x, plug in y. *)
  assumption.              (* Then p y is an hypothesis. *)
  intros [H1 [y H2]].
  exists y.
  split.
  assumption.
  assumption.
Qed.

Check frobenius.
Print frobenius.
(**
    Remarks:
    1. The last subgoal was q /\ p y, and these both appeared 
       as hypotheses above the line, so you can just type auto 
       and Coq will complete the proof.

    2. Coq can prove the Frobenius Theorem automatically.  
    Try this instead of the proof above:

        Proof.
          firstorder.
        Qed.
  
    Then, to see what the proof looks like, evaluate the line

        Print frobenius.
*)